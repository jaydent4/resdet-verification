#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SPEC_DIR="$ROOT_DIR/spec"
JAR="${TLA2TOOLS_JAR:-$ROOT_DIR/tools/tla2tools.jar}"
JAVA_BIN="${JAVA_BIN:-java}"
MODE="${1:-all}"

if [[ ! -f "$JAR" ]]; then
    "$ROOT_DIR/scripts/fetch-tlc.sh"
fi

case "$MODE" in
    all|passing|mutants) ;;
    *)
        printf 'usage: %s [all|passing|mutants]\n' "$0" >&2
        exit 2
        ;;
esac

run_root="$(mktemp -d "${TMPDIR:-/tmp}/resdet-tlc.XXXXXX")"
trap 'rm -rf "$run_root"' EXIT

run_tlc() {
    local config="$1"
    local name="${config##*/}"
    name="${name%.cfg}"
    "$JAVA_BIN" -XX:+UseParallelGC -jar "$JAR" \
        -cleanup \
        -terse \
        -workers 1 \
        -metadir "$run_root/$name" \
        -config "$config" \
        Resdet
}

run_passing() {
    local configs=(
        ResdetCore.cfg
        ResdetStrict.cfg
        ResdetBatching.cfg
        ResdetFailures.cfg
        ResdetRetry.cfg
        ResdetFallback.cfg
        ResdetLiveness.cfg
    )
    for config in "${configs[@]}"; do
        local log="$run_root/${config%.cfg}.log"
        printf '\n==> PASS expected: %s\n' "$config"
        if ! (cd "$SPEC_DIR" && run_tlc "$config") >"$log" 2>&1; then
            cat "$log" >&2
            return 1
        fi
        grep -m 1 'Model checking completed' "$log"
        grep -m 1 -E \
            '[0-9]+ states generated, [0-9]+ distinct states found' \
            "$log"
    done
}

run_expected_failure() {
    local config="$1"
    local invariant="$2"
    local label="${3:-COUNTEREXAMPLE}"
    local log="$run_root/${config##*/}.log"

    printf '\n==> %s expected: %s (%s)\n' \
        "$label" "$config" "$invariant"
    if (cd "$SPEC_DIR" && run_tlc "$config") >"$log" 2>&1; then
        printf 'TLC unexpectedly accepted mutant %s\n' "$config" >&2
        cat "$log" >&2
        return 1
    fi
    if ! grep -q "$invariant" "$log"; then
        printf 'TLC failed, but not for expected invariant %s\n' \
            "$invariant" >&2
        cat "$log" >&2
        return 1
    fi
    grep -m 1 -E \
        "Invariant .*${invariant}|${invariant} is violated" \
        "$log" || true
}

run_mutants() {
    run_expected_failure mutants/NoDedup.cfg AtMostOnceDelivery
    run_expected_failure mutants/NonContiguous.cfg ProcessedPrefixLearned
    run_expected_failure mutants/AllDispatch.cfg AtMostOnePhysicalDispatch
    run_expected_failure mutants/NoQuorum.cfg SelectionJustified
    run_expected_failure mutants/EarlyDelivery.cfg AppliedPrefixCorrect
    run_expected_failure mutants/NoLeaderDirect.cfg ResponseAgreement
}

# A witness is a reachability check, not a mutant: the protocol is unchanged
# and TLC is expected to find a state that violates the stated non-invariant.
run_witnesses() {
    run_expected_failure witness/RetryConflict.cfg NoConflictingResponses \
        WITNESS
}

# ResdetPaper.tla, the paper-level specification, is checked through the
# finite instance in spec/paper-mc.
PAPER_DIR="$SPEC_DIR/paper-mc"

run_paper_tlc() {
    local config="$1"
    local name="${config##*/}"
    name="paper-${name%.cfg}"
    "$JAVA_BIN" -XX:+UseParallelGC "-DTLA-Library=$SPEC_DIR" -jar "$JAR" \
        -cleanup \
        -terse \
        -workers 1 \
        -metadir "$run_root/$name" \
        -config "$config" \
        MCResdetPaper
}

run_paper() {
    local config log
    for config in PaperSafety.cfg PaperLiveness.cfg PaperLiveness2.cfg; do
        log="$run_root/paper-${config%.cfg}.log"
        printf '\n==> PASS expected: paper-mc/%s\n' "$config"
        if ! (cd "$PAPER_DIR" && run_paper_tlc "$config") >"$log" 2>&1; then
            cat "$log" >&2
            return 1
        fi
        grep -m 1 'Model checking completed' "$log"
        grep -m 1 -E \
            '[0-9]+ states generated, [0-9]+ distinct states found' \
            "$log"
    done
    # Negative controls. Liveness must fail when leaders are replaced
    # forever although one is always in place, when the leader crashes and
    # none is elected, and when request deduplication survives a change of
    # leader.
    for config in witness/PaperLeaderFlapping.cfg \
            witness/PaperNoStableLeader.cfg \
            witness/PaperPersistentDedup.cfg; do
        log="$run_root/paper-${config##*/}.log"
        printf '\n==> LIVENESS VIOLATION expected: paper-mc/%s\n' "$config"
        if (cd "$PAPER_DIR" && run_paper_tlc "$config") >"$log" 2>&1; then
            printf 'TLC unexpectedly accepted %s\n' "$config" >&2
            cat "$log" >&2
            return 1
        fi
        if ! grep -q 'Temporal properties were violated' "$log"; then
            printf 'TLC failed on %s, but not with a liveness violation\n' \
                "$config" >&2
            cat "$log" >&2
            return 1
        fi
        grep -m 1 'Temporal properties were violated' "$log"
    done
}

if [[ "$MODE" == "all" || "$MODE" == "passing" ]]; then
    run_passing
    run_witnesses
    run_paper
fi
if [[ "$MODE" == "all" || "$MODE" == "mutants" ]]; then
    run_mutants
fi

printf '\nAll requested TLC checks behaved as expected.\n'
