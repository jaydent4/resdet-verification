#!/usr/bin/env bash
# Machine-check the TLAPS proofs of the paper's Theorem 1 (safety) with its
# companions and of Theorem 2 (liveness). Local only: this does not launch,
# stop, or modify any TLC run.
#
# Every proof module is re-proved from scratch (no cached results) and must
# report all obligations proved with no missing proof (tlapm --strict). An
# audit first rejects axioms, omitted proofs, module-level assumptions, and
# local modules that are not checked here.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SPEC_DIR="$ROOT_DIR/spec"
TLAPM="${TLAPM:-$ROOT_DIR/tools/tlapm/bin/tlapm}"
THREADS="${TLAPS_THREADS:-4}"

# In dependency order. tlapm checks only the proofs of the module it is
# given, so each module is checked on its own.
MODULES=(
    ResdetFold
    ResdetDelivery
    ResdetPrefix
    ResdetValidity
    ResdetTheorems
    ResdetRequests
    ResdetApplied
    ResdetComplete
    ResdetLiveInv
    ResdetLiveProgress
    ResdetLiveEnabled
    ResdetLiveTermination
    ResdetLiveness
    ResdetContinuation
    ResdetPaperSafety
    ResdetPaperLive
    ResdetPaperLemma3
    ResdetPaperLemma45
    ResdetPaperTheorems
)

# The specifications the proofs are about, each with the name of its one
# permitted assumption about its constants.
SPECS=(
    "Resdet:ConstantAssumptions"
    "ResdetPaper:PaperAssumptions"
)

if [[ ! -x "$TLAPM" ]]; then
    bash "$ROOT_DIR/scripts/fetch-tlaps.sh"
fi

# ---------------------------------------------------------------------------
# Audit. tlapm trusts every fact it is handed: an AXIOM, a module-level
# ASSUME, a proof marked OMITTED, and any theorem of a module it was not
# asked to check. The checks below make sure none of those can carry the
# result. They are deliberately conservative and fail on anything unusual.
# ---------------------------------------------------------------------------
audit_failed=0
fail_audit() {
    printf 'Audit: %s\n' "$1" >&2
    audit_failed=1
}

# 1. Every local module is either the specification or a checked proof
#    module, and none shadows a standard or TLAPS library module.
for file in "$SPEC_DIR"/*.tla; do
    name="$(basename "$file" .tla)"
    known=0
    for spec in "${SPECS[@]}"; do
        [[ "$name" == "${spec%%:*}" ]] && known=1
    done
    for module in "${MODULES[@]}"; do
        [[ "$name" == "$module" ]] && known=1
    done
    if [[ "$known" -eq 0 ]]; then
        fail_audit "spec/$name.tla is neither a specification nor a checked proof module."
    fi
done
for library in Naturals Integers Reals Sequences FiniteSets Bags TLC TLAPS \
        NaturalsInduction WellFoundedInduction FiniteSetTheorems \
        SequenceTheorems FunctionTheorems Functions Folds BagsTheorems \
        RealTime; do
    if [[ -e "$SPEC_DIR/$library.tla" ]]; then
        fail_audit "spec/$library.tla shadows a library module."
    fi
done

# 2. A specification states no theorem (tlapm would accept it unproved)
#    and has exactly one assumption, the named one about its constants.
for spec in "${SPECS[@]}"; do
    name="${spec%%:*}"
    assumption="${spec##*:}"
    file="$SPEC_DIR/$name.tla"
    if [[ ! -f "$file" ]]; then
        fail_audit "missing specification spec/$name.tla."
        continue
    fi
    if grep -nE '\b(THEOREM|LEMMA|PROPOSITION|COROLLARY|AXIOM|ASSUMPTION|OMITTED)\b' \
            "$file"; then
        fail_audit "$name.tla states a theorem or axiom."
    fi
    assumes="$(grep -E '\bASSUME\b' "$file" || true)"
    if [[ "$assumes" != "ASSUME $assumption ==" ]]; then
        fail_audit "$name.tla must have exactly one ASSUME, $assumption."
    fi
done
if grep -n 'RECURSIVE' "$SPEC_DIR"/Resdet.tla "$SPEC_DIR"/ResdetPaper.tla \
        | grep -v 'TLAPS rejects'; then
    fail_audit 'A specification declares a RECURSIVE operator, which TLAPS rejects.'
fi

# 3. Proof modules contain no axiom and no omitted proof, at any
#    indentation, and every ASSUME is part of a theorem statement or of a
#    proof step: it either follows a step number or SUFFICES on its own
#    line, or opens the statement right after a THEOREM/LEMMA header.
for module in "${MODULES[@]}"; do
    file="$SPEC_DIR/$module.tla"
    if [[ ! -f "$file" ]]; then
        fail_audit "missing proof module spec/$module.tla."
        continue
    fi
    if grep -nE '\b(AXIOM|ASSUMPTION|OMITTED)\b' "$file"; then
        fail_audit "$module.tla contains an axiom or an omitted proof."
    fi
    if ! awk '
        /^[[:space:]]*$/ { next }
        /(^|[^A-Za-z0-9_])ASSUME([^A-Za-z0-9_]|$)/ {
            step = ($0 ~ /^[[:space:]]*<[0-9]+>[0-9A-Za-z]*\.?[[:space:]]+(SUFFICES[[:space:]]+)?ASSUME([^A-Za-z0-9_]|$)/)
            statement = ($0 ~ /^[[:space:]]+ASSUME([^A-Za-z0-9_]|$)/ &&
                         previous ~ /^(THEOREM|LEMMA)[[:space:]]+[A-Za-z0-9_]+[[:space:]]*==[[:space:]]*$/)
            if (!step && !statement) {
                printf "%s:%d: %s\n", FILENAME, FNR, $0
                bad = 1
            }
        }
        { previous = $0 }
        END { exit bad }
    ' "$file"; then
        fail_audit "$module.tla has an ASSUME outside a theorem statement or proof step."
    fi
done
# 4. No theorem or lemma name is used twice within one family of modules
#    (the modules about one specification extend each other). tlapm does
#    not reject a second theorem of the same name, and which one a later
#    citation refers to is then unclear.
for family in 'ResdetPaper' 'other'; do
    names=""
    for module in "${MODULES[@]}"; do
        case "$module" in
            ResdetPaper*) [[ "$family" == 'ResdetPaper' ]] || continue ;;
            *) [[ "$family" == 'other' ]] || continue ;;
        esac
        [[ -f "$SPEC_DIR/$module.tla" ]] || continue
        names+="$(grep -hE '^(THEOREM|LEMMA) +[A-Za-z0-9_]+ *==' \
            "$SPEC_DIR/$module.tla" | awk '{print $2}')"$'\n'
    done
    duplicates="$(printf '%s' "$names" | sort | uniq -d)"
    if [[ -n "$duplicates" ]]; then
        printf '%s\n' "$duplicates" >&2
        fail_audit "a theorem or lemma name is defined twice."
    fi
done

if [[ "$audit_failed" -ne 0 ]]; then
    exit 1
fi
printf 'Audit passed: no axioms, omitted proofs, stray assumptions, or unchecked modules.\n'

run_root="$(mktemp -d "${TMPDIR:-/tmp}/resdet-tlaps.XXXXXX")"
trap 'rm -rf "$run_root"' EXIT

total=0
for module in "${MODULES[@]}"; do
    log="$run_root/$module.log"
    printf '\n==> %s\n' "$module.tla"
    if ! (cd "$SPEC_DIR" && "$TLAPM" --cleanfp --strict \
            --threads "$THREADS" --cache-dir "$run_root/cache" \
            "$module.tla") >"$log" 2>&1; then
        grep -v '^$' "$log" | tail -60 >&2
        printf 'TLAPS failed on %s\n' "$module.tla" >&2
        exit 1
    fi
    summary="$(grep -E 'All [0-9]+ obligations? proved' "$log" | tail -1)"
    if [[ -z "$summary" ]] || grep -qE 'obligations? failed|Proof incomplete' "$log"; then
        grep -v '^$' "$log" | tail -60 >&2
        printf 'TLAPS did not prove every obligation of %s\n' "$module.tla" >&2
        exit 1
    fi
    count="$(printf '%s\n' "$summary" | grep -oE '[0-9]+' | head -1)"
    total=$((total + count))
    printf '%s\n' "${summary#*: }"
done

printf '\nAll TLAPS proofs checked: %d obligations in %d modules.\n' \
    "$total" "${#MODULES[@]}"
