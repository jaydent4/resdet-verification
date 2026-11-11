#!/usr/bin/env bash
# Project-local TLAPS (tlapm plus its bundled Zenon, Z3, Isabelle, and LS4);
# no profile changes and no global install.
#
# Upstream publishes native arm64 macOS builds only as the rolling
# "1.6.0-pre" release, whose assets are replaced on every new build. The
# checksums below pin the build these proofs were checked with (tlapm
# ff40755, published 2026-11-10). If upstream has rebuilt the asset, the
# checksum no longer matches and this script refuses to install it: review
# the new build, then update the checksum here.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
release=1.6.0-pre
case "$(uname -s)-$(uname -m)" in
  Darwin-arm64)
    platform=arm64-darwin
    checksum=76c2b7871fce30f26543e432d0e2cff506450fc90f70d18f7a032cf05a614a16 ;;
  Linux-x86_64)
    platform=x86_64-linux-gnu
    checksum=99db29f119cb6f43ffed653b212ba2d005e5bf8e242c53468876cb0d08da6bcc ;;
  *) echo 'Unsupported platform; install tlapm yourself and set TLAPM.' >&2; exit 1 ;;
esac
destination="$repo_root/tools/tlapm"
if [[ -x "$destination/bin/tlapm" ]]; then
  printf 'tlapm %s is already available at %s\n' \
    "$("$destination/bin/tlapm" --version)" "$destination"
  exit 0
fi
if [[ -e "$destination" ]]; then
  echo "Incomplete TLAPS installation at $destination; refusing to overwrite it." >&2
  exit 1
fi
mkdir -p "$repo_root/tools"
archive="$(mktemp "$repo_root/tools/tlapm-download.XXXXXX")"
trap 'rm -f "$archive"' EXIT
curl --fail --location --retry 3 --connect-timeout 20 \
  "https://github.com/tlaplus/tlapm/releases/download/$release/tlapm-$release-$platform.tar.gz" \
  --output "$archive"
if command -v sha256sum >/dev/null 2>&1; then
  actual="$(sha256sum "$archive" | awk '{print $1}')"
else
  actual="$(shasum -a 256 "$archive" | awk '{print $1}')"
fi
if [[ "$actual" != "$checksum" ]]; then
  echo "TLAPS archive checksum mismatch: expected $checksum, got $actual" >&2
  exit 1
fi
tar -xzf "$archive" -C "$repo_root/tools"
printf 'Installed tlapm %s at %s\n' \
  "$("$destination/bin/tlapm" --version)" "$destination"
