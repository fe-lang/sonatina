#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 1 || $1 != /* || -e $1 ]]; then
  echo 'Usage: bash install-toolchain.sh /absolute/new/installation-directory' >&2
  exit 1
fi
destination=$1
release=succinct-1.96.0-64bit-v2
case "$(uname -s)/$(uname -m)" in
  Darwin/arm64)
    host=aarch64-apple-darwin
    checksum=2ef4ca7fcb796bc01a352548841809562489e6bad5b99637ea1af215321dbf77 ;;
  Darwin/x86_64)
    host=x86_64-apple-darwin
    checksum=a5909912d18c076677a130aeb1cabff07e2302fa6e9c0b4b085da28207eb5228 ;;
  Linux/aarch64)
    host=aarch64-unknown-linux-gnu
    checksum=cf77553c41afac55aa2311ee8bade3e1f692986f4f6813d167c96a18642439eb ;;
  Linux/x86_64)
    host=x86_64-unknown-linux-gnu
    checksum=ff3afc3a6f22af93d162652972f254fcecf443ca4b2de18897312f19997fb94b ;;
  *) echo 'SP1 runtime linking requires a supported Linux or macOS host' >&2; exit 1 ;;
esac

archive=$(mktemp "${TMPDIR:-/tmp}/sonatina-sp1-archive.XXXXXX")
curl --fail --location --retry 3 \
  "https://github.com/succinctlabs/rust/releases/download/$release/rust-toolchain-$host.tar.gz" \
  --output "$archive"
if command -v sha256sum >/dev/null; then
  printf '%s  %s\n' "$checksum" "$archive" | sha256sum --check -
else
  printf '%s  %s\n' "$checksum" "$archive" | shasum -a 256 --check -
fi
mkdir -p "$(dirname "$destination")"
mkdir "$destination"
tar -xzf "$archive" -C "$destination"
printf 'Toolchain installed at %s\nArchive retained at %s\n' "$destination" "$archive"
