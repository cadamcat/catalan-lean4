#!/usr/bin/env bash
set -Eeuo pipefail
umask 022
mkdir -p /srv/catalan-audit/{downloads,evidence,logs,tools-src,audit}
trap 'rc=$?; printf "%s\n" "$rc" > /srv/catalan-audit/logs/bootstrap.exit; date -u +%FT%TZ > /srv/catalan-audit/logs/bootstrap.ended; exit "$rc"' EXIT
date -u +%FT%TZ > /srv/catalan-audit/logs/bootstrap.started
export DEBIAN_FRONTEND=noninteractive
export GOPATH=/srv/catalan-audit/go
export GOCACHE=/srv/catalan-audit/go-build-cache
export CARGO_HOME=/srv/catalan-audit/cargo
export LAKE_NO_CACHE=true
export LAKE_ARTIFACT_CACHE=false
export MATHLIB_NO_CACHE_ON_UPDATE=1
apt-get update -qq
apt-get install -y -qq --no-install-recommends git curl ca-certificates zstd xz-utils gcc g++ make pkg-config libssl-dev python3 python3-venv dbus-user-session iptables time nodejs npm
id verifier >/dev/null 2>&1 || useradd --create-home --uid 2000 --shell /bin/bash verifier
passwd -l verifier
chmod 0700 /home/verifier
loginctl enable-linger verifier
systemctl start user@2000.service
cd /srv/catalan-audit/downloads
curl --fail --location --retry 3 -o lean.tar.zst https://github.com/leanprover/lean4/releases/download/v4.33.1/lean-4.33.1-linux.tar.zst
printf '%s\n' '890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235  lean.tar.zst' | sha256sum -c -
mkdir -p /opt/lean-4.33.1
tar --zstd -xf lean.tar.zst -C /opt/lean-4.33.1 --strip-components=1
export PATH=/opt/lean-4.33.1/bin:/opt/go/bin:/opt/rust/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
lean --version
lake --version
python3 - <<'PY'
import urllib.request,json
from pathlib import Path
data=json.load(urllib.request.urlopen('https://go.dev/dl/?mode=json&include=all'))
release=next(r for r in data if r['version']=='go1.27.1')
item=next(f for f in release['files'] if f['filename']=='go1.27.1.linux-amd64.tar.gz')
Path('/srv/catalan-audit/evidence/go-release.json').write_text(json.dumps(item,indent=2)+'\n')
Path('go.sha256').write_text(item['sha256']+'  '+item['filename']+'\n')
PY
curl --fail --location --retry 3 -o go1.27.1.linux-amd64.tar.gz https://go.dev/dl/go1.27.1.linux-amd64.tar.gz
sha256sum -c go.sha256
tar -xzf go1.27.1.linux-amd64.tar.gz -C /opt
go version
rust_archive=rust-1.98.1-x86_64-unknown-linux-gnu.tar.xz
curl --fail --location --retry 3 -O "https://static.rust-lang.org/dist/$rust_archive"
curl --fail --location --retry 3 -O "https://static.rust-lang.org/dist/$rust_archive.sha256"
sha256sum -c "$rust_archive.sha256"
tar -xJf "$rust_archive"
./rust-1.98.1-x86_64-unknown-linux-gnu/install.sh --prefix=/opt/rust --without=rust-docs --disable-ldconfig
rustc --version
cargo --version
mkdir -p /opt/catalan-checkers
cd /srv/catalan-audit/tools-src
git clone https://github.com/Zouuup/landrun.git landrun
git -C landrun checkout --detach 811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
(cd landrun && go build -o /opt/catalan-checkers/landrun cmd/landrun/main.go)
git clone https://github.com/leanprover/lean4export.git lean4export
git -C lean4export checkout --detach 15f6055e299ad5b89345e533cc2192f4cc00f659
(cd lean4export && lake build lean4export)
cp lean4export/.lake/build/bin/lean4export /opt/catalan-checkers/
git clone https://github.com/leanprover/comparator.git comparator
git -C comparator checkout --detach 3927ad383f208ae977c340a91c48ac9b497d2097
(cd comparator && lake build comparator)
cp comparator/.lake/build/bin/comparator /opt/catalan-checkers/
git clone https://github.com/ammkrn/nanoda_lib.git nanoda_lib
git -C nanoda_lib checkout --detach 4c544ed4099c8227f07d5de77ad1e69fb0740a27
(cd nanoda_lib && cargo build --release --locked)
cp nanoda_lib/target/release/nanoda_bin /opt/catalan-checkers/
cp comparator/README.md /srv/catalan-audit/evidence/comparator-README.md
sha256sum /opt/catalan-checkers/* > /srv/catalan-audit/evidence/checker-binaries.sha256
for tool in landrun lean4export comparator nanoda_lib; do
  git -C "$tool" rev-parse HEAD
  git -C "$tool" status --porcelain
done > /srv/catalan-audit/evidence/tool-source-identity.txt
chmod -R go-w /opt/catalan-checkers /opt/lean-4.33.1 /opt/go /opt/rust
printf '%s\n' 'Trusted tool bootstrap completed; no submitted project has been cloned or compiled.'
