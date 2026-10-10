# Cloud Lean setup from GitHub (no laptop needed)

A cloud chat can compile against the full pinned Mathlib in its own Linux
workspace by downloading the laptop's prebuilt oleans from a public GitHub
release. This replaces "stage the chunks from the laptop" in
TURING_PLAYBOOK.md section 3.3; everything else in 3.3 still applies.
The official checks are unchanged: the worker job of the final chain
(`jobs/` queue, see REPO_PROTOCOL.md) and `verify_golden_offline.bat`.

- Public repo (README only): https://github.com/fahad-96/turing-oleans
- Release: https://github.com/fahad-96/turing-oleans/releases/tag/mathlib-9944fe29-lean-4.33.0-rc1
- Lean toolchain `leanprover/lean4:v4.33.0-rc1`, Mathlib commit
  `9944fe2973b8dc0b86949101ed98232c07cd54a0`
- 11 archives, 2,051,755,958 bytes (about 2.05 GB) to download, about 5.95 GB
  extracted. Lean needs all three kinds: `oleans_*` (.olean, .olean.private),
  `server_01` (.olean.server), `ir_01` (.ir, .ir.sig).
- No login is needed. The downloads redirect from github.com to
  release-assets.githubusercontent.com (or objects.githubusercontent.com), so
  the workspace must be allowed to reach both.

## 1. Toolchain (about 900 MB)

```
mkdir -p ~/work/pkgs && cd ~/work
curl -L -f -o lean.zip https://github.com/leanprover/lean4/releases/download/v4.33.0-rc1/lean-4.33.0-rc1-linux.zip
unzip -q lean.zip && rm lean.zip
export PATH=$HOME/work/lean-4.33.0-rc1-linux/bin:$PATH
lean --version
```

(The zip unpacks to `lean-4.33.0-rc1-linux/`; `bin/lean` works directly. If the
folder name differs, adjust PATH.)

## 2. Oleans: download, verify, extract into one folder

```
cd ~/work
cat > SHA256SUMS <<'EOF'
8da32faf72bcacdbc23da5ee93de3635187ea531cdf29423e9d1aaae2acedd97  oleans_01.tgz
1c1bc3d37663ddf568e31747662c1df351436aac072e47918f41e7304cccfaa7  oleans_02.tgz
fbf8b1d16973736d2e91b090dde5b2f72e23d0673fb12e95da4557ab7623b85a  oleans_03.tgz
f1be865e1b0a9f617ea847a25d6099f079f1db2769142ebe2be690808a9b1cd1  oleans_04.tgz
fa1226e014e6f04ea9cbedb3ae78f7ca3a08284c390ddbd4adbcfd640ae0ae40  oleans_05.tgz
3901afb1d7d13d639b88f6a8588e6d5b49849c3f1575172cd527a8b882f93ee4  oleans_06.tgz
eefbc61c444bb1a81f4c45b88dd8015119b11e4929c5dd3f4c4843fb3397f146  oleans_07.tgz
346e4430d0ad666611e82ecc568c8adde81807b6f4007da9d2eeac5dabc446ea  oleans_08.tgz
349e0dbe8bfa0593f127f862c5038bfb110ad24037c62d32b2f42d5834076191  oleans_09.tgz
6b2df85074039219f2e5bcb0a458696c4cc6d451b6e483518bcd57da908c1086  server_01.tgz
6d3760e32bc0d1424354b9c5f50ea65dc39deb7c57452a918a2ec6ee41363b26  ir_01.tgz
EOF
```

Then one archive at a time (download, check, extract, delete - this keeps
the disk use low). Each line is independent; rerun a line that fails.

```
curl -L -f -O https://github.com/fahad-96/turing-oleans/releases/download/mathlib-9944fe29-lean-4.33.0-rc1/oleans_01.tgz && sha256sum -c --ignore-missing SHA256SUMS && tar -xzf oleans_01.tgz -C pkgs && rm oleans_01.tgz
curl -L -f -O https://github.com/fahad-96/turing-oleans/releases/download/mathlib-9944fe29-lean-4.33.0-rc1/oleans_02.tgz && sha256sum -c --ignore-missing SHA256SUMS && tar -xzf oleans_02.tgz -C pkgs && rm oleans_02.tgz
curl -L -f -O https://github.com/fahad-96/turing-oleans/releases/download/mathlib-9944fe29-lean-4.33.0-rc1/oleans_03.tgz && sha256sum -c --ignore-missing SHA256SUMS && tar -xzf oleans_03.tgz -C pkgs && rm oleans_03.tgz
curl -L -f -O https://github.com/fahad-96/turing-oleans/releases/download/mathlib-9944fe29-lean-4.33.0-rc1/oleans_04.tgz && sha256sum -c --ignore-missing SHA256SUMS && tar -xzf oleans_04.tgz -C pkgs && rm oleans_04.tgz
curl -L -f -O https://github.com/fahad-96/turing-oleans/releases/download/mathlib-9944fe29-lean-4.33.0-rc1/oleans_05.tgz && sha256sum -c --ignore-missing SHA256SUMS && tar -xzf oleans_05.tgz -C pkgs && rm oleans_05.tgz
curl -L -f -O https://github.com/fahad-96/turing-oleans/releases/download/mathlib-9944fe29-lean-4.33.0-rc1/oleans_06.tgz && sha256sum -c --ignore-missing SHA256SUMS && tar -xzf oleans_06.tgz -C pkgs && rm oleans_06.tgz
curl -L -f -O https://github.com/fahad-96/turing-oleans/releases/download/mathlib-9944fe29-lean-4.33.0-rc1/oleans_07.tgz && sha256sum -c --ignore-missing SHA256SUMS && tar -xzf oleans_07.tgz -C pkgs && rm oleans_07.tgz
curl -L -f -O https://github.com/fahad-96/turing-oleans/releases/download/mathlib-9944fe29-lean-4.33.0-rc1/oleans_08.tgz && sha256sum -c --ignore-missing SHA256SUMS && tar -xzf oleans_08.tgz -C pkgs && rm oleans_08.tgz
curl -L -f -O https://github.com/fahad-96/turing-oleans/releases/download/mathlib-9944fe29-lean-4.33.0-rc1/oleans_09.tgz && sha256sum -c --ignore-missing SHA256SUMS && tar -xzf oleans_09.tgz -C pkgs && rm oleans_09.tgz
curl -L -f -O https://github.com/fahad-96/turing-oleans/releases/download/mathlib-9944fe29-lean-4.33.0-rc1/server_01.tgz && sha256sum -c --ignore-missing SHA256SUMS && tar -xzf server_01.tgz -C pkgs && rm server_01.tgz
curl -L -f -O https://github.com/fahad-96/turing-oleans/releases/download/mathlib-9944fe29-lean-4.33.0-rc1/ir_01.tgz && sha256sum -c --ignore-missing SHA256SUMS && tar -xzf ir_01.tgz -C pkgs && rm ir_01.tgz
```

The same as a loop:

```
REL=https://github.com/fahad-96/turing-oleans/releases/download/mathlib-9944fe29-lean-4.33.0-rc1
for f in oleans_01 oleans_02 oleans_03 oleans_04 oleans_05 oleans_06 oleans_07 oleans_08 oleans_09 server_01 ir_01; do
  curl -L -f -O $REL/$f.tgz && sha256sum -c --ignore-missing SHA256SUMS && tar -xzf $f.tgz -C pkgs && rm $f.tgz || { echo "FAILED $f"; break; }
done
```

Afterwards `~/work/pkgs/` holds eight folders, each with
`.lake/build/lib/lean/...`: mathlib, batteries, aesop, Qq, proofwidgets,
importGraph, LeanSearchClient, plausible. Expected file count: 43,251
(`find pkgs -type f | wc -l`).

The manifests (chunk, files, raw bytes, compressed bytes) are assets too:

```
curl -L -f -O https://github.com/fahad-96/turing-oleans/releases/download/mathlib-9944fe29-lean-4.33.0-rc1/pack_manifest.txt
curl -L -f -O https://github.com/fahad-96/turing-oleans/releases/download/mathlib-9944fe29-lean-4.33.0-rc1/pack_server_manifest.txt
curl -L -f -O https://github.com/fahad-96/turing-oleans/releases/download/mathlib-9944fe29-lean-4.33.0-rc1/pack_ir_manifest.txt
```

## 3. LEAN_PATH and compiling (as in TURING_PLAYBOOK.md section 3.3)

`<project>` is the folder that contains `TuringTask/` and `TuringTask.lean`.

```
P=$HOME/work/pkgs
export LEAN_PATH=<project>/.lake/build/lib/lean:$P/mathlib/.lake/build/lib/lean:$P/batteries/.lake/build/lib/lean:$P/aesop/.lake/build/lib/lean:$P/Qq/.lake/build/lib/lean:$P/proofwidgets/.lake/build/lib/lean:$P/importGraph/.lake/build/lib/lean:$P/LeanSearchClient/.lake/build/lib/lean:$P/plausible/.lake/build/lib/lean

cd <project>
lean TuringTask/Basic.lean
mkdir -p .lake/build/lib/lean/TuringTask
lean -o .lake/build/lib/lean/TuringTask/X.olean TuringTask/X.lean
```

`lean File.lean` checks one file; `lean -o ...olean` also writes the olean so
that the next file of an import chain can import it. The first
`import Mathlib` takes about 6 minutes (cold disk cache), later ones about
9 s. Warnings print as in `lake build`; exit 0 with no output means no
warnings.

Quick test:

```
printf 'import Mathlib\n\ntheorem smoke : (2 : Nat) + 2 = 4 := by norm_num\n#print axioms smoke\n' > /tmp/smoke.lean
lean /tmp/smoke.lean
```

Expected output: `'smoke' depends on axioms: [propext]`.

## What was verified when this was written (10 Oct 2026)

- Every asset on GitHub has the size and sha256 listed above (compared with
  the files in `D:\lean\_xfer` on the laptop).
- The archives contain only the eight packages' `.lake/build/lib/lean`
  files (43,251 files); nothing of Project Turing.
- An anonymous `curl -L` download of an asset works and matches its sha256.
- NOT run by the author of this file: the Lean commands of sections 1 and 3 on
  Linux. They are the steps of playbook section 3.3, which earlier chats used
  with the same archives.
