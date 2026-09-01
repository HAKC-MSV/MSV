#!/usr/bin/env bash
set -euo pipefail

# ============================================================
# Generate LLVM 14 bitcode for one Linux kernel source file.
#
# Example:
#   ./build-kernel-bc.sh arch/x86/kernel/msr.c
#
# Output:
#   arch/x86/kernel/msr.bc
#   arch/x86/kernel/msr.ll
#
# Assumptions:
#   1. Run this script from the Linux kernel source root.
#   2. .config already exists, or CONFIG_FILE points to one.
#   3. LLVM 14 is installed/built at LLVM14 below.
# ============================================================

# ---------- Configuration ----------

# LLVM 14 toolchain
LLVM14="/path/to/llvm-project-14.0.0.src/build/bin"

# Optional config file.
# Leave empty if .config is already prepared.
CONFIG_FILE=""

# Disable HAKC because stock LLVM 14 does not understand --enable-hakc.
DISABLE_HAKC=1

# Disable CONFIG_WERROR because Linux 6.14 contains warning options
# that Clang 14 may not recognize.
DISABLE_WERROR=1


# ---------- Target ----------

if [[ $# -ne 1 ]]; then
    echo "Usage: $0 <kernel-source-file.c>"
    echo "Example: $0 arch/x86/kernel/msr.c"
    exit 1
fi

SRC="$1"

if [[ ! -f "$SRC" ]]; then
    echo "Error: source file does not exist: $SRC"
    exit 1
fi

# Convert:
#   arch/x86/kernel/msr.c
# to:
#   arch/x86/kernel/msr.o
#   arch/x86/kernel/msr.bc
#   arch/x86/kernel/msr.ll
OBJ="${SRC%.c}.o"
BC="${SRC%.c}.bc"
LL="${SRC%.c}.ll"


# ---------- Check LLVM 14 ----------

CLANG="${LLVM14}/clang"
LLVM_DIS="${LLVM14}/llvm-dis"

if [[ ! -x "$CLANG" ]]; then
    echo "Error: LLVM 14 clang not found at:"
    echo "  $CLANG"
    exit 1
fi

if [[ ! -x "$LLVM_DIS" ]]; then
    echo "Error: llvm-dis not found at:"
    echo "  $LLVM_DIS"
    exit 1
fi

echo "=== LLVM toolchain ==="
"$CLANG" --version | head -n 1


# ---------- Prepare kernel configuration ----------

if [[ -n "$CONFIG_FILE" ]]; then
    echo "=== Installing kernel config ==="
    cp "$CONFIG_FILE" .config
fi

if [[ ! -f .config ]]; then
    echo "Error: .config does not exist."
    echo "Provide CONFIG_FILE or create .config first."
    exit 1
fi

if [[ "$DISABLE_HAKC" -eq 1 ]]; then
    echo "=== Disabling HAKC ==="
    ./scripts/config --disable HAKC
fi

if [[ "$DISABLE_WERROR" -eq 1 ]]; then
    echo "=== Disabling CONFIG_WERROR ==="
    ./scripts/config --disable WERROR
fi

# Re-evaluate compiler-dependent Kconfig options using LLVM 14.
echo "=== Running olddefconfig with LLVM 14 ==="
make LLVM="${LLVM14}/" olddefconfig


# ---------- Generate required kernel headers ----------

echo "=== Preparing kernel build environment ==="
make LLVM="${LLVM14}/" prepare


# ---------- Obtain the exact Kbuild compile command ----------

# Remove an existing object so that Kbuild is forced to compile it again.
rm -f "$OBJ"

echo "=== Obtaining Kbuild compile command for $SRC ==="

TMP_LOG="$(mktemp)"

# V=1 prints the full clang command.
make LLVM="${LLVM14}/" V=1 "$OBJ" 2>&1 | tee "$TMP_LOG"

# Extract the clang command that compiles exactly our source file.
#
# We specifically require:
#   LLVM14/clang ... -c -o TARGET.o TARGET.c
#
# tail -n 1 handles the unlikely case that the source appears more than once.
CMD="$(
    grep -F "${CLANG} " "$TMP_LOG" |
    grep -F "$SRC" |
    grep -F " -c " |
    tail -n 1
)"

rm -f "$TMP_LOG"

if [[ -z "$CMD" ]]; then
    echo "Error: could not extract clang command for:"
    echo "  $SRC"
    exit 1
fi

echo
echo "=== Original Kbuild command ==="
echo "$CMD"


# ---------- Convert normal Kbuild command into LLVM bitcode command ----------

# Use Python here because modifying a large shell command reliably with sed
# becomes fragile.
#
# Changes:
#   -O1/-O2/-O3/-Os/-Oz -> -O0
#   remove -gsplit-dwarf
#   preserve -g / DWARF information
#   add -fno-discard-value-names
#   add -Xclang -disable-O0-optnone
#   add -emit-llvm
#   TARGET.o -> TARGET.bc

export CMD SRC OBJ BC

BC_CMD="$(
python3 <<'PY'
import os
import shlex

cmd = os.environ["CMD"]
src = os.environ["SRC"]
obj = os.environ["OBJ"]
bc  = os.environ["BC"]

args = shlex.split(cmd)

new = []
skip_next = False
found_opt = False
found_g = False

i = 0
while i < len(args):
    arg = args[i]

    # Remove optimization levels. We add -O0 later.
    if arg in ("-O0", "-O1", "-O2", "-O3", "-Os", "-Oz", "-Og", "-Ofast"):
        found_opt = True
        i += 1
        continue

    # Avoid split DWARF because we want debug information retained directly
    # with the LLVM IR/bitcode as much as possible.
    if arg == "-gsplit-dwarf":
        i += 1
        continue

    if arg == "-g" or arg.startswith("-gdwarf"):
        found_g = True

    # Replace output object with output bitcode.
    if arg == "-o" and i + 1 < len(args):
        old_output = args[i + 1]

        if old_output == obj:
            new.extend(["-o", bc])
            i += 2
            continue

    new.append(arg)
    i += 1

# Add analysis-friendly options immediately before compilation input/output
# handling. Order matters: the final optimization level should be -O0.
new.extend([
    "-O0",
    "-g",
    "-fno-discard-value-names",
    "-Xclang",
    "-disable-O0-optnone",
    "-emit-llvm",
])

print(" ".join(shlex.quote(x) for x in new))
PY
)"


echo
echo "=== LLVM bitcode command ==="
echo "$BC_CMD"


# ---------- Generate the bitcode ----------

echo
echo "=== Generating $BC ==="
eval "$BC_CMD"


# ---------- Verify bitcode ----------

if [[ ! -f "$BC" ]]; then
    echo "Error: bitcode was not generated."
    exit 1
fi

echo
echo "=== Bitcode file ==="
file "$BC"


# ---------- Generate readable LLVM IR ----------

echo
echo "=== Generating textual LLVM IR ==="
"$LLVM_DIS" "$BC" -o "$LL"


# ---------- Verify debug metadata ----------

echo
echo "=== Checking debug metadata ==="

if grep -q '!DICompileUnit' "$LL"; then
    echo "[OK] DICompileUnit found"
else
    echo "[WARN] DICompileUnit not found"
fi

if grep -q '!DISubprogram' "$LL"; then
    echo "[OK] DISubprogram found"
else
    echo "[WARN] DISubprogram not found"
fi

if grep -q '!DILocation' "$LL"; then
    echo "[OK] DILocation found"
else
    echo "[WARN] DILocation not found"
fi


# ---------- Verify optimization/pass attributes ----------

if grep -q 'optnone' "$LL"; then
    echo "[WARN] optnone still appears in IR"
else
    echo "[OK] no optnone function attribute"
fi


echo
echo "============================================================"
echo "Done"
echo "Source : $SRC"
echo "Bitcode: $BC"
echo "LLVM IR: $LL"
echo "============================================================"

