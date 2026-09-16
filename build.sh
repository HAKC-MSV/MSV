#!/usr/bin/env bash
set -e

ROOT_DIR=$(pwd)

SVF_DIR="$ROOT_DIR/Unified-Memory-Safety-Validation/program-dependence-graph/SVF"
SVF_CORE="$SVF_DIR/Release-build/svf/libSvfCore.so"
SVF_LLVM="$SVF_DIR/Release-build/svf-llvm/libSvfLLVM.so"

LLVM_SRC="$ROOT_DIR/llvm-project-14.0.0.src"
LLVM_BUILD="$LLVM_SRC/build"
LLVM_CLANG="$LLVM_BUILD/bin/clang"
LLVM_CONFIG="$LLVM_BUILD/lib/cmake/llvm/LLVMConfig.cmake"

PDG_DIR="$ROOT_DIR/Unified-Memory-Safety-Validation/program-dependence-graph"
PDG_BUILD="$PDG_DIR/build"
PDG_LIB="$PDG_BUILD/libpdg_shared.a"

MSV_DIR="$ROOT_DIR/Unified-Memory-Safety-Validation"


# ============================================================
# SVF
# ============================================================

if [ -f "$SVF_CORE" ] && [ -f "$SVF_LLVM" ]; then
    echo "SVF is already built. Skipping SVF build."
else
    echo "Building SVF ..."
    cd "$SVF_DIR"
    bash build.sh
fi


# ============================================================
# LLVM 14.0.0
# ============================================================

cd "$ROOT_DIR"

if [ -x "$LLVM_CLANG" ] && [ -f "$LLVM_CONFIG" ]; then
    echo "LLVM 14.0.0 is already built. Skipping LLVM build."
else
    if [ ! -d "$LLVM_SRC" ]; then
        echo "Downloading LLVM 14.0.0..."

        if [ ! -f "$ROOT_DIR/llvm-project-14.0.0.src.tar.xz" ]; then
            wget https://github.com/llvm/llvm-project/releases/download/llvmorg-14.0.0/llvm-project-14.0.0.src.tar.xz
        fi

        echo "Extracting LLVM 14 source code..."
        tar -xf llvm-project-14.0.0.src.tar.xz
        rm -f llvm-project-14.0.0.src.tar.xz
    else
        echo "LLVM 14 source already exists. Skipping download and extraction."
    fi

    echo "Applying LLVM patches ..."
    cp "$ROOT_DIR/LLVM_FIX/SafeStack.cpp" "$LLVM_SRC/llvm/lib/CodeGen/SafeStack.cpp"
    cp "$ROOT_DIR/LLVM_FIX/X86SpeculativeLoadHardening.cpp" "$LLVM_SRC/llvm/lib/Target/X86/X86SpeculativeLoadHardening.cpp"

    echo "Building LLVM 14.0.0 ..."

    mkdir -p "$LLVM_BUILD"
    cd "$LLVM_BUILD"

    cmake -G Ninja -DCMAKE_C_COMPILER=gcc-11 -DCMAKE_CXX_COMPILER=g++-11 -DCMAKE_BUILD_TYPE="Release" -DLLVM_ENABLE_ASSERTIONS=Off -DLLVM_FORCE_ENABLE_STATS=ON -DLLVM_ENABLE_PROJECTS='clang;lld;compiler-rt' -DLLVM_TARGETS_TO_BUILD='X86' ../llvm

    ninja -j4
fi


# ============================================================
# PDG
# ============================================================

if [ -f "$PDG_LIB" ]; then
    echo "PDG is already built. Skipping PDG build."
else
    echo "Building PDG ..."

    cd "$PDG_DIR"
    mkdir -p build
    cd build

    cmake -G Ninja ..
    ninja -j4
fi


# ============================================================
# MSV
#
# Always run the incremental build because MSV source code may
# have changed. Ninja only recompiles files that need rebuilding.
# ============================================================

echo "Building MSV ..."

cd "$MSV_DIR"
mkdir -p build
cd build

cmake -G Ninja ..
ninja -j4


echo "Setup completed."

