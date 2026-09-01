set -e

ROOT_DIR=$(pwd)

#sudo apt update
#sudo apt install git build-essential python3 ninja-build wget cmake libtinfo-dev libtinfo6
#sudo apt install flex bison libssl-dev libelf-dev bc dwarves
#sudo apt install gcc-11 g++-11

# Build SVF using Pre-built LLVM 14 Binaries
echo "Building SVF ..."
cd Unified-Memory-Safety-Validation/program-dependence-graph/SVF
bash build.sh

# build llvm-14 from source
cd $ROOT_DIR
echo "Downloading LLVM 14.0.0..."
wget https://github.com/llvm/llvm-project/releases/download/llvmorg-14.0.0/llvm-project-14.0.0.src.tar.xz
echo "Extracting LLVM 14 source code..."
tar -xf llvm-project-14.0.0.src.tar.xz
rm  llvm-project-14.0.0.src.tar.xz

# apply patches and build LLVM 14.0.0
cp LLVM_FIX/SafeStack.cpp llvm-project-14.0.0.src/llvm/lib/CodeGen/SafeStack.cpp
cp LLVM_FIX/X86SpeculativeLoadHardening.cpp llvm-project-14.0.0.src/llvm/lib/Target/X86/X86SpeculativeLoadHardening.cpp

mkdir -p llvm-project-14.0.0.src/build
cd llvm-project-14.0.0.src/build

cmake -G Ninja -DCMAKE_C_COMPILER=gcc-11 -DCMAKE_CXX_COMPILER=g++-11 -DCMAKE_BUILD_TYPE="Release"  -DLLVM_ENABLE_ASSERTIONS=Off -DLLVM_FORCE_ENABLE_STATS=ON -DLLVM_ENABLE_PROJECTS='clang;lld;compiler-rt' -DLLVM_TARGETS_TO_BUILD='X86' ../llvm
ninja -j4

# PDG
echo "Building PDG ..."
cd $ROOT_DIR/Unified-Memory-Safety-Validation/program-dependence-graph
mkdir -p build
cd build
cmake -G Ninja ..
ninja -j4

# memory analysis
echo "Building MSV ..."
cd $ROOT_DIR/Unified-Memory-Safety-Validation
mkdir -p build
cd build
cmake -G Ninja ..
ninja -j4

echo "Setup completed."
