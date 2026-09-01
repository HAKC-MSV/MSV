#
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

cmake_minimum_required(VERSION 3.5)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

project(UnifiedMemSafe)

set(DEFAULT_LLVM_DIR "../llvm-project-14.0.0.src/build/lib/cmake/llvm")
set(LLVM_DIR ${DEFAULT_LLVM_DIR} CACHE PATH "Path to LLVMConfig.cmake")

find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
message(STATUS "Using LLVM Library in: ${LLVM_LIBS}")
message(STATUS "Using LLVM Library in: ${LLVM_INCLUDE_DIRS}")

message("LLVM STATUS:
  Definitions ${LLVM_DEFINITIONS}
  Includes    ${LLVM_INCLUDE_DIRS}
  Libraries   ${LLVM_LIBRARY_DIRS}
  Targets     ${LLVM_TARGETS_TO_BUILD}"
)


include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})
add_definitions(${LLVM_DEFINITIONS})
set(NO_RTTI "-fno-rtti")
add_definitions(${NO_RTTI})
add_compile_options(-std=c++17) 

include_directories("${CMAKE_SOURCE_DIR}/program-dependence-graph/include")
include_directories("program-dependence-graph/SVF/svf-llvm/include")
include_directories("program-dependence-graph/SVF/svf/include")
include_directories("program-dependence-graph/SVF/Release-build/include")

# Compiler flag
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fdiagnostics-color=always -fno-rtti -g")

# set(CMAKE_CXX_STANDARD 14 CACHE STRING "")

add_library(UnifiedMemSafe SHARED
    UnifiedMemSafe.cpp
    Utils.cpp
    Utils.hpp
    ValueRange.cpp
    ValueRange.hpp
    DataflowAnalysis.h
    DataGuard.cpp
    DataGuard.hpp
    CompatibleType.cpp
    CompatibleType.hpp
    Uriah.cpp
    Uriah.hpp
    LLVMEssentials.hh
    OutOfWindow.cpp
    Taint.cpp
    IRSafeStack.cpp
)

target_link_libraries(UnifiedMemSafe PUBLIC 
    "${CMAKE_SOURCE_DIR}/program-dependence-graph/build/libpdg_shared.a"
    "${CMAKE_SOURCE_DIR}/program-dependence-graph/SVF/Release-build/svf/libSvfCore.so"
    "${CMAKE_SOURCE_DIR}/program-dependence-graph/SVF/Release-build/svf-llvm/libSvfLLVM.so"
)

set_target_properties(UnifiedMemSafe PROPERTIES BUILD_PATH 
    "${CMAKE_SOURCE_DIR}/program-dependence-graph/SVF/Release-build/svf;${CMAKE_SOURCE_DIR}/program-dependence-graph/SVF/Release-build/svf-llvm")

if(APPLE)
    set_target_properties(UnifiedMemSafe PROPERTIES LINK_FLAGS "-undefined dynamic_lookup")
endif(APPLE)
