cmake_minimum_required(VERSION 3.16)
project(fasm2netlist CXX)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release)
endif()

add_executable(fasm2netlist
  src/main.cpp
  src/netlist_core.cpp
  src/cells_slice.cpp
  src/cells_dsp.cpp
  src/cells_bram.cpp)
target_compile_options(fasm2netlist PRIVATE -Wall -Wextra)

# LVS miter support: a small and-inverter graph plus exporters for the two
# formats a solver is likely to accept (DIMACS CNF, SMT-LIB 2) and a runner
# that shells out to one.  Kept a library of its own so the matcher being
# ported from tests/lvs/*.py can link it without going through main.cpp.
# Tile configuration: FASM -> the tile model's own config vocabulary, with a
# canonical dump so a model change is a diff.
add_library(lvs_tileconfig STATIC src/lvs/tileconfig.cpp)
target_compile_options(lvs_tileconfig PRIVATE -Wall -Wextra)
target_include_directories(lvs_tileconfig PUBLIC src)

add_executable(tileverilog src/lvs/tileverilog.cpp src/lvs/regmap.cpp)
target_link_libraries(tileverilog PRIVATE lvs_tileconfig)
target_include_directories(tileverilog PRIVATE src)
target_compile_options(tileverilog PRIVATE -Wall -Wextra)

add_executable(tiledump src/lvs/tiledump.cpp)
target_link_libraries(tiledump PRIVATE lvs_tileconfig)
target_compile_options(tiledump PRIVATE -Wall -Wextra)

add_library(lvs_miter STATIC src/lvs/boolnet.cpp src/lvs/solver.cpp)
target_compile_options(lvs_miter PRIVATE -Wall -Wextra)
target_include_directories(lvs_miter PUBLIC src)

# Z3 as a library rather than a command, when it is installed to be linked
# against.  It is not required: without it every solver is still reachable as
# a command, just a process and a re-parse per question.  Set LVS_Z3=OFF to
# build the command-only way deliberately.
option(LVS_Z3 "Link Z3 when it is available" ON)
if(LVS_Z3)
  find_path(Z3_INCLUDE_DIR z3++.h)
  find_library(Z3_LIBRARY NAMES z3)
  if(Z3_INCLUDE_DIR AND Z3_LIBRARY)
    target_include_directories(lvs_miter PUBLIC ${Z3_INCLUDE_DIR})
    target_link_libraries(lvs_miter PUBLIC ${Z3_LIBRARY})
    target_compile_definitions(lvs_miter PUBLIC LVS_HAVE_Z3)
    message(STATUS "lvs: linking ${Z3_LIBRARY}")
  else()
    message(STATUS "lvs: no libz3 found; solvers will be run as commands")
  endif()
else()
  message(STATUS "lvs: LVS_Z3=OFF; solvers will be run as commands")
endif()

# CaDiCaL, the preferred solver: the miters are pure Boolean, and a CDCL solver over a Tseitin encoding answers them an order of magnitude
# faster than Z3.  Taken from, in order: an installed copy under CADICAL_ROOT (include/cadical.hpp, lib/libcadical.a), or the
# third_party/cadical submodule, built here with its own configure/make (`git submodule update --init`).  With neither, Z3 or a command.
option(LVS_CADICAL "Link CaDiCaL when it is available" ON)
if(LVS_CADICAL)
  find_path(CADICAL_INCLUDE_DIR cadical.hpp HINTS ${CADICAL_ROOT}/include $ENV{CADICAL_ROOT}/include NO_DEFAULT_PATH)
  find_library(CADICAL_LIBRARY NAMES cadical HINTS ${CADICAL_ROOT}/lib $ENV{CADICAL_ROOT}/lib NO_DEFAULT_PATH)
  if(NOT (CADICAL_INCLUDE_DIR AND CADICAL_LIBRARY))
    find_path(CADICAL_INCLUDE_DIR cadical.hpp)
    find_library(CADICAL_LIBRARY NAMES cadical)
  endif()
  set(CADICAL_SUBMODULE ${CMAKE_CURRENT_SOURCE_DIR}/third_party/cadical)
  if(CADICAL_INCLUDE_DIR AND CADICAL_LIBRARY)
    target_include_directories(lvs_miter PUBLIC ${CADICAL_INCLUDE_DIR})
    target_link_libraries(lvs_miter PUBLIC ${CADICAL_LIBRARY})
    target_compile_definitions(lvs_miter PUBLIC LVS_HAVE_CADICAL)
    message(STATUS "lvs: linking ${CADICAL_LIBRARY}")
  elseif(EXISTS ${CADICAL_SUBMODULE}/configure)
    include(ExternalProject)
    ExternalProject_Add(cadical_ext
      SOURCE_DIR ${CADICAL_SUBMODULE}
      BUILD_IN_SOURCE 1
      CONFIGURE_COMMAND ./configure
      BUILD_COMMAND make -j4
      INSTALL_COMMAND ""
      BUILD_BYPRODUCTS ${CADICAL_SUBMODULE}/build/libcadical.a)
    add_dependencies(lvs_miter cadical_ext)
    target_include_directories(lvs_miter PUBLIC ${CADICAL_SUBMODULE}/src)
    target_link_libraries(lvs_miter PUBLIC ${CADICAL_SUBMODULE}/build/libcadical.a)
    target_compile_definitions(lvs_miter PUBLIC LVS_HAVE_CADICAL)
    message(STATUS "lvs: building CaDiCaL from the third_party/cadical submodule")
  else()
    message(STATUS "lvs: no CaDiCaL (run `git submodule update --init`, or set CADICAL_ROOT); using Z3 or a command")
  endif()
endif()

# Structural Verilog reader, generated from src/lvs/verilog.{l,y}.  flex and
# bison are code generators, not link-time dependencies -- the sources they
# emit are self-contained C++ -- so this keeps the "no external libraries"
# property of the tool itself.  Without them installed the reader simply is
# not built, and what depends on it is skipped rather than failing.
find_package(BISON)
find_package(FLEX)
if(BISON_FOUND AND FLEX_FOUND)
  # bison writes the defines file itself and will not create the directory
  file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/lvs)
  bison_target(VerilogParser src/lvs/verilog.y ${CMAKE_CURRENT_BINARY_DIR}/verilog.tab.cpp
               DEFINES_FILE ${CMAKE_CURRENT_BINARY_DIR}/lvs/verilog.tab.hpp)
  flex_target(VerilogLexer src/lvs/verilog.l ${CMAKE_CURRENT_BINARY_DIR}/verilog.yy.cpp)
  add_flex_bison_dependency(VerilogLexer VerilogParser)

  add_library(lvs_verilog STATIC
    ${BISON_VerilogParser_OUTPUTS}
    ${FLEX_VerilogLexer_OUTPUTS}
    src/lvs/verilog_reader.cpp
    src/lvs/json_netlist.cpp)
  # two entries on purpose: the generated parser includes the defines file
  # by basename, while our own sources include it as lvs/verilog.tab.hpp
  target_include_directories(lvs_verilog PUBLIC src ${CMAKE_CURRENT_BINARY_DIR}
                                                ${CMAKE_CURRENT_BINARY_DIR}/lvs)
  # generated sources are not ours to keep warning-clean
  target_compile_options(lvs_verilog PRIVATE -Wall -Wextra -Wno-unused-function)
  # Per-register equivalence: netlist -> cones -> miter -> whichever solver.
  add_executable(lvs_equiv src/lvs/lvs_equiv.cpp src/lvs/cone.cpp src/lvs/regmap.cpp)
  target_link_libraries(lvs_equiv PRIVATE lvs_verilog lvs_miter)
  target_compile_options(lvs_equiv PRIVATE -Wall -Wextra)

  set(LVS_VERILOG_AVAILABLE TRUE)
else()
  message(STATUS "flex/bison not found -- the structural Verilog reader will not be built")
  set(LVS_VERILOG_AVAILABLE FALSE)
endif()

install(TARGETS fasm2netlist RUNTIME DESTINATION bin)

enable_testing()
add_subdirectory(tests)
