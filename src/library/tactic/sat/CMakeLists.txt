add_library(sat OBJECT
  minisat/core/Solver.cc
  minisat/simp/SimpSolver.cc
  minisat/utils/Options.cc

  drup.cpp
)

target_include_directories(sat PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})