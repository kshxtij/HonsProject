file(REMOVE_RECURSE
  "libAnalyzer.pdb"
  "libAnalyzer.so"
)

# Per-language clean rules from dependency scanning.
foreach(lang CXX)
  include(CMakeFiles/Analyzer.dir/cmake_clean_${lang}.cmake OPTIONAL)
endforeach()
