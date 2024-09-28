file(REMOVE_RECURSE
  "libAnalyzerStatic.a"
  "libAnalyzerStatic.pdb"
)

# Per-language clean rules from dependency scanning.
foreach(lang CXX)
  include(CMakeFiles/AnalyzerStatic.dir/cmake_clean_${lang}.cmake OPTIONAL)
endforeach()
