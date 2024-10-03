set (AnalyzerSourceCodes
  Common.h
  Common.cc
	Analyzer.h
	Analyzer.cc
  TypeBuilder/TypeBuilder.h
  TypeBuilder/TypeBuilder.cc
  TypeBuilder/TypeBuilderTools.cc
	CallGraph/CallGraph.h
  CallGraph/CallGraph.cc
  CallGraph/LayerAnalysis.cc
  CallGraph/DebugInfoHandler.cc
  CallGraph/CallGraphTools.cc
  CallGraph/CheckReturnCompType.cc
  CallGraph/DataFlowAnalysis.cc
  CallGraph/EscapeHandler.cc
  CallGraph/OneLayerHandler.cc
  CallGraph/FuncAnalysis.cc
  CallGraph/TypeAnalysis.cc
  CallGraph/InitinGlobal.cc
  AliasAnalysis/AliasAnalysis.h
  AliasAnalysis/ICallAliasAnalysis.cc
  AliasAnalysis/FuncAliasAnalysis.cc
  AliasAnalysis/InstHandler.cc
  AliasAnalysis/InterAliasAnalysis.cc
  AliasAnalysis/AliasAnalysisTools.cc
  AliasAnalysis/ICallDFAnalysis.cc
  Tools.h
  Tools.cc
)

#file(COPY configs/ DESTINATION configs)

# Build libraries.
add_library (AnalyzerObj OBJECT ${AnalyzerSourceCodes})
#add_library (Analyzer SHARED $<TARGET_OBJECTS:AnalyzerObj>)
add_library (AnalyzerStatic STATIC $<TARGET_OBJECTS:AnalyzerObj>)

# Build executable analyzer.
set (EXECUTABLE_OUTPUT_PATH ${UNISAN_BINARY_DIR})
link_directories (${UNISAN_BINARY_DIR}/lib)
add_executable(analyzer ${AnalyzerSourceCodes})
target_link_libraries(analyzer
  LLVMAsmParser 
  LLVMSupport 
  LLVMCore 
  LLVMAnalysis
  LLVMIRReader
  AnalyzerStatic
  )