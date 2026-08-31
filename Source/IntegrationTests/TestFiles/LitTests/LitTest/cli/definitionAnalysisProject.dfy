// The analysis should treat every Dafny source selected by a project file as an analysis target.
// RUN: %baredafny definition-analysis --include-source-facts "%S/Inputs/definitionAnalysisProject/dfyconfig.toml" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"

// CHECK-L: "fullName": "DefinitionAnalysisProjectA.Value",
// CHECK-L: "fullName": "DefinitionAnalysisProjectB.Use",
// CHECK-L: "DefinitionAnalysisProjectA.Value"
// CHECK-L: "name": "DefinitionAnalysisProjectA",
// CHECK-L: "name": "DefinitionAnalysisProjectB",
