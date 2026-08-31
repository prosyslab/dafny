module DefinitionAnalysisProjectB {
  import ProjectA = DefinitionAnalysisProjectA

  function Use(): int {
    ProjectA.Value()
  }
}
