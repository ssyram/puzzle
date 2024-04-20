module TestExport (
  ExportTypeOnly,
  ExportPartialConstructors(ExportConstructorsC1)
) where


-- Only the mentioned ones are exported
-- So actual data can be controlled and held within one specific place

data ExportTypeOnly =
    ExportTypeOnlyConstructor1
  | ExportTypeOnlyConstructor2


data ExportPartialConstructors =
    ExportConstructorsC1
  | ExportConstructorsC2

