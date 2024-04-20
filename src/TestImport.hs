module TestImport where

import TestExport
import Utils

testTypeOnly :: ExportTypeOnly
testTypeOnly = undefined  -- the value cannot be its constructors


testPartialConstructor :: ExportPartialConstructors
testPartialConstructor = ExportConstructorsC1  -- only C1 can be called



