# Package

version       = "0.9.0"
author        = "Gerd Mathar"
description   = "Explicit concepts and an implements-relationship between concepts and types."
license       = "Apache License 2.0"
skipDirs      = @["tests"]

# Dependencies

requires "nim >= 0.17.2"

# Tasks

task test, "run the tests":
  --path: "../"
  --run
  setCommand "c", "tests/testrunner.nim"
