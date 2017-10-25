# Package

version       = "0.8.0"
author        = "Gerd Mathar"
description   = "Explicit concepts and an implements-relationship between concepts and types."
license       = "MIT"
skipDirs      = @["tests"]

# Dependencies

requires "nim >= 0.17.2"

# Tasks

task test, "run the tests":
  --path: "../"
  --run
  setCommand "c", "tests/testrunner.nim"