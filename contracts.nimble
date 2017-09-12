# Package

version       = "0.1.0"
author        = "Gerd Mathar"
description   = "Contracts are explicitly satisfied concepts"
license       = "MIT"
skipDirs      = @["tests"]

# Dependencies

requires "nim >= 0.17.2"

# Tasks

task test, "run the tests":
  --path: "../"
  --run
  setCommand "c", "tests/testrunner.nim"
