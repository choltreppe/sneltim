# Package

version       = "0.1.0"
author        = "Joel Lienhard"
description   = "A svelte-like web framework for nim"
license       = "MIT"
srcDir        = "src"


# Dependencies

requires "nim >= 1.9.1"


task test, "test":
  withDir "tests":
    exec "nim js test_app.nim"