import std/macros
import sneltim {.all.}


expandMacros:

  test(@[@[0], @[1], @[2], @[3], @[4], @[5], @[6]]):
    var x = 3
    var y = 6
    var z: string

    proc incX: int = 
      inc x
      x

    proc test1(x: int): int =
      y + x

    proc test2(x: int) =
      y += x * incX()


    dynamicContent:
      z & $x

    dynamicContent:
      x - 2*y

    dynamicContent:
      block:
        let x = 2
        x + y

    dynamicContent:
      incX()

    dynamicContent:
      test1(2)

    dynamicContent:
      test2(4)

    dynamicContent:
      test2(4)