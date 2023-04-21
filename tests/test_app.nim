import sneltim
import std/[macros, strformat]


proc editableNum: int = 42

let testComp = component:

  var x = [2,6,3]
  let y* = "foo"
  let z = 0.7
  var w*: char

  html:
    <>`div`(a = 6, on[click] = inc x[0]):
      <%>editableNum(value=x[1], title="foo:")
      (<>b text "x"); <>br
      for i, v in x:
        <>a(href="/"):
          text $v