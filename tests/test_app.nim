import sneltim
import std/[macros, strformat]


let editableNum = component:
  let title* = ""  # this is a public let member (it can only be set (and changed) from parent)
  var value*: int  # this is a public var member (it can be set from parent and self, and chnages from self effect parent)

  html:
    text title & ":"
    <>button(on[click] = dec value): text "-"
    text $value
    <>button(on[click] = inc value): text "+"


let testComponent = component:
  var a = 2  # this is a private member (its not visible to parent)
  var b = 3
  var vals = @[1, 2, 3]
  var matrix: array[3, array[3, int]]
  var listlen0, listlen1 = 2

  proc getValSum: int =  # you can use procs
    for v in vals:
      result += v

  html:
    <>`div`:
      <%>editableNum(title="edit a", value=a); <>br
      <%>editableNum(title="edit b", value=b); <>br
      text &"a + b = {a+b}"; <>br
      <>button(on[click] = (inc a; inc b)) text "inc a and b"

    <>`div`:
      <>b(style="color: #333") (text "loop test:"); <>br

      for i, v in vals.mpairs:
        <%>editableNum(title= "val" & $i, value=v); <>button(on[click] = (vals[i] += 2)); <>br

      for v in vals:
        text $v; <>br

      <>b text &"sum: {getValSum()}"; <>br
        
      <>button(on[click] = (vals &= 0)): text "add val"
      <>button(on[click] = (vals.setLen len(vals) - 1)): text "del val"

    <>`div`:
      <>b text "matrix:"; <>br

      for row in matrix.mitems:
        for v in row.mitems:
          <%>editableNum(value=v)
        <>button(on[click] = (for v in row.mitems: inc v)) text "inc row"; <>br

    <>`div`:
      <>b text "hook test (2 for loops):"; <>br

      for _ in 0 ..< listlen0:
        text $listlen0; <>br
      for _ in 0 ..< listlen1:
        text "x"; <>br
      
      <%>editableNum(title="list0", value=listlen0); <>br
      <%>editableNum(title="list1", value=listlen1); <>br

      #if listlen0 == 0:
      #  <>b text "listlen0 == 0"


run testComponent