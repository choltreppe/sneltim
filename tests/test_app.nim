import sneltim
import sneltim/sizes
import std/[strformat, macros]


proc editableNum[T](title: string, value: var T) {.component.} =
  html:
    text title & ":"
    <>button(on[click] = (value -= 1)): text "-"
    text $value
    <>button(on[click] = (value += 1)): text "+"


proc titledBox(title: string) {.component.} =
  html:
    <>`div`:
      style:
        for side in ["left", "top"]:
          padding-{side} := "20px"
        margin := 4.px
        backgroundColor := "#eee"
        -:hover:
          backgroundColor := "#ccc"

      <>`div`:
        style:
          marginBottom := "3px"

        text title
      
      <>`div`:
        <..>_
      <>br


proc twice {.component.} =
  html:
    <..>_
    <..>_

proc ntimes(n = 1) {.component.} =
  html:
    for _ in 0 ..< n:
      <..>_

proc testNamedSlots {.component.} =
  html:
    <>b: text "slot a:"; <>br
    <..>a; <>br
    <>b: text "slot b:"; <>br
    <..>b; <>br


proc testComponent {.component.} =
  var a = 2.0
  var b = 3.0
  var vals = @[1, 2, 3]
  var matrix: array[3, array[3, int]]
  var listlen0, listlen1 = 2

  proc getValSum: int =
    for v in vals:
      result += v

  html:
    
    <%>titledBox(title="binding test (bind a)"):
      <>input(`type`="text", bind[value]=a)

    <%>titledBox(title="basic patching test"):
      <%>editableNum[float](title="edit a", value=a); <>br
      <%>editableNum[float](title="edit b", value=b); <>br
      text &"a + b = {a+b}"; <>br

      <>button(on[click] = (a += 0.5; b += 0.5)):
        style:
          marginLeft := &"{a*4}px"
        text "inc a and b by 0.5"

    <%>titledBox(title="loop test"):
      
      for i, v in vals.mpairs:
        <%>editableNum[int](title= "val" & $i, value=v); <>button(on[click] = (vals[i] += 2)); <>br

      for v in vals:
        text $v; <>br

      <>b text &"sum: {getValSum()}"; <>br
        
      <>button(on[click] = (vals &= 0)): text "add val"
      <>button(on[click] = (vals.setLen len(vals) - 1)): text "del val"
      <>br

      case len(vals)
      of 0: text "theres no element"
      of 1: text "theres one element"
      elif (let v = vals[^1]; v mod 2 == 0):
        text "the last elem is even"; <>br
        text "its a " & $v
      else:
        text "there is a list"

    <%>titledBox(title="matrix"):

      for row in matrix.mitems:
        for v in row.mitems:
          <%>editableNum[int](value=v)
        <>button(on[click] = (for v in row.mitems: inc v)) text "inc row"; <>br

    <%>titledBox(title="hook test (2 for loops)"):

      for _ in 0 ..< listlen0:
        text $listlen0; <>br
      for _ in 0 ..< listlen1:
        text "x"; <>br
      
      <%>editableNum[int](title="list0", value=listlen0); <>br
      <%>editableNum[int](title="list1", value=listlen1); <>br

      if listlen0 == 3:
        <>b text "listlen0 == 3"; <>br
      elif (let l = listlen0 + listlen1; l < 5):
        <>b text "listlen0 + listlen1 < 5"; <>br;
        text "to be precise: " & $l; <>br

    <%>titledBox(title="some slot tests"):
      <%>twice:
        <>b text "foo"; <>br
      <%>ntimes(n = listlen1):
        text $listlen0; <>br
      <%>testNamedSlots:
        <=>a:
          text "some content for a"
        <=>b:
          text "some content for b"



run testComponent