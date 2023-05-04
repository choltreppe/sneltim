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


let titledBox = component:
  let title* = ""

  html:
    <>`div`:
      style:
        --padding: "8px"
        --margin: "4px"
        --backgroundColor: "#eee"
        -:hover:
          --backgroundColor: "#ccc"

      <>`div`:
        style:
          --marginBottom: "3px"

        text title
      
      <>`div`:
        <..>_
      <>br

let twice = component:
  html:
    <..>_
    <..>_

let ntimes = component:
  let n* = 1
  html:
    for _ in 0 ..< n:
      <..>_

let testNamedSlots = component:
  html:
    <>b: text "slot a:"; <>br
    <..>a; <>br
    <>b: text "slot b:"; <>br
    <..>b; <>br


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
    <%>titledBox(title="binding test (bind a)"):
      <>input(`type`="text", bind[value]=a)

    <%>titledBox(title="basic patching test"):
      <%>editableNum(title="edit a", value=a); <>br
      <%>editableNum(title="edit b", value=b); <>br
      text &"a + b = {a+b}"; <>br

      <>button(on[click] = (inc a; inc b)):
        style:
          --marginLeft: &"{a*4}px"
        text "inc a and b"

    <%>titledBox(title="loop test"):
      
      for i, v in vals.mpairs:
        <%>editableNum(title= "val" & $i, value=v); <>button(on[click] = (vals[i] += 2)); <>br

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
          <%>editableNum(value=v)
        <>button(on[click] = (for v in row.mitems: inc v)) text "inc row"; <>br

    <%>titledBox(title="hook test (2 for loops)"):

      for _ in 0 ..< listlen0:
        text $listlen0; <>br
      for _ in 0 ..< listlen1:
        text "x"; <>br
      
      <%>editableNum(title="list0", value=listlen0); <>br
      <%>editableNum(title="list1", value=listlen1); <>br

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