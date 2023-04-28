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


let testComp = component:

  var x = [2,6,3]

  html:
    <%>editableNum(value=x[1], title="foo"); <>br
    <>`div`(a = 6, on[click] = inc x[1]):
      (<>b text "x"); <>br
      text $x
      for i, v in x:
        <>a(href="/"):
          text $v


run testComp