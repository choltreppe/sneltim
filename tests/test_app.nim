import sneltim
import std/[macros, strformat]


component:

  var x = [2,6,3]

  html:
    <>`div`(a = 6, on[click] = (x)):
      <>b: text "x"
      for i, v in x:
        <>a(href="/"):
          text $v