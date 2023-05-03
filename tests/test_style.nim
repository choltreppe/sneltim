import std/[macros, strformat]
import sneltim/private/styles


let style = newStyleTempl:
  --backgroundColor: "#FFDD11"
  let margin = 4
  --margin: &"1px {margin}"
  -:hover:
    --color: "black"
  -::selection:
    --fontSize: "30px"
    -:hover:
      --cursor: "pointer"

echo `$`(style(), "foo")