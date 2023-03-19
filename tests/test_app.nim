import std/macros
import sneltim


let boldNum = component:
  var n*: int

  templ"<b>{n}</b>"


let testComponent = component:
  var i = 2
  var j* = 3

  proc countUp =
    inc i

  templ"""
    <div>
      <h1 on:click={countUp()}>i = {i}</>
      <span color="red">j = {j}</span>
    </div>
  """


let c = testComponent()
c.mount(document.body, nil)
discard setTimeout(proc = c.patch(4, [true]), 1000)
#discard setTimeout(proc = c.detatch(document.body), 1000)