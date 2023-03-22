import std/macros
import sneltim


let boldNum = component:
  var n*: int

  templ"<b>{n}</b>"


let testComponent = component:
  var i = 2
  var j* = 3

  proc countUpI =
    inc i

  templ"""
    <div>
      <h1>i = {i}</>
      <button on:click={countUpI()}>increment i</>
      <button on:click={j += 2}>increment j by 2</><br/>
      <span>j = <{boldNum} n = {j}/></span><br/>
      i + j = <{boldNum} n = {i+j}/>
    </div>
  """


debugEcho testComponent.exportedVars
let c = testComponent.create()
c.mount(document.body, nil)
discard setTimeout(proc = c.patch((4,), @[true]), 1000)
#discard setTimeout(proc = c.detatch(document.body), 1000)