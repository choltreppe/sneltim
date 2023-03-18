import std/macros
import sneltim


expandMacros:
  component testComponent:
    var i = 2
    var j = 3

    proc countUp =
      inc i

    templ"""
      <div>
        <h1 on:click={countUp()}>i = {i}</>
        <span color="red">j = {j}</span>
        <input value={i + j}/>
      </div>
    """


let c = testComponent()
c.mount(document.body, nil)
#discard setTimeout(proc = c.detatch(document.body), 1000)