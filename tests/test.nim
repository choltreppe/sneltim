
import snelim


component testComponent:

  var i = 2
  var j = 3

  proc countUp =
    inc i

  html"""
    <div>
      <h1 on:click={countUp()}> {i} </>
      <span color="red" >alan stinkt</span>
      <button val={
        j = 3
        i
      }/>
    </div>
  """


let c = testComponent()
c.mount(document.body, nil)
discard setTimeout(proc = c.detatch(document.body), 1000)