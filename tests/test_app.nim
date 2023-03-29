import std/macros
import sneltim {.all.}


let editableNum = component:
  let title* = ""  # this is a public let member (it can only be set (and changed) from parent)
  var value*: int  # this is a public var member (it can be set from parent and self, and chnages from self effect parent)

  templ"""
    {title}:
    <button on:click={dec value}>-</>
    {value}
    <button on:click={inc value}>+</>
  """


let testComponent = component:
  var i = 2  # this is a private member (its not visible to parent)
  var j = 3

  proc countUpI =
    inc i

  templ"""
    <div>
      <{editableNum} title={"edit i"} value={i}/><br/>
      <{editableNum} title={"edit j"} value={j}/><br/>
      i + j = {i+j}
    </div>
  """


let c = testComponent.create(nil)
c.mount(document.body, nil)
#discard setTimeout(proc = c.detatch(document.body), 1000)