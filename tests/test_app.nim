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
  var a = 2  # this is a private member (its not visible to parent)
  var b = 3
  var vals = @[1, 2, 3]

  proc getValSum: int =  # you can use procs
    for v in vals:
      result += v

  templ"""
    {vals}
    <div>
      <{editableNum} title={"edit a"} value={a}/><br/>
      <{editableNum} title={"edit b"} value={b}/><br/>
      i + j = {a+b}
    </div>
    <div>
      <b>loop test:</><br/>
      {% for i, v in vals.mpairs %}
        <{editableNum} title={"val" & $i} value={v}/><br/>
      {% endfor %}
      <b>sum: {getValSum()}</>
    </>
    <button on:click={vals &= 0}> add val </>
    <button on:click={vals.setLen len(vals) - 1}> del val </>
  """


run testComponent