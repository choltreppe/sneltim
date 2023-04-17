import sneltim
import std/strformat


let editableNum = component:
  let title* = ""  # this is a public let member (it can only be set (and changed) from parent)
  var value*: int  # this is a public var member (it can be set from parent and self, and chnages from self effect parent)

  templ:
    title & ":"
    <button(on.click= dec value): "-"
    $value
    <button(on.click= inc value): "+"

let testComponent = component:
  var a = 2  # this is a private member (its not visible to parent)
  var b = 3
  var vals = @[1, 2, 3]
  var matrix: array[3, array[3, int]]
  var listlen0, listlen1 = 2

  proc getValSum: int =  # you can use procs
    for v in vals:
      result += v

  templ:
    <`div`:
      <%editableNum(title="edit a", value=a); <br
      <%editableNum(title="edit b", value=b); <br
      &"a + b = {a+b}"; <br
      <button(on.click = (inc a; inc b)) "inc a and b"

    <`div`:
      <b(style="color: #333") ("loop test:"); <br

      for i, v in vals.mpairs:
        <%editableNum(title= "val" & $i, value=v); <button(on.click = (vals[i] += 2)); <br

      <b &"sum: {getValSum()}"; <br
        
      <button(on.click = (vals &= 0)): "add val"
      <button(on.click = (vals.setLen len(vals) - 1)): "del val"

    <`div`:
      <b "matrix:"; <br;

      for row in matrix.mitems:
        for v in row.mitems:
          <%editableNum(value=v);
        <button(on.click = (for v in row.mitems: inc v)) "inc row"; <br

    <`div`:
      <b "hook test (2 for loops):"; <br;

      for _ in 0 ..< listlen0:
        "0"; <br
      for _ in 0 ..< listlen1:
        "1"; <br
      
      <%editableNum(title="list0", value=listlen0);
      <%editableNum(title="list1", value=listlen1);


run testComponent