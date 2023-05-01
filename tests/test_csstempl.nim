import std/macros
import sneltim/private/csstempl

static:
  echo: parseSelector: quote do:
    [> a.after ~ id"elem", > _[type="text"].nthChild(n+1)]