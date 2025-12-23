import Ski

open Term in
def main : IO Unit := do
  IO.println "SKI Calculus"
  IO.println s!"S combinator: {repr S}"
  IO.println s!"K combinator: {repr K}"
  IO.println s!"I combinator: {repr I}"
  IO.println s!"Example term S K K: {repr (S ⬝ K ⬝ K)}"
