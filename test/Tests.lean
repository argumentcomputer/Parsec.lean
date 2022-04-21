import Parsec
import Tests.URI

open Parsec Tests

def main (args : List String) : IO UInt32 := do
  try
    URI.tests
    pure 0
  catch e =>
    IO.eprintln <| "error: " ++ toString e -- avoid "uncaught exception: ..."
    pure 1

