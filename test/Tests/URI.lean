import Std
import Parsec

open Std Parsec

namespace Tests

instance {K V : Type} [BEq K] [BEq V] [Hashable K] : BEq <| HashMap K V where
  beq a b := a.toList ==  b.toList

instance {K V : Type} [BEq K] [BEq V] [Hashable K] [Repr K] [Repr V] : Repr <| HashMap K V where
  reprPrec a n := Repr.reprPrec a.toList n


structure URI where
  userInfo : Option (String × Option String) := none
  host: String
  port: Option UInt16 := none
  scheme: String
  path: List String := []
  query: HashMap String String := HashMap.empty
  fragment: HashMap String String := HashMap.empty
  deriving Repr, BEq

instance : ToString URI where
  toString uri := reprStr uri

namespace URI
namespace Parser

def schemeParser : Parsec String :=
  manyChars (asciiLetter <|> oneOf ['+', '-', '.'])

def hostName : Parsec String := do
  let name := many1Chars (asciiLetter <|> digit <|> oneOf [ '-', '.' ])
  many1Strings name

def parseDigit! (c : Char) : Nat :=
  match c with
  | '0' => 0
  | '1' => 1
  | '2' => 2
  | '3' => 3
  | '4' => 4
  | '5' => 5
  | '6' => 6
  | '7' => 7
  | '8' => 8
  | '9' => 9
  | _ => panic! "Not a digit"

def parseUInt16 : Parsec UInt16 := do
  let as ← many1 digit
  let mut n := 0
  for (i, c) in as.toList.reverse.enum do
    let d := parseDigit! c
    n := n + d * 10 ^ i
  return n.toUInt16

def maybePort : Parsec (Option UInt16) := option <| do
  skipChar ':'
  parseUInt16

def psegment : Parsec String :=
  many1Chars <| oneOf ['-', '%', '_', '+', '$', '.', ':', '*', '@' ] <|> asciiLetter <|> digit

partial def pathParser : Parsec <| List String := do
  let rec comp : Parsec <| List String := do
    if ← test <| pstring "/" then
      let part ← (·.getD "") <$> option psegment
      let rest ← comp
      pure <| part :: rest
    else
      pure []
  comp

def usernameParser := many1Chars <| asciiLetter <|> digit
def passwordParser := many1Chars <| asciiLetter <|> digit

def userInfoParser : Parsec (String × Option String) := do
  let username ← usernameParser
  let password ← option do skipChar ':'; passwordParser
  skipChar '@'
  return ( username, password )

partial def queryParser : Parsec (HashMap String String) := do
  skipChar '?'
  let rec entries := do
    let k ← psegment
    skipChar '='
    let v ← psegment
    if ← test $ skipChar '&' then
      pure <| (k, v) :: (← entries)
    else
      pure [(k, v)]
  HashMap.ofList <$> entries

partial def fragmentParser : Parsec (HashMap String String) := do
  skipChar '#'
  let rec entries := do
    let k ← psegment
    let v ← (if ← test <| skipChar '=' then
      psegment
    else
      pure ""
    )
    if ← test $ skipChar '&' then
      pure <| (k, v) :: (← entries)
    else
      pure [(k, v)]
  HashMap.ofList <$> entries

def url : Parsec URI := do
  let scheme ← schemeParser
  skipString "://"
  let userInfo ← option userInfoParser
  let host ← hostName
  let optPort ← maybePort
  let path ← pathParser
  let query ← (Option.getD · HashMap.empty) <$> option queryParser
  let fragment ← (Option.getD · HashMap.empty) <$> option fragmentParser
  return { scheme, host, port := optPort, path, query, fragment, userInfo : URI }

end Parser

def parse (s : String) : Except String URI := Parser.url.parse s

def tests : IO Unit := do
  toString <$> (IO.ofExcept <| URI.parse "test://host/path") >>= IO.println
  toString <$> (IO.ofExcept <| URI.parse "git+ssh://github.io/path/1/2") >>= IO.println
  return ()

end URI

end Tests
