import Lean
import SMTParser.LexInit

namespace Auto
open Lexer
namespace Parser.SMTTerm

inductive LexVal
  | lparen
  | rparen
  -- n + dec * 10^(-ndec)
  | nat (n : Nat)
  -- n / m
  | rat (n : Nat) (m : Nat)
  | str (s : String)
  | symb (s : String)
  | kw (s : String)
  | reserved (s : String) -- e.g. "forall" and "exists"
deriving Inhabited, BEq, Hashable

def LexVal.toString : LexVal → String
| .lparen  => "("
| .rparen  => ")"
| .nat n   => s!"{n}"
| .rat n m =>
  let pow := s!"{m}".length - 1
  if m != Nat.pow 10 pow then
    panic!"LexVal :: .rat {n} {m} is not yet supported, because {m} is not a power of 10"
  else
    let nint := n / m
    let nfrac := n % m
    let nfracs := s!"{nfrac}"
    let nfracs :=
      String.mk ((List.range (pow - nfracs.length)).map (fun _ => '0')) ++
      nfracs
    s!"{nint}." ++ nfracs
| .str s   => "\"" ++ String.intercalate "\"\"" (s.splitOn "\"") ++ "\""
| .symb s  => s!"|{s}|"
| .kw s    => s!":{s}"
| .reserved s => s

instance : ToString LexVal where
  toString := LexVal.toString

private def hexDigitToNat (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def LexVal.ofString (s : String) (attr : String) : LexVal :=
  match attr with
  | "("           => .lparen
  | ")"           => .rparen
  | "numeral"     => .nat s.toNat!
  | "decimal"     =>
    if let [a, b] := s.splitOn "." then
      let a := a.toNat!
      let fracDigits := b.length
      let fracPow := Nat.pow 10 fracDigits
      let b := b.toNat!
      .rat (a * fracPow + b) fracPow
    else
      panic! s!"LexVal.ofString :: {repr s} is not a valid decimal number"
  | "hexadecimal" =>
    let hdigs := s.drop 2
    .nat (hdigs.foldl (fun x c => x * 16 + hexDigitToNat c) 0)
  | "binary" =>
    let bdigs := s.drop 2
    .nat (bdigs.foldl (fun x c => x * 2 + c.toNat - '0'.toNat) 0)
  | "string" =>
    let subs := ((s.drop 1).take (s.length - 2)).splitOn "\"\""
    .str (String.intercalate "\"" subs)
  | "simplesymbol" => .symb s
  | "quotedsymbol" => .symb ((s.drop 1).take (s.length - 2))
  | "keyword"      => .kw (s.drop 1)
  | "reserved"     => .reserved s
  | "forall"       => .reserved "forall"
  | "exists"       => .reserved "exists"
  | _              => panic! s!"LexVal.ofString :: {repr attr} is not a valid attribute"

inductive Term where
  | atom : LexVal → Term
  | app  : Array Term → Term
deriving Inhabited, BEq, Hashable

partial def Term.toString : Term → String
| .atom l => ToString.toString l
| .app ls => "(" ++ String.intercalate " " (ls.map toString).data ++ ")"

instance : ToString Term where
  toString e := Term.toString e

structure PartialResult where
  -- Lexer state
  lst     : Nat := 0
  -- Partially matched lexicon
  lexpart : String := ""
  -- Parser stack
  pstk    : Array (Array Term) := #[]
deriving Inhabited, BEq, Hashable

def PartialResult.toString : PartialResult → String := fun ⟨lst, lexpart, pstk⟩ =>
  s!"PartialResult \{ lst := {lst}, lexpart := {repr lexpart}, pstk := {pstk.toList.map (·.toList)}}"

instance : ToString PartialResult where
  toString := PartialResult.toString

inductive ParseResult where
  -- SMTTerm: Result
  -- String.pos: The position of the next character
  | complete   : Term → String.Pos → ParseResult
  -- Array (Array Sexp): Parser stack
  -- Nat: State of lexer
  -- String.pos: The position of the next character
  | incomplete : PartialResult → String.Pos → ParseResult
  -- Malformed input
  | malformed  : ParseResult
deriving Inhabited, BEq, Hashable

def ParseResult.toString : ParseResult → String
| .complete s p => s!"ParseResult.complete {s} {p}"
| .incomplete pr p => s!"ParseResult.incomplete {pr} {p}"
| .malformed => "ParseResult.malformed"

local instance : Hashable Char := ⟨fun c => hash c.val⟩

/--
  Note: Make sure that the next character of `s` is either `EOF` or white space
  This is because wee rely on the property that:
     For each lexicon `l` with a white space at position `p`, the
     part of `l` before `p` will always be identified as `incomplete`
     by `ERE.ADFALexEagerL SMTSexp.lexiconADFA`, and never as `done`.
-/
def parseTerm [Monad m] [Lean.MonadError m] (s : String) (p : String.Pos)
  (partialResult : PartialResult) : m ParseResult := do
  if p == s.endPos then
    return .incomplete partialResult p
  let nextLexicon (p : String.Pos) (lst : Nat) :=
    Regex.ERE.ADFALexEagerL SMT.lexiconADFA ⟨s, p, s.endPos⟩
      {strict := true, initS := lst, prependBeginS := false, appendEndS := false}
  let mut lst := partialResult.lst
  let mut lexpart := partialResult.lexpart
  let mut pstk := partialResult.pstk
  let mut p := p
  let endPos := s.endPos
  while true do
    -- If we're not resuming from an incomplete
    --   match of lexicon, skip white space
    if lexpart == "" then
      -- Skip whitespace characters
      while p != endPos do
        let c := s.get! p
        if SMT.whitespace.contains c then
          p := p + c
        else
          break
    -- This indicates incomplete input
    if p == endPos then
      return .incomplete ⟨0, "", pstk⟩ p
    match nextLexicon p lst with
    | ⟨.complete, matched, _, state⟩ =>
      -- It is possible for there to be more than one attr if "forall" or "exists" is interpreted
      -- both as a symbol and as a reserved word. If this happens, the reserved word should be prioritized
      let attr ←
        match (SMT.lexiconADFA.getAttrs state).toList with
        | [attr] => pure attr
        | [attr1, attr2] =>
          if attr1 == "forall" || attr1 == "exists" then pure attr1
          else if attr2 == "forall" || attr2 == "exists" then pure attr2
          else throwError "parseTerm :: Attribute conflict not caused by forall or exists"
        | _ => throwError "parseTerm :: Invalid number of attributes"

      p := matched.stopPos
      let lexval := LexVal.ofString (lexpart ++ matched.toString) attr
      -- Restore lexer state
      lst := 0; lexpart := ""
      match lexval with
      | .lparen =>
        pstk := pstk.push #[]
      | .rparen =>
        if pstk.size == 0 then
          -- Too many right parentheses
          return .malformed
        else
          let final := pstk.back
          pstk := pstk.pop
          if pstk.size == 0 then
            return .complete (.app final) p
          else
            pstk := pstk.modify (pstk.size - 1) (fun arr => arr.push (.app final))
      | l       =>
        -- Ordinary lexicons must be separated by whitespace or parentheses
        match s.get? p with
        | some c =>
          if !SMT.whitespace.contains c ∧ c != ')' ∧ c != '(' then
            return .malformed
        | none => pure ()
        if pstk.size == 0 then
          -- An atom
          return .complete (.atom lexval) p
        pstk := pstk.modify (pstk.size - 1) (fun arr => arr.push (.atom l))
    | ⟨.incomplete, m, _, lst'⟩ => return .incomplete ⟨lst', lexpart ++ m.toString, pstk⟩ m.stopPos
    | ⟨.malformed, _, _, _⟩  => return .malformed
  throwError s!"parseSexp :: Unexpected error when parsing string {s}"

private def testit (s : String) (p : String.Pos) (print := true) : Lean.Meta.MetaM Unit := do
  match ← parseTerm s p {} with
  | .complete e p => if print then IO.println e; IO.println (Substring.toString ⟨s, p, s.endPos⟩)
  | .malformed .. => IO.println "malformed"
  | .incomplete .. => IO.println "incomplete"

#eval testit "(exists (x Int) (y Int) x0)" ⟨0⟩
