namespace Compiler.Json

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + '0'.toNat) else Char.ofNat (n - 10 + 'a'.toNat)

private def toHex2 (n : Nat) : String :=
  let hi := n / 16
  let lo := n % 16
  String.mk [hexDigit hi, hexDigit lo]

def escapeJsonChar (c : Char) : String :=
  match c with
  | '"' => "\\\""
  | '\\' => "\\\\"
  | '\n' => "\\n"
  | '\r' => "\\r"
  | '\t' => "\\t"
  | '\u0008' => "\\b"
  | '\u000c' => "\\f"
  | _ =>
      if c.toNat < 0x20 then
        "\\u00" ++ toHex2 c.toNat
      else
        String.singleton c

def escapeJsonString (s : String) : String :=
  s.data.foldl (fun acc c => acc ++ escapeJsonChar c) ""

def jsonString (s : String) : String :=
  "\"" ++ escapeJsonString s ++ "\""

def jsonArray (items : List String) : String :=
  "[" ++ String.intercalate "," items ++ "]"

def jsonObject (fields : List (String × String)) : String :=
  "{" ++ String.intercalate "," (fields.map fun (name, value) => jsonString name ++ ":" ++ value) ++ "}"

end Compiler.Json
