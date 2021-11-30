Add LoadPath "c:\users\aap\documents\github\advent2021v\" as ADV.
From ADV Require Import day1_2020.
From ADV Require Import regex.
Require Import Decimal.
Require Export Coq.Strings.String.
Require Export Coq.Strings.Ascii.
Require Export Coq.PArith.BinPosDef.
Require Export BinNums.
Require Export Coq.Numbers.DecimalString.
Local Open Scope string_scope.

Load "day2_2020_input.V".


Local Close Scope string_scope.
Local Open Scope char_scope.
Check day2_2020_input.

Definition line_regex := 
  (* (star 2 digits)-(star 2 digits) whitespace lowercase: whitespace (star 50 lowercase) *)
  let s2dig := star 2 digits in
  let dash := Char "-" in
  let col := Char ":" in
  let s50low := star 50 lowercase in
  App s2dig (App dash (App s2dig (App whitespace (App lowercase (App col (App whitespace s50low)))))).

Search regex.

Definition cap_results := (map (captchat line_regex) day2_2020_input).

Definition normalize := map (fun w => norm2 (normalize_caps (snd w))) cap_results.

Check normalize.

Local Close Scope char_scope.

Definition parse_list (ls : list string) :=
  match ls with
  | min_str :: max_str :: leftover :: xs => (min_str, max_str, leftover)
  | _ => (empty_string,empty_string,empty_string)
  end. 

Definition destruct1 := map parse_list normalize.

Local Open Scope Z_scope.


Definition destruct2 := map (fun w => (BinInt.Z.of_int (NilEmpty.int_of_string (fst (fst w))), opp (BinInt.Z.of_int (NilEmpty.int_of_string (snd (fst w)))), snd w)) destruct1. 


Compute destruct2. 
