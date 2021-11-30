Add LoadPath "c:\users\aap\documents\github\advent2021v\" as ADV.
From ADV Require Import day1_2020.
Require Export Coq.Strings.String.
Require Export Coq.Strings.Ascii.
Require Export Coq.PArith.BinPosDef.
Require Export BinNums.
Local Open Scope string_scope.

Definition empty_string := "".

Inductive regex : Set :=
  | Empty : regex
  | Char : ascii -> regex
  | Union : regex -> regex -> regex
  | App : regex -> regex -> regex.

Local Open Scope char_scope.

Fixpoint union_list (l : list ascii) :=
  match l with
  | [] => Empty
  | x :: xs => Union (Char x) (union_list xs)
  end.

Definition digits := union_list ["0";"1";"2";"3";"4";"5";"6";"7";"8";"9"].

Definition lowercase := union_list ["a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z"].

Definition uppercase := union_list ["A";"B";"C";"D";"E";"F";"G";"H";"I";"J";"K";"L";"M";"N";"O";"P";"Q";"R";"S";"T";"U";"V";"W";"X";"Y";"Z"].

Definition pseq (start length:nat) : list positive :=
  map Pos.of_nat (seq start length).
    
Definition allchars_list := map ascii_of_pos (pseq 0%nat 128%nat).

Definition neg_union_list (l : list ascii) :=
  let nchars := filter (fun c => existsb (fun c2 => c =? c2) l) allchars_list in
  union_list nchars.

Definition whitespace := union_list ["032";"009";"010";"011";"012";"013"].

Definition non_whitespace := neg_union_list ["032";"009";"010";"011";"012";"013"].

Local Open Scope nat_scope.

Fixpoint appn n r :=
  match n with
  | 0 => Empty
  | S n' => App r (appn n' r)
  end.

Fixpoint star n r := 
  match n with
  | 0 => Empty
  | S n' => Union (appn n r) (star n' r)
  end.

Local Close Scope nat_scope.

Fixpoint matchat (reg : regex) (s : string) :=
  match reg with
  | Char c => 
    match s with
    | EmptyString => (false, s)
    | String a ss => (a =? c, ss)
    end
  | Union r1 r2 => 
    let v1 := matchat r1 s in
    let v2 := matchat r2 s in
    if (fst v1) then v1
    else
      if (fst v2) then v2
      else (false, empty_string)
  | App r1 r2 =>
    let v1 := matchat r1 s in
    if fst v1 then matchat r2 (snd v1) else (false, empty_string)
  | Empty => (true, s)
  end.

Inductive capture_results : Set :=
  | nocap : capture_results
  | capture : ascii -> capture_results
  | app_capture : capture_results -> capture_results -> capture_results.

Local Close Scope char_scope.

Fixpoint normalize_caps (apc : capture_results) :=
  match apc with
  | nocap => [empty_string]
  | capture c => [String c EmptyString]
  | app_capture (capture c) apc' =>
    let v1 := normalize_caps apc' in
    match v1 with
    | [] => []
    | [s] => [append (String c EmptyString) s]
    | x :: xs => (append (String c EmptyString) x) :: xs
    end
  | app_capture al ar => app (normalize_caps al) (normalize_caps ar)
  end.

Fixpoint norm2 (sl : list string) :=
  match sl with
  | [] => []
  | "" :: xs => norm2 xs
  | b :: xs => b :: (norm2 xs)
  end. 

Local Open Scope char_scope.

Fixpoint captchat (reg : regex) (s : string) :=
  match reg with
  | Char c => 
    match s with
    | EmptyString => (false, empty_string, nocap)
    | String a ss => (a =? c, ss, if a =? c then capture c else nocap )
    end
  | Union r1 r2 => 
    let v1 := captchat r1 s in
    let v2 := captchat r2 s in
    if (fst (fst v1)) then v1
    else
      if (fst (fst v2)) then v2
      else (false, empty_string, nocap)
  | App r1 r2 =>
    let v1 := captchat r1 s in
    if fst (fst v1) 
    then 
      let v2 := captchat r2 (snd (fst v1)) in 
      if fst (fst v2)
      then (fst v2, app_capture (snd v1) (snd v2))
      else (false, empty_string, nocap)
    else (false, empty_string, nocap)
  | Empty => (true, s, nocap)
  end.
