Require Export String.
Require Export Coq.Numbers.BinNums.
Require Export PArith.
Require Export Coq.Lists.List.
Require Export Coq.Init.Nat.
Require Export Coq.Sorting.Mergesort.
Add LoadPath "c:\users\aap\documents\github\advent2021v\" as ADV.
From ADV Require Export Maps.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(* list option helpers *)

Fixpoint firstsome {T : Type} (l1 : list (option T)) (defaultval : T) :=
  match l1 with
  | [] => defaultval
  | Some v :: l1' => v
  | None :: l1' => firstsome l1' defaultval
  end.

(* list bool helpers *)
Definition hasb {T : Type} (l : list T) := 
  match l with
  | [] => false
  | x :: xs => true
  end.

(* pair option helpers *)

Definition optout {T : Type} (p1 : T * option T) :=
  match snd p1 with
  | None => None
  | Some p => Some (fst p1, p)
  end.

(* double list helpers *)

Definition cross {T : Type} (l1 : list T) (l2 : list T) :=
  flat_map (fun t => map (fun s => (t,s)) l2) l1. 

Definition cross3 {T : Type} (l1 : list T) (l2 : list T) (l3 : list T) :=
  flat_map (fun t => flat_map (fun s => map (fun u => (t,s,u)) l3) l2) l1. 

Definition crossfilter {T : Type} (f : T -> T -> bool) (l1 : list T) (l2 : list T) :=
  let fp := (fun w => f (fst w) (snd w)) in
  filter fp (cross l1 l2).

Definition crossfilter3 {T : Type} (f : T -> T -> T -> bool) (l1 : list T) (l2 : list T) (l3 : list T) :=
  let fp3 := (fun (w : T * T * T) => f (fst (fst w)) (snd (fst w)) (snd w)) in
  filter fp3 (cross3 l1 l2 l3).

(* Input : receive values as Positive binary type  not Peano *)
Open Scope positive_scope.

Definition day1_2020_input := [1974;1902;1356;1724;1550;1870;1436;1945;1640;1766;1508;1802;1495;1837;131;1754;1296;1627;1768;1451;1252;1566;1611;1531;1868;1745;1894;1799;1948;1930;1400;2003;1777;1279;472;1474;1787;1406;1522;1646;1865;1581;1609;1705;1383;1276;1613;1190;1856;1528;1091;1540;1720;1824;1734;1919;1681;1686;1344;1644;1670;1710;1708;1458;1728;1972;1630;1995;1763;1935;451;1392;1990;14;1893;1437;1632;1933;1887;1975;1453;1897;2005;2008;1959;1716;1635;1619;1994;1674;1942;1817;1825;196;769;1065;1662;1079;1574;1554;1621;1857;1312;1544;2001;1991;1602;1669;1982;1309;1556;1855;1284;1641;1786;735;1921;1661;1934;1552;1012;1748;1782;1631;1607;1659;1997;1600;1594;1798;1405;1790;1993;1960;1717;999;1687;1771;1977;1809;1884;1795;1639;1565;1299;1643;1700;2002;1823;1369;1572;1657;1683;1966;1606;1792;1756;1936;1718;2009;1711;1461;1638;1645;1914;1963;1546;1846;1737;1788;1589;1860;1830;1905;1571;1989;1780;1878;1767;1776;1727;1582;1769;1040;694;1327;1623;1688;1694;1932;2000;1969;1590;1425;1917;1324;1852;1753;1743;1551].

Definition rule n m := n + m =? 2020.

Definition rule3 n m o := n + m + o =? 2020.

Definition matchpairs := crossfilter rule day1_2020_input day1_2020_input.

Definition fstpair := if hasb matchpairs then nth O matchpairs (1,1) else (1,1).

Definition mp3 := crossfilter3 rule3 day1_2020_input day1_2020_input day1_2020_input.

Definition fst3p := if hasb mp3 then nth O mp3 (1,1,1) else (1,1,1).

Definition resultP1 := fst fstpair * snd fstpair.

Definition resultP2 := fst (fst fst3p) * snd (fst fst3p) * snd fst3p.

(* Expect 357504 *)
Compute resultP1.
(* Expect 12747392 *)
Compute resultP2.


