import TuringTask.Basic

open TuringTask

example (p : Nat) [Fact p.Prime] (hp : p % 3 = 1) (L M : Int)
    (hLM : 4 * (p : Int) = L ^ 2 + 27 * M ^ 2) (hL : L % 3 = 1) :
    ((Finset.univ.filter (fun q : Prod (ZMod p) (ZMod p) => q.1 ^ 3 + q.2 ^ 3 = 1)).card : Int) =
      (p : Int) - 2 + L :=
  TuringTask.card_cubic p hp L M hLM hL

example (p : Nat) [Fact p.Prime] (hp : p % 3 = 1) (L M : Int)
    (hLM : 4 * (p : Int) = L ^ 2 + 27 * M ^ 2) (hL : L % 3 = 1) :
    9 * ((Finset.univ.filter (fun x : ZMod p => Not (x = 0) /\ Not (x + 1 = 0) /\
      (exists u : ZMod p, u ^ 3 = x) /\ (exists v : ZMod p, v ^ 3 = x + 1))).card : Int) =
      (p : Int) - 8 + L :=
  TuringTask.card_cube_pairs p hp L M hLM hL

example (p : Nat) [Fact p.Prime] (hp : p % 3 = 1) (L M : Int)
    (hLM : 4 * (p : Int) = L ^ 2 + 27 * M ^ 2) (hL : L % 3 = 1) :
    9 * ((Finset.univ.filter (fun x : ZMod p => Not (exists u : ZMod p, u ^ 3 = x) /\
      Not (exists v : ZMod p, v ^ 3 = x + 1) /\
      (exists w : ZMod p, w ^ 3 = x * (x + 1)))).card : Int) =
      2 * ((p : Int) + 1 + L) :=
  TuringTask.card_noncube_pairs p hp L M hLM hL

example (p : Nat) [Fact p.Prime] (hp : p % 3 = 1) :
    (exists z : ZMod p, z ^ 3 = 2) <-> exists x y : Int, (p : Int) = x ^ 2 + 27 * y ^ 2 :=
  TuringTask.two_cube_iff p hp

example (p : Nat) [Fact p.Prime] (hp : p % 3 = 1) (L M : Int)
    (hLM : 4 * (p : Int) = L ^ 2 + 27 * M ^ 2) (hL : L % 3 = 1)
    (a : ZMod p) (ha : Not (a = 0)) (G : Complex)
    (hG : G = Finset.sum Finset.univ (fun x : ZMod p =>
      Complex.exp (2 * Real.pi * Complex.I * ((a * x ^ 3).val : Complex) / (p : Complex)))) :
    G ^ 3 = 3 * (p : Complex) * G + (p : Complex) * (L : Complex) :=
  TuringTask.cubic_sum p hp L M hLM hL a ha G hG

#print axioms TuringTask.card_cubic
#print axioms TuringTask.card_cube_pairs
#print axioms TuringTask.card_noncube_pairs
#print axioms TuringTask.two_cube_iff
#print axioms TuringTask.cubic_sum
