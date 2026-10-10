import Mathlib

namespace TuringTask

theorem card_cubic (p : Nat) [Fact p.Prime] (hp : p % 3 = 1) (L M : Int)
    (hLM : 4 * (p : Int) = L ^ 2 + 27 * M ^ 2) (hL : L % 3 = 1) :
    ((Finset.univ.filter (fun q : Prod (ZMod p) (ZMod p) => q.1 ^ 3 + q.2 ^ 3 = 1)).card : Int) =
      (p : Int) - 2 + L := by
  sorry

theorem card_cube_pairs (p : Nat) [Fact p.Prime] (hp : p % 3 = 1) (L M : Int)
    (hLM : 4 * (p : Int) = L ^ 2 + 27 * M ^ 2) (hL : L % 3 = 1) :
    9 * ((Finset.univ.filter (fun x : ZMod p => Not (x = 0) /\ Not (x + 1 = 0) /\
      (exists u : ZMod p, u ^ 3 = x) /\ (exists v : ZMod p, v ^ 3 = x + 1))).card : Int) =
      (p : Int) - 8 + L := by
  sorry

theorem card_noncube_pairs (p : Nat) [Fact p.Prime] (hp : p % 3 = 1) (L M : Int)
    (hLM : 4 * (p : Int) = L ^ 2 + 27 * M ^ 2) (hL : L % 3 = 1) :
    9 * ((Finset.univ.filter (fun x : ZMod p => Not (exists u : ZMod p, u ^ 3 = x) /\
      Not (exists v : ZMod p, v ^ 3 = x + 1) /\
      (exists w : ZMod p, w ^ 3 = x * (x + 1)))).card : Int) =
      2 * ((p : Int) + 1 + L) := by
  sorry

theorem two_cube_iff (p : Nat) [Fact p.Prime] (hp : p % 3 = 1) :
    (exists z : ZMod p, z ^ 3 = 2) <-> exists x y : Int, (p : Int) = x ^ 2 + 27 * y ^ 2 := by
  sorry

theorem cubic_sum (p : Nat) [Fact p.Prime] (hp : p % 3 = 1) (L M : Int)
    (hLM : 4 * (p : Int) = L ^ 2 + 27 * M ^ 2) (hL : L % 3 = 1)
    (a : ZMod p) (ha : Not (a = 0)) (G : Complex)
    (hG : G = Finset.sum Finset.univ (fun x : ZMod p =>
      Complex.exp (2 * Real.pi * Complex.I * ((a * x ^ 3).val : Complex) / (p : Complex)))) :
    G ^ 3 = 3 * (p : Complex) * G + (p : Complex) * (L : Complex) := by
  sorry

end TuringTask
