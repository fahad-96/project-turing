import Mathlib

namespace TuringTask

noncomputable def csum (p : Nat) [Fact p.Prime] (c : Int) : Int :=
  Finset.sum (Finset.range p) (fun x : Nat => legendreSym p ((x : Int) ^ 3 - c * (x : Int)))

theorem csum_sq_add_sq (p : Nat) [Fact p.Prime] (hp : p % 4 = 1) (c r : Int)
    (hc : legendreSym p c = 1) (hr : legendreSym p r = -1) :
    csum p c ^ 2 + csum p r ^ 2 = 4 * (p : Int) := by
  sorry

theorem csum_sq_of_sq (p : Nat) [Fact p.Prime] (hp : p % 4 = 1) (a b c : Int)
    (hab : a ^ 2 + b ^ 2 = (p : Int)) (ha : a % 2 = 1) (hc : legendreSym p c = 1) :
    csum p c ^ 2 = 4 * a ^ 2 := by
  sorry

theorem csum_one_emod (p : Nat) [Fact p.Prime] (hp : p % 4 = 1) :
    csum p 1 % 8 = if p % 8 = 5 then 2 else 6 := by
  sorry

theorem choose_modEq (p : Nat) [Fact p.Prime] (hp : p % 4 = 1) (a b : Int)
    (hab : a ^ 2 + b ^ 2 = (p : Int)) (ha : a % 4 = 1) :
    Int.ModEq (p : Int) ((Nat.choose (p / 2) (p / 4) : Nat) : Int) (2 * a) := by
  sorry

theorem card_curve (p : Nat) [Fact p.Prime] (hp : p % 4 = 1) (a b : Int)
    (hab : a ^ 2 + b ^ 2 = (p : Int)) (ha : a % 4 = 1) :
    ((Finset.univ.filter (fun q : Prod (ZMod p) (ZMod p) => q.2 ^ 2 = q.1 ^ 3 - q.1)).card : Int) =
      (p : Int) - 2 * (-1) ^ (p / 4) * a := by
  sorry

end TuringTask
