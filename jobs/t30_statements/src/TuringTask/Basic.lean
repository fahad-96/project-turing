import Mathlib

namespace TuringTask

theorem sum_divisors_sum_dedekind_eq_sigma_mul (s : Nat -> Nat -> Rat)
    (hs : forall x y : Nat, s x y = Finset.sum (Finset.range y) (fun r =>
      ((r : Rat) / y - 1 / 2) *
        (if x * r % y = 0 then 0 else ((x * r % y : Nat) : Rat) / y - 1 / 2)))
    (h k n : Nat) :
    Finset.sum (Nat.divisors n) (fun d =>
        Finset.sum (Finset.range d) (fun b => s (n / d * h + b * k) (d * k))) =
      (ArithmeticFunction.sigma 1 n : Rat) * s h k := by
  sorry

theorem exists_int_eq_two_mul_gcd_mul_dedekind (s : Nat -> Nat -> Rat)
    (hs : forall x y : Nat, s x y = Finset.sum (Finset.range y) (fun r =>
      ((r : Rat) / y - 1 / 2) *
        (if x * r % y = 0 then 0 else ((x * r % y : Nat) : Rat) / y - 1 / 2)))
    (h k : Nat) :
    exists m : Int, ((2 * Nat.gcd 3 k * k : Nat) : Rat) * s h k = m := by
  sorry

theorem dedekind_modEq_eight (s : Nat -> Nat -> Rat)
    (hs : forall x y : Nat, s x y = Finset.sum (Finset.range y) (fun r =>
      ((r : Rat) / y - 1 / 2) *
        (if x * r % y = 0 then 0 else ((x * r % y : Nat) : Rat) / y - 1 / 2)))
    (h k : Nat) (hk : k % 2 = 1) (hhk : Nat.Coprime h k) :
    exists m : Int, (12 * k : Rat) * s h k = k + 1 - 2 * jacobiSym h k + 8 * m := by
  sorry

theorem dedekind_eq_zero_iff (s : Nat -> Nat -> Rat)
    (hs : forall x y : Nat, s x y = Finset.sum (Finset.range y) (fun r =>
      ((r : Rat) / y - 1 / 2) *
        (if x * r % y = 0 then 0 else ((x * r % y : Nat) : Rat) / y - 1 / 2)))
    (h k : Nat) (hk : 0 < k) (hhk : Nat.Coprime h k) :
    s h k = 0 <-> (h ^ 2 + 1) % k = 0 := by
  sorry

theorem dedekind_eq_iff (s : Nat -> Nat -> Rat)
    (hs : forall x y : Nat, s x y = Finset.sum (Finset.range y) (fun r =>
      ((r : Rat) / y - 1 / 2) *
        (if x * r % y = 0 then 0 else ((x * r % y : Nat) : Rat) / y - 1 / 2)))
    (a b k : Nat) (hk : k.Prime) (ha : Nat.Coprime a k) (hb : Nat.Coprime b k) :
    s a k = s b k <-> (a % k = b % k \/ a * b % k = 1) := by
  sorry

end TuringTask
