import Mathlib
import TuringTask.Transpose

/-!
# The five statements

The results of `Zolotarev`, `Units`, `Power` and `Transpose` in the form of the task.
-/

namespace TuringTask

open Equiv

/-- Zolotarev and Frobenius: for odd `n`, `sgn μ_a = J(a | n)`. -/
theorem main_odd (n a : ℕ) [NeZero n] (hn : n % 2 = 1) (ha : Nat.Coprime a n) :
    (Equiv.Perm.sign (Units.mulLeft (ZMod.unitOfCoprime a ha)) : ℤ) = jacobiSym a n :=
  sign_odd n hn a ha

/-- Lerch: the sign of `μ_a` for even `n`. -/
theorem main_even (n a : ℕ) [NeZero n] (hn : n % 2 = 0) (ha : Nat.Coprime a n) :
    (Equiv.Perm.sign (Units.mulLeft (ZMod.unitOfCoprime a ha)) : ℤ) =
      if n % 4 = 2 then 1 else if a % 4 = 1 then 1 else -1 :=
  sign_even n hn a ha

/-- The sign of `u ↦ a u` on the unit group. -/
theorem main_units (n : ℕ) [NeZero n] (u : (ZMod n)ˣ) :
    Equiv.Perm.sign (Equiv.mulLeft u) = -1 ↔
      (n = 4 ∨ ∃ p k : ℕ, p.Prime ∧ p % 2 = 1 ∧ 0 < k ∧ (n = p ^ k ∨ n = 2 * p ^ k)) ∧
        ¬ IsSquare u :=
  sign_units_iff n u

/-- The sign of a bijective power map modulo a prime. -/
theorem main_pow (p k : ℕ) [NeZero p] (hp : p.Prime)
    (hk : Function.Bijective (fun x : ZMod p => x ^ k)) :
    (Equiv.Perm.sign (Equiv.ofBijective (fun x : ZMod p => x ^ k) hk) : ℤ) =
      if p % 4 = 1 ∧ k % 4 = 3 then -1 else 1 :=
  sign_powMap p k hp hk

/-- The sign of the transposition of an `m × n` array. -/
theorem main_transpose (m n : ℕ) :
    (Equiv.Perm.sign ((finProdFinEquiv.symm.trans (Equiv.prodComm (Fin m) (Fin n))).trans
        (finProdFinEquiv.trans (finCongr (Nat.mul_comm n m)))) : ℤ) =
      (-1) ^ (Nat.choose m 2 * Nat.choose n 2) :=
  sign_transpose' m n

end TuringTask
