import Mathlib

/-!
# Polynomial lemmas for Weyl differencing

The key fact: if `P` has degree `d ≥ 1` and `r ≠ 0`, then `Q = P(X + r) - P(X)` has degree
`d - 1` and leading coefficient `d * r * P.leadingCoeff`.
-/

open Polynomial

namespace TuringTask

noncomputable section

variable {P : ℝ[X]}

/-- The top Hasse derivative of a polynomial of degree at most `d` is the constant `coeff d`. -/
lemma hasseDeriv_top (P : ℝ[X]) {d : ℕ} (hd : P.natDegree ≤ d) :
    hasseDeriv d P = C (P.coeff d) := by
  have h0 : (hasseDeriv d P).natDegree = 0 := by
    have h := P.natDegree_hasseDeriv_le d
    omega
  have h1 := eq_C_of_natDegree_eq_zero h0
  rw [h1, hasseDeriv_coeff]
  simp

/-- The second-from-top Hasse derivative of a polynomial of degree at most `d`. -/
lemma hasseDeriv_sub_one (P : ℝ[X]) {d : ℕ} (hd : P.natDegree ≤ d) (hd1 : 1 ≤ d) :
    hasseDeriv (d - 1) P = C ((d : ℝ) * P.coeff d) * X + C (P.coeff (d - 1)) := by
  have hle : (hasseDeriv (d - 1) P).natDegree ≤ 1 := by
    have h := P.natDegree_hasseDeriv_le (d - 1)
    omega
  have h1 := eq_X_add_C_of_natDegree_le_one hle
  rw [h1]
  congr 1
  · congr 1
    rw [hasseDeriv_coeff]
    have : 1 + (d - 1) = d := by omega
    rw [this]
    have : d.choose (d - 1) = d := by
      have h := Nat.choose_symm (show d - 1 ≤ d by omega)
      rw [← h]
      have h2 : d - (d - 1) = 1 := by omega
      rw [h2, Nat.choose_one_right]
    rw [this]
  · congr 1
    rw [hasseDeriv_coeff]
    simp

/-- The difference polynomial `P(X + r) - P(X)`. -/
def diffPoly (P : ℝ[X]) (r : ℝ) : ℝ[X] := P.comp (X + C r) - P

lemma eval_diffPoly (P : ℝ[X]) (r x : ℝ) :
    (diffPoly P r).eval x = P.eval (x + r) - P.eval x := by
  simp [diffPoly, eval_comp]

/-- `P.comp (X + C r)` has the same degree as `P`. -/
lemma natDegree_comp_shift (P : ℝ[X]) (r : ℝ) :
    (P.comp (X + C r)).natDegree = P.natDegree := by
  rw [natDegree_comp, natDegree_X_add_C, mul_one]

/-- The `k`-th coefficient of `P.comp (X + C r)` is `eval r (hasseDeriv k P)`. -/
lemma coeff_comp_shift (P : ℝ[X]) (r : ℝ) (k : ℕ) :
    (P.comp (X + C r)).coeff k = (hasseDeriv k P).eval r := by
  rw [← taylor_apply, taylor_coeff]

/-- Degree of the difference polynomial. -/
lemma natDegree_diffPoly_le (P : ℝ[X]) {d : ℕ} (hd : P.natDegree ≤ d) (hd1 : 1 ≤ d) (r : ℝ) :
    (diffPoly P r).natDegree ≤ d - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  have hNd : d ≤ N := by omega
  rcases eq_or_lt_of_le hNd with (rfl | hlt)
  · -- N = d
    simp only [diffPoly, coeff_sub, coeff_comp_shift]
    rw [hasseDeriv_top P hd]
    simp
  · -- N > d
    have h1 : (P.comp (X + C r)).coeff N = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_comp_shift]; omega
    have h2 : P.coeff N = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    simp [diffPoly, coeff_sub, h1, h2]

/-- Top coefficient of the difference polynomial. -/
lemma coeff_diffPoly_top (P : ℝ[X]) {d : ℕ} (hd : P.natDegree ≤ d) (hd1 : 1 ≤ d) (r : ℝ) :
    (diffPoly P r).coeff (d - 1) = (d : ℝ) * r * P.coeff d := by
  have hdd : d - 1 + 1 = d := by omega
  simp only [diffPoly, coeff_sub, coeff_comp_shift]
  rw [hasseDeriv_sub_one P hd hd1]
  simp only [eval_add, eval_mul, eval_C, eval_X]
  ring

end

end TuringTask
