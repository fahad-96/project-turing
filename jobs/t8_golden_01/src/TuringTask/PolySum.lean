import Mathlib
import TuringTask.Phase

/-!
# Averages of `exp(2 pi i P(n))` for polynomials with irrational leading coefficient

`tendsto_avg_ephase_poly`: if `P` has degree `m + 1` and an irrational leading coefficient, then
`(1/N) sum_(n<N) ephase (P n) -> 0`.  Degree one is a geometric sum; the induction step applies
`tendsto_avg_zero_of_corr` to the shifted differences `P(X + r) - P(X)`.
-/

open Finset Filter Polynomial

namespace TuringTask

/-- The shifted difference `P(X + r) - P(X)` of a polynomial of degree `m + 1` has degree at most
`m`, and its coefficient of `X^m` is `(m + 1) r lc(P)`. -/
lemma shift_sub_natDegree_coeff (P : ℝ[X]) (m : ℕ) (hP : P.natDegree = m + 1) (r : ℝ) :
    (taylor r P - P).natDegree ≤ m ∧
      (taylor r P - P).coeff m = (m + 1) * r * P.leadingCoeff := by
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hP
  constructor
  · by_cases h0 : taylor r P - P = 0
    · rw [h0, natDegree_zero]
      exact Nat.zero_le _
    · have hlt : (taylor r P - P).degree < (taylor r P).degree :=
        degree_sub_lt (degree_taylor P r) ((taylor_eq_zero r P).not.mpr hP0)
          (leadingCoeff_taylor r P)
      have := natDegree_lt_natDegree h0 hlt
      rw [natDegree_taylor, hP] at this
      omega
  · rw [coeff_sub, taylor_coeff]
    have hdeg : (hasseDeriv m P).natDegree < 2 := by
      rw [natDegree_hasseDeriv, hP]
      omega
    rw [eval_eq_sum_range' hdeg, Finset.sum_range_succ, Finset.sum_range_one,
      hasseDeriv_coeff, hasseDeriv_coeff, leadingCoeff, hP]
    simp only [zero_add, Nat.choose_self, Nat.cast_one, one_mul, pow_zero, mul_one, pow_one]
    rw [add_comm 1 m, Nat.choose_succ_self_right]
    push_cast
    ring

lemma ephase_ne_one_of_irrational (a : ℝ) (ha : Irrational a) : ephase a ≠ 1 := by
  intro h
  unfold ephase at h
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
  apply ha
  refine ⟨k, ?_⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have e : ((a : ℝ) : ℂ) = (k : ℂ) := by
    have := hk
    push_cast at this
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [hpi, Complex.I_ne_zero]
    apply mul_right_cancel₀ h2
    linear_combination this
  exact_mod_cast e.symm

/-- Degree one: a geometric sum. -/
lemma tendsto_avg_ephase_linear (a b : ℝ) (ha : Irrational a) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, ephase (a * n + b)) / N) atTop (nhds 0) := by
  set q := ephase a with hq
  have hq1 : q ≠ 1 := ephase_ne_one_of_irrational a ha
  have hq1' : q - 1 ≠ 0 := sub_ne_zero.mpr hq1
  have hsum : ∀ N : ℕ, ∑ n ∈ range N, ephase (a * n + b) = ephase b * ((q ^ N - 1) / (q - 1)) := by
    intro N
    rw [← geom_sum_eq hq1, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [ephase_add, mul_comm a, ephase_nat_mul, mul_comm]
  have hbound : ∀ N : ℕ, ‖(∑ n ∈ range N, ephase (a * n + b)) / N‖ ≤ (2 / ‖q - 1‖) / N := by
    intro N
    rw [hsum, norm_div, norm_mul, norm_ephase, one_mul, norm_div, Complex.norm_natCast]
    gcongr
    calc ‖q ^ N - 1‖ ≤ ‖q ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hq, norm_ephase]; norm_num
  exact squeeze_zero_norm hbound (tendsto_const_div_atTop_nhds_zero_nat _)

/-- Weyl's theorem on polynomial phases, in the form needed here. -/
theorem tendsto_avg_ephase_poly (m : ℕ) :
    ∀ P : ℝ[X], P.natDegree = m + 1 → Irrational P.leadingCoeff →
      Tendsto (fun N : ℕ => (∑ n ∈ range N, ephase (P.eval (n : ℝ))) / N) atTop (nhds 0) := by
  induction m with
  | zero =>
    intro P hP hirr
    have hP1 : P.natDegree ≤ 1 := hP.le
    have e := eq_X_add_C_of_natDegree_le_one hP1
    have hlc : P.leadingCoeff = P.coeff 1 := by rw [leadingCoeff, hP]
    have hev : ∀ n : ℕ, P.eval (n : ℝ) = P.coeff 1 * n + P.coeff 0 := by
      intro n
      conv_lhs => rw [e]
      simp
    simp_rw [hev]
    exact tendsto_avg_ephase_linear _ _ (hlc ▸ hirr)
  | succ m ih =>
    intro P hP hirr
    apply tendsto_avg_zero_of_corr (fun n => ephase (P.eval (n : ℝ)))
      (fun n => (norm_ephase _).le)
    intro r hr
    obtain ⟨hdeg, hcoeff⟩ := shift_sub_natDegree_coeff P (m + 1) hP r
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
    have hlc0 : P.leadingCoeff ≠ 0 := hirr.ne_zero
    have hm0 : ((m + 1 : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    have hc0 : (taylor (r : ℝ) P - P).coeff (m + 1) ≠ 0 := by
      rw [hcoeff]
      exact mul_ne_zero (mul_ne_zero hm0 hr0) hlc0
    have hdeg' : (taylor (r : ℝ) P - P).natDegree = m + 1 :=
      le_antisymm hdeg (le_natDegree_of_ne_zero hc0)
    have hlc' : (taylor (r : ℝ) P - P).leadingCoeff = (m + 2 : ℕ) * r * P.leadingCoeff := by
      rw [leadingCoeff, hdeg', hcoeff]
      push_cast
      ring
    have hirr' : Irrational (taylor (r : ℝ) P - P).leadingCoeff := by
      rw [hlc', mul_assoc]
      refine Irrational.natCast_mul ?_ (by omega)
      exact Irrational.natCast_mul hirr (by omega)
    have key := ih _ hdeg' hirr'
    refine key.congr fun N => ?_
    congr 1
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [ephase_mul_conj, eval_sub, taylor_eval]
    push_cast
    ring_nf

end TuringTask
