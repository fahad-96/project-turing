import Mathlib
import TuringTask.Poly
import TuringTask.Weyl
import TuringTask.Equid
import TuringTask.Criterion
import TuringTask.Trap
import TuringTask.Bridge
import TuringTask.Digits

/-!
# Weyl equidistribution: the five theorems

All five statements are consequences of Weyl's equidistribution theorem for polynomial
sequences, proved in `TuringTask.Equid` via van der Corput's inequality, combined with the
Weyl criterion (`TuringTask.Criterion`) and the transfer to interval indicators
(`TuringTask.Trap`, `TuringTask.Bridge`).
-/

open Finset Filter Complex Polynomial MeasureTheory AddCircle

namespace TuringTask

set_option maxHeartbeats 1000000

noncomputable section

/-- A real polynomial of degree at least one with irrational leading coefficient gives rise to
an equidistributed sequence. -/
lemma weylEquid_poly (P : Polynomial ℝ) (hP : Irrational P.leadingCoeff)
    (hdeg : 1 ≤ P.natDegree) : WeylEquid (fun n : ℕ => P.eval (n : ℝ)) := by
  apply weylEquid_of_weylNull
  intro m hm
  have hmP : (fun n : ℕ => (m : ℝ) * P.eval (n : ℝ))
      = fun n : ℕ => (Polynomial.C (m : ℝ) * P).eval (n : ℝ) := by funext n; simp
  rw [hmP]
  apply weylNull_main P.natDegree hdeg
  · rw [Polynomial.natDegree_C_mul (by exact_mod_cast hm)]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_natDegree]
    exact hP.intCast_mul hm

end

theorem freq_sq_unif (x : Real) (hx : Irrational x) (e : Real) (he : 0 < e) :
    exists N0 : Nat, forall N : Nat, N0 <= N -> forall a b : Real, 0 <= a -> a <= b -> b <= 1 ->
      abs ((((Finset.range N).filter (fun n : Nat =>
        a <= Int.fract ((n : Real) ^ 2 * x) /\ Int.fract ((n : Real) ^ 2 * x) < b)).card : Real)
        / N - (b - a)) < e := by
  classical
  set P : Polynomial ℝ := Polynomial.C x * Polynomial.X ^ 2 with hP
  have hlead : P.leadingCoeff = x := by
    rw [hP, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_X_pow, mul_one]
  have hdeg : P.natDegree = 2 := by
    rw [hP, Polynomial.natDegree_C_mul hx.ne_zero, Polynomial.natDegree_X_pow]
  have hg := weylEquid_poly P (by rw [hlead]; exact hx) (by omega)
  have heval : ∀ n : ℕ, P.eval (n : ℝ) = (n : ℝ) ^ 2 * x := by
    intro n
    rw [hP, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      mul_comm]
  obtain ⟨N0, hN0⟩ := cnt_unif_ab _ hg e he
  refine ⟨N0, fun N hN a b ha hab hb => ?_⟩
  have h := hN0 N hN a b ha hab hb
  rw [cnt] at h
  simpa only [heval] using h

theorem freq_poly (P : Polynomial Real) (hP : Irrational P.leadingCoeff) (hdeg : 1 ≤ P.natDegree)
    (a b : Real) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Filter.Tendsto (fun N : Nat => (((Finset.range N).filter (fun n : Nat =>
      a ≤ Int.fract (Polynomial.eval (n : Real) P) ∧
        Int.fract (Polynomial.eval (n : Real) P) < b)).card : Real) / N)
      Filter.atTop (nhds (b - a)) := by
  have hg := weylEquid_poly P hP hdeg
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N0, hN0⟩ := cnt_unif_ab _ hg ε hε
  refine ⟨N0, fun N hN => ?_⟩
  have := hN0 N hN a b ha hab hb
  rw [Real.dist_eq]
  rw [cnt] at this
  exact this

theorem freq_lead_sq (d : Nat) (hd : 1 ≤ d) (hd' : d ≤ 9) :
    Filter.Tendsto (fun N : Nat => (((Finset.range N).filter (fun n : Nat =>
      2 ^ (n ^ 2) / 10 ^ Nat.log 10 (2 ^ (n ^ 2)) = d)).card : Real) / N)
      Filter.atTop (nhds (Real.logb 10 (((d : Real) + 1) / d))) := by
  set P : ℝ[X] := Polynomial.C Lg * Polynomial.X^2 with hP
  have hlead : P.leadingCoeff = Lg := by
    rw [hP, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_X_pow, mul_one]
  have hdeg : P.natDegree = 2 := by
    rw [hP, Polynomial.natDegree_C_mul Lg_irrational.ne_zero, Polynomial.natDegree_X_pow]
  have hg := weylEquid_poly P (by rw [hlead]; exact Lg_irrational) (by omega)
  -- the interval
  set a : ℝ := Real.logb 10 d with ha
  set b : ℝ := Real.logb 10 ((d:ℝ)+1) with hb
  have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have ha0 : 0 ≤ a := Real.logb_nonneg (by norm_num) hdR
  have hab : a ≤ b := Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
  have h9 : (d:ℝ) ≤ 9 := by exact_mod_cast hd'
  have hb1 : b ≤ 1 := by
    have hone : (1:ℝ) = Real.logb 10 10 := by rw [Real.logb_self_eq_one] <;> norm_num
    rw [hb, hone]
    exact Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
  have hlim : Real.logb 10 (((d : Real) + 1) / d) = b - a := by
    rw [hb, ha, Real.logb_div (by positivity) (by linarith)]
  rw [hlim]
  -- the filter condition matches
  have hev : ∀ n : ℕ, (2 ^ (n ^ 2) / 10 ^ Nat.log 10 (2 ^ (n ^ 2)) = d)
      ↔ (a ≤ Int.fract (P.eval (n:ℝ)) ∧ Int.fract (P.eval (n:ℝ)) < b) := by
    intro n
    have heval : P.eval (n:ℝ) = ((n^2 : ℕ) : ℝ) * Lg := by
      rw [hP]; push_cast; simp; ring
    rw [heval, ha, hb]
    exact digit_iff d (n^2) hd
  simp only [hev]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N0, hN0⟩ := cnt_unif_ab _ hg ε hε
  refine ⟨N0, fun N hN => ?_⟩
  have := hN0 N hN a b ha0 hab hb1
  rw [Real.dist_eq]
  rw [cnt] at this
  exact this

theorem mean_abs_sin_sq :
    Filter.Tendsto (fun N : Nat =>
      Finset.sum (Finset.range N) (fun n : Nat => abs (Real.sin ((n : Real) ^ 2))) / N)
      Filter.atTop (nhds (2 / Real.pi)) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  set y : ℝ := 1/Real.pi with hy
  have hyirr : Irrational y := by rw [hy, one_div]; exact irrational_pi.inv
  set P : ℝ[X] := Polynomial.C y * Polynomial.X^2 with hP
  have hlead : P.leadingCoeff = y := by
    rw [hP, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_X_pow, mul_one]
  have hdeg : P.natDegree = 2 := by
    rw [hP, Polynomial.natDegree_C_mul hyirr.ne_zero, Polynomial.natDegree_X_pow]
  have hg := weylEquid_poly P (by rw [hlead]; exact hyirr) (by omega)
  -- the test function
  set f : ℝ → ℝ := fun u => Real.sin (Real.pi * u) with hf
  have hcont : ContinuousOn f (Set.Icc 0 1) := by
    apply Continuous.continuousOn
    rw [hf]; fun_prop
  have hf01 : f 0 = f 1 := by rw [hf]; simp
  have := tendsto_avg_real (fun n : ℕ => P.eval (n:ℝ)) hg f hf01 hcont
  -- compute the integral
  have hint : ∫ u in Set.Ioc (0:ℝ) 1, f u = 2/Real.pi := by
    rw [← intervalIntegral.integral_of_le zero_le_one, hf]
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) Real.pi_ne_zero]
    simp; ring
  rw [hint] at this
  -- identify the summands
  have hsum : ∀ n : ℕ, f (Int.fract (P.eval (n:ℝ))) = |Real.sin ((n:ℝ)^2)| := by
    intro n
    have hev : P.eval (n:ℝ) = (n:ℝ)^2 / Real.pi := by
      rw [hP]; simp [hy]; ring
    rw [hev, hf]
    set t : ℝ := (n:ℝ)^2 with ht
    set u := Int.fract (t/Real.pi) with hu
    have hu0 : 0 ≤ u := Int.fract_nonneg _
    have hu1 : u < 1 := Int.fract_lt_one _
    have htt : t = Real.pi * u + ⌊t/Real.pi⌋ * Real.pi := by
      rw [hu, Int.fract]; field_simp; ring
    rw [htt, Real.sin_add_int_mul_pi, abs_mul]
    have h1 : Real.sin (Real.pi * u) ≥ 0 := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · positivity
      · nlinarith
    rw [abs_of_nonneg h1]
    simp [abs_pow]
  simp only [hsum] at this
  exact this

theorem mean_cos_sq (x : Real) (hx : Irrational (x / Real.pi)) :
    Filter.Tendsto (fun N : Nat =>
      Finset.sum (Finset.range N) (fun n : Nat => Real.cos ((n : Real) ^ 2 * x)) / N)
      Filter.atTop (nhds 0) := by
  set y : ℝ := x / (2 * Real.pi) with hy
  have hyirr : Irrational y := by
    rw [hy, show x / (2*Real.pi) = (x/Real.pi) / ((2:ℕ):ℝ) by push_cast; field_simp]
    exact hx.div_natCast (by norm_num)
  set P : ℝ[X] := Polynomial.C y * Polynomial.X^2 with hP
  have hlead : P.leadingCoeff = y := by
    rw [hP, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_X_pow, mul_one]
  have hdeg : P.natDegree = 2 := by
    rw [hP, Polynomial.natDegree_C_mul hyirr.ne_zero, Polynomial.natDegree_X_pow]
  have hnull := weylNull_main 2 (by norm_num) P (by omega) (by
    rw [show P.coeff 2 = P.leadingCoeff by rw [← Polynomial.coeff_natDegree, hdeg], hlead]
    exact hyirr)
  rw [WeylNull] at hnull
  -- the real part
  have hre : ∀ N : ℕ, (weylAvg (fun n => P.eval (n:ℝ)) N).re
      = (∑ n ∈ Finset.range N, Real.cos ((n:ℝ)^2 * x)) / N := by
    intro N
    rw [weylAvg]
    rw [show (∑ n ∈ Finset.range N, e (P.eval (n:ℝ))) / (N:ℂ)
        = (∑ n ∈ Finset.range N, e (P.eval (n:ℝ))) * ((N:ℝ):ℂ)⁻¹ by push_cast; ring]
    rw [Complex.mul_re]
    have h1 : (((N:ℝ):ℂ)⁻¹).im = 0 := by
      rcases eq_or_ne (N:ℝ) 0 with h | h
      · simp [h]
      · simp
    have h2 : (((N:ℝ):ℂ)⁻¹).re = ((N:ℝ))⁻¹ := by
      rcases eq_or_ne (N:ℝ) 0 with h | h
      · simp [h]
      · simp
    rw [h1, h2]
    simp only [mul_zero, sub_zero]
    rw [Complex.re_sum, div_eq_mul_inv]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    have hev : P.eval (n:ℝ) = (n:ℝ)^2 * x / (2 * Real.pi) := by
      rw [hP]; simp [hy]; ring
    rw [hev]
    rw [e]
    rw [show (2 * (Real.pi:ℂ) * Complex.I * (((n:ℝ)^2 * x / (2*Real.pi) : ℝ) : ℂ))
        = (((n:ℝ)^2 * x : ℝ):ℂ) * Complex.I by
      push_cast
      field_simp]
    rw [Complex.exp_mul_I]
    set t : ℝ := (n:ℝ)^2 * x with ht
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_im]
  have := Complex.continuous_re.continuousAt.tendsto.comp hnull
  simp only [Function.comp_def] at this
  simp only [hre] at this
  simpa using this

end TuringTask
