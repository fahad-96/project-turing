import Mathlib
import TuringTask.LeadDigit

/-!
# The five statements

* `phaseNull_eval`: a polynomial with irrational leading coefficient and degree `>= 1` gives a
  sequence satisfying the exponential-sum hypothesis (apply Weyl's theorem to `k P`).
* `integral_abs_sin_circle`: the mean of `|sin (2 pi t)|` over the circle is `2 / pi`.
* The theorems `uniform_freq_sq_mul`, `tendsto_freq_eval`, `tendsto_freq_lead_digit`,
  `tendsto_avg_abs_sin_sq`, `tendsto_avg_cos_sq_mul` are the five statements of `Basic.lean`.
-/

open Finset Filter Polynomial MeasureTheory AddCircle

namespace TuringTask

lemma phaseNull_eval (P : ℝ[X]) (hP : Irrational P.leadingCoeff) (hdeg : 1 ≤ P.natDegree) :
    PhaseNull (fun n => P.eval (n : ℝ)) := by
  intro k hk
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hdQ : (C (k : ℝ) * P).natDegree = (P.natDegree - 1) + 1 := by
    rw [natDegree_C_mul hk']
    omega
  have hlQ : Irrational (C (k : ℝ) * P).leadingCoeff := by
    rw [leadingCoeff_mul, leadingCoeff_C]
    exact hP.intCast_mul hk
  refine (tendsto_avg_ephase_poly _ _ hdQ hlQ).congr fun N => ?_
  simp [eval_mul]

lemma phaseNull_sq_mul (x : ℝ) (hx : Irrational x) :
    PhaseNull (fun n => (n : ℝ) ^ 2 * x) := by
  have h := phaseNull_eval (C x * X ^ 2) (by rwa [leadingCoeff_C_mul_X_pow])
    (by rw [natDegree_C_mul_X_pow 2 x hx.ne_zero]; norm_num)
  intro k hk
  refine (h k hk).congr fun N => ?_
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  congr 1
  refine Finset.sum_congr rfl (fun n _ => ?_)
  ring_nf

/-- The integral of `|sin (2 pi t)|` over `[0, 1]`. -/
lemma integral_abs_sin_two_pi :
    ∫ t in (0 : ℝ)..1, |Real.sin (2 * Real.pi * t)| = 2 / Real.pi := by
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [intervalIntegral.integral_comp_mul_left (fun t => |Real.sin t|) (by positivity),
    mul_zero, mul_one]
  have hc : Continuous fun t => |Real.sin t| := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := Real.pi)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : ∫ t in (0 : ℝ)..Real.pi, |Real.sin t| = 2 := by
    rw [intervalIntegral.integral_congr (g := Real.sin)]
    · rw [integral_sin, Real.cos_zero, Real.cos_pi]
      norm_num
    · intro t ht
      rw [Set.uIcc_of_le hpi.le] at ht
      exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2)
  have h2 : ∫ t in Real.pi..2 * Real.pi, |Real.sin t| = 2 := by
    have := intervalIntegral.integral_comp_add_right (fun t => |Real.sin t|) Real.pi
      (a := 0) (b := Real.pi)
    simp only [zero_add] at this
    rw [show 2 * Real.pi = Real.pi + Real.pi by ring, ← this, ← h1]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [Real.sin_add_pi, abs_neg]
  rw [h1, h2, smul_eq_mul]
  field_simp
  norm_num

/-- `t |-> |Im (fourier 1 t)| = |sin (2 pi t)|` as a continuous function on the circle. -/
noncomputable def sinAbsOnCircle : C(AddCircle (1 : ℝ), ℝ) :=
  ⟨fun t => |(fourier 1 t).im|, by fun_prop⟩

lemma sinAbsOnCircle_coe (t : ℝ) :
    sinAbsOnCircle (t : AddCircle (1 : ℝ)) = |Real.sin (2 * Real.pi * t)| := by
  change |(fourier 1 (t : AddCircle (1 : ℝ))).im| = _
  rw [fourier_coe_eq_ephase]
  unfold ephase
  rw [Complex.exp_ofReal_mul_I_im]
  push_cast
  ring_nf

lemma integral_abs_sin_circle :
    ∫ t, sinAbsOnCircle t ∂(haarAddCircle (T := (1 : ℝ))) = 2 / Real.pi := by
  rw [haar_eq_volume_one, ← AddCircle.intervalIntegral_preimage (1 : ℝ) 0, zero_add]
  simp_rw [sinAbsOnCircle_coe]
  exact integral_abs_sin_two_pi

theorem uniform_freq_sq_mul (x : ℝ) (hx : Irrational x) (e : ℝ) (he : 0 < e) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      |(((range N).filter (fun n : ℕ =>
        a ≤ Int.fract ((n : ℝ) ^ 2 * x) ∧ Int.fract ((n : ℝ) ^ 2 * x) < b)).card : ℝ)
        / N - (b - a)| < e := by
  obtain ⟨N0, hN0⟩ := freqR_uniform _ (phaseNull_sq_mul x hx) e he
  refine ⟨N0, fun N hN a b h0a hab hb1 => ?_⟩
  rw [card_div_eq_freqR (fun n => (n : ℝ) ^ 2 * x)]
  exact hN0 N hN a b h0a hab hb1

theorem tendsto_freq_eval (P : ℝ[X]) (hP : Irrational P.leadingCoeff) (hdeg : 1 ≤ P.natDegree)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => (((range N).filter (fun n : ℕ =>
      a ≤ Int.fract (P.eval (n : ℝ)) ∧ Int.fract (P.eval (n : ℝ)) < b)).card : ℝ) / N)
      atTop (nhds (b - a)) := by
  refine (tendsto_freqR _ (phaseNull_eval P hP hdeg) a b ha hab hb).congr fun N => ?_
  rw [card_div_eq_freqR (fun n => P.eval (n : ℝ))]

theorem tendsto_freq_lead_digit (d : ℕ) (hd : 1 ≤ d) (hd' : d ≤ 9) :
    Tendsto (fun N : ℕ => (((range N).filter (fun n : ℕ =>
      2 ^ (n ^ 2) / 10 ^ Nat.log 10 (2 ^ (n ^ 2)) = d)).card : ℝ) / N)
      atTop (nhds (Real.logb 10 (((d : ℝ) + 1) / d))) := by
  set u : ℕ → ℝ := fun n => (n : ℝ) ^ 2 * Real.logb 10 2 with hu
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hlo : 0 ≤ Real.logb 10 (d : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hd)
  have hmid : Real.logb 10 (d : ℝ) ≤ Real.logb 10 ((d : ℝ) + 1) :=
    (Real.logb_le_logb (by norm_num) hd0 (by positivity)).mpr (by linarith)
  have hhi : Real.logb 10 ((d : ℝ) + 1) ≤ 1 := by
    have h9 : (d : ℝ) + 1 ≤ 10 := by
      have : (d : ℝ) ≤ 9 := by exact_mod_cast hd'
      linarith
    calc Real.logb 10 ((d : ℝ) + 1) ≤ Real.logb 10 10 :=
          (Real.logb_le_logb (by norm_num) (by positivity) (by norm_num)).mpr h9
      _ = 1 := Real.logb_self_eq_one (by norm_num)
  have hlim := tendsto_freqR u (phaseNull_sq_mul _ logb_ten_two_irrational) _ _ hlo hmid hhi
  rw [← Real.logb_div (by positivity) hd0.ne'] at hlim
  refine hlim.congr fun N => ?_
  rw [← card_div_eq_freqR u]
  congr 3
  refine Finset.filter_congr fun n _ => ?_
  have hm : 1 ≤ 2 ^ (n ^ 2) := Nat.one_le_two_pow
  rw [div_pow_log_eq_iff _ d hm hd]
  have e : Real.logb 10 (((2 ^ (n ^ 2) : ℕ)) : ℝ) = u n := by
    rw [hu]
    push_cast
    rw [Real.logb_pow]
    push_cast
    ring
  rw [e]

theorem tendsto_avg_abs_sin_sq :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, |Real.sin ((n : ℝ) ^ 2)|) / N) atTop (nhds (2 / Real.pi)) := by
  have hirr : Irrational (1 / (2 * Real.pi)) := by
    rw [one_div]
    exact (irrational_pi.natCast_mul (m := 2) (by norm_num)).inv
  have hu := phaseNull_sq_mul _ hirr
  have h := tendsto_avg_circle_real _ hu sinAbsOnCircle
  rw [integral_abs_sin_circle] at h
  refine h.congr fun N => ?_
  congr 1
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [sinAbsOnCircle_coe]
  congr 2
  field_simp

theorem tendsto_avg_cos_sq_mul (x : ℝ) (hx : Irrational (x / Real.pi)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, Real.cos ((n : ℝ) ^ 2 * x)) / N) atTop (nhds 0) := by
  have hirr : Irrational (x / (2 * Real.pi)) := by
    have := hx.div_natCast (m := 2) (by norm_num)
    convert this using 1
    push_cast
    ring
  have hu := phaseNull_sq_mul _ hirr
  have h := (Complex.continuous_re.tendsto _).comp (hu 1 one_ne_zero)
  rw [Complex.zero_re] at h
  refine h.congr fun N => ?_
  simp only [Function.comp_apply, Int.cast_one, one_mul]
  rw [Complex.div_natCast_re, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [ephase_re]
  congr 1
  field_simp

end TuringTask
