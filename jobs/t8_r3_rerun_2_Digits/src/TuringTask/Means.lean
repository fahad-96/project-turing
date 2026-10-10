import TuringTask.Equidistribution

namespace TuringTask

open Filter MeasureTheory
open scoped BigOperators

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

noncomputable section

private theorem liftIoc_periodic_apply (g : ℝ → ℂ) (hg : Function.Periodic g 1) (x : ℝ) :
    AddCircle.liftIoc 1 0 g (x : AddCircle (1 : ℝ)) = g x := by
  let y := AddCircle.equivIoc 1 0 (x : AddCircle (1 : ℝ))
  have hy : (y : ℝ) ∈ Set.Ioc 0 (0 + 1) := y.property
  calc
    AddCircle.liftIoc 1 0 g (x : AddCircle (1 : ℝ)) =
        AddCircle.liftIoc 1 0 g ((y : ℝ) : AddCircle (1 : ℝ)) := by
          rw [AddCircle.coe_equivIoc]
    _ = g y := AddCircle.liftIoc_coe_apply hy
    _ = hg.lift ((y : ℝ) : AddCircle (1 : ℝ)) := (hg.lift_coe _).symm
    _ = hg.lift (x : AddCircle (1 : ℝ)) := by rw [AddCircle.coe_equivIoc]
    _ = g x := hg.lift_coe x

private def absSinFunction (t : ℝ) : ℂ :=
  (|Real.sin (Real.pi * t)| : ℝ)

private theorem absSinFunction_periodic : Function.Periodic absSinFunction 1 := by
  intro t
  change ((|Real.sin (Real.pi * (t + 1))| : ℝ) : ℂ) =
    ((|Real.sin (Real.pi * t)| : ℝ) : ℂ)
  rw [show Real.pi * (t + 1) = Real.pi * t + Real.pi by ring,
    Real.sin_add_pi, abs_neg]

private def absSinCircle : C(AddCircle (1 : ℝ), ℂ) where
  toFun := AddCircle.liftIoc 1 0 absSinFunction
  continuous_toFun := AddCircle.liftIoc_zero_continuous (by
    simp [absSinFunction]) (by
    apply Continuous.continuousOn
    change Continuous fun t : ℝ => ((|Real.sin (Real.pi * t)| : ℝ) : ℂ)
    fun_prop)

private theorem integral_abs_sin_pi :
    (∫ t in (0 : ℝ)..1, |Real.sin (Real.pi * t)|) = 2 / Real.pi := by
  have hnonneg (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
      0 ≤ Real.sin (Real.pi * t) := by
    rw [Set.uIcc_of_le (by norm_num)] at ht
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · exact mul_nonneg Real.pi_pos.le ht.1
    · simpa using mul_le_mul_of_nonneg_left ht.2 Real.pi_pos.le
  rw [intervalIntegral.integral_congr (fun t ht => abs_of_nonneg (hnonneg t ht)),
    intervalIntegral.integral_comp_mul_left (f := Real.sin) Real.pi_ne_zero]
  simp [integral_sin, div_eq_mul_inv]
  ring

private theorem integral_absSinCircle :
    (∫ z : AddCircle (1 : ℝ), absSinCircle z ∂AddCircle.haarAddCircle) =
      (2 / Real.pi : ℝ) := by
  rw [AddCircle.integral_haarAddCircle]
  simp only [inv_one, one_smul]
  change (∫ z : AddCircle (1 : ℝ), AddCircle.liftIoc 1 0 absSinFunction z) = _
  rw [AddCircle.integral_liftIoc_eq_intervalIntegral]
  change (∫ t in (0 : ℝ)..0 + 1,
    ((|Real.sin (Real.pi * t)| : ℝ) : ℂ)) = _
  rw [intervalIntegral.integral_ofReal]
  norm_num
  simpa using congrArg (fun r : ℝ => (r : ℂ)) integral_abs_sin_pi

/-- The Cesaro means of `|sin (n^2)|` converge to `2 / pi`. -/
theorem mean_abs_sin_sq_aux :
    Filter.Tendsto (fun N : Nat =>
      Finset.sum (Finset.range N) (fun n : Nat => abs (Real.sin ((n : Real) ^ 2))) / N)
      Filter.atTop (nhds (2 / Real.pi)) := by
  let P : Polynomial ℝ := Polynomial.C (Real.pi⁻¹) * Polynomial.X ^ 2
  have hP : Irrational P.leadingCoeff := by
    simpa [P, Polynomial.leadingCoeff_C_mul_X_pow] using Real.irrational_pi.inv
  have hdeg : 1 ≤ P.natDegree := by
    change 1 ≤ (Polynomial.C (Real.pi⁻¹) * Polynomial.X ^ 2).natDegree
    rw [Polynomial.natDegree_C_mul_X_pow 2 Real.pi⁻¹ (inv_ne_zero Real.pi_ne_zero)]
    norm_num
  have hsample (n : ℕ) :
      absSinCircle
          ((Polynomial.eval (n : ℝ) P : ℝ) : AddCircle (1 : ℝ)) =
        ((|Real.sin ((n : ℝ) ^ 2)| : ℝ) : ℂ) := by
    change AddCircle.liftIoc 1 0 absSinFunction
      ((Polynomial.eval (n : ℝ) P : ℝ) : AddCircle (1 : ℝ)) = _
    rw [liftIoc_periodic_apply absSinFunction absSinFunction_periodic]
    simp only [absSinFunction, P, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    congr 2
    field_simp [Real.pi_ne_zero]
  have havg (N : ℕ) :
      Equidistribution.circleAverage P absSinCircle N =
        ((Finset.sum (Finset.range N)
          (fun n : ℕ => |Real.sin ((n : ℝ) ^ 2)|) / N : ℝ) : ℂ) := by
    simp [Equidistribution.circleAverage, hsample]
  have h := Equidistribution.tendsto_circleAverage P hP hdeg absSinCircle
  have hre := Complex.continuous_re.continuousAt.tendsto.comp h
  change Tendsto (fun N => (Equidistribution.circleAverage P absSinCircle N).re)
    atTop (nhds ((∫ z : AddCircle (1 : ℝ),
      absSinCircle z ∂AddCircle.haarAddCircle).re)) at hre
  simpa only [havg, Complex.ofReal_re, integral_absSinCircle] using hre

private def cosFunction (t : ℝ) : ℂ :=
  (Real.cos (2 * Real.pi * t) : ℝ)

private theorem cosFunction_periodic : Function.Periodic cosFunction 1 := by
  intro t
  change ((Real.cos (2 * Real.pi * (t + 1)) : ℝ) : ℂ) =
    ((Real.cos (2 * Real.pi * t) : ℝ) : ℂ)
  rw [show 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi by ring,
    Real.cos_add_two_pi]

private def cosCircle : C(AddCircle (1 : ℝ), ℂ) where
  toFun := AddCircle.liftIoc 1 0 cosFunction
  continuous_toFun := AddCircle.liftIoc_zero_continuous (by
    simp [cosFunction]) (by
    apply Continuous.continuousOn
    change Continuous fun t : ℝ => ((Real.cos (2 * Real.pi * t) : ℝ) : ℂ)
    fun_prop)

private theorem integral_cosCircle :
    (∫ z : AddCircle (1 : ℝ), cosCircle z ∂AddCircle.haarAddCircle) = 0 := by
  rw [AddCircle.integral_haarAddCircle]
  simp only [inv_one, one_smul]
  change (∫ z : AddCircle (1 : ℝ), AddCircle.liftIoc 1 0 cosFunction z) = 0
  rw [AddCircle.integral_liftIoc_eq_intervalIntegral]
  change (∫ t in (0 : ℝ)..0 + 1,
    ((Real.cos (2 * Real.pi * t) : ℝ) : ℂ)) = 0
  rw [intervalIntegral.integral_ofReal,
    intervalIntegral.integral_comp_mul_left (f := Real.cos)
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)]
  simp [integral_cos]

/-- The Cesaro means of `cos (n^2 x)` vanish when `x / pi` is irrational. -/
theorem mean_cos_sq_aux (x : Real) (hx : Irrational (x / Real.pi)) :
    Filter.Tendsto (fun N : Nat =>
      Finset.sum (Finset.range N) (fun n : Nat => Real.cos ((n : Real) ^ 2 * x)) / N)
      Filter.atTop (nhds 0) := by
  let P : Polynomial ℝ := Polynomial.C (x / (2 * Real.pi)) * Polynomial.X ^ 2
  have hcoeff : Irrational (x / (2 * Real.pi)) := by
    have h := hx.div_natCast (m := 2) (by norm_num)
    convert h using 1 <;> field_simp [Real.pi_ne_zero] <;> ring
  have hP : Irrational P.leadingCoeff := by
    simpa [P, Polynomial.leadingCoeff_C_mul_X_pow] using hcoeff
  have hdeg : 1 ≤ P.natDegree := by
    change 1 ≤ (Polynomial.C (x / (2 * Real.pi)) * Polynomial.X ^ 2).natDegree
    rw [Polynomial.natDegree_C_mul_X_pow 2 (x / (2 * Real.pi)) hcoeff.ne_zero]
    norm_num
  have hsample (n : ℕ) :
      cosCircle ((Polynomial.eval (n : ℝ) P : ℝ) : AddCircle (1 : ℝ)) =
        ((Real.cos ((n : ℝ) ^ 2 * x) : ℝ) : ℂ) := by
    change AddCircle.liftIoc 1 0 cosFunction
      ((Polynomial.eval (n : ℝ) P : ℝ) : AddCircle (1 : ℝ)) = _
    rw [liftIoc_periodic_apply cosFunction cosFunction_periodic]
    simp only [cosFunction, P, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    congr 2
    field_simp [Real.pi_ne_zero]
  have havg (N : ℕ) :
      Equidistribution.circleAverage P cosCircle N =
        ((Finset.sum (Finset.range N)
          (fun n : ℕ => Real.cos ((n : ℝ) ^ 2 * x)) / N : ℝ) : ℂ) := by
    simp [Equidistribution.circleAverage, hsample]
  have h := Equidistribution.tendsto_circleAverage P hP hdeg cosCircle
  have hre := Complex.continuous_re.continuousAt.tendsto.comp h
  change Tendsto (fun N => (Equidistribution.circleAverage P cosCircle N).re)
    atTop (nhds ((∫ z : AddCircle (1 : ℝ),
      cosCircle z ∂AddCircle.haarAddCircle).re)) at hre
  simpa only [havg, Complex.ofReal_re, integral_cosCircle, Complex.zero_re] using hre

end

end TuringTask
