import TuringTask.Weyl

namespace TuringTask.Equidistribution

open scoped BigOperators ENNReal
open Filter MeasureTheory

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
noncomputable local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

noncomputable def circleAverage (P : Polynomial ℝ)
    (f : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N,
    f ((Polynomial.eval (n : ℝ) P : ℝ) : AddCircle (1 : ℝ))) / N

private theorem norm_circleAverage_le (P : Polynomial ℝ)
    (f : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    ‖circleAverage P f N‖ ≤ ‖f‖ := by
  by_cases hN : N = 0
  · simp [circleAverage, hN]
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  rw [circleAverage, norm_div, norm_natCast]
  apply (div_le_iff₀ hNr).2
  calc
    ‖∑ n ∈ Finset.range N,
        f ((Polynomial.eval (n : ℝ) P : ℝ) : AddCircle (1 : ℝ))‖ ≤
        ∑ _n ∈ Finset.range N, ‖f‖ := by
      calc
        _ ≤ ∑ n ∈ Finset.range N,
            ‖f ((Polynomial.eval (n : ℝ) P : ℝ) : AddCircle (1 : ℝ))‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range N, ‖f‖ := by
          exact Finset.sum_le_sum fun n hn => ContinuousMap.norm_coe_le_norm f _
    _ = (N : ℝ) * ‖f‖ := by simp
    _ = ‖f‖ * (N : ℝ) := by rw [mul_comm]

private theorem circleAverage_sub (P : Polynomial ℝ)
    (f g : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    circleAverage P f N - circleAverage P g N = circleAverage P (f - g) N := by
  simp only [circleAverage, ContinuousMap.sub_apply]
  rw [← sub_div, ← Finset.sum_sub_distrib]

private theorem integral_fourier_eq_zero (k : ℤ) (hk : k ≠ 0) :
    ∫ x : AddCircle (1 : ℝ), fourier k x ∂AddCircle.haarAddCircle = 0 := by
  let y : AddCircle (1 : ℝ) := (1 / (2 * (k : ℝ)) : ℝ)
  have hky : fourier k y = -1 := by
    change fourier k ((1 / (2 * (k : ℝ)) : ℝ) : AddCircle (1 : ℝ)) = -1
    rw [fourier_apply, ← AddCircle.coe_zsmul, AddCircle.toCircle_apply_mk, Circle.coe_exp]
    simp only [zsmul_eq_mul]
    push_cast
    change Complex.exp
      ((2 * Real.pi / (1 : ℝ) * ((k : ℝ) * (1 / (2 * (k : ℝ))))) * Complex.I) = -1
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    convert Complex.exp_pi_mul_I using 2 <;> push_cast <;> field_simp <;> ring
  have hadd (x : AddCircle (1 : ℝ)) : fourier k (y + x) = -fourier k x := by
    rw [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]
    change fourier k y * fourier k x = -fourier k x
    rw [hky]
    ring
  let μ := AddCircle.haarAddCircle (T := (1 : ℝ))
  have hmap : Measure.map (fun x : AddCircle (1 : ℝ) => y + x) μ = μ :=
    Measure.IsAddLeftInvariant.map_add_left_eq_self y
  have hchange :
      (∫ x : AddCircle (1 : ℝ), fourier k (y + x) ∂μ) =
        ∫ x : AddCircle (1 : ℝ), fourier k x ∂μ := by
    calc
      _ = ∫ x : AddCircle (1 : ℝ), fourier k x ∂Measure.map (fun x => y + x) μ :=
        (integral_map (continuous_const.add continuous_id).aemeasurable
          (fourier k).continuous.aestronglyMeasurable).symm
      _ = _ := by rw [hmap]
  have hneg :
      (∫ x : AddCircle (1 : ℝ), fourier k (y + x) ∂μ) =
        -(∫ x : AddCircle (1 : ℝ), fourier k x ∂μ) := by
    simp_rw [hadd]
    exact integral_neg _
  have heq : (∫ x : AddCircle (1 : ℝ), fourier k x ∂μ) =
      -(∫ x : AddCircle (1 : ℝ), fourier k x ∂μ) := hchange.symm.trans hneg
  have htwo : (2 : ℂ) * (∫ x : AddCircle (1 : ℝ), fourier k x ∂μ) = 0 := by
    linear_combination heq
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

private theorem integral_fourier (k : ℤ) :
    (∫ x : AddCircle (1 : ℝ), fourier k x ∂AddCircle.haarAddCircle) =
      if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [fourier_zero]
  · rw [if_neg hk]
    exact integral_fourier_eq_zero k hk

private theorem fourier_coe_eq_phase (k : ℤ) (x : ℝ) :
    fourier k (x : AddCircle (1 : ℝ)) = Weyl.phase ((k : ℝ) * x) := by
  rw [fourier_apply, ← AddCircle.coe_zsmul, AddCircle.toCircle_apply_mk,
    Circle.coe_exp, Weyl.phase]
  simp only [zsmul_eq_mul]
  push_cast
  change Complex.exp
    ((2 * Real.pi / (1 : ℝ) * ((k : ℝ) * x)) * Complex.I) =
      Complex.exp (2 * Real.pi * ((k : ℝ) * x) * Complex.I)
  congr 1
  push_cast
  ring

private theorem tendsto_circleAverage_fourier (P : Polynomial ℝ)
    (hP : Irrational P.leadingCoeff) (hdeg : 1 ≤ P.natDegree) (k : ℤ) :
    Tendsto (circleAverage P (fourier k)) atTop
      (nhds (∫ x : AddCircle (1 : ℝ), fourier k x ∂AddCircle.haarAddCircle)) := by
  by_cases hk : k = 0
  · subst k
    rw [integral_fourier]
    simp only [if_pos]
    refine (tendsto_congr' (show ∀ᶠ N : ℕ in atTop, circleAverage P (fourier 0) N = 1 by
      filter_upwards [eventually_ge_atTop 1] with N hN
      simp [circleAverage, fourier_zero, Nat.ne_of_gt hN])).2 tendsto_const_nhds
  · rw [integral_fourier, if_neg hk]
    have h := Weyl.tendsto_phase_polynomial_int_mul P hP hdeg k hk
    have heq : circleAverage P (fourier k) = fun N : ℕ =>
        (∑ n ∈ Finset.range N,
          Weyl.phase ((k : ℝ) * Polynomial.eval (n : ℝ) P)) / (N : ℂ) := by
      funext N
      apply congrArg (fun z : ℂ => z / (N : ℂ))
      apply Finset.sum_congr rfl
      intro n hn
      exact fourier_coe_eq_phase k _
    rw [heq]
    exact h

private theorem circleAverage_zero (P : Polynomial ℝ) (N : ℕ) :
    circleAverage P 0 N = 0 := by
  simp [circleAverage]

private theorem circleAverage_add (P : Polynomial ℝ)
    (f g : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    circleAverage P (f + g) N = circleAverage P f N + circleAverage P g N := by
  simp only [circleAverage, ContinuousMap.add_apply, Finset.sum_add_distrib, add_div]

private theorem circleAverage_smul (P : Polynomial ℝ) (c : ℂ)
    (f : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    circleAverage P (c • f) N = c • circleAverage P f N := by
  simp only [circleAverage, ContinuousMap.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

private theorem continuousMap_integrable (f : C(AddCircle (1 : ℝ), ℂ)) :
    Integrable f AddCircle.haarAddCircle := by
  simpa [IntegrableOn] using
    (ContinuousOn.integrableOn_compact isCompact_univ f.continuous.continuousOn)

private theorem tendsto_circleAverage_span (P : Polynomial ℝ)
    (hP : Irrational P.leadingCoeff) (hdeg : 1 ≤ P.natDegree)
    (f : C(AddCircle (1 : ℝ), ℂ))
    (hf : f ∈ Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))) :
    Tendsto (circleAverage P f) atTop
      (nhds (∫ x : AddCircle (1 : ℝ), f x ∂AddCircle.haarAddCircle)) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨k, rfl⟩ := hf
      exact tendsto_circleAverage_fourier P hP hdeg k
  | zero =>
      convert (tendsto_const_nhds (x := (0 : ℂ))) using 1
      · funext N
        exact circleAverage_zero P N
      · simp
  | add f g hf hg hft hgt =>
      have hfi : Integrable f AddCircle.haarAddCircle := by
        exact continuousMap_integrable f
      have hgi : Integrable g AddCircle.haarAddCircle := by
        exact continuousMap_integrable g
      convert hft.add hgt using 1
      · funext N
        exact circleAverage_add P f g N
      · exact congrArg nhds (integral_add hfi hgi)
  | smul c f hf hft =>
      convert hft.const_smul c using 1
      · funext N
        exact circleAverage_smul P c f N
      · exact congrArg nhds (integral_smul c f)

/-- Weyl's criterion on the unit additive circle, in continuous-test-function
form. -/
theorem tendsto_circleAverage (P : Polynomial ℝ)
    (hP : Irrational P.leadingCoeff) (hdeg : 1 ≤ P.natDegree)
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (circleAverage P f) atTop
      (nhds (∫ x : AddCircle (1 : ℝ), f x ∂AddCircle.haarAddCircle)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hdense : Dense
      (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) :
        Set C(AddCircle (1 : ℝ), ℂ)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr span_fourier_closure_eq_top
  obtain ⟨g, hgspan, hfg⟩ := (Metric.mem_closure_iff.mp (hdense f)) (ε / 3) (by positivity)
  have hg := tendsto_circleAverage_span P hP hdeg g hgspan
  rw [Metric.tendsto_nhds] at hg
  filter_upwards [hg (ε / 3) (by positivity)] with N hN
  rw [dist_eq_norm]
  have havg : ‖circleAverage P f N - circleAverage P g N‖ < ε / 3 := by
    rw [circleAverage_sub]
    exact lt_of_le_of_lt (norm_circleAverage_le P (f - g) N) (by simpa [dist_eq_norm] using hfg)
  have hint : ‖(∫ x, g x ∂AddCircle.haarAddCircle) -
      ∫ x, f x ∂AddCircle.haarAddCircle‖ < ε / 3 := by
    rw [← integral_sub (continuousMap_integrable g) (continuousMap_integrable f)]
    refine lt_of_le_of_lt (norm_integral_le_of_norm_le_const (C := ‖g - f‖) ?_) ?_
    · filter_upwards [] with x
      exact ContinuousMap.norm_coe_le_norm (g - f) x
    · have hmass : AddCircle.haarAddCircle (T := (1 : ℝ)).real Set.univ = 1 := by
        simp [MeasureTheory.measureReal_def]
      rw [hmass, mul_one]
      simpa [dist_eq_norm, norm_sub_rev] using hfg
  calc
    ‖circleAverage P f N - ∫ x, f x ∂AddCircle.haarAddCircle‖ =
        ‖(circleAverage P f N - circleAverage P g N) +
          (circleAverage P g N - ∫ x, f x ∂AddCircle.haarAddCircle)‖ := by
      congr 1
      ring
    _ ≤
        ‖circleAverage P f N - circleAverage P g N‖ +
          ‖circleAverage P g N - ∫ x, f x ∂AddCircle.haarAddCircle‖ := norm_add_le _ _
    _ ≤
        ‖circleAverage P f N - circleAverage P g N‖ +
          ‖circleAverage P g N - ∫ x, g x ∂AddCircle.haarAddCircle‖ +
          ‖(∫ x, g x ∂AddCircle.haarAddCircle) -
            ∫ x, f x ∂AddCircle.haarAddCircle‖ := by
      have hdecomp : circleAverage P g N - ∫ x, f x ∂AddCircle.haarAddCircle =
          (circleAverage P g N - ∫ x, g x ∂AddCircle.haarAddCircle) +
            ((∫ x, g x ∂AddCircle.haarAddCircle) -
              ∫ x, f x ∂AddCircle.haarAddCircle) := by ring
      rw [hdecomp]
      calc
        _ ≤ ‖circleAverage P f N - circleAverage P g N‖ +
            (‖circleAverage P g N - ∫ x, g x ∂AddCircle.haarAddCircle‖ +
              ‖(∫ x, g x ∂AddCircle.haarAddCircle) -
                ∫ x, f x ∂AddCircle.haarAddCircle‖) := by
          convert add_le_add_left (norm_add_le
            (circleAverage P g N - ∫ x, g x ∂AddCircle.haarAddCircle)
            ((∫ x, g x ∂AddCircle.haarAddCircle) -
              ∫ x, f x ∂AddCircle.haarAddCircle))
              ‖circleAverage P f N - circleAverage P g N‖ using 1 <;> ring
        _ = _ := by ring
    _ < ε := by
      have hN' : ‖circleAverage P g N -
          ∫ x, g x ∂AddCircle.haarAddCircle‖ < ε / 3 := by
        simpa [dist_eq_norm] using hN
      linarith

noncomputable def haarProbability : ProbabilityMeasure (AddCircle (1 : ℝ)) :=
  ⟨AddCircle.haarAddCircle, inferInstance⟩

noncomputable def empiricalMeasureRaw (P : Polynomial ℝ) (N : ℕ) :
    Measure (AddCircle (1 : ℝ)) :=
  if N = 0 then AddCircle.haarAddCircle else
    (N : ENNReal)⁻¹ • ∑ n ∈ Finset.range N,
      Measure.dirac ((Polynomial.eval (n : ℝ) P : ℝ) : AddCircle (1 : ℝ))

private theorem empiricalMeasureRaw_isProbability (P : Polynomial ℝ) (N : ℕ) :
    IsProbabilityMeasure (empiricalMeasureRaw P N) := by
  by_cases hN : N = 0
  · rw [empiricalMeasureRaw, if_pos hN]
    infer_instance
  · refine ⟨?_⟩
    rw [empiricalMeasureRaw, if_neg hN]
    rw [Measure.smul_apply, Measure.finset_sum_apply]
    simp only [Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast hN) (ENNReal.natCast_ne_top N)

noncomputable def empiricalMeasure (P : Polynomial ℝ) (N : ℕ) :
    ProbabilityMeasure (AddCircle (1 : ℝ)) :=
  ⟨empiricalMeasureRaw P N, empiricalMeasureRaw_isProbability P N⟩

private theorem integral_empiricalMeasure (P : Polynomial ℝ) (N : ℕ) (hN : N ≠ 0)
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    (∫ x, f x ∂(empiricalMeasure P N : Measure (AddCircle (1 : ℝ)))) =
      circleAverage P f N := by
  rw [empiricalMeasure, ProbabilityMeasure.coe_mk, empiricalMeasureRaw, if_neg hN]
  have hi : ∀ n ∈ Finset.range N, Integrable f
      (Measure.dirac ((Polynomial.eval (n : ℝ) P : ℝ) : AddCircle (1 : ℝ))) := by
    intro n hn
    exact integrable_dirac (by simp)
  rw [integral_smul_measure, integral_finset_sum_measure hi]
  simp_rw [integral_dirac]
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  simp only [circleAverage]
  rw [Algebra.smul_def]
  push_cast
  rw [div_eq_mul_inv, mul_comm]

/-- The empirical measures of the polynomial values modulo one converge weakly
to Haar probability measure on the unit additive circle. -/
theorem tendsto_empiricalMeasure (P : Polynomial ℝ)
    (hP : Irrational P.leadingCoeff) (hdeg : 1 ≤ P.natDegree) :
    Tendsto (empiricalMeasure P) atTop (nhds haarProbability) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ]
  intro f
  have h := tendsto_circleAverage P hP hdeg f.toContinuousMap
  have h' := (tendsto_congr' (show ∀ᶠ N : ℕ in atTop,
      (∫ x, f x ∂(empiricalMeasure P N : Measure (AddCircle (1 : ℝ)))) =
        circleAverage P f.toContinuousMap N by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact integral_empiricalMeasure P N (Nat.ne_of_gt hN) f.toContinuousMap)).2 h
  simpa [haarProbability] using h'

private theorem empiricalMeasure_apply (P : Polynomial ℝ) (N : ℕ) (hN : N ≠ 0)
    (s : Set (AddCircle (1 : ℝ))) :
    ((empiricalMeasure P N) s : ℝ) =
      (((Finset.range N).filter fun n : ℕ =>
        ((Polynomial.eval (n : ℝ) P : ℝ) : AddCircle (1 : ℝ)) ∈ s).card : ℝ) / N := by
  classical
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn, empiricalMeasure,
    ProbabilityMeasure.coe_mk, empiricalMeasureRaw, if_neg hN,
    MeasureTheory.measureReal_def, Measure.smul_apply, Measure.finset_sum_apply]
  simp only [Measure.dirac_apply, Set.indicator, Pi.one_apply]
  rw [smul_eq_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [Finset.sum_boole]
  rw [ENNReal.toReal_natCast]
  rw [div_eq_mul_inv, mul_comm]

/-- Portmanteau consequence of polynomial Weyl equidistribution. This reusable
form applies to every continuity set of Haar measure on the unit circle. -/
theorem frequency_of_null_frontier (P : Polynomial ℝ)
    (hP : Irrational P.leadingCoeff) (hdeg : 1 ≤ P.natDegree)
    (s : Set (AddCircle (1 : ℝ)))
    (hfront : haarProbability (frontier s) = 0) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter fun n : ℕ =>
        ((Polynomial.eval (n : ℝ) P : ℝ) : AddCircle (1 : ℝ)) ∈ s).card : ℝ) / N)
      atTop (nhds (haarProbability s : ℝ)) := by
  classical
  have hweak := tendsto_empiricalMeasure P hP hdeg
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
    hweak hfront
  have hreal : Tendsto (fun N => ((empiricalMeasure P N) s : ℝ)) atTop
      (nhds (haarProbability s : ℝ)) := NNReal.tendsto_coe.mpr hport
  refine (tendsto_congr' (show ∀ᶠ N : ℕ in atTop,
      ((empiricalMeasure P N) s : ℝ) =
        (((Finset.range N).filter fun n : ℕ =>
          ((Polynomial.eval (n : ℝ) P : ℝ) : AddCircle (1 : ℝ)) ∈ s).card : ℝ) / N by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact empiricalMeasure_apply P N (Nat.ne_of_gt hN) s)).1 hreal

private def intervalArc (a b : ℝ) : Set (AddCircle (1 : ℝ)) :=
  QuotientAddGroup.mk '' Set.Ico a b

private theorem mem_intervalArc_iff (a b x : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) :
    (x : AddCircle (1 : ℝ)) ∈ intervalArc a b ↔
      a ≤ Int.fract x ∧ Int.fract x < b := by
  constructor
  · rintro ⟨y, hy, heq⟩
    have hy01 : y ∈ Set.Ico (0 : ℝ) 1 := ⟨ha.trans hy.1, hy.2.trans_le hb⟩
    have hfr01 : Int.fract x ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
    have hyeq : y = Int.fract x :=
      (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := (0 : ℝ))
        (by simpa using hy01) (by simpa using hfr01)).mp
        (heq.trans (AddCircle.coe_fract x).symm)
    simpa [hyeq] using hy
  · intro hx
    exact ⟨Int.fract x, hx, AddCircle.coe_fract x⟩

private theorem intervalArc_topology (a b : ℝ) (hab : a ≤ b) (hlen : b - a < 1) :
    IsClosed (intervalArc a b ∪ {(b : AddCircle (1 : ℝ))}) ∧
      IsOpen ((fun x : ℝ => (x : AddCircle (1 : ℝ))) '' Set.Ioo a b) ∧
      frontier (intervalArc a b) ⊆
        {(a : AddCircle (1 : ℝ)), (b : AddCircle (1 : ℝ))} := by
  let d := (1 - (b - a)) / 2
  let t := a - d
  have hd : 0 < d := by dsimp [d]; linarith
  have hta : t < a := by dsimp [t]; linarith
  have hbt : b < t + 1 := by dsimp [t, d]; linarith
  let C : Set (AddCircle (1 : ℝ)) := QuotientAddGroup.mk '' Set.Icc a b
  let O : Set (AddCircle (1 : ℝ)) := QuotientAddGroup.mk '' Set.Ioo a b
  have hCclosed : IsClosed C := by
    exact (isCompact_Icc.image (AddCircle.continuous_mk' (1 : ℝ))).isClosed
  have hCI : C = intervalArc a b ∪ {(b : AddCircle (1 : ℝ))} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      by_cases hyb : y = b
      · subst y
        simp
      · left
        exact ⟨y, ⟨hy.1, lt_of_le_of_ne hy.2 hyb⟩, rfl⟩
    · rintro (hx | rfl)
      · rcases hx with ⟨y, hy, rfl⟩
        exact ⟨y, ⟨hy.1, hy.2.le⟩, rfl⟩
      · exact ⟨b, ⟨hab, le_rfl⟩, rfl⟩
  have hsource : Set.Ioo a b ⊆ (AddCircle.openPartialHomeomorphCoe (1 : ℝ) t).source := by
    rw [AddCircle.openPartialHomeomorphCoe_source]
    intro x hx
    exact ⟨hta.trans hx.1, hx.2.trans hbt⟩
  have htarget : O ⊆ (AddCircle.openPartialHomeomorphCoe (1 : ℝ) t).target := by
    rw [AddCircle.openPartialHomeomorphCoe_target]
    rintro _ ⟨x, hx, rfl⟩ heq
    simp only [Set.mem_singleton_iff] at heq
    have hxioc : x ∈ Set.Ioc t (t + 1) := ⟨hta.trans hx.1, hx.2.trans hbt |>.le⟩
    have htIoc : t + 1 ∈ Set.Ioc t (t + 1) := ⟨by linarith, le_rfl⟩
    have heq' : (x : AddCircle (1 : ℝ)) = (t + 1 : ℝ) := by
      simpa [AddCircle.coe_add_period] using heq
    have := (AddCircle.coe_eq_coe_iff_of_mem_Ioc hxioc htIoc).mp heq'
    have hxb := hx.2
    rw [this] at hxb
    linarith
  have himage : (AddCircle.openPartialHomeomorphCoe (1 : ℝ) t).IsImage
      (Set.Ioo a b) O := by
    apply OpenPartialHomeomorph.IsImage.of_image_eq
    rw [Set.inter_eq_right.mpr hsource, Set.inter_eq_right.mpr htarget]
    simp only [O]
    apply Set.image_congr
    intro x hx
    exact AddCircle.openPartialHomeomorphCoe_apply (1 : ℝ) t x
  have hOopen : IsOpen O := by
    have hopen := himage.isOpen_iff.mp (by
      rw [Set.inter_eq_right.mpr hsource]
      exact isOpen_Ioo)
    rw [Set.inter_eq_right.mpr htarget] at hopen
    exact hopen
  refine ⟨hCI ▸ hCclosed, hOopen, ?_⟩
  intro x hx
  have hxC : x ∈ C := closure_minimal (by
      intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      exact ⟨y, ⟨hy.1, hy.2.le⟩, rfl⟩) hCclosed
    (frontier_subset_closure hx)
  have hxnotO : x ∉ O := by
    intro hxO
    exact hx.2 (interior_maximal (by
      intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      exact ⟨y, ⟨hy.1.le, hy.2⟩, rfl⟩) hOopen hxO)
  rcases hxC with ⟨y, hy, rfl⟩
  have hy_not : y ∉ Set.Ioo a b := fun hy' => hxnotO ⟨y, hy', rfl⟩
  have : y = a ∨ y = b := by
    rcases lt_or_eq_of_le hy.1 with hya | hya
    · right
      exact le_antisymm hy.2 (le_of_not_gt fun hyb => hy_not ⟨hya, hyb⟩)
    · exact Or.inl hya.symm
  rcases this with rfl | rfl <;> simp

private theorem intervalArc_measure (a b : ℝ) (hab : a ≤ b) (hlen : b - a < 1) :
    (haarProbability (intervalArc a b) : ℝ) = b - a ∧
      haarProbability (frontier (intervalArc a b)) = 0 := by
  let d := (1 - (b - a)) / 2
  let t := a - d
  have hd : 0 < d := by dsimp [d]; linarith
  have hta : t < a := by dsimp [t]; linarith
  have hbt : b < t + 1 := by dsimp [t, d]; linarith
  have hb_lt : b < a + 1 := by linarith
  have hbnot : (b : AddCircle (1 : ℝ)) ∉ intervalArc a b := by
    rintro ⟨y, hy, heq⟩
    have hyIco : y ∈ Set.Ico a (a + 1) := ⟨hy.1, hy.2.trans hb_lt⟩
    have hbIco : b ∈ Set.Ico a (a + 1) := ⟨hab, hb_lt⟩
    have : y = b := (AddCircle.coe_eq_coe_iff_of_mem_Ico hyIco hbIco).mp heq
    have hyb := hy.2
    rw [this] at hyb
    exact (lt_irrefl b hyb)
  have hclosed := (intervalArc_topology a b hab hlen).1
  have hmeas : MeasurableSet (intervalArc a b) := by
    have heq : intervalArc a b =
        (intervalArc a b ∪ {(b : AddCircle (1 : ℝ))}) \ {(b : AddCircle (1 : ℝ))} := by
      ext x
      simp only [Set.mem_diff, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · intro hx
        exact ⟨Or.inl hx, fun hxb => hbnot (hxb ▸ hx)⟩
      · exact fun hx => hx.1.resolve_right hx.2
    rw [heq]
    exact hclosed.measurableSet.diff (MeasurableSet.singleton _)
  have hpre : QuotientAddGroup.mk ⁻¹' intervalArc a b ∩ Set.Ioc t (t + 1) =
      Set.Ico a b := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, heq⟩, hx⟩
      have hyIoc : y ∈ Set.Ioc t (t + 1) :=
        ⟨hta.trans_le hy.1, hy.2.trans hbt |>.le⟩
      have hxy : x = y :=
        (AddCircle.coe_eq_coe_iff_of_mem_Ioc hx hyIoc).mp heq.symm
      simpa [hxy] using hy
    · intro hx
      exact ⟨⟨x, hx, rfl⟩, ⟨hta.trans_le hx.1, hx.2.trans hbt |>.le⟩⟩
  have hproj := AddCircle.add_projection_respects_measure (1 : ℝ) t hmeas
  rw [hpre, Real.volume_Ico] at hproj
  have hvol : (volume : Measure (AddCircle (1 : ℝ))) = AddCircle.haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  have hmass : AddCircle.haarAddCircle (intervalArc a b) = ENNReal.ofReal (b - a) := by
    rw [← hvol]
    exact hproj
  constructor
  · rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn]
    change AddCircle.haarAddCircle.real (intervalArc a b) = b - a
    rw [MeasureTheory.measureReal_def, hmass, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  · apply (ProbabilityMeasure.null_iff_toMeasure_null haarProbability _).mpr
    change AddCircle.haarAddCircle (frontier (intervalArc a b)) = 0
    apply measure_mono_null (intervalArc_topology a b hab hlen).2.2
    change AddCircle.haarAddCircle
      ({(a : AddCircle (1 : ℝ))} ∪ {(b : AddCircle (1 : ℝ))}) = 0
    have hsingle (x : AddCircle (1 : ℝ)) : AddCircle.haarAddCircle {x} = 0 := by
      rw [← hvol, ← Metric.closedBall_zero, AddCircle.volume_closedBall]
      norm_num
    exact measure_union_null (hsingle _) (hsingle _)

/-- Fixed half-open interval frequencies for the fractional parts of a real
polynomial with irrational leading coefficient. This matches the intended
`TuringTask.freq_poly` signature without importing the placeholder in
`Basic.lean`. -/
theorem freq_poly (P : Polynomial ℝ) (hP : Irrational P.leadingCoeff)
    (hdeg : 1 ≤ P.natDegree) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => (((Finset.range N).filter (fun n : ℕ =>
      a ≤ Int.fract (Polynomial.eval (n : ℝ) P) ∧
        Int.fract (Polynomial.eval (n : ℝ) P) < b)).card : ℝ) / N)
      atTop (nhds (b - a)) := by
  by_cases hlen : b - a < 1
  · have hm := intervalArc_measure a b hab hlen
    have hf := frequency_of_null_frontier P hP hdeg (intervalArc a b) hm.2
    rw [hm.1] at hf
    simpa only [mem_intervalArc_iff a b _ ha hb] using hf
  · have hba : b - a = 1 := by linarith
    have ha0 : a = 0 := by linarith
    have hb1 : b = 1 := by linarith
    subst a
    subst b
    refine (tendsto_congr' (show ∀ᶠ N : ℕ in atTop,
        (((Finset.range N).filter (fun n : ℕ =>
          0 ≤ Int.fract (Polynomial.eval (n : ℝ) P) ∧
            Int.fract (Polynomial.eval (n : ℝ) P) < 1)).card : ℝ) / N = 1 by
      filter_upwards [eventually_ge_atTop 1] with N hN
      simp [Int.fract_nonneg, Int.fract_lt_one, Nat.ne_of_gt hN])).2 ?_
    simpa using (tendsto_const_nhds (x := (1 : ℝ)))

end TuringTask.Equidistribution
