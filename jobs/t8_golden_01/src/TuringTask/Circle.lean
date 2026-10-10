import Mathlib
import TuringTask.PolySum

/-!
# Averages of continuous functions on the circle

If `(1/N) sum_(n<N) ephase (k u_n) -> 0` for every integer `k != 0`, then for every continuous
`F : AddCircle 1 -> C` the averages `(1/N) sum_(n<N) F (u_n)` tend to the integral of `F` against
the normalised Haar measure.  Proof: approximate `F` uniformly by a finite combination of the
monomials `fourier k` (`span_fourier_closure_eq_top`) and compare three terms.
-/

open Finset Filter MeasureTheory AddCircle

namespace TuringTask

lemma fourier_coe_eq_ephase (k : ℤ) (t : ℝ) :
    fourier k (t : AddCircle (1 : ℝ)) = ephase (k * t) := by
  rw [fourier_coe_apply]
  unfold ephase
  congr 1
  push_cast
  ring

lemma integral_fourier_haar (k : ℤ) :
    ∫ t, fourier k t ∂(haarAddCircle (T := (1 : ℝ))) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk
    simp
  · exact integral_eq_zero_of_add_right_eq_neg (μ := haarAddCircle)
      (fourier_add_half_inv_index hk one_pos)

lemma integrable_haar (F : C(AddCircle (1 : ℝ), ℂ)) :
    Integrable F (haarAddCircle (T := (1 : ℝ))) :=
  F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma tendsto_avg_fourier (u : ℕ → ℝ)
    (hu : ∀ k : ℤ, k ≠ 0 →
      Tendsto (fun N : ℕ => (∑ n ∈ range N, ephase (k * u n)) / N) atTop (nhds 0))
    (k : ℤ) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, fourier k (u n : AddCircle (1 : ℝ))) / N) atTop
      (nhds (if k = 0 then 1 else 0)) := by
  split_ifs with hk
  · subst hk
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN1
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    simp [hN']
  · refine (hu k hk).congr fun N => ?_
    simp_rw [fourier_coe_eq_ephase]

/-- The norm of an average of values of `F` is at most the sup norm of `F`. -/
lemma norm_mean_le_sup (F : C(AddCircle (1 : ℝ), ℂ)) (u : ℕ → ℝ) (N : ℕ) :
    ‖(∑ n ∈ range N, F (u n)) / N‖ ≤ ‖F‖ := by
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp
  · have hN : (0 : ℝ) < N := by exact_mod_cast hpos
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ hN]
    refine (norm_sum_le _ _).trans ?_
    have := Finset.sum_le_sum fun n (_ : n ∈ range N) => F.norm_coe_le_norm (u n)
    simpa [mul_comm] using this

/-- Equidistribution in the form of continuous test functions. -/
theorem tendsto_avg_circle (u : ℕ → ℝ)
    (hu : ∀ k : ℤ, k ≠ 0 →
      Tendsto (fun N : ℕ => (∑ n ∈ range N, ephase (k * u n)) / N) atTop (nhds 0))
    (F : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, F (u n)) / N) atTop
      (nhds (∫ t, F t ∂(haarAddCircle (T := (1 : ℝ))))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hF : F ∈ (Submodule.span ℂ (Set.range (@fourier (1 : ℝ)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    exact Submodule.mem_top
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hF
  obtain ⟨G, hG, hFG⟩ := hF (ε / 3) (by positivity)
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hG
  set G : C(AddCircle (1 : ℝ), ℂ) := c.sum fun i a => a • fourier i with hGdef
  have hGapp : ∀ t, G t = ∑ i ∈ c.support, c i * fourier i t := by
    intro t
    simp [hGdef, Finsupp.sum, ContinuousMap.coe_sum]
  -- the averages of `G` converge to `c 0`
  have hlimG : Tendsto (fun N : ℕ => (∑ n ∈ range N, G (u n)) / N) atTop (nhds (c 0)) := by
    have hsum : Tendsto (fun N : ℕ => ∑ i ∈ c.support,
        c i * ((∑ n ∈ range N, fourier i (u n : AddCircle (1 : ℝ))) / N)) atTop
        (nhds (∑ i ∈ c.support, c i * (if i = 0 then 1 else 0))) :=
      tendsto_finsetSum _ fun i _ => (tendsto_avg_fourier u hu i).const_mul (c i)
    have hval : ∑ i ∈ c.support, c i * (if i = 0 then (1 : ℂ) else 0) = c 0 := by
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq']
      split_ifs with h
      · rfl
      · exact (Finsupp.notMem_support_iff.mp h).symm
    rw [hval] at hsum
    refine hsum.congr fun N => ?_
    simp_rw [hGapp]
    rw [Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, mul_div_assoc]
  have hintG : ∫ t, G t ∂(haarAddCircle (T := (1 : ℝ))) = c 0 := by
    simp_rw [hGapp]
    rw [integral_finsetSum _ fun i _ => (integrable_haar (fourier i)).const_mul (c i)]
    simp_rw [integral_const_mul, integral_fourier_haar]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · exact (Finsupp.notMem_support_iff.mp h).symm
  have hint : ‖∫ t, F t ∂(haarAddCircle (T := (1 : ℝ))) - c 0‖ < ε / 3 := by
    rw [← hintG, ← integral_sub (integrable_haar F) (integrable_haar G)]
    have hb : ∀ t, ‖F t - G t‖ ≤ ‖F - G‖ := fun t => (F - G).norm_coe_le_norm t
    have := norm_integral_le_of_norm_le_const (μ := haarAddCircle (T := (1 : ℝ)))
      (Filter.Eventually.of_forall hb)
    rw [probReal_univ, mul_one] at this
    rw [dist_eq_norm] at hFG
    linarith
  obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.mp hlimG) (ε / 3) (by positivity)
  refine ⟨N0, fun N hN => ?_⟩
  have h1 : ‖(∑ n ∈ range N, F (u n)) / N - (∑ n ∈ range N, G (u n)) / N‖ < ε / 3 := by
    have e : (∑ n ∈ range N, F (u n)) / N - (∑ n ∈ range N, G (u n)) / N
        = (∑ n ∈ range N, (F - G) (u n)) / N := by
      rw [← sub_div]
      rw [← Finset.sum_sub_distrib]
      rfl
    rw [e]
    refine lt_of_le_of_lt (norm_mean_le_sup (F - G) u N) ?_
    rwa [dist_eq_norm] at hFG
  have h2 := hN0 N hN
  rw [dist_eq_norm] at h2 ⊢
  have := norm_sub_le_norm_sub_add_norm_sub ((∑ n ∈ range N, F (u n)) / N)
    ((∑ n ∈ range N, G (u n)) / N) (c 0)
  have h3 : ‖c 0 - ∫ t, F t ∂(haarAddCircle (T := (1 : ℝ)))‖ < ε / 3 := by
    rwa [norm_sub_rev]
  have := norm_sub_le_norm_sub_add_norm_sub ((∑ n ∈ range N, F (u n)) / N) (c 0)
    (∫ t, F t ∂(haarAddCircle (T := (1 : ℝ))))
  linarith

end TuringTask
