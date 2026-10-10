import Mathlib
import TuringTask.Equid

/-!
# The Weyl criterion

If all nontrivial Weyl sums of a sequence `g : ℕ → ℝ` vanish, then for every continuous
`1`-periodic function the Cesàro averages converge to the integral over one period.
-/

open Finset Filter Complex Polynomial MeasureTheory AddCircle

namespace TuringTask

noncomputable section

instance factOneLtZero : Fact ((0:ℝ) < 1) := ⟨one_pos⟩

/-- The normalized averages of a function along a sequence in the circle. -/
def avg (g : ℕ → ℝ) (f : AddCircle (1:ℝ) → ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N, f ((g n : ℝ) : AddCircle (1:ℝ))) / N

/-- `WeylEquid g` : the averages of continuous functions along `g` converge to the Haar integral. -/
def WeylEquid (g : ℕ → ℝ) : Prop :=
  ∀ f : C(AddCircle (1:ℝ), ℂ),
    Tendsto (avg g f) atTop (nhds (∫ x, f x ∂(@haarAddCircle 1 factOneLtZero)))

lemma fourier_apply_real (m : ℤ) (x : ℝ) :
    (fourier (T := (1:ℝ)) m) ((x : ℝ) : AddCircle (1:ℝ)) = e ((m : ℝ) * x) := by
  rw [fourier_coe_apply, e]
  congr 1
  push_cast
  ring

lemma integral_fourier_zero :
    ∫ x, (fourier (T := (1:ℝ)) 0) x ∂(@haarAddCircle 1 factOneLtZero) = 1 := by
  simp

lemma integral_fourier_ne_zero {m : ℤ} (hm : m ≠ 0) :
    ∫ x, (fourier (T := (1:ℝ)) m) x ∂(@haarAddCircle 1 factOneLtZero) = 0 := by
  have h := fourierCoeff_fourier (T := (1:ℝ)) m
  have h0 := congrFun h 0
  rw [fourierCoeff] at h0
  simp only [fourier_zero, smul_eq_mul] at h0
  rw [Pi.single_eq_of_ne' hm] at h0
  simpa using h0


lemma integrable_cont (f : C(AddCircle (1:ℝ), ℂ)) :
    Integrable f (@haarAddCircle 1 factOneLtZero) :=
  (map_continuous f).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma norm_avg_le (g : ℕ → ℝ) (f : C(AddCircle (1:ℝ), ℂ)) (N : ℕ) (hN : 0 < N) :
    ‖avg g f N‖ ≤ ‖f‖ := by
  rw [avg, norm_div, Complex.norm_natCast, div_le_iff₀ (by exact_mod_cast hN)]
  calc ‖∑ n ∈ Finset.range N, f ((g n : ℝ) : AddCircle (1:ℝ))‖
      ≤ ∑ n ∈ Finset.range N, ‖f ((g n : ℝ) : AddCircle (1:ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range N, ‖f‖ := Finset.sum_le_sum fun n _ => f.norm_coe_le_norm _
    _ = ‖f‖ * N := by rw [Finset.sum_const, Finset.card_range]; ring

lemma norm_integral_sub_le (f1 f2 : C(AddCircle (1:ℝ), ℂ)) :
    ‖(∫ x, f1 x ∂(@haarAddCircle 1 factOneLtZero))
      - ∫ x, f2 x ∂(@haarAddCircle 1 factOneLtZero)‖ ≤ ‖f1 - f2‖ := by
  rw [← integral_sub (integrable_cont f1) (integrable_cont f2)]
  have := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := (@haarAddCircle 1 factOneLtZero)) (f := fun x => f1 x - f2 x) (C := ‖f1 - f2‖)
    (by filter_upwards with x; exact (f1 - f2).norm_coe_le_norm x)
  simpa using this

def Good (g : ℕ → ℝ) : Submodule ℂ C(AddCircle (1:ℝ), ℂ) where
  carrier := {f | Tendsto (avg g f) atTop (nhds (∫ x, f x ∂(@haarAddCircle 1 factOneLtZero)))}
  add_mem' := by
    intro f1 f2 h1 h2
    simp only [Set.mem_setOf_eq] at *
    have hint : ∫ x, (f1 + f2) x ∂(@haarAddCircle 1 factOneLtZero)
        = (∫ x, f1 x ∂(@haarAddCircle 1 factOneLtZero)) + ∫ x, f2 x ∂(@haarAddCircle 1 factOneLtZero) := by
      rw [← integral_add]
      · rfl
      · exact (map_continuous f1).integrable_of_hasCompactSupport (by exact HasCompactSupport.of_compactSpace _)
      · exact (map_continuous f2).integrable_of_hasCompactSupport (by exact HasCompactSupport.of_compactSpace _)
    rw [hint]
    have heq : avg g (⇑(f1 + f2)) = fun N => avg g f1 N + avg g f2 N := by
      funext N
      simp only [avg, ContinuousMap.coe_add, Pi.add_apply]
      rw [← add_div, Finset.sum_add_distrib]
    rw [heq]
    exact h1.add h2
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    have heq : avg g (⇑(0 : C(AddCircle (1:ℝ), ℂ))) = fun _ => (0:ℂ) := by
      funext N; simp [avg]
    rw [heq]
    simp
  smul_mem' := by
    intro c f h
    simp only [Set.mem_setOf_eq] at *
    have hint : ∫ x, (c • f) x ∂(@haarAddCircle 1 factOneLtZero)
        = c * ∫ x, f x ∂(@haarAddCircle 1 factOneLtZero) := by
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      rw [MeasureTheory.integral_const_mul]
    rw [hint]
    have heq : avg g (⇑(c • f)) = fun N => c * avg g f N := by
      funext N
      simp only [avg, ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [← Finset.mul_sum, mul_div_assoc]
    rw [heq]
    exact h.const_mul c


lemma isClosed_good (g : ℕ → ℝ) : IsClosed (Good g : Set C(AddCircle (1:ℝ), ℂ)) := by
  rw [← closure_subset_iff_isClosed]
  intro f hf
  show Tendsto (avg g f) atTop (nhds (∫ x, f x ∂(@haarAddCircle 1 factOneLtZero)))
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.mem_closure_iff] at hf
  obtain ⟨h, hhS, hdist⟩ := hf (ε/3) (by linarith)
  rw [dist_eq_norm] at hdist
  have hh : Tendsto (avg g h) atTop (nhds (∫ x, h x ∂(@haarAddCircle 1 factOneLtZero))) := hhS
  rw [Metric.tendsto_atTop] at hh
  obtain ⟨N0, hN0⟩ := hh (ε/3) (by linarith)
  refine ⟨max N0 1, fun N hN => ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le one_pos (le_trans (le_max_right N0 1) hN)
  have h1 : ‖avg g f N - avg g h N‖ ≤ ‖f - h‖ := by
    have heq : avg g f N - avg g h N = avg g (⇑(f - h)) N := by
      simp only [avg, ContinuousMap.coe_sub, Pi.sub_apply]
      rw [← sub_div, Finset.sum_sub_distrib]
    rw [heq]
    exact norm_avg_le g (f - h) N hNpos
  have h2 := hN0 N (le_trans (le_max_left N0 1) hN)
  rw [dist_eq_norm] at h2 ⊢
  have h3 := norm_integral_sub_le h f
  have h4 : ‖h - f‖ = ‖f - h‖ := norm_sub_rev _ _
  calc ‖avg g f N - ∫ x, f x ∂(@haarAddCircle 1 factOneLtZero)‖
      ≤ ‖avg g f N - avg g h N‖ + ‖avg g h N - ∫ x, h x ∂(@haarAddCircle 1 factOneLtZero)‖
        + ‖(∫ x, h x ∂(@haarAddCircle 1 factOneLtZero)) - ∫ x, f x ∂(@haarAddCircle 1 factOneLtZero)‖ := by
        have := norm_add₃_le (a := avg g f N - avg g h N)
          (b := avg g h N - ∫ x, h x ∂(@haarAddCircle 1 factOneLtZero))
          (c := (∫ x, h x ∂(@haarAddCircle 1 factOneLtZero)) - ∫ x, f x ∂(@haarAddCircle 1 factOneLtZero))
        simpa using this
    _ < ε := by rw [h4] at h3; linarith

lemma fourier_mem_good (g : ℕ → ℝ) (hg : ∀ m : ℤ, m ≠ 0 → WeylNull (fun n => (m:ℝ) * g n)) (m : ℤ) :
    (fourier (T := (1:ℝ)) m) ∈ Good g := by
  show Tendsto (avg g (fourier (T := (1:ℝ)) m)) atTop
    (nhds (∫ x, (fourier (T := (1:ℝ)) m) x ∂(@haarAddCircle 1 factOneLtZero)))
  have havg : ∀ N : ℕ, avg g (fourier (T := (1:ℝ)) m) N = weylAvg (fun n => (m:ℝ) * g n) N := by
    intro N
    rw [avg, weylAvg]
    congr 1
    exact Finset.sum_congr rfl fun n _ => fourier_apply_real m (g n)
  simp only [funext havg]
  rcases eq_or_ne m 0 with rfl | hm
  · rw [integral_fourier_zero]
    have hev : ∀ᶠ N in atTop, weylAvg (fun n => ((0:ℤ):ℝ) * g n) N = 1 := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hNR : (N:ℂ) ≠ 0 := by
        have : 0 < N := hN
        exact_mod_cast this.ne'
      rw [weylAvg]
      simp only [Int.cast_zero, zero_mul]
      rw [show (∑ _n ∈ Finset.range N, e (0:ℝ)) = (N:ℂ) by
        simp [e]]
      exact div_self hNR
    exact Tendsto.congr' (EventuallyEq.symm hev) tendsto_const_nhds
  · rw [integral_fourier_ne_zero hm]
    exact hg m hm

lemma weylEquid_aux (g : ℕ → ℝ) (hclosed : IsClosed (Good g : Set C(AddCircle (1:ℝ), ℂ)))
    (hmono : ∀ m : ℤ, (fourier (T := (1:ℝ)) m) ∈ Good g) : WeylEquid g := by
  intro f
  have hsub : (Submodule.span ℂ (Set.range (fourier (T := (1:ℝ))))).topologicalClosure ≤ Good g := by
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      rintro x ⟨m, rfl⟩
      exact hmono m
    · exact hclosed
  rw [span_fourier_closure_eq_top] at hsub
  exact hsub (Submodule.mem_top)

/-- **The Weyl criterion.** -/
theorem weylEquid_of_weylNull (g : ℕ → ℝ)
    (hg : ∀ m : ℤ, m ≠ 0 → WeylNull (fun n => (m:ℝ) * g n)) : WeylEquid g :=
  weylEquid_aux g (isClosed_good g) (fourier_mem_good g hg)


end

end TuringTask
