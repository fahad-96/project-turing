import Mathlib

namespace TuringTask

open Finset Filter Topology Real MeasureTheory

/-- `log` is monotone on `[1, N]`. -/
lemma monotoneOn_log (N : ℕ) : MonotoneOn Real.log (Set.Icc ((1 : ℕ) : ℝ) ((N : ℕ) : ℝ)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Icc, Nat.cast_one] at hx hy
  exact Real.log_le_log (by linarith [hx.1]) hxy

/-- `∫_1^N log x dx = N log N - N + 1`. -/
lemma integral_log_one_to (N : ℕ) :
    ∫ x in ((1 : ℕ) : ℝ)..((N : ℕ) : ℝ), Real.log x = (N : ℝ) * Real.log N - N + 1 := by
  rw [integral_log]
  simp

/-- Elementary Stirling bound: `0 ≤ ∑_{n ≤ N} log n - (N log N - N + 1) ≤ log N`. -/
lemma log_factorial_bounds (N : ℕ) (hN : 1 ≤ N) :
    0 ≤ (∑ n ∈ Icc 1 N, Real.log n) - ((N : ℝ) * Real.log N - N + 1) ∧
      (∑ n ∈ Icc 1 N, Real.log n) - ((N : ℝ) * Real.log N - N + 1) ≤ Real.log N := by
  have hIco : Icc 1 N = Ico 1 (N + 1) := by ext x; simp
  -- upper comparison: `∑_{x ∈ Ico 1 N} log x ≤ ∫_1^N log`
  have hup := MonotoneOn.sum_le_integral_Ico (f := Real.log) hN (monotoneOn_log N)
  -- lower comparison: `∫_1^N log ≤ ∑_{i ∈ Ico 1 N} log (i+1)`
  have hlo := MonotoneOn.integral_le_sum_Ico (f := Real.log) hN (monotoneOn_log N)
  rw [integral_log_one_to N] at hup hlo
  -- relate the two sums to `∑_{n ∈ Icc 1 N} log n`
  have hsum1 : ∑ x ∈ Ico 1 N, Real.log x = (∑ n ∈ Icc 1 N, Real.log n) - Real.log N := by
    rw [hIco, Finset.sum_Ico_succ_top (by omega : 1 ≤ N)]
    ring
  have hsum2 : ∑ i ∈ Ico 1 N, Real.log ((i : ℕ) + 1 : ℕ) = ∑ n ∈ Icc 1 N, Real.log n := by
    rw [Finset.sum_Ico_add' (fun n : ℕ => Real.log n) 1 N 1, hIco,
      Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < N + 1)]
    norm_num
  rw [hsum1] at hup
  rw [hsum2] at hlo
  constructor
  · linarith
  · linarith

/-! ### The weighted sum `∑ n log n` -/

/-- `x² log x / 2 - x²/4` has derivative `x log x` on `(0, ∞)`. -/
lemma hasDerivAt_xlogx (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t => t ^ 2 * Real.log t / 2 - t ^ 2 / 4) (x * Real.log x) x := by
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
  have h2 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have h3 : HasDerivAt (fun t : ℝ => t ^ 2 * Real.log t) (2 * x * Real.log x + x ^ 2 * x⁻¹) x :=
    h1.mul h2
  have h4 := (h3.div_const 2).sub (h1.div_const 4)
  have heq : (2 * x * Real.log x + x ^ 2 * x⁻¹) / 2 - 2 * x / 4 = x * Real.log x := by
    field_simp; ring
  rwa [heq] at h4

/-- `∫_1^N x log x dx = N² log N / 2 - N²/4 + 1/4`. -/
lemma integral_xlogx (N : ℕ) (hN : 1 ≤ N) :
    ∫ x in ((1 : ℕ) : ℝ)..((N : ℕ) : ℝ), x * Real.log x
      = (N : ℝ) ^ 2 * Real.log N / 2 - (N : ℝ) ^ 2 / 4 + 1 / 4 := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => t ^ 2 * Real.log t / 2 - t ^ 2 / 4)]
  · simp
  · intro x hx
    rw [Set.uIcc_of_le (by exact_mod_cast hNR)] at hx
    simp only [Nat.cast_one, Set.mem_Icc] at hx
    exact hasDerivAt_xlogx x (by linarith [hx.1])
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_id
    apply Real.continuousOn_log.mono
    intro x hx
    rw [Set.uIcc_of_le (by exact_mod_cast hNR)] at hx
    simp only [Nat.cast_one, Set.mem_Icc] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt (by linarith [hx.1])

/-- `x ↦ x log x` is monotone on `[1, N]`. -/
lemma monotoneOn_xlogx (N : ℕ) :
    MonotoneOn (fun x : ℝ => x * Real.log x) (Set.Icc ((1 : ℕ) : ℝ) ((N : ℕ) : ℝ)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Icc, Nat.cast_one] at hx hy
  have hx1 : (1 : ℝ) ≤ x := hx.1
  have hy1 : (1 : ℝ) ≤ y := hy.1
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hly : Real.log x ≤ Real.log y := Real.log_le_log (by linarith) hxy
  nlinarith

/-- Bracketing for `∑_{n ≤ N} n log n`. -/
lemma sum_xlogx_bounds (N : ℕ) (hN : 1 ≤ N) :
    0 ≤ (∑ n ∈ Icc 1 N, (n : ℝ) * Real.log n) -
          ((N : ℝ) ^ 2 * Real.log N / 2 - (N : ℝ) ^ 2 / 4 + 1 / 4) ∧
      (∑ n ∈ Icc 1 N, (n : ℝ) * Real.log n) -
          ((N : ℝ) ^ 2 * Real.log N / 2 - (N : ℝ) ^ 2 / 4 + 1 / 4) ≤ (N : ℝ) * Real.log N := by
  have hIco : Icc 1 N = Ico 1 (N + 1) := by ext x; simp
  have hup := MonotoneOn.sum_le_integral_Ico (f := fun x : ℝ => x * Real.log x) hN
    (monotoneOn_xlogx N)
  have hlo := MonotoneOn.integral_le_sum_Ico (f := fun x : ℝ => x * Real.log x) hN
    (monotoneOn_xlogx N)
  rw [integral_xlogx N hN] at hup hlo
  have hsum1 : ∑ x ∈ Ico 1 N, (x : ℝ) * Real.log x
      = (∑ n ∈ Icc 1 N, (n : ℝ) * Real.log n) - (N : ℝ) * Real.log N := by
    rw [hIco, Finset.sum_Ico_succ_top (by omega : 1 ≤ N)]
    ring
  have hsum2 : ∑ i ∈ Ico 1 N, ((i + 1 : ℕ) : ℝ) * Real.log ((i + 1 : ℕ) : ℝ)
      = ∑ n ∈ Icc 1 N, (n : ℝ) * Real.log n := by
    rw [Finset.sum_Ico_add' (fun n : ℕ => (n : ℝ) * Real.log n) 1 N 1, hIco,
      Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < N + 1)]
    norm_num
  rw [hsum1] at hup
  rw [hsum2] at hlo
  exact ⟨by linarith, by linarith⟩

end TuringTask
