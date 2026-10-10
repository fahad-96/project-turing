import Mathlib

namespace TuringTask

open Finset Filter Topology Real

/-- The `N`-th harmonic number as a real number. -/
noncomputable def H (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, (1 : ℝ) / n

lemma H_eq_harmonic (N : ℕ) : H N = ((harmonic N : ℚ) : ℝ) := by
  rw [H, harmonic]
  push_cast
  rw [show Icc 1 N = Ico 1 (N + 1) from by ext x; simp, Finset.sum_Ico_eq_sum_range]
  simp [add_comm]

/-- `γ < H N - log N` for `N ≥ 1`. -/
lemma gamma_lt_H_sub_log (N : ℕ) (hN : 1 ≤ N) :
    eulerMascheroniConstant < H N - Real.log N := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' N
  rwa [Real.eulerMascheroniSeq', if_neg (by omega), ← H_eq_harmonic] at h

/-- `H N - log (N+1) < γ`. -/
lemma H_sub_log_succ_lt_gamma (N : ℕ) :
    H N - Real.log ((N : ℝ) + 1) < eulerMascheroniConstant := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant N
  rwa [Real.eulerMascheroniSeq, ← H_eq_harmonic] at h

/-- The error `H N - log N - γ` lies in `(0, 1/N]`. -/
lemma H_error_pos (N : ℕ) (hN : 1 ≤ N) :
    0 < H N - Real.log N - eulerMascheroniConstant := by
  have := gamma_lt_H_sub_log N hN; linarith

lemma H_error_le (N : ℕ) (hN : 1 ≤ N) :
    H N - Real.log N - eulerMascheroniConstant ≤ 1 / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := H_sub_log_succ_lt_gamma N
  have h2 : Real.log ((N : ℝ) + 1) - Real.log N ≤ 1 / N := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have heq : ((N : ℝ) + 1) / N = 1 + 1 / N := by field_simp
    rw [heq]
    calc Real.log (1 + 1 / N) ≤ (1 + 1 / N) - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ = 1 / N := by ring
  linarith

/-- Combined: `|H N - log N - γ| ≤ 1/N`. -/
lemma abs_H_error_le (N : ℕ) (hN : 1 ≤ N) :
    |H N - Real.log N - eulerMascheroniConstant| ≤ 1 / N := by
  rw [abs_of_pos (H_error_pos N hN)]
  exact H_error_le N hN

end TuringTask
