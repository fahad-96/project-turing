import Mathlib

namespace TuringTask

open Finset Filter Topology Real MeasureTheory

/-- `(log x)²/2` has derivative `log x / x` on `(0, ∞)`. -/
theorem hasDerivAt_log_sq_div_two (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t => (Real.log t) ^ 2 / 2) (Real.log x / x) x := by
  have h0 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have h1 : HasDerivAt (fun t : ℝ => Real.log t ^ 2) (2 * Real.log x ^ (2 - 1) * x⁻¹) x := h0.pow 2
  have h2 := h1.div_const 2
  have heq : 2 * Real.log x ^ (2 - 1) * x⁻¹ / 2 = Real.log x / x := by norm_num; ring
  rwa [heq] at h2

/-- `∫_a^b log x / x dx = (log b)²/2 - (log a)²/2` for `0 < a ≤ b`. -/
theorem integral_log_div_self (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, Real.log x / x = (Real.log b) ^ 2 / 2 - (Real.log a) ^ 2 / 2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => (Real.log t) ^ 2 / 2)]
  · intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact hasDerivAt_log_sq_div_two x (lt_of_lt_of_le ha hx.1)
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.div (Real.continuousOn_log.mono ?_) continuousOn_id
    · intro x hx; exact ne_of_gt (lt_of_lt_of_le ha hx.1)
    · intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (lt_of_lt_of_le ha hx.1)

/-- `log x / x` is antitone on `[3, ∞)`. -/
theorem antitoneOn_log_div_self : AntitoneOn (fun x : ℝ => Real.log x / x) (Set.Ici 3) := by
  apply Real.log_div_self_antitoneOn.mono
  intro x hx
  simp only [Set.mem_Ici] at *
  have h : Real.exp 1 ≤ 3 := le_trans Real.exp_one_lt_d9.le (by norm_num)
  linarith

/-- `G(N) = ∑_{a ≤ N} (log a)/a`. -/
noncomputable def G (N : ℕ) : ℝ := ∑ a ∈ Icc 1 N, Real.log a / a

lemma G_split (N : ℕ) (hN : 3 ≤ N) :
    G N = Real.log 2 / 2 + ∑ a ∈ Ico 3 (N + 1), Real.log a / a := by
  rw [G, show Icc 1 N = Ico 1 (N + 1) from by ext x; simp,
    ← Finset.sum_Ico_consecutive _ (by omega : (1 : ℕ) ≤ 3) (by omega : (3 : ℕ) ≤ N + 1)]
  congr 1
  rw [show Finset.Ico 1 3 = {1, 2} from by decide]
  norm_num

/-- Antitonicity of `log x / x` on the real interval `[3, N]`. -/
lemma anti_on_Icc (N : ℕ) : AntitoneOn (fun x : ℝ => Real.log x / x) (Set.Icc (3 : ℕ) (N : ℕ)) := by
  apply antitoneOn_log_div_self.mono
  intro x hx
  simp only [Set.mem_Icc, Set.mem_Ici, Nat.cast_ofNat] at *
  exact hx.1

/-- Upper bound: `∑_{3 ≤ a ≤ N} log a / a ≤ (log N)²/2 - (log 3)²/2 + log 3 / 3`. -/
lemma tail_le (N : ℕ) (hN : 3 ≤ N) :
    ∑ a ∈ Ico 3 (N + 1), Real.log a / a
      ≤ (Real.log N) ^ 2 / 2 - (Real.log 3) ^ 2 / 2 + Real.log 3 / 3 := by
  -- `∑_{a ∈ Ico 3 N} f(a+1) ≤ ∫_3^N f`, and the sum over `Ico 3 (N+1)` is `f 3 + ∑_{Ico 3 N} f(a+1)`
  have hcmp := AntitoneOn.sum_le_integral_Ico (f := fun x : ℝ => Real.log x / x) hN (anti_on_Icc N)
  norm_num at hcmp
  rw [integral_log_div_self 3 N (by norm_num) (by exact_mod_cast hN)] at hcmp
  have hsplit : ∑ a ∈ Ico 3 (N + 1), Real.log a / a
      = Real.log 3 / 3 + ∑ a ∈ Ico 3 N, Real.log ((a : ℝ) + 1) / ((a : ℝ) + 1) := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 3 < N + 1)]
    norm_num
    rw [← Finset.sum_Ico_add' (fun a : ℕ => Real.log a / a) 3 N 1]
    exact Finset.sum_congr rfl fun a _ => by push_cast; ring
  rw [hsplit]
  linarith [hcmp]

/-- Lower bound: `(log N)²/2 - (log 3)²/2 ≤ ∑_{3 ≤ a ≤ N} log a / a`. -/
lemma le_tail (N : ℕ) (hN : 3 ≤ N) :
    (Real.log N) ^ 2 / 2 - (Real.log 3) ^ 2 / 2 ≤ ∑ a ∈ Ico 3 (N + 1), Real.log a / a := by
  have hcmp := AntitoneOn.integral_le_sum_Ico (f := fun x : ℝ => Real.log x / x) hN (anti_on_Icc N)
  norm_num at hcmp
  rw [integral_log_div_self 3 N (by norm_num) (by exact_mod_cast hN)] at hcmp
  have hsub : ∑ a ∈ Ico 3 N, Real.log a / a ≤ ∑ a ∈ Ico 3 (N + 1), Real.log a / a := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.Ico_subset_Ico le_rfl (by omega)
    · intro a ha _
      rw [Finset.mem_Ico] at ha
      have h1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (by omega : 1 ≤ a)
      exact div_nonneg (Real.log_nonneg h1) (by linarith)
  linarith

/-- Two-sided bracketing of `G(N)` for `N ≥ 3`. -/
lemma G_bounds (N : ℕ) (hN : 3 ≤ N) :
    (Real.log N) ^ 2 / 2 - 0.26 ≤ G N ∧ G N ≤ (Real.log N) ^ 2 / 2 + 0.26 := by
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlog3lo : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    exact le_trans Real.exp_one_lt_d9.le (by norm_num)
  have hlog3' : Real.log 3 ≤ 1.0987 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.0987) 9
    simp_rw [Finset.sum_range_succ, Nat.factorial] at hs
    norm_num at hs ⊢
    linarith
  have hlog3'' : Real.log 3 ≤ 1.2 := by
    have he : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have h2 : Real.log (3 / 2) ≤ 1 / 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 2 by norm_num); linarith
    have h3 := Real.log_two_lt_d9
    rw [he]; norm_num at h3 ⊢; linarith
  have hlo := le_tail N hN
  have hhi := tail_le N hN
  have h1 : (0 : ℝ) ≤ (Real.log 3) ^ 2 / 2 := by positivity
  have h2 : Real.log 3 / 3 ≤ 1 := by linarith
  have h3 : (0.5 : ℝ) ≤ (Real.log 3) ^ 2 / 2 := by nlinarith
  have h4 : (Real.log 3) ^ 2 / 2 ≤ 0.6037 := by nlinarith [hlog3', hlog3lo]
  have h5 : Real.log 3 / 3 ≤ 0.368 := by linarith
  have h6 : (0.3465 : ℝ) ≤ Real.log 2 / 2 := by
    have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  have h7 : Real.log 2 / 2 ≤ 0.347 := by
    have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
  rw [G_split N hN]
  constructor
  · linarith
  · linarith

/-- `|G(N) - (log N)²/2| ≤ 0.26` for all `N ≥ 1`. -/
lemma abs_G_sub_le (N : ℕ) (hN : 1 ≤ N) : |G N - (Real.log N) ^ 2 / 2| ≤ 0.26 := by
  rcases (by omega : N = 1 ∨ N = 2 ∨ 3 ≤ N) with rfl | rfl | h3
  · simp [G]; norm_num
  · have hG : G 2 = Real.log 2 / 2 := by
      rw [G, show Finset.Icc 1 2 = {1, 2} from by decide]
      norm_num
    rw [hG]
    have h1 := Real.log_two_lt_d9
    have h2 := Real.log_two_gt_d9
    rw [abs_le]
    norm_num at h1 h2 ⊢
    constructor <;> nlinarith
  · have := G_bounds N h3
    rw [abs_le]
    constructor <;> linarith [this.1, this.2]

end TuringTask
