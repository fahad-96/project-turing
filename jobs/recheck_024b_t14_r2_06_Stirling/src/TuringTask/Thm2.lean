import TuringTask.Divisors
import TuringTask.Floor
import TuringTask.LogSum

namespace TuringTask

open Finset Filter Topology Real

/-- `∑_{n ≤ N} d(n)/n = ∑_{a ≤ N} (1/a) H(⌊N/a⌋)`. -/
lemma sum_div_eq (N : ℕ) :
    ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) / n
      = ∑ a ∈ Icc 1 N, (1 / (a : ℝ)) * H (N / a) := by
  have h := sum_hypN_fiberwise (M := ℝ) N (fun n => 1 / (n : ℝ))
  simp only [nsmul_eq_mul] at h
  have hL : ∑ p ∈ hypN N, (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ)
      = ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 (N / a), (1 : ℝ) / ((a * b : ℕ) : ℝ) := by
    rw [hypN_eq_hypL, sum_hypL]
  rw [hL] at h
  have hR : ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 (N / a), (1 : ℝ) / ((a * b : ℕ) : ℝ)
      = ∑ a ∈ Icc 1 N, (1 / (a : ℝ)) * H (N / a) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [mem_Icc] at ha
    rw [H, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    push_cast
    ring
  rw [hR] at h
  rw [h]
  exact Finset.sum_congr rfl fun n _ => by rw [mul_one_div]

/-- Per-term error bound: with `m = ⌊N/a⌋ ≥ 1`, we have
`|H m - log(N/a) - γ| ≤ 1/m`. -/
lemma term_error_bound (N a : ℕ) (ha : 1 ≤ a) (haN : a ≤ N) :
    |H (N / a) - (Real.log N - Real.log a) - eulerMascheroniConstant| ≤ 1 / ((N / a : ℕ) : ℝ) := by
  set m := N / a with hm
  have hm1 : 1 ≤ m := Nat.one_le_div_iff (by omega) |>.mpr haN
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 1 ≤ N)
  -- `log N - log a = log (N/a)`
  have hlogdiv : Real.log N - Real.log a = Real.log ((N : ℝ) / a) :=
    (Real.log_div hNR.ne' haR.ne').symm
  -- `m ≤ N/a < m+1`
  have hmle : (m : ℝ) ≤ (N : ℝ) / a := by
    rw [le_div_iff₀ haR]
    exact_mod_cast Nat.div_mul_le_self N a
  have hmlt : (N : ℝ) / a < (m : ℝ) + 1 := by
    rw [div_lt_iff₀ haR]
    have hkey : N < a * (m + 1) := by
      have h1 := Nat.div_add_mod N a
      have h2 := Nat.mod_lt N (show 0 < a by omega)
      have hexp : a * (m + 1) = a * m + a := by ring
      rw [hexp, hm]
      omega
    have : (N : ℝ) < (a : ℝ) * ((m : ℝ) + 1) := by exact_mod_cast hkey
    linarith
  -- harmonic bracketing at `m`
  have hlo : 0 < H m - Real.log m - eulerMascheroniConstant := H_error_pos m hm1
  have hhi : H m - Real.log m - eulerMascheroniConstant ≤ 1 / m := H_error_le m hm1
  -- `0 ≤ log(N/a) - log m ≤ log(1 + 1/m) ≤ 1/m`
  have hd0 : 0 ≤ Real.log ((N : ℝ) / a) - Real.log m :=
    sub_nonneg.mpr (Real.log_le_log hmR hmle)
  have hd1 : Real.log ((N : ℝ) / a) - Real.log m ≤ 1 / m := by
    have hstep : Real.log ((N : ℝ) / a) ≤ Real.log ((m : ℝ) + 1) :=
      Real.log_le_log (by positivity) hmlt.le
    have hlog1 : Real.log ((m : ℝ) + 1) - Real.log m ≤ 1 / m := by
      rw [← Real.log_div (by positivity) hmR.ne']
      have heq : ((m : ℝ) + 1) / m = 1 + 1 / m := by field_simp
      rw [heq]
      calc Real.log (1 + 1 / m) ≤ (1 + 1 / m) - 1 := Real.log_le_sub_one_of_pos (by positivity)
        _ = 1 / m := by ring
    linarith
  rw [hlogdiv, abs_le]
  constructor <;> linarith

/-- `1/⌊N/a⌋ ≤ 2a/N` for `1 ≤ a ≤ N`, since `⌊x⌋ > x - 1 ≥ x/2` for `x ≥ 1`. -/
lemma one_div_natDiv_le (N a : ℕ) (ha : 1 ≤ a) (haN : a ≤ N) :
    1 / ((N / a : ℕ) : ℝ) ≤ 2 * (a : ℝ) / N := by
  set m := N / a with hm
  have hm1 : 1 ≤ m := Nat.one_le_div_iff (by omega) |>.mpr haN
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 1 ≤ N)
  -- `N ≤ 2 * a * m` : from `N < a*(m+1) = a*m + a` and `a ≤ a*m`
  have hNat : N ≤ 2 * (a * m) := by
    have h1 := Nat.div_add_mod N a
    have h2 := Nat.mod_lt N (show 0 < a by omega)
    have h3 : a ≤ a * m := Nat.le_mul_of_pos_right a hm1
    rw [hm] at h3 ⊢
    omega
  have hcast : (N : ℝ) ≤ 2 * ((a : ℝ) * (m : ℝ)) := by exact_mod_cast hNat
  rw [div_le_div_iff₀ hmR hNR]
  linarith

/-- Total weighted error bound: `∑_{a ≤ N} (1/a)·(1/⌊N/a⌋) ≤ 2`. -/
lemma sum_weighted_error_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ a ∈ Icc 1 N, (1 / (a : ℝ)) * (1 / ((N / a : ℕ) : ℝ)) ≤ 2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  calc ∑ a ∈ Icc 1 N, (1 / (a : ℝ)) * (1 / ((N / a : ℕ) : ℝ))
      ≤ ∑ a ∈ Icc 1 N, (1 / (a : ℝ)) * (2 * (a : ℝ) / N) := by
        apply Finset.sum_le_sum
        intro a ha
        rw [mem_Icc] at ha
        have haR : (0 : ℝ) < a := by exact_mod_cast ha.1
        exact mul_le_mul_of_nonneg_left (one_div_natDiv_le N a ha.1 ha.2) (by positivity)
    _ = ∑ _a ∈ Icc 1 N, (2 : ℝ) / N := by
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [mem_Icc] at ha
        have haR : (0 : ℝ) ≠ (a : ℝ) := by
          have : (0 : ℝ) < a := by exact_mod_cast ha.1
          linarith
        field_simp
    _ = 2 := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp only [Nat.add_sub_cancel]
        field_simp

/-! ### The main estimate for Theorem 2 -/

/-- Decomposition: `∑_{n≤N} d(n)/n = (log N + γ)·H N - G N + T`, where `|T| ≤ 2`. -/
lemma sum_div_decomp (N : ℕ) (hN : 1 ≤ N) :
    ∃ T : ℝ, |T| ≤ 2 ∧
      ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) / n
        = (Real.log N + eulerMascheroniConstant) * H N - G N + T := by
  refine ⟨∑ a ∈ Icc 1 N, (1 / (a : ℝ)) *
    (H (N / a) - (Real.log N - Real.log a) - eulerMascheroniConstant), ?_, ?_⟩
  · -- bound the error
    calc |∑ a ∈ Icc 1 N, (1 / (a : ℝ)) *
            (H (N / a) - (Real.log N - Real.log a) - eulerMascheroniConstant)|
        ≤ ∑ a ∈ Icc 1 N, |(1 / (a : ℝ)) *
            (H (N / a) - (Real.log N - Real.log a) - eulerMascheroniConstant)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ Icc 1 N, (1 / (a : ℝ)) * (1 / ((N / a : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum
          intro a ha
          rw [mem_Icc] at ha
          have haR : (0 : ℝ) < a := by exact_mod_cast ha.1
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (a : ℝ))]
          exact mul_le_mul_of_nonneg_left (term_error_bound N a ha.1 ha.2) (by positivity)
      _ ≤ 2 := sum_weighted_error_le N hN
  · -- the algebraic identity
    rw [sum_div_eq N]
    have hexp : ∀ a ∈ Icc 1 N, (1 / (a : ℝ)) * H (N / a)
        = (1 / (a : ℝ)) * (Real.log N - Real.log a + eulerMascheroniConstant)
          + (1 / (a : ℝ)) * (H (N / a) - (Real.log N - Real.log a)
              - eulerMascheroniConstant) := by
      intro a _; ring
    rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib]
    congr 1
    have hmain : ∑ a ∈ Icc 1 N, (1 / (a : ℝ)) *
        (Real.log N - Real.log a + eulerMascheroniConstant)
        = (Real.log N + eulerMascheroniConstant) * ∑ a ∈ Icc 1 N, (1 / (a : ℝ))
          - ∑ a ∈ Icc 1 N, Real.log a / a := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      field_simp
      ring
    rw [hmain, H, G]

/-- `log N / N ≤ 1/2` for `N ≥ 1`. -/
lemma log_div_self_le_half (N : ℕ) (hN : 1 ≤ N) : Real.log N / N ≤ 1 / 2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_iff₀ hNR]
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < Real.sqrt N by positivity)
  rw [Real.log_sqrt hNR.le] at h
  have hsq : Real.sqrt N * Real.sqrt N = (N : ℝ) := Real.mul_self_sqrt hNR.le
  have hpos : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (Real.sqrt N - 2), hsq, hpos]

/-- **Theorem 2 (main estimate).** -/
theorem main_estimate_two (N : ℕ) (hN : 1 ≤ N) :
    |∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) / n - (Real.log N) ^ 2 / 2 -
      2 * eulerMascheroniConstant * Real.log N| ≤ 4 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨T, hT, hTeq⟩ := sum_div_decomp N hN
  -- harmonic error
  set t := H N - Real.log N - eulerMascheroniConstant with htdef
  have ht0 : 0 < t := H_error_pos N hN
  have ht1 : t ≤ 1 / N := H_error_le N hN
  have hHN : H N = Real.log N + eulerMascheroniConstant + t := by rw [htdef]; ring
  -- `G` error
  set c := G N - (Real.log N) ^ 2 / 2 with hcdef
  have hc : |c| ≤ 0.26 := abs_G_sub_le N hN
  have hGN : G N = (Real.log N) ^ 2 / 2 + c := by rw [hcdef]; ring
  -- the algebra
  have hkey : ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) / n - (Real.log N) ^ 2 / 2 -
      2 * eulerMascheroniConstant * Real.log N
      = eulerMascheroniConstant ^ 2 + (Real.log N + eulerMascheroniConstant) * t - c + T := by
    rw [hTeq, hHN, hGN]; ring
  rw [hkey]
  -- bounds on `γ`
  have hg0 : (0 : ℝ) < eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hg1 : eulerMascheroniConstant < 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds
  -- `log N ≥ 0`
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  -- `log N * t ≤ log N / N ≤ 1/2`
  have hlt : Real.log N * t ≤ 1 / 2 := by
    calc Real.log N * t ≤ Real.log N * (1 / N) :=
          mul_le_mul_of_nonneg_left ht1 hlogN
      _ = Real.log N / N := by ring
      _ ≤ 1 / 2 := log_div_self_le_half N hN
  -- `γ * t ≤ γ ≤ 2/3`
  have hgt : eulerMascheroniConstant * t ≤ 2 / 3 := by
    have h1 : t ≤ 1 := by
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have : (1 : ℝ) / N ≤ 1 := by rw [div_le_one hNR]; exact hN1
      linarith
    nlinarith [hg0, hg1, ht0]
  have hgsq : eulerMascheroniConstant ^ 2 ≤ 4 / 9 := by nlinarith [hg0, hg1]
  have hgsq0 : (0 : ℝ) ≤ eulerMascheroniConstant ^ 2 := sq_nonneg _
  have hltpos : (0 : ℝ) ≤ Real.log N * t := mul_nonneg hlogN ht0.le
  have hgtpos : (0 : ℝ) ≤ eulerMascheroniConstant * t := by positivity
  rw [abs_le] at hT hc ⊢
  constructor
  · nlinarith [hT.1, hc.2, hgsq0, hltpos, hgtpos]
  · nlinarith [hT.2, hc.1, hgsq, hlt, hgt]

end TuringTask
