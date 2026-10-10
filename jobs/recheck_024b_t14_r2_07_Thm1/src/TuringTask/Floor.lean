import TuringTask.Harmonic

namespace TuringTask

open Finset Filter Topology Real

/-- `⌊N/a⌋ ≤ N/a` as reals. -/
lemma natDiv_le (N a : ℕ) (ha : 1 ≤ a) : ((N / a : ℕ) : ℝ) ≤ (N : ℝ) / a := by
  rw [le_div_iff₀ (by positivity)]
  exact_mod_cast Nat.div_mul_le_self N a

/-- `N/a - 1 < ⌊N/a⌋` as reals. -/
lemma sub_one_lt_natDiv (N a : ℕ) (ha : 1 ≤ a) : (N : ℝ) / a - 1 < ((N / a : ℕ) : ℝ) := by
  have hkey : N < a * (N / a) + a := by
    have h1 := Nat.div_add_mod N a
    have h2 := Nat.mod_lt N (show 0 < a by omega)
    omega
  have : (N : ℝ) < a * ((N / a : ℕ) : ℝ) + a := by exact_mod_cast hkey
  rw [sub_lt_iff_lt_add, div_lt_iff₀ (by positivity)]
  nlinarith [show (0:ℝ) < a by exact_mod_cast ha]

/-- The "fractional part" `N/a - ⌊N/a⌋` lies in `[0,1)`. -/
lemma natDiv_err_nonneg (N a : ℕ) (ha : 1 ≤ a) : 0 ≤ (N : ℝ) / a - ((N / a : ℕ) : ℝ) := by
  have := natDiv_le N a ha; linarith

lemma natDiv_err_lt_one (N a : ℕ) (ha : 1 ≤ a) : (N : ℝ) / a - ((N / a : ℕ) : ℝ) < 1 := by
  have := sub_one_lt_natDiv N a ha; linarith

/-- `∑_{a ≤ K} ⌊N/a⌋ = N * H K - E` where `0 ≤ E ≤ K - 1`.

The sharper bound `K - 1` (rather than `K`) comes from the `a = 1` term, whose error vanishes. -/
lemma sum_natDiv_eq (N K : ℕ) (hK : 1 ≤ K) :
    ∃ E : ℝ, 0 ≤ E ∧ E ≤ (K : ℝ) - 1 ∧
      (∑ a ∈ Icc 1 K, ((N / a : ℕ) : ℝ)) = (N : ℝ) * H K - E := by
  refine ⟨(∑ a ∈ Icc 1 K, ((N : ℝ) / a - ((N / a : ℕ) : ℝ))), ?_, ?_, ?_⟩
  · apply Finset.sum_nonneg
    intro a ha
    rw [mem_Icc] at ha
    exact natDiv_err_nonneg N a ha.1
  · -- split off `a = 1`, whose error term is `0`
    have hsplit : Icc 1 K = insert 1 (Icc 2 K) := by
      ext a
      simp only [mem_insert, mem_Icc]
      omega
    rw [hsplit, Finset.sum_insert (by simp)]
    have h1 : (N : ℝ) / (1 : ℕ) - ((N / 1 : ℕ) : ℝ) = 0 := by norm_num
    rw [h1, zero_add]
    calc (∑ a ∈ Icc 2 K, ((N : ℝ) / a - ((N / a : ℕ) : ℝ)))
        ≤ ∑ _a ∈ Icc 2 K, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro a ha
          rw [mem_Icc] at ha
          exact (natDiv_err_lt_one N a (by omega)).le
      _ = (K : ℝ) - 1 := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
          have : K + 1 - 2 = K - 1 := by omega
          rw [this, Nat.cast_sub hK]
          norm_num
  · have : (N : ℝ) * H K = ∑ a ∈ Icc 1 K, (N : ℝ) / a := by
      rw [H, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [this, Finset.sum_sub_distrib]
    ring

end TuringTask
