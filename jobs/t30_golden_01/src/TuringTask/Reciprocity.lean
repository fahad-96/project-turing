import Mathlib
import TuringTask.Formulas

/-!
# Dedekind reciprocity

For coprime `h, k ≥ 1` let `q(r) = ⌊h r / k⌋`.
* `floor_eq_card`: for `t < h`, `⌊k t / h⌋` counts the `r` with `1 ≤ r < k` and `h r < k t`
  (`h r = k t` is impossible).
* `two_S2_swap`: counting the pairs `(r, t)` with `h r < k t` both ways gives
  `2 S₂(k, h) = (k - 1) h (h - 1) - (Q(h, k) + Σq(h, k))`.
* `reciprocity`: with `twelve_k_dsum`, `twelve_h_S2` and `two_Sq`,
  `12 h k (s(h, k) + s(k, h)) = h² + k² + 1 - 3 h k`.
-/

namespace TuringTask

open Finset

lemma floor_eq_card {h k t : ℕ} (hhk : Nat.Coprime h k) (ht : t < h) :
    k * t / h = ((range k).filter (fun r => 0 < r ∧ h * r < k * t)).card := by
  have hh : 0 < h := lt_of_le_of_lt (Nat.zero_le t) ht
  rcases Nat.eq_zero_or_pos t with ht0 | ht0
  · subst ht0
    rw [mul_zero, Nat.zero_div]
    symm
    rw [card_eq_zero, filter_eq_empty_iff]
    intro r _ h'
    omega
  set m := k * t / h with hm
  have hmk : m < k := by
    rw [hm, Nat.div_lt_iff_lt_mul hh]
    exact Nat.mul_lt_mul_of_pos_left ht (by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        exfalso
        have := Nat.Coprime.eq_one_of_dvd hhk (dvd_zero h)
        omega
      · exact hk)
  have hne : ∀ r, h * r ≠ k * t := by
    intro r hr
    have hdvd : h ∣ k * t := ⟨r, hr.symm⟩
    have := Nat.Coprime.dvd_of_dvd_mul_left hhk hdvd
    have := Nat.le_of_dvd ht0 this
    omega
  have hset : (range k).filter (fun r => 0 < r ∧ h * r < k * t) = Icc 1 m := by
    ext r
    simp only [mem_filter, mem_range, mem_Icc]
    constructor
    · rintro ⟨-, hr0, hr⟩
      refine ⟨hr0, ?_⟩
      rw [hm, Nat.le_div_iff_mul_le hh, mul_comm]
      exact hr.le
    · rintro ⟨hr0, hr⟩
      refine ⟨by omega, hr0, ?_⟩
      have : r * h ≤ k * t := (Nat.le_div_iff_mul_le hh).mp hr
      rw [mul_comm] at this
      exact lt_of_le_of_ne this (hne r)
  rw [hset, Nat.card_Icc, Nat.add_sub_cancel]

lemma sum_Ioo_rat (q h : ℕ) (hqh : q < h) :
    2 * ∑ t ∈ (range h).filter (fun t => q < t), (t : ℚ) = h * (h - 1) - q * (q + 1) := by
  have hset : (range h).filter (fun t => q < t) = Ico (q + 1) h := by
    ext t; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [hset]
  have := sum_range_add_sum_Ico (fun t => (t : ℚ)) (show q + 1 ≤ h by omega)
  rw [sum_range_id_rat, sum_range_id_rat] at this
  push_cast at this
  linarith

lemma two_S2_swap {h k : ℕ} (hhk : Nat.Coprime h k) (hk : 0 < k) :
    2 * (dS2 k h : ℚ) = (k - 1) * h * (h - 1) - ((dQ h k : ℚ) + (dSq h k : ℚ)) := by
  have step1 : (dS2 k h : ℚ) = ∑ r ∈ range k, ∑ t ∈ range h,
      (if 0 < r ∧ h * r < k * t then (t : ℚ) else 0) := by
    unfold dS2
    push_cast
    rw [sum_comm]
    apply sum_congr rfl
    intro t ht
    rw [floor_eq_card hhk (mem_range.mp ht), ← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  have step2 : ∀ r ∈ range k, 2 * ∑ t ∈ range h,
      (if 0 < r ∧ h * r < k * t then (t : ℚ) else 0) =
      (if r = 0 then 0 else (h : ℚ) * (h - 1) - ((h * r / k : ℕ) : ℚ) ^ 2 -
        ((h * r / k : ℕ) : ℚ)) := by
    intro r hr
    have hrk := mem_range.mp hr
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0; simp
    · rw [if_neg h0.ne']
      have hq : h * r / k < h := by
        rw [Nat.div_lt_iff_lt_mul hk]
        exact Nat.mul_lt_mul_of_pos_left hrk (by
          rcases Nat.eq_zero_or_pos h with hh | hh
          · subst hh
            exfalso
            have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hhk) (dvd_zero k)
            omega
          · exact hh)
      have hfilt : ∑ t ∈ range h, (if 0 < r ∧ h * r < k * t then (t : ℚ) else 0) =
          ∑ t ∈ (range h).filter (fun t => h * r / k < t), (t : ℚ) := by
        rw [sum_filter]
        apply sum_congr rfl
        intro t _
        have : (0 < r ∧ h * r < k * t) ↔ h * r / k < t := by
          rw [Nat.div_lt_iff_lt_mul hk, mul_comm t k]
          exact ⟨fun h' => h'.2, fun h' => ⟨h0, h'⟩⟩
        simp only [this]
      rw [hfilt, sum_Ioo_rat _ _ hq]
      ring
  rw [step1, mul_sum, sum_congr rfl step2]
  unfold dQ dSq
  push_cast
  have hsplit : ∀ r ∈ range k, (if r = 0 then (0 : ℚ) else (h : ℚ) * (h - 1) -
      ((h * r / k : ℕ) : ℚ) ^ 2 - ((h * r / k : ℕ) : ℚ)) =
      (h : ℚ) * (h - 1) - ((h * r / k : ℕ) : ℚ) ^ 2 - ((h * r / k : ℕ) : ℚ) -
        (if r = 0 then (h : ℚ) * (h - 1) else 0) := by
    intro r _
    split_ifs with h0
    · subst h0; simp
    · ring
  rw [sum_congr rfl hsplit]
  simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  rw [sum_ite_eq' (range k) 0 (fun _ => (h : ℚ) * (h - 1)), if_pos (mem_range.mpr hk)]
  ring

/-- Dedekind's reciprocity law. -/
theorem reciprocity {h k : ℕ} (hhk : Nat.Coprime h k) (hh : 0 < h) (hk : 0 < k) :
    12 * h * k * (dsum h k + dsum k h) = h ^ 2 + k ^ 2 + 1 - 3 * h * k := by
  have e1 := twelve_k_dsum hhk hk
  have e2 := twelve_k_dsum (Nat.Coprime.symm hhk) hh
  have e3 := twelve_h_S2 hhk hk
  have e4 := two_S2_swap hhk hk
  have e5 := two_Sq hhk hk
  linear_combination (h : ℚ) * e1 + (k : ℚ) * e2 - e3 - 6 * (k : ℚ) * e4 + 3 * (k : ℚ) * e5

end TuringTask
