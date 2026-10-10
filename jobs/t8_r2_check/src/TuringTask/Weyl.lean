import Mathlib
import TuringTask.Poly

/-!
# Weyl sums and van der Corput's inequality
-/

open Finset Filter Complex Polynomial

namespace TuringTask

noncomputable section

/-- `e t = exp (2 π i t)`. -/
def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

@[simp] lemma norm_e (t : ℝ) : ‖e t‖ = 1 := by
  rw [e, Complex.norm_exp]
  norm_num

lemma e_add (s t : ℝ) : e (s + t) = e s * e t := by
  rw [e, e, e, ← Complex.exp_add]
  push_cast
  ring_nf

lemma e_ne_zero (t : ℝ) : e t ≠ 0 := Complex.exp_ne_zero _

lemma conj_e (t : ℝ) : (starRingEnd ℂ) (e t) = e (-t) := by
  rw [e, e, ← Complex.exp_conj]
  congr 1
  simp [Complex.ext_iff]

lemma e_sub (s t : ℝ) : e (s - t) = e s * (starRingEnd ℂ) (e t) := by
  rw [conj_e, ← e_add]; ring_nf

lemma e_intCast (m : ℤ) : e (m : ℝ) = 1 := by
  rw [e, Complex.exp_eq_one_iff]
  exact ⟨m, by push_cast; ring⟩

lemma e_eq_one_iff {t : ℝ} : e t = 1 ↔ ∃ m : ℤ, t = m := by
  constructor
  · intro h
    rw [e, Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    refine ⟨m, ?_⟩
    have hpi : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    have h2 : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
      simp [hpi, Complex.I_ne_zero]
    have : (t : ℂ) = (m : ℂ) := by
      apply mul_left_cancel₀ h2
      rw [hm]; ring
    exact_mod_cast this
  · rintro ⟨m, rfl⟩; exact e_intCast m

lemma e_nat_mul (t : ℝ) (n : ℕ) : e t ^ n = e (n * t) := by
  rw [e, e, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `e α ≠ 1` when `α` is irrational. -/
lemma e_ne_one_of_irrational {α : ℝ} (hα : Irrational α) : e α ≠ 1 := by
  intro h
  obtain ⟨m, hm⟩ := e_eq_one_iff.1 h
  exact hα.ne_int m hm

end


noncomputable section

open scoped ComplexConjugate

/-- Extension of `u : ℕ → ℂ` by zero outside `[0, N)`, as a function on `ℤ`. -/
def xt (u : ℕ → ℂ) (N : ℕ) (m : ℤ) : ℂ :=
  if 0 ≤ m ∧ m < (N : ℤ) then u m.toNat else 0

lemma xt_eq_zero (u : ℕ → ℂ) (N : ℕ) {m : ℤ} (hm : m ∉ Finset.Ico (0 : ℤ) (N : ℤ)) :
    xt u N m = 0 := by
  simp only [Finset.mem_Ico, not_and, not_lt] at hm
  unfold xt
  split_ifs with h
  · exact absurd (hm h.1) (not_le.2 h.2)
  · rfl

lemma xt_of_mem (u : ℕ → ℂ) (N : ℕ) {m : ℤ} (h1 : 0 ≤ m) (h2 : m < (N : ℤ)) :
    xt u N m = u m.toNat := by
  unfold xt; rw [if_pos ⟨h1, h2⟩]

lemma norm_xt_le (u : ℕ → ℂ) (hu : ∀ n, ‖u n‖ ≤ 1) (N : ℕ) (m : ℤ) : ‖xt u N m‖ ≤ 1 := by
  unfold xt; split_ifs
  · exact hu _
  · simp

lemma xt_nonneg_sum (u : ℕ → ℂ) (N : ℕ) :
    ∑ m ∈ Finset.Ico (0 : ℤ) (N : ℤ), xt u N m = ∑ n ∈ Finset.range N, u n := by
  rw [show ∑ m ∈ Finset.Ico (0 : ℤ) (N : ℤ), xt u N m
      = ∑ n ∈ Finset.range N, xt u N (n : ℤ) from ?_]
  · refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_range] at hn
    rw [xt_of_mem u N (by positivity) (by exact_mod_cast hn)]
    simp
  · refine Finset.sum_nbij' (i := Int.toNat) (j := fun n : ℕ => (n : ℤ)) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp at ha ⊢; omega
    · intro a ha; simp at ha ⊢; omega
    · intro a ha; simp at ha ⊢; omega
    · intro a _; simp
    · intro a ha; simp at ha; congr 1; omega

end


/-- Reindexing the off-diagonal correlation sums. -/
lemma corr_reindex (N H : ℕ) (u : ℕ → ℂ) (h1 h2 : ℕ) (hle : h2 ≤ h1) (hh2 : h2 < H) :
    ∑ m ∈ Finset.Ico (-(H:ℤ)) (N:ℤ), xt u N (m + h1) * (starRingEnd ℂ) (xt u N (m + h2))
      = ∑ n ∈ Finset.range (N - (h1 - h2)), u (n + (h1 - h2)) * (starRingEnd ℂ) (u n) := by
  set k : ℕ := h1 - h2 with hkdef
  have hk : (h1 : ℤ) = h2 + k := by omega
  rw [show ∑ m ∈ Finset.Ico (-(H:ℤ)) (N:ℤ), xt u N (m + h1) * (starRingEnd ℂ) (xt u N (m + h2))
      = ∑ n ∈ Finset.Ico (-(H:ℤ) + h2) ((N:ℤ) + h2),
          xt u N (n + k) * (starRingEnd ℂ) (xt u N n) from ?_]
  · rw [show ∑ n ∈ Finset.Ico (-(H:ℤ) + h2) ((N:ℤ) + h2),
          xt u N (n + k) * (starRingEnd ℂ) (xt u N n)
        = ∑ n ∈ Finset.Ico (0:ℤ) ((N:ℤ) - k),
          xt u N (n + k) * (starRingEnd ℂ) (xt u N n) from ?_]
    · refine Finset.sum_nbij' (i := Int.toNat) (j := fun n : ℕ => (n : ℤ)) ?_ ?_ ?_ ?_ ?_
      · intro a ha; simp only [Finset.mem_Ico, Finset.mem_range] at ha ⊢; omega
      · intro a ha; simp only [Finset.mem_range, Finset.mem_Ico] at ha ⊢; omega
      · intro a ha; simp only [Finset.mem_Ico] at ha; omega
      · intro a _; simp
      · intro a ha
        simp only [Finset.mem_Ico] at ha
        rw [xt_of_mem u N (by omega) (by omega), xt_of_mem u N ha.1 (by omega)]
        congr 2 <;> omega
    · refine (Finset.sum_subset ?_ ?_).symm
      · intro x hx; simp only [Finset.mem_Ico] at hx ⊢; omega
      · intro x hx hx2
        simp only [Finset.mem_Ico] at hx hx2
        by_cases h : 0 ≤ x ∧ x < (N:ℤ)
        · rw [show xt u N (x + (k:ℤ)) = 0 from
            xt_eq_zero u N (by simp only [Finset.mem_Ico]; omega)]
          ring
        · rw [show xt u N x = 0 from xt_eq_zero u N (by simp only [Finset.mem_Ico]; omega)]
          simp
  · rw [← Finset.map_add_right_Ico (-(H:ℤ)) (N:ℤ) (h2:ℤ), Finset.sum_map]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [addRightEmbedding_apply]
    congr 2
    omega

/-- The correlation sum `C u N k = ∑_{n < N - k} u (n + k) * conj (u n)`. -/
def corr (u : ℕ → ℂ) (N k : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (N - k), u (n + k) * (starRingEnd ℂ) (u n)

lemma corr_zero_norm_le (u : ℕ → ℂ) (hu : ∀ n, ‖u n‖ ≤ 1) (N : ℕ) : ‖corr u N 0‖ ≤ N := by
  rw [corr]
  calc ‖∑ n ∈ Finset.range (N - 0), u (n + 0) * (starRingEnd ℂ) (u n)‖
      ≤ ∑ n ∈ Finset.range (N - 0), ‖u (n + 0) * (starRingEnd ℂ) (u n)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (N - 0), (1 : ℝ) := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [norm_mul, RCLike.norm_conj]
        exact mul_le_one₀ (hu _) (norm_nonneg _) (hu n)
    _ = N := by simp

/-- **Van der Corput's inequality.** -/
theorem van_der_corput (N H : ℕ) (hH : 0 < H) (u : ℕ → ℂ) (hu : ∀ n, ‖u n‖ ≤ 1) :
    (H:ℝ) * ‖∑ n ∈ Finset.range N, u n‖^2
      ≤ ((N:ℝ) + H) * ((N:ℝ) + 2 * ∑ k ∈ Finset.Ico 1 H, ‖corr u N k‖) := by
  have hHR : (0:ℝ) < H := by exact_mod_cast hH
  have main : (H:ℝ)^2 * ‖∑ n ∈ Finset.range N, u n‖^2
      ≤ ((N:ℝ) + H) * ((H:ℝ) * N + 2 * ((H:ℝ) * ∑ k ∈ Finset.Ico 1 H, ‖corr u N k‖)) := ?_
  · have hrw : ((N:ℝ) + H) * ((H:ℝ) * N + 2 * ((H:ℝ) * ∑ k ∈ Finset.Ico 1 H, ‖corr u N k‖))
        = (H:ℝ) * (((N:ℝ) + H) * ((N:ℝ) + 2 * ∑ k ∈ Finset.Ico 1 H, ‖corr u N k‖)) := by ring
    rw [hrw] at main
    have h2 : (H:ℝ)^2 * ‖∑ n ∈ Finset.range N, u n‖^2
        = (H:ℝ) * ((H:ℝ) * ‖∑ n ∈ Finset.range N, u n‖^2) := by ring
    rw [h2] at main
    exact le_of_mul_le_mul_left main hHR
  set v := xt u N with hvdef
  have hv : ∀ m, m ∉ Finset.Ico (0:ℤ) (N:ℤ) → v m = 0 := fun m hm => xt_eq_zero u N hm
  have hsum : ∑ m ∈ Finset.Ico (0:ℤ) (N:ℤ), v m = ∑ n ∈ Finset.range N, u n := xt_nonneg_sum u N
  set J := Finset.Ico (-(H:ℤ)) (N:ℤ) with hJ
  have step1 : (H : ℂ) * ∑ n ∈ Finset.range N, u n
      = ∑ m ∈ J, ∑ h ∈ Finset.range H, v (m + h) := by
    rw [← hsum]
    have key : ∀ h ∈ Finset.range H,
        ∑ m ∈ J, v (m + h) = ∑ m ∈ Finset.Ico (0:ℤ) (N:ℤ), v m := by
      intro h hh
      simp only [Finset.mem_range] at hh
      rw [show ∑ m ∈ J, v (m + h) = ∑ m ∈ Finset.Ico (-(H:ℤ) + h) ((N:ℤ) + h), v m from ?_]
      · refine (Finset.sum_subset ?_ ?_).symm
        · intro x hx; simp only [Finset.mem_Ico] at hx ⊢; omega
        · intro x _ hx; exact hv x hx
      · rw [hJ, ← Finset.map_add_right_Ico (-(H:ℤ)) (N:ℤ) (h:ℤ), Finset.sum_map]; rfl
    rw [Finset.sum_comm, Finset.sum_congr rfl key]
    simp [Finset.sum_const]
  have hcard : (J.card : ℝ) = (N:ℝ) + H := by
    rw [hJ, Int.card_Ico]
    rw [show ((N:ℤ) - -(H:ℤ)).toNat = N + H by omega]
    push_cast; ring
  have cs : ‖∑ m ∈ J, ∑ h ∈ Finset.range H, v (m + h)‖^2
      ≤ (J.card : ℝ) * ∑ m ∈ J, ‖∑ h ∈ Finset.range H, v (m + h)‖^2 := by
    calc ‖∑ m ∈ J, ∑ h ∈ Finset.range H, v (m + h)‖^2
        ≤ (∑ m ∈ J, ‖∑ h ∈ Finset.range H, v (m + h)‖)^2 := by
          have h0 : (0:ℝ) ≤ ∑ m ∈ J, ‖∑ h ∈ Finset.range H, v (m + h)‖ :=
            Finset.sum_nonneg fun i _ => norm_nonneg _
          have := norm_sum_le J fun m => ∑ h ∈ Finset.range H, v (m + h)
          nlinarith [norm_nonneg (∑ m ∈ J, ∑ h ∈ Finset.range H, v (m + h))]
      _ ≤ (J.card : ℝ) * ∑ m ∈ J, ‖∑ h ∈ Finset.range H, v (m + h)‖^2 := sq_sum_le_card_mul_sum_sq
  have expand : ∀ m : ℤ, ((‖∑ h ∈ Finset.range H, v (m + h)‖:ℝ):ℂ)^2
      = ∑ h1 ∈ Finset.range H, ∑ h2 ∈ Finset.range H,
          v (m + h1) * (starRingEnd ℂ) (v (m + h2)) := by
    intro m; rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
  have swap : ((∑ m ∈ J, ‖∑ h ∈ Finset.range H, v (m + h)‖^2 : ℝ) : ℂ)
      = ∑ h1 ∈ Finset.range H, ∑ h2 ∈ Finset.range H,
          ∑ m ∈ J, v (m + h1) * (starRingEnd ℂ) (v (m + h2)) := by
    push_cast
    rw [Finset.sum_congr rfl fun m _ => expand m, Finset.sum_comm]
    exact Finset.sum_congr rfl fun h1 _ => Finset.sum_comm
  have swapR : (∑ m ∈ J, ‖∑ h ∈ Finset.range H, v (m + h)‖^2)
      ≤ ∑ h1 ∈ Finset.range H, ∑ h2 ∈ Finset.range H,
          ‖∑ m ∈ J, v (m + h1) * (starRingEnd ℂ) (v (m + h2))‖ := by
    have hre : (∑ m ∈ J, ‖∑ h ∈ Finset.range H, v (m + h)‖^2)
        = (∑ h1 ∈ Finset.range H, ∑ h2 ∈ Finset.range H,
            ∑ m ∈ J, v (m + h1) * (starRingEnd ℂ) (v (m + h2))).re := by
      rw [← swap]; simp only [← Complex.ofReal_pow, Complex.ofReal_re]
    rw [hre]
    calc (∑ h1 ∈ Finset.range H, ∑ h2 ∈ Finset.range H,
            ∑ m ∈ J, v (m + h1) * (starRingEnd ℂ) (v (m + h2))).re
        ≤ ‖∑ h1 ∈ Finset.range H, ∑ h2 ∈ Finset.range H,
            ∑ m ∈ J, v (m + h1) * (starRingEnd ℂ) (v (m + h2))‖ := Complex.re_le_norm _
      _ ≤ ∑ h1 ∈ Finset.range H, ‖∑ h2 ∈ Finset.range H,
            ∑ m ∈ J, v (m + h1) * (starRingEnd ℂ) (v (m + h2))‖ := norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun h1 _ => norm_sum_le _ _
  -- Bound the double sum of correlation norms.
  have hterm : ∀ h1 ∈ Finset.range H, ∀ h2 ∈ Finset.range H,
      ‖∑ m ∈ J, v (m + h1) * (starRingEnd ℂ) (v (m + h2))‖
        ≤ if h1 = h2 then (N:ℝ) else ‖corr u N (max h1 h2 - min h1 h2)‖ := by
    intro h1 hmem1 h2 hmem2
    split_ifs with hEq
    · subst hEq
      rw [hJ, corr_reindex N H u h1 h1 le_rfl (by simpa using ‹h1 ∈ Finset.range H›)]
      simpa [corr] using corr_zero_norm_le u hu N
    · rcases le_total h2 h1 with hle | hle
      · rw [hJ, corr_reindex N H u h1 h2 hle (by simpa using ‹h2 ∈ Finset.range H›)]
        rw [max_eq_left hle, min_eq_right hle]
        rfl
      · -- h1 < h2, use conjugate symmetry
        have : ∑ m ∈ J, v (m + h1) * (starRingEnd ℂ) (v (m + h2))
            = (starRingEnd ℂ) (∑ m ∈ J, v (m + h2) * (starRingEnd ℂ) (v (m + h1))) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun m _ => by simp [mul_comm]
        rw [this, RCLike.norm_conj, hJ, corr_reindex N H u h2 h1 hle
          (by simpa using ‹h1 ∈ Finset.range H›)]
        rw [max_eq_right hle, min_eq_left hle]
        rfl
  have hdouble : ∑ h1 ∈ Finset.range H, ∑ h2 ∈ Finset.range H,
      ‖∑ m ∈ J, v (m + h1) * (starRingEnd ℂ) (v (m + h2))‖
      ≤ (H:ℝ) * N + 2 * ((H:ℝ) * ∑ k ∈ Finset.Ico 1 H, ‖corr u N k‖) := by
    refine le_trans (Finset.sum_le_sum fun h1 hh1 =>
      Finset.sum_le_sum fun h2 hh2 => hterm h1 hh1 h2 hh2) ?_
    -- count: diagonal gives H * N; off diagonal pairs with |h1-h2| = k appear ≤ 2 * (H-k) ≤ 2H times
    -- but we bound each inner sum directly
    have inner : ∀ h1 ∈ Finset.range H,
        ∑ h2 ∈ Finset.range H, (if h1 = h2 then (N:ℝ) else ‖corr u N (max h1 h2 - min h1 h2)‖)
          ≤ (N:ℝ) + 2 * ∑ k ∈ Finset.Ico 1 H, ‖corr u N k‖ := by
      intro h1 hh1
      simp only [Finset.mem_range] at hh1
      classical
      have hsplit : ∑ h2 ∈ Finset.range H,
          (if h1 = h2 then (N:ℝ) else ‖corr u N (max h1 h2 - min h1 h2)‖)
          = (N:ℝ) + ∑ h2 ∈ (Finset.range H).erase h1,
              ‖corr u N (max h1 h2 - min h1 h2)‖ := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hh1)]
        simp only [if_pos rfl]
        congr 1
        refine Finset.sum_congr rfl fun h2 hh2 => ?_
        rw [if_neg (Finset.ne_of_mem_erase hh2).symm]
      rw [hsplit]
      gcongr
      -- Now bound the erased sum by 2 * sum over k in [1,H)
      -- map h2 ↦ |h1 - h2| ∈ [1, H), each value attained at most twice
      have : ∑ h2 ∈ (Finset.range H).erase h1, ‖corr u N (max h1 h2 - min h1 h2)‖
          = ∑ h2 ∈ (Finset.range H).filter (fun h2 => h2 < h1), ‖corr u N (h1 - h2)‖
            + ∑ h2 ∈ (Finset.range H).filter (fun h2 => h1 < h2), ‖corr u N (h2 - h1)‖ := by
        rw [← Finset.sum_filter_add_sum_filter_not ((Finset.range H).erase h1)
          (fun h2 => h2 < h1)]
        congr 1
        · refine Finset.sum_congr ?_ fun h2 hh2 => ?_
          · ext h2; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range]
            constructor
            · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h, h'⟩
            · rintro ⟨h, h'⟩; exact ⟨⟨by omega, h⟩, h'⟩
          · simp only [Finset.mem_filter, Finset.mem_erase] at hh2
            rw [max_eq_left (by omega : h2 ≤ h1), min_eq_right (by omega : h2 ≤ h1)]
        · refine Finset.sum_congr ?_ fun h2 hh2 => ?_
          · ext h2
            simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range, not_lt]
            constructor
            · rintro ⟨⟨hne, h⟩, h'⟩; exact ⟨h, by omega⟩
            · rintro ⟨h, h'⟩; exact ⟨⟨by omega, h⟩, by omega⟩
          · simp only [Finset.mem_filter, Finset.mem_range] at hh2
            rw [max_eq_right (by omega : h1 ≤ h2), min_eq_left (by omega : h1 ≤ h2)]
      rw [this, two_mul]
      gcongr ?_ + ?_
      · have h1eq : (Finset.range H).filter (fun h2 => h2 < h1) = Finset.range h1 := by
          ext h2; simp only [Finset.mem_filter, Finset.mem_range]
          constructor
          · rintro ⟨_, h⟩; exact h
          · intro h; exact ⟨by omega, h⟩
        rw [h1eq]
        rw [show ∑ h2 ∈ Finset.range h1, ‖corr u N (h1 - h2)‖
            = ∑ k ∈ Finset.Ico 1 (h1+1), ‖corr u N k‖ from ?_]
        · exact Finset.sum_le_sum_of_subset_of_nonneg
            (fun x hx => by simp only [Finset.mem_Ico] at hx ⊢; omega)
            (fun i _ _ => norm_nonneg _)
        · refine Finset.sum_nbij' (i := fun h2 => h1 - h2) (j := fun k => h1 - k) ?_ ?_ ?_ ?_ ?_
          · intro a ha; simp only [Finset.mem_range, Finset.mem_Ico] at ha ⊢; omega
          · intro a ha; simp only [Finset.mem_Ico, Finset.mem_range] at ha ⊢; omega
          · intro a ha; simp only [Finset.mem_range] at ha; omega
          · intro a ha; simp only [Finset.mem_Ico] at ha; omega
          · intro a _; rfl
      · have h1eq : (Finset.range H).filter (fun h2 => h1 < h2) = Finset.Ico (h1+1) H := by
          ext h2; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
        rw [h1eq]
        rw [show ∑ h2 ∈ Finset.Ico (h1+1) H, ‖corr u N (h2 - h1)‖
            = ∑ k ∈ Finset.Ico 1 (H - h1), ‖corr u N k‖ from ?_]
        · exact Finset.sum_le_sum_of_subset_of_nonneg
            (fun x hx => by simp only [Finset.mem_Ico] at hx ⊢; omega)
            (fun i _ _ => norm_nonneg _)
        · refine Finset.sum_nbij' (i := fun h2 => h2 - h1) (j := fun k => k + h1) ?_ ?_ ?_ ?_ ?_
          · intro a ha; simp only [Finset.mem_Ico] at ha ⊢; omega
          · intro a ha; simp only [Finset.mem_Ico] at ha ⊢; omega
          · intro a ha; simp only [Finset.mem_Ico] at ha; omega
          · intro a ha; simp only [Finset.mem_Ico] at ha; omega
          · intro a _; rfl
    calc ∑ h1 ∈ Finset.range H, ∑ h2 ∈ Finset.range H,
          (if h1 = h2 then (N:ℝ) else ‖corr u N (max h1 h2 - min h1 h2)‖)
        ≤ ∑ _h1 ∈ Finset.range H, ((N:ℝ) + 2 * ∑ k ∈ Finset.Ico 1 H, ‖corr u N k‖) :=
          Finset.sum_le_sum inner
      _ = (H:ℝ) * N + 2 * ((H:ℝ) * ∑ k ∈ Finset.Ico 1 H, ‖corr u N k‖) := by
          rw [Finset.sum_const, Finset.card_range]; push_cast; ring
  have hLHS : (H:ℝ)^2 * ‖∑ n ∈ Finset.range N, u n‖^2
      = ‖∑ m ∈ J, ∑ h ∈ Finset.range H, v (m + h)‖^2 := by
    rw [← step1, norm_mul]
    simp [mul_pow]
  rw [hLHS]
  calc ‖∑ m ∈ J, ∑ h ∈ Finset.range H, v (m + h)‖^2
      ≤ (J.card : ℝ) * ∑ m ∈ J, ‖∑ h ∈ Finset.range H, v (m + h)‖^2 := cs
    _ ≤ ((N:ℝ) + H) * ((H:ℝ) * N + 2 * ((H:ℝ) * ∑ k ∈ Finset.Ico 1 H, ‖corr u N k‖)) := by
        rw [hcard]
        exact mul_le_mul_of_nonneg_left (le_trans swapR hdouble) (by positivity)

end TuringTask
