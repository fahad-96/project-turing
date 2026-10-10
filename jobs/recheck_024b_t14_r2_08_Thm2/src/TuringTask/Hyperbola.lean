import Mathlib

namespace TuringTask

open Finset Filter Topology Real

/-! ### Lattice points under a hyperbola -/

/-- All lattice points `(a,b)` with `a,b ≥ 1` and `a*b ≤ N`. -/
def hypN (N : ℕ) : Finset (ℕ × ℕ) := (Icc 1 N ×ˢ Icc 1 N).filter (fun p => p.1 * p.2 ≤ N)

/-- Those with `a ≤ K`. -/
def hypL (N K : ℕ) : Finset (ℕ × ℕ) := (Icc 1 K ×ˢ Icc 1 N).filter (fun p => p.1 * p.2 ≤ N)

/-- Those with `b ≤ K`. -/
def hypR (N K : ℕ) : Finset (ℕ × ℕ) := (Icc 1 N ×ˢ Icc 1 K).filter (fun p => p.1 * p.2 ≤ N)

lemma hypN_eq_hypL (N : ℕ) : hypN N = hypL N N := rfl

lemma mem_hypN {N : ℕ} {p : ℕ × ℕ} : p ∈ hypN N ↔ 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 * p.2 ≤ N := by
  simp only [hypN, mem_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, -⟩, ⟨h3, -⟩⟩, h5⟩; exact ⟨h1, h3, h5⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨⟨h1, le_trans (by nlinarith) h3⟩, ⟨h2, le_trans (by nlinarith) h3⟩⟩, h3⟩

lemma mem_hypL {N K : ℕ} {p : ℕ × ℕ} :
    p ∈ hypL N K ↔ 1 ≤ p.1 ∧ p.1 ≤ K ∧ 1 ≤ p.2 ∧ p.1 * p.2 ≤ N := by
  simp only [hypL, mem_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, ⟨h3, -⟩⟩, h5⟩; exact ⟨h1, h2, h3, h5⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, ⟨h3, le_trans (by nlinarith) h4⟩⟩, h4⟩

lemma mem_hypR {N K : ℕ} {p : ℕ × ℕ} :
    p ∈ hypR N K ↔ 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.2 ≤ K ∧ p.1 * p.2 ≤ N := by
  simp only [hypR, mem_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, -⟩, ⟨h3, h4⟩⟩, h5⟩; exact ⟨h1, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, le_trans (by nlinarith) h4⟩, ⟨h2, h3⟩⟩, h4⟩

lemma hypN_union (N K : ℕ) (hK : N < (K + 1) * (K + 1)) : hypN N = hypL N K ∪ hypR N K := by
  ext p
  rw [mem_union, mem_hypN, mem_hypL, mem_hypR]
  constructor
  · rintro ⟨h1, h2, h3⟩
    by_cases hc : p.1 ≤ K
    · exact Or.inl ⟨h1, hc, h2, h3⟩
    · refine Or.inr ⟨h1, h2, ?_, h3⟩
      by_contra hc2
      simp only [Nat.not_le] at hc hc2
      exact absurd h3 (Nat.not_le.mpr (lt_of_lt_of_le hK (Nat.mul_le_mul hc hc2)))
  · rintro (⟨h1, -, h3, h4⟩ | ⟨h1, h2, -, h4⟩)
    · exact ⟨h1, h3, h4⟩
    · exact ⟨h1, h2, h4⟩

lemma hypLR_inter (N K : ℕ) (hK : K * K ≤ N) : hypL N K ∩ hypR N K = Icc 1 K ×ˢ Icc 1 K := by
  ext p
  rw [mem_inter, mem_hypL, mem_hypR, mem_product, mem_Icc, mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2, h3, -⟩, ⟨-, -, h6, -⟩⟩; exact ⟨⟨h1, h2⟩, ⟨h3, h6⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    have hle : p.1 * p.2 ≤ N := le_trans (Nat.mul_le_mul h2 h4) hK
    exact ⟨⟨h1, h2, h3, hle⟩, ⟨h1, h3, h4, hle⟩⟩

/-- `hypL` fibres over the first coordinate. -/
lemma sum_hypL {M : Type*} [AddCommMonoid M] (N K : ℕ) (f : ℕ × ℕ → M) :
    ∑ p ∈ hypL N K, f p = ∑ a ∈ Icc 1 K, ∑ b ∈ Icc 1 (N / a), f (a, b) := by
  rw [hypL, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [mem_Icc] at ha
  rw [← Finset.sum_filter]
  congr 1
  ext b
  simp only [mem_filter, mem_Icc]
  rw [Nat.le_div_iff_mul_le ha.1, mul_comm b a]
  refine ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, ?_⟩, h.2⟩⟩
  calc b = 1 * b := by ring
    _ ≤ a * b := Nat.mul_le_mul_right _ ha.1
    _ ≤ N := h.2

lemma sum_hypR {M : Type*} [AddCommMonoid M] (N K : ℕ) (f : ℕ × ℕ → M) :
    ∑ p ∈ hypR N K, f p = ∑ b ∈ Icc 1 K, ∑ a ∈ Icc 1 (N / b), f (a, b) := by
  have key := sum_hypL N K (fun p => f p.swap)
  simp only [Prod.swap_prod_mk] at key
  rw [← key]
  refine (Finset.sum_nbij' (fun p => p.swap) (fun p => p.swap) ?_ ?_ ?_ ?_ ?_).symm
  · intro a ha; rw [mem_hypL] at ha; rw [mem_hypR]
    exact ⟨ha.2.2.1, ha.1, ha.2.1, by rw [Prod.fst_swap, Prod.snd_swap, mul_comm]; exact ha.2.2.2⟩
  · intro a ha; rw [mem_hypR] at ha; rw [mem_hypL]
    exact ⟨ha.2.1, ha.2.2.1, ha.1, by rw [Prod.fst_swap, Prod.snd_swap, mul_comm]; exact ha.2.2.2⟩
  · intro a _; simp
  · intro a _; simp
  · intro a _; simp

end TuringTask
