import TuringTask.Hyperbola

namespace TuringTask

open Finset Filter Topology Real

/-- The fibre of `hypN N` over `n` is `n.divisorsAntidiagonal`, for `1 ≤ n ≤ N`. -/
lemma hypN_fiber (N n : ℕ) (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    {p ∈ hypN N | p.1 * p.2 = n} = n.divisorsAntidiagonal := by
  ext p
  simp only [mem_filter, mem_hypN, Nat.mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨-, h⟩; exact ⟨h, by omega⟩
  · rintro ⟨h, -⟩
    refine ⟨⟨?_, ?_, by omega⟩, h⟩
    · rcases Nat.eq_zero_or_pos p.1 with h0 | h0
      · rw [h0, zero_mul] at h; omega
      · exact h0
    · rcases Nat.eq_zero_or_pos p.2 with h0 | h0
      · rw [h0, mul_zero] at h; omega
      · exact h0

lemma card_divisorsAntidiagonal (n : ℕ) (_hn : n ≠ 0) :
    n.divisorsAntidiagonal.card = n.divisors.card := by
  rw [← Nat.map_div_right_divisors, Finset.card_map]

/-- Summing an arbitrary function of the product over `hypN N` groups into divisor counts. -/
lemma sum_hypN_fiberwise {M : Type*} [AddCommMonoid M] (N : ℕ) (g : ℕ → M) :
    ∑ p ∈ hypN N, g (p.1 * p.2) = ∑ n ∈ Icc 1 N, (n.divisors.card) • g n := by
  have hmaps : ∀ p ∈ hypN N, p.1 * p.2 ∈ Icc 1 N := by
    intro p hp
    rw [mem_hypN] at hp
    rw [mem_Icc]
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), hp.2.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun p => g (p.1 * p.2))]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [mem_Icc] at hn
  have : ∀ p ∈ {p ∈ hypN N | p.1 * p.2 = n}, g (p.1 * p.2) = g n := by
    intro p hp; rw [mem_filter] at hp; rw [hp.2]
  rw [Finset.sum_congr rfl this, Finset.sum_const,
    hypN_fiber N n hn.1 hn.2, card_divisorsAntidiagonal n (by omega)]


/-! ### Specialisations -/

/-- `D(N) = ∑_{a ≤ N} ⌊N/a⌋`. -/
lemma sum_card_divisors_eq (N : ℕ) :
    ∑ n ∈ Icc 1 N, n.divisors.card = ∑ a ∈ Icc 1 N, N / a := by
  have h := sum_hypN_fiberwise N (fun _ => (1 : ℕ))
  simp only [smul_eq_mul, mul_one] at h
  rw [← h, hypN_eq_hypL, sum_hypL]
  simp

/-- Dirichlet hyperbola identity: `D(N) + K² = 2 ∑_{a ≤ K} ⌊N/a⌋` with `K = ⌊√N⌋`. -/
lemma dirichlet_hyperbola (N : ℕ) :
    (∑ n ∈ Icc 1 N, n.divisors.card) + Nat.sqrt N * Nat.sqrt N
      = 2 * ∑ a ∈ Icc 1 (Nat.sqrt N), N / a := by
  set K := Nat.sqrt N with hK
  have h1 : K * K ≤ N := Nat.sqrt_le N
  have h2 : N < (K + 1) * (K + 1) := Nat.lt_succ_sqrt N
  have hcard := Finset.card_union_add_card_inter (hypL N K) (hypR N K)
  rw [← hypN_union N K h2, hypLR_inter N K h1] at hcard
  have hL : (hypL N K).card = ∑ a ∈ Icc 1 K, N / a := by
    rw [Finset.card_eq_sum_ones, sum_hypL]
    simp
  have hR : (hypR N K).card = ∑ b ∈ Icc 1 K, N / b := by
    rw [Finset.card_eq_sum_ones, sum_hypR]
    simp
  have hN : (hypN N).card = ∑ n ∈ Icc 1 N, n.divisors.card := by
    have h := sum_hypN_fiberwise N (fun _ => (1 : ℕ))
    simp only [smul_eq_mul, mul_one] at h
    rw [Finset.card_eq_sum_ones, h]
  rw [hL, hR, hN, Finset.card_product, Nat.card_Icc] at hcard
  simp only [Nat.add_sub_cancel] at hcard
  omega


end TuringTask
