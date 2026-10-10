import Mathlib

namespace TuringTask

open Finset

-- ============================================================================
-- Section 1: Divisor pairs and Dirichlet hyperbola decomposition
-- ============================================================================

def divPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 N) ×ˢ (Icc 1 N)).filter (fun p => p.1 * p.2 ≤ N)

lemma mem_divPairs {N a b : ℕ} :
    (a, b) ∈ divPairs N ↔ 1 ≤ a ∧ a ≤ N ∧ 1 ≤ b ∧ b ≤ N ∧ a * b ≤ N := by
  simp [divPairs, mem_filter, mem_product, mem_Icc, and_assoc]

lemma mem_divPairs_swap {N a b : ℕ} :
    (a, b) ∈ divPairs N ↔ (b, a) ∈ divPairs N := by
  rw [mem_divPairs, mem_divPairs, mul_comm]
  tauto

lemma card_divPairs_filter_snd_eq (N K : ℕ) :
    ((divPairs N).filter (fun p => p.2 ≤ K)).card =
    ((divPairs N).filter (fun p => p.1 ≤ K)).card := by
  let e : ℕ × ℕ ≃ ℕ × ℕ := Equiv.prodComm ℕ ℕ
  rw [← card_map e.toEmbedding]
  congr 1
  ext ⟨a, b⟩
  rw [mem_filter, mem_map_equiv, mem_filter]
  dsimp [e]
  rw [mem_divPairs_swap]

lemma card_divPairs_fiber_eq_card_divisors (N : ℕ) {n : ℕ} (hn : n ∈ Icc 1 N) :
    ((divPairs N).filter (fun p => p.1 * p.2 = n)).card = n.divisors.card := by
  rw [mem_Icc] at hn
  apply Finset.card_bij (fun p _ => p.1)
  · intro ⟨a, b⟩ hp
    rw [mem_filter] at hp
    rcases hp with ⟨hp, hmul⟩
    rw [Nat.mem_divisors]
    exact ⟨⟨b, hmul.symm⟩, by omega⟩
  · intro ⟨a1, b1⟩ h1 ⟨a2, b2⟩ h2 heq
    rw [mem_filter] at h1 h2
    dsimp at heq
    subst heq
    have h1m : (divPairs N) ⊆ ((Icc 1 N) ×ˢ (Icc 1 N)) := filter_subset _ _
    have h1a : (a1, b1) ∈ ((Icc 1 N) ×ˢ (Icc 1 N)) := h1m h1.1
    rw [mem_product, mem_Icc] at h1a
    have ha1 : a1 ≠ 0 := by omega
    have : a1 * b1 = a1 * b2 := by rw [h1.2, h2.2]
    exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left (by omega) this)
  · intro d hd
    rw [Nat.mem_divisors] at hd
    rcases hd with ⟨⟨k, hk⟩, hn0⟩
    have hd_pos : 1 ≤ d := by
      rcases d with _ | d
      · exfalso; rw [MulZeroClass.zero_mul] at hk; omega
      · omega
    have hk_pos : 1 ≤ k := by
      rcases k with _ | k
      · exfalso; rw [MulZeroClass.mul_zero] at hk; omega
      · omega
    have hdN : d ≤ N := by
      have : d ≤ n := by
        rw [hk]
        have : d * 1 ≤ d * k := Nat.mul_le_mul_left d hk_pos
        simpa using this
      omega
    have hkN : k ≤ N := by
      have : k ≤ n := by
        rw [hk]
        have : 1 * k ≤ d * k := Nat.mul_le_mul_right k hd_pos
        simpa using this
      omega
    refine ⟨(d, k), ?_, rfl⟩
    rw [mem_filter]
    refine ⟨?_, hk.symm⟩
    rw [divPairs, mem_filter, mem_product, mem_Icc, mem_Icc]
    refine ⟨⟨⟨hd_pos, hdN⟩, ⟨hk_pos, hkN⟩⟩, ?_⟩
    dsimp
    rw [hk.symm]
    exact hn.2

lemma card_divPairs_eq_sum_divisors (N : ℕ) :
    (divPairs N).card = ∑ n ∈ Icc 1 N, n.divisors.card := by
  have H : Set.MapsTo (fun p : ℕ × ℕ => p.1 * p.2) ↑(divPairs N) ↑(Icc 1 N) := by
    intro ⟨a, b⟩ hp
    simp only [divPairs, mem_coe, mem_filter, mem_product, mem_Icc] at hp
    rcases hp with ⟨⟨⟨h1a, _⟩, ⟨h1b, _⟩⟩, hab⟩
    exact mem_Icc.mpr ⟨by nlinarith, hab⟩
  rw [Finset.card_eq_sum_card_fiberwise H]
  apply Finset.sum_congr rfl
  intro n hn
  exact card_divPairs_fiber_eq_card_divisors N hn

lemma inter_divPairs_filter (N K : ℕ) (hK2 : K ^ 2 ≤ N) (hK_le_N : K ≤ N) :
    ((divPairs N).filter (fun p => p.1 ≤ K)) ∩ ((divPairs N).filter (fun p => p.2 ≤ K)) =
    (Icc 1 K) ×ˢ (Icc 1 K) := by
  ext ⟨a, b⟩
  simp only [mem_inter, mem_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨⟨h, haK⟩, ⟨_, hbK⟩⟩
    rw [mem_divPairs] at h
    exact ⟨⟨h.1, haK⟩, ⟨h.2.2.1, hbK⟩⟩
  · rintro ⟨⟨h1a, haK⟩, ⟨h1b, hbK⟩⟩
    have haN : a ≤ N := haK.trans hK_le_N
    have hbN : b ≤ N := hbK.trans hK_le_N
    have hab : a * b ≤ N := by
      have : a * b ≤ K * K := Nat.mul_le_mul haK hbK
      have hKK : K * K = K ^ 2 := (sq K).symm
      exact this.trans (hKK.symm ▸ hK2)
    have hp : (a, b) ∈ divPairs N := by
      rw [mem_divPairs]
      exact ⟨h1a, haN, h1b, hbN, hab⟩
    exact ⟨⟨hp, haK⟩, ⟨hp, hbK⟩⟩

lemma card_divPairs_filter_fst (N K : ℕ) (hK2 : K ^ 2 ≤ N) (hK_le_N : K ≤ N) :
    ((divPairs N).filter (fun p => p.1 ≤ K)).card = ∑ a ∈ Icc 1 K, (N / a) := by
  let A := (divPairs N).filter (fun p => p.1 ≤ K)
  have H : Set.MapsTo (fun p : ℕ × ℕ => p.1) (A : Set (ℕ × ℕ)) (Icc 1 K : Set ℕ) := by
    intro ⟨a, b⟩ hp
    rw [Finset.mem_coe, mem_filter, mem_divPairs] at hp
    rw [Finset.mem_coe, mem_Icc]
    exact ⟨hp.1.1, hp.2⟩
  rw [card_eq_sum_card_fiberwise H]
  apply sum_congr rfl
  intro a ha
  rw [mem_Icc] at ha
  have ha_pos : 0 < a := by omega
  have hfiber : {p ∈ A | p.1 = a} = (Icc 1 (N / a)).map ⟨fun b => (a, b), fun _ _ h => (Prod.ext_iff.mp h).2⟩ := by
    ext ⟨x, y⟩
    rw [mem_filter, mem_filter, mem_map]
    constructor
    · rintro ⟨⟨hdp, hxK⟩, hxa⟩
      dsimp at hxa
      subst hxa
      rw [mem_divPairs] at hdp
      refine ⟨y, ?_, rfl⟩
      rw [mem_Icc]
      refine ⟨hdp.2.2.1, ?_⟩
      rw [Nat.le_div_iff_mul_le ha_pos, mul_comm]
      exact hdp.2.2.2.2
    · rintro ⟨y, hy, heq⟩
      injection heq with hx hy_eq
      subst hx hy_eq
      rw [mem_Icc] at hy
      have hyN : y ≤ N := by
        have : N / a ≤ N := Nat.div_le_self N a
        omega
      have hmul : a * y ≤ N := by
        have := (Nat.le_div_iff_mul_le ha_pos).mp hy.2
        rwa [mul_comm] at this
      have hdp : (a, y) ∈ divPairs N := by
        rw [mem_divPairs]
        exact ⟨ha.1, ha.2.trans hK_le_N, hy.1, hyN, hmul⟩
      exact ⟨⟨hdp, ha.2⟩, rfl⟩
  rw [hfiber, card_map, Nat.card_Icc]
  have hNa_pos : 1 ≤ N / a := by
    rw [Nat.le_div_iff_mul_le ha_pos]
    have : 1 * a ≤ K * K := by
      rw [one_mul]
      nlinarith
    have hKK : K * K = K ^ 2 := (sq K).symm
    exact this.trans (hKK.symm ▸ hK2)
  omega

lemma sum_card_divisors_eq_hyperbola (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) =
    2 * ∑ a ∈ Icc 1 (Nat.sqrt N), ((N / a : ℕ) : ℝ) - ((Nat.sqrt N : ℝ) ^ 2) := by
  let K := Nat.sqrt N
  have hK_pos : 1 ≤ K := Nat.le_sqrt.mpr (by simpa using hN)
  have hK2 : K ^ 2 ≤ N := Nat.sqrt_le' N
  have hK_le_N : K ≤ N := by
    have : K ≤ K ^ 2 := by
      rcases K with _ | K
      · omega
      · nlinarith
    exact this.trans hK2
  let A := (divPairs N).filter (fun p => p.1 ≤ K)
  let B := (divPairs N).filter (fun p => p.2 ≤ K)
  have h_union : A ∪ B = divPairs N := by
    ext ⟨a, b⟩
    rw [mem_union, mem_filter, mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      by_cases ha : a ≤ K
      · exact Or.inl ⟨h, ha⟩
      · right
        refine ⟨h, ?_⟩
        by_contra hb
        have ha_ge : K + 1 ≤ a := by omega
        have hb_ge : K + 1 ≤ b := by omega
        have hab : (K + 1) * (K + 1) ≤ a * b := Nat.mul_le_mul ha_ge hb_ge
        have hlt : N < (K + 1) * (K + 1) := Nat.lt_succ_sqrt N
        rw [mem_divPairs] at h
        omega
  have h_card_inter : (A ∩ B).card = K ^ 2 := by
    rw [inter_divPairs_filter N K hK2 hK_le_N, card_product, Nat.card_Icc]
    have : K + 1 - 1 = K := by omega
    rw [this, sq]
  have h_card_B : B.card = A.card := card_divPairs_filter_snd_eq N K
  have h_card_A : A.card = ∑ a ∈ Icc 1 K, (N / a) := card_divPairs_filter_fst N K hK2 hK_le_N
  have h_inc_exc := card_union_add_card_inter A B
  rw [h_union, h_card_B, h_card_inter, h_card_A] at h_inc_exc
  have h_nat : (divPairs N).card + K ^ 2 = 2 * ∑ a ∈ Icc 1 K, (N / a) := by linarith
  have h_real : ((divPairs N).card : ℝ) + (K : ℝ) ^ 2 = 2 * ∑ a ∈ Icc 1 K, ((N / a : ℕ) : ℝ) := by
    have h1 : (((divPairs N).card + K ^ 2 : ℕ) : ℝ) = ((2 * ∑ a ∈ Icc 1 K, (N / a) : ℕ) : ℝ) := by
      exact_mod_cast h_nat
    push_cast at h1
    exact h1
  have h_sum : ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) = ((divPairs N).card : ℝ) := by
    rw [card_divPairs_eq_sum_divisors]
    push_cast
    rfl
  linarith

lemma sum_div_card_divisors_eq_pairs (N : ℕ) :
    ∑ n ∈ Icc 1 N, ((n.divisors.card : ℝ) / (n : ℝ)) =
    ∑ p ∈ divPairs N, (1 / ((p.1 : ℝ) * (p.2 : ℝ))) := by
  have H : Set.MapsTo (fun p : ℕ × ℕ => p.1 * p.2) ↑(divPairs N) ↑(Icc 1 N) := by
    intro ⟨a, b⟩ hp
    simp only [divPairs, mem_coe, mem_filter, mem_product, mem_Icc] at hp
    rcases hp with ⟨⟨⟨h1a, _⟩, ⟨h1b, _⟩⟩, hab⟩
    exact mem_Icc.mpr ⟨by nlinarith, hab⟩
  rw [← Finset.sum_fiberwise_of_maps_to H]
  apply sum_congr rfl
  intro n hn
  have hn_pos : (n : ℝ) ≠ 0 := by
    have : 1 ≤ n := (mem_Icc.mp hn).1
    positivity
  have h_term : ∀ p ∈ (divPairs N).filter (fun p => p.1 * p.2 = n),
      1 / ((p.1 : ℝ) * (p.2 : ℝ)) = 1 / (n : ℝ) := by
    intro ⟨a, b⟩ hp
    rw [mem_filter] at hp
    have : (a : ℝ) * (b : ℝ) = (n : ℝ) := by exact_mod_cast hp.2
    rw [this]
  rw [sum_congr rfl h_term, sum_const, nsmul_eq_mul]
  have h_fiber := card_divPairs_fiber_eq_card_divisors N hn
  rw [h_fiber]
  ring

lemma sum_pairs_eq_sum_harmonic (N : ℕ) :
    ∑ p ∈ divPairs N, (1 / ((p.1 : ℝ) * (p.2 : ℝ))) =
    ∑ a ∈ Icc 1 N, (1 / (a : ℝ)) * (harmonic (N / a) : ℝ) := by
  have H : Set.MapsTo (fun p : ℕ × ℕ => p.1) ↑(divPairs N) ↑(Icc 1 N) := by
    intro ⟨a, b⟩ hp
    rw [Finset.mem_coe, mem_divPairs] at hp
    exact mem_Icc.mpr ⟨hp.1, hp.2.1⟩
  rw [← Finset.sum_fiberwise_of_maps_to H]
  apply sum_congr rfl
  intro a ha
  rw [mem_Icc] at ha
  have ha_pos : 0 < a := by omega
  have hfiber : {p ∈ divPairs N | p.1 = a} = (Icc 1 (N / a)).map ⟨fun b => (a, b), fun b1 b2 h => by cases h; rfl⟩ := by
    ext ⟨x, y⟩
    rw [mem_filter, mem_map]
    constructor
    · rintro ⟨hdp, hxa⟩
      dsimp at hxa
      subst hxa
      rw [mem_divPairs] at hdp
      refine ⟨y, ?_, rfl⟩
      rw [mem_Icc]
      refine ⟨hdp.2.2.1, ?_⟩
      rw [Nat.le_div_iff_mul_le ha_pos, mul_comm]
      exact hdp.2.2.2.2
    · rintro ⟨y, hy, heq⟩
      injection heq with hx hy_eq
      subst hx hy_eq
      rw [mem_Icc] at hy
      have hyN : y ≤ N := by
        have : N / a ≤ N := Nat.div_le_self N a
        omega
      have hmul : a * y ≤ N := by
        have := (Nat.le_div_iff_mul_le ha_pos).mp hy.2
        rwa [mul_comm] at this
      have hdp : (a, y) ∈ divPairs N := by
        rw [mem_divPairs]
        exact ⟨ha.1, ha.2, hy.1, hyN, hmul⟩
      exact ⟨hdp, rfl⟩
  rw [hfiber, sum_map]
  have h_harm : (harmonic (N / a) : ℝ) = ∑ b ∈ Icc 1 (N / a), (1 / (b : ℝ)) := by
    rw [harmonic_eq_sum_Icc]; push_cast; simp_rw [one_div]
  rw [h_harm, mul_sum]
  apply sum_congr rfl
  intro b hb
  show 1 / ((a : ℝ) * (b : ℝ)) = 1 / (a : ℝ) * (1 / (b : ℝ))
  ring

lemma sum_div_card_divisors_eq_harmonic (N : ℕ) :
    ∑ n ∈ Icc 1 N, ((n.divisors.card : ℝ) / (n : ℝ)) =
    ∑ a ∈ Icc 1 N, (1 / (a : ℝ)) * (harmonic (N / a) : ℝ) := by
  rw [sum_div_card_divisors_eq_pairs, sum_pairs_eq_sum_harmonic]

-- ============================================================================
-- Section 2: Harmonic and Logarithmic Estimates
-- ============================================================================

lemma sum_div_eq_mul_harmonic_sub (N K : ℕ) :
    ∑ a ∈ Icc 1 K, ((N / a : ℕ) : ℝ) =
    (N : ℝ) * (harmonic K : ℝ) - ∑ a ∈ Icc 1 K, (((N % a : ℕ) : ℝ) / (a : ℝ)) := by
  have h_term : ∀ a ∈ Icc 1 K, ((N / a : ℕ) : ℝ) = (N : ℝ) * (a : ℝ)⁻¹ - (((N % a : ℕ) : ℝ) / (a : ℝ)) := by
    intro a ha
    rw [mem_Icc] at ha
    have ha_pos : (a : ℝ) ≠ 0 := by
      have : 0 < a := by omega
      positivity
    have h_div : (N : ℝ) = (a : ℝ) * ((N / a : ℕ) : ℝ) + ((N % a : ℕ) : ℝ) := by
      have := Nat.div_add_mod N a
      have h2 : (N : ℝ) = ((a * (N / a) + N % a : ℕ) : ℝ) := by exact_mod_cast this.symm
      push_cast at h2
      exact h2
    have : ((N / a : ℕ) : ℝ) = (N : ℝ) / (a : ℝ) - ((N % a : ℕ) : ℝ) / (a : ℝ) := by
      calc
        ((N / a : ℕ) : ℝ) = ((a : ℝ) * ((N / a : ℕ) : ℝ)) / (a : ℝ) := by rw [mul_div_cancel_left₀ _ ha_pos]
        _ = ((N : ℝ) - ((N % a : ℕ) : ℝ)) / (a : ℝ) := by
          congr 1; linarith
        _ = (N : ℝ) / (a : ℝ) - ((N % a : ℕ) : ℝ) / (a : ℝ) := by rw [sub_div]
    rw [this, div_eq_mul_inv]
  rw [sum_congr rfl h_term, sum_sub_distrib, ← mul_sum]
  congr 1
  rw [harmonic_eq_sum_Icc]
  push_cast
  rfl

lemma sum_mod_div_nonneg (N K : ℕ) :
    0 ≤ ∑ a ∈ Icc 1 K, (((N % a : ℕ) : ℝ) / (a : ℝ)) := by
  apply sum_nonneg
  intro a ha
  rw [mem_Icc] at ha
  have : 0 < a := by omega
  positivity

lemma sum_mod_div_le (N K : ℕ) :
    ∑ a ∈ Icc 1 K, (((N % a : ℕ) : ℝ) / (a : ℝ)) ≤ (K : ℝ) := by
  calc
    ∑ a ∈ Icc 1 K, (((N % a : ℕ) : ℝ) / (a : ℝ)) ≤ ∑ a ∈ Icc 1 K, (1 : ℝ) := by
      apply sum_le_sum
      intro a ha
      rw [mem_Icc] at ha
      have ha_pos : 0 < (a : ℝ) := by
        have : 0 < a := by omega
        positivity
      rw [div_le_one₀ ha_pos]
      have : N % a < a := Nat.mod_lt N (by omega)
      exact_mod_cast (Nat.le_of_lt this)
    _ ≤ (K : ℝ) := by
      rw [sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc]
      have : K + 1 - 1 ≤ K := by omega
      exact_mod_cast this

lemma sum_mod_div_one (N : ℕ) :
    ∑ a ∈ Icc 1 1, (((N % a : ℕ) : ℝ) / (a : ℝ)) = 0 := by
  have : Icc 1 1 = {1} := rfl
  rw [this, sum_singleton]
  have : N % 1 = 0 := Nat.mod_one N
  simp [this]

lemma harmonic_sub_log_sub_gamma_nonneg (K : ℕ) (hK : 1 ≤ K) :
    0 ≤ (harmonic K : ℝ) - Real.log K - Real.eulerMascheroniConstant := by
  have hK_ne : K ≠ 0 := by omega
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' K
  rw [Real.eulerMascheroniSeq', if_neg hK_ne] at h
  linarith

lemma harmonic_sub_log_sub_gamma_le (K : ℕ) (hK : 1 ≤ K) :
    (harmonic K : ℝ) - Real.log K - Real.eulerMascheroniConstant ≤ 1 / (K : ℝ) := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant K
  rw [Real.eulerMascheroniSeq.eq_1] at h
  have hK_pos : 0 < (K : ℝ) := by positivity
  have h_log : Real.log ((K : ℝ) + 1) - Real.log K ≤ 1 / (K : ℝ) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have h_eq : ((K : ℝ) + 1) / (K : ℝ) = 1 + 1 / (K : ℝ) := by
      rw [add_div, div_self (ne_of_gt hK_pos)]
    rw [h_eq]
    have := Real.log_le_sub_one_of_pos (x := 1 + 1 / (K : ℝ)) (by positivity)
    linarith
  linarith

lemma log_sq_div_bound (N K : ℕ) (hK : 1 ≤ K) (hK2 : K ^ 2 ≤ N) :
    (N : ℝ) * (Real.log ((K : ℝ) ^ 2) - Real.log N) + ((N : ℝ) - (K : ℝ) ^ 2) ≤ 0 := by
  have hN_pos : 0 < (N : ℝ) := by
    have : 1 ≤ N := by nlinarith
    positivity
  have hK2_pos : 0 < (K : ℝ) ^ 2 := by positivity
  have h_div : Real.log ((K : ℝ) ^ 2) - Real.log N = Real.log ((K : ℝ) ^ 2 / (N : ℝ)) := by
    rw [Real.log_div (ne_of_gt hK2_pos) (ne_of_gt hN_pos)]
  rw [h_div]
  have h_le := Real.log_le_sub_one_of_pos (x := (K : ℝ) ^ 2 / (N : ℝ)) (by positivity)
  have h_mul : (N : ℝ) * ((K : ℝ) ^ 2 / (N : ℝ) - 1) = (K : ℝ) ^ 2 - (N : ℝ) := by
    rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hN_pos), mul_one]
  nlinarith

lemma log_sq_div_lower_bound (N K : ℕ) (hK : 1 ≤ K) (hK2 : K ^ 2 ≤ N) (hlt : N < (K + 1) ^ 2) :
    -4 ≤ (N : ℝ) * (Real.log ((K : ℝ) ^ 2) - Real.log N) + ((N : ℝ) - (K : ℝ) ^ 2) := by
  have hN_pos : 0 < (N : ℝ) := by
    have : 1 ≤ N := by nlinarith
    positivity
  have hK_pos : 0 < (K : ℝ) := by positivity
  have hK2_pos : 0 < (K : ℝ) ^ 2 := by positivity
  have h_div : Real.log ((K : ℝ) ^ 2) - Real.log N = - Real.log ((N : ℝ) / (K : ℝ) ^ 2) := by
    rw [Real.log_div (ne_of_gt hN_pos) (ne_of_gt hK2_pos)]
    ring
  rw [h_div]
  have h_le := Real.log_le_sub_one_of_pos (x := (N : ℝ) / (K : ℝ) ^ 2) (by positivity)
  have hN_le : (N : ℝ) ≤ (K : ℝ) ^ 2 + 2 * (K : ℝ) := by
    have h1 : N ≤ K ^ 2 + 2 * K := by
      have : (K + 1) ^ 2 = K ^ 2 + 2 * K + 1 := by ring
      omega
    have h2 : (N : ℝ) ≤ ((K ^ 2 + 2 * K : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact h2
  have hN_ge : (K : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast hK2
  set R := (N : ℝ) - (K : ℝ) ^ 2 with hR_def
  have hR_nonneg : 0 ≤ R := by linarith
  have hR_le : R ≤ 2 * (K : ℝ) := by linarith
  have h_sub : (N : ℝ) / (K : ℝ) ^ 2 - 1 = R / (K : ℝ) ^ 2 := by
    dsimp [R]
    rw [sub_div, div_self (ne_of_gt hK2_pos)]
  have h_alg : (N : ℝ) * (R / (K : ℝ) ^ 2) = R + R ^ 2 / (K : ℝ) ^ 2 := by
    have : (N : ℝ) = (K : ℝ) ^ 2 + R := by linarith
    calc
      (N : ℝ) * (R / (K : ℝ) ^ 2) = ((K : ℝ) ^ 2 + R) * (R / (K : ℝ) ^ 2) := by rw [this]
      _ = (K : ℝ) ^ 2 * (R / (K : ℝ) ^ 2) + R * (R / (K : ℝ) ^ 2) := by ring
      _ = R + R * (R / (K : ℝ) ^ 2) := by rw [mul_div_cancel₀ _ (ne_of_gt hK2_pos)]
      _ = R + R ^ 2 / (K : ℝ) ^ 2 := by ring
  have h_sq : R ^ 2 / (K : ℝ) ^ 2 ≤ 4 := by
    rw [div_le_iff₀ hK2_pos]
    have : R ^ 2 ≤ (2 * (K : ℝ)) ^ 2 := by
      nlinarith
    have : (2 * (K : ℝ)) ^ 2 = 4 * (K : ℝ) ^ 2 := by ring
    linarith
  have : (N : ℝ) * Real.log ((N : ℝ) / (K : ℝ) ^ 2) ≤ R + 4 := by
    calc
      (N : ℝ) * Real.log ((N : ℝ) / (K : ℝ) ^ 2) ≤ (N : ℝ) * ((N : ℝ) / (K : ℝ) ^ 2 - 1) := by nlinarith
      _ = (N : ℝ) * (R / (K : ℝ) ^ 2) := by rw [h_sub]
      _ = R + R ^ 2 / (K : ℝ) ^ 2 := h_alg
      _ ≤ R + 4 := by linarith
  linarith

lemma B_of_one (N : ℕ) :
    2 * (N : ℝ) * ((harmonic 1 : ℝ) - Real.log 1 - Real.eulerMascheroniConstant) ≤ (N : ℝ) := by
  have h_harm : (harmonic 1 : ℝ) = 1 := by
    rw [harmonic_succ, harmonic_zero]
    push_cast
    ring
  rw [h_harm, Real.log_one, sub_zero]
  have h_gam : 1 / 2 < Real.eulerMascheroniConstant := Real.one_half_lt_eulerMascheroniConstant
  have : 1 - Real.eulerMascheroniConstant ≤ 1 / 2 := by linarith
  have : 0 ≤ (N : ℝ) := by positivity
  nlinarith

lemma sqrt_eq_one_of_le_three (N : ℕ) (hN : N = 1 ∨ N = 2 ∨ N = 3) :
    Nat.sqrt N = 1 := by
  rcases hN with rfl | rfl | rfl
  · exact Nat.sqrt_one
  · exact Nat.sqrt_two
  · have h1 : 1 ≤ Nat.sqrt 3 := Nat.le_sqrt.mpr (by omega)
    have h2 : Nat.sqrt 3 < 2 := Nat.sqrt_lt.mpr (by omega)
    omega

-- ============================================================================
-- Theorem 1: sum_card_divisors_sub_le
-- ============================================================================

theorem sum_card_divisors_sub_le (N : Nat) (hN : 1 <= N) :
    abs ((Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real)) - (N : Real) * Real.log N -
        (2 * Real.eulerMascheroniConstant - 1) * N) <= 4 * Real.sqrt N := by
  let K := Nat.sqrt N
  have hK_pos : 1 ≤ K := Nat.le_sqrt.mpr (by simpa using hN)
  have hK_real_pos : 0 < (K : ℝ) := by positivity
  have hK2 : K ^ 2 ≤ N := Nat.sqrt_le' N
  have hlt : N < (K + 1) ^ 2 := by
    rw [sq]
    exact Nat.lt_succ_sqrt N
  have h_hyp := sum_card_divisors_eq_hyperbola N hN
  have h_harm := sum_div_eq_mul_harmonic_sub N K
  set S_mod := ∑ a ∈ Icc 1 K, (((N % a : ℕ) : ℝ) / (a : ℝ)) with hS_mod_def
  have hD_eq : ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) =
      2 * ((N : ℝ) * (harmonic K : ℝ) - S_mod) - (K : ℝ) ^ 2 := by
    rw [h_hyp, h_harm]
  have h_log_sq : Real.log ((K : ℝ) ^ 2) = 2 * Real.log K := by
    rw [sq, Real.log_mul (ne_of_gt hK_real_pos) (ne_of_gt hK_real_pos)]
    ring
  set A := (N : ℝ) * (Real.log ((K : ℝ) ^ 2) - Real.log N) + ((N : ℝ) - (K : ℝ) ^ 2)
  set B := 2 * (N : ℝ) * ((harmonic K : ℝ) - Real.log K - Real.eulerMascheroniConstant)
  have h_decomp : (Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real)) - (N : Real) * Real.log N -
      (2 * Real.eulerMascheroniConstant - 1) * N = A + B - 2 * S_mod := by
    dsimp [A, B]
    rw [hD_eq, h_log_sq]
    ring
  rw [h_decomp]
  have hA_le : A ≤ 0 := log_sq_div_bound N K hK_pos hK2
  have hA_ge : -4 ≤ A := log_sq_div_lower_bound N K hK_pos hK2 hlt
  have hB_ge : 0 ≤ B := by
    have := harmonic_sub_log_sub_gamma_nonneg K hK_pos
    have : 0 ≤ (N : ℝ) := by positivity
    positivity
  have hB_le : B ≤ 2 * (K : ℝ) + 4 := by
    have h_le := harmonic_sub_log_sub_gamma_le K hK_pos
    have h_N_le : (N : ℝ) ≤ (K : ℝ) ^ 2 + 2 * (K : ℝ) := by
      have h1 : N ≤ K ^ 2 + 2 * K := by
        have : (K + 1) ^ 2 = K ^ 2 + 2 * K + 1 := by ring
        omega
      have h2 : (N : ℝ) ≤ ((K ^ 2 + 2 * K : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h2
      exact h2
    calc
      B = 2 * (N : ℝ) * ((harmonic K : ℝ) - Real.log K - Real.eulerMascheroniConstant) := rfl
      _ ≤ 2 * (N : ℝ) * (1 / (K : ℝ)) := by
        have : 0 ≤ 2 * (N : ℝ) := by positivity
        nlinarith
      _ = 2 * (N : ℝ) / (K : ℝ) := by ring
      _ ≤ 2 * ((K : ℝ) ^ 2 + 2 * (K : ℝ)) / (K : ℝ) := by
        rw [div_le_div_iff_of_pos_right hK_real_pos]
        linarith
      _ = 2 * (K : ℝ) + 4 := by
        have : 2 * ((K : ℝ) ^ 2 + 2 * (K : ℝ)) = (2 * (K : ℝ) + 4) * (K : ℝ) := by ring
        rw [this, mul_div_cancel_right₀ _ (ne_of_gt hK_real_pos)]
  have hS_nonneg : 0 ≤ S_mod := sum_mod_div_nonneg N K
  have hS_le : S_mod ≤ (K : ℝ) := sum_mod_div_le N K
  have hK_le_sqrt : (K : ℝ) ≤ Real.sqrt N := by
    have : (K : ℝ) = Real.sqrt ((K : ℝ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    rw [this]
    apply Real.sqrt_le_sqrt
    exact_mod_cast hK2
  have h_sqrt_ge_one : 1 ≤ Real.sqrt N := by
    have : Real.sqrt 1 ≤ Real.sqrt N := Real.sqrt_le_sqrt (by exact_mod_cast hN)
    rwa [Real.sqrt_one] at this
  have h_upper : A + B - 2 * S_mod ≤ 4 * Real.sqrt N := by
    by_cases h4 : 4 ≤ N
    · have h_sqrt2 : 2 ≤ Real.sqrt N := by
        have : Real.sqrt 4 ≤ Real.sqrt N := Real.sqrt_le_sqrt (by exact_mod_cast h4)
        have : Real.sqrt 4 = 2 := by
          have : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
          rw [this, Real.sqrt_sq (by norm_num)]
        linarith
      calc
        A + B - 2 * S_mod ≤ 0 + (2 * (K : ℝ) + 4) - 0 := by linarith
        _ = 2 * (K : ℝ) + 4 := by ring
        _ ≤ 2 * Real.sqrt N + 4 := by linarith
        _ ≤ 2 * Real.sqrt N + 2 * Real.sqrt N := by linarith
        _ = 4 * Real.sqrt N := by ring
    · have hN_cases : N = 1 ∨ N = 2 ∨ N = 3 := by omega
      have hK1 : K = 1 := sqrt_eq_one_of_le_three N hN_cases
      have hB_le_N : B ≤ (N : ℝ) := by
        dsimp [B]
        rw [hK1]
        push_cast
        exact B_of_one N
      have hN_le_4sqrt : (N : ℝ) ≤ 4 * Real.sqrt N := by
        rcases hN_cases with rfl | rfl | rfl
        · norm_num
        · push_cast
          have h2 : 1 ≤ Real.sqrt 2 := by
            have : Real.sqrt 1 ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
            rwa [Real.sqrt_one] at this
          have : 4 ≤ 4 * Real.sqrt 2 := by linarith
          linarith
        · push_cast
          have h2 : 1 ≤ Real.sqrt 3 := by
            have : Real.sqrt 1 ≤ Real.sqrt 3 := Real.sqrt_le_sqrt (by norm_num)
            rwa [Real.sqrt_one] at this
          have : 4 ≤ 4 * Real.sqrt 3 := by linarith
          linarith
      calc
        A + B - 2 * S_mod ≤ 0 + B - 0 := by linarith
        _ ≤ (N : ℝ) := by linarith
        _ ≤ 4 * Real.sqrt N := hN_le_4sqrt
  have h_lower : - (4 * Real.sqrt N) ≤ A + B - 2 * S_mod := by
    by_cases h4 : 4 ≤ N
    · have h_sqrt2 : 2 ≤ Real.sqrt N := by
        have : Real.sqrt 4 ≤ Real.sqrt N := Real.sqrt_le_sqrt (by exact_mod_cast h4)
        have : Real.sqrt 4 = 2 := by
          have : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
          rw [this, Real.sqrt_sq (by norm_num)]
        linarith
      calc
        - (4 * Real.sqrt N) = - (2 * Real.sqrt N + 2 * Real.sqrt N) := by ring
        _ ≤ - (2 * (K : ℝ) + 4) := by linarith
        _ = -4 - 2 * (K : ℝ) := by ring
        _ ≤ A + 0 - 2 * S_mod := by linarith
        _ ≤ A + B - 2 * S_mod := by linarith
    · have hN_cases : N = 1 ∨ N = 2 ∨ N = 3 := by omega
      have hK1 : K = 1 := sqrt_eq_one_of_le_three N hN_cases
      have hS0 : S_mod = 0 := by
        dsimp [S_mod]
        rw [hK1]
        exact sum_mod_div_one N
      calc
        - (4 * Real.sqrt N) ≤ -4 * 1 := by nlinarith
        _ = -4 := by ring
        _ ≤ A := hA_ge
        _ = A + 0 - 2 * 0 := by ring
        _ ≤ A + B - 2 * S_mod := by linarith
  exact abs_le.mpr ⟨h_lower, h_upper⟩

-- ============================================================================
-- Section 3: Helpers and Proof for Theorem 2
-- ============================================================================

lemma div_bounds (N a : ℕ) (ha : 1 ≤ a) :
    let m := N / a
    (m : ℝ) ≤ (N : ℝ) / (a : ℝ) ∧ (N : ℝ) / (a : ℝ) ≤ (m : ℝ) + 1 := by
  intro m
  have ha_pos : 0 < (a : ℝ) := by positivity
  constructor
  · rw [le_div_iff₀ ha_pos]
    have : (m * a : ℕ) ≤ N := by
      have := Nat.div_mul_le_self N a
      dsimp [m]
      omega
    have h1 : (m : ℝ) * (a : ℝ) = ((m * a : ℕ) : ℝ) := by push_cast; rfl
    rw [h1]
    exact_mod_cast this
  · rw [div_le_iff₀ ha_pos]
    have : N ≤ (m + 1) * a := by
      dsimp [m]
      have h1 := Nat.div_add_mod N a
      have h2 := Nat.mod_lt N (by omega : 0 < a)
      have h3 : (N / a + 1) * a = a * (N / a) + a := by ring
      omega
    have h1 : ((m : ℝ) + 1) * (a : ℝ) = (((m + 1) * a : ℕ) : ℝ) := by push_cast; ring
    rw [h1]
    exact_mod_cast this

lemma harmonic_div_sub_log_div_le (N a : ℕ) (ha : 1 ≤ a) (haN : a ≤ N) :
    abs ((harmonic (N / a) : ℝ) - (Real.log ((N : ℝ) / (a : ℝ)) + Real.eulerMascheroniConstant)) ≤
    1 / ((N / a : ℕ) : ℝ) := by
  set m := N / a with hm_def
  have hm_pos : 1 ≤ m := by
    dsimp [m]
    exact Nat.div_pos haN (by omega)
  have hm_real_pos : 0 < (m : ℝ) := by positivity
  have ha_pos : 0 < (a : ℝ) := by positivity
  have hN_pos : 0 < (N : ℝ) := by
    have : 1 ≤ N := ha.trans haN
    positivity
  have hNa_pos : 0 < (N : ℝ) / (a : ℝ) := div_pos hN_pos ha_pos
  have h_bds := div_bounds N a ha
  dsimp [m] at h_bds
  have h1 : (m : ℝ) ≤ (N : ℝ) / (a : ℝ) := h_bds.1
  have h2 : (N : ℝ) / (a : ℝ) ≤ (m : ℝ) + 1 := h_bds.2
  have h_log1 : Real.log (m : ℝ) ≤ Real.log ((N : ℝ) / (a : ℝ)) :=
    Real.log_le_log hm_real_pos h1
  have h_log2 : Real.log ((N : ℝ) / (a : ℝ)) ≤ Real.log ((m : ℝ) + 1) :=
    Real.log_le_log hNa_pos h2
  have h_log_gap : Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) ≤ 1 / (m : ℝ) := by
    rw [← Real.log_div (by positivity) (ne_of_gt hm_real_pos)]
    have h_eq : ((m : ℝ) + 1) / (m : ℝ) = 1 + 1 / (m : ℝ) := by
      rw [add_div, div_self (ne_of_gt hm_real_pos)]
    rw [h_eq]
    have := Real.log_le_sub_one_of_pos (x := 1 + 1 / (m : ℝ)) (by positivity)
    linarith
  have h_harm_low := harmonic_sub_log_sub_gamma_nonneg m hm_pos
  have h_harm_up := harmonic_sub_log_sub_gamma_le m hm_pos
  rw [abs_le]
  constructor
  · linarith
  · linarith

lemma mul_div_ge_half (N a : ℕ) (ha : 1 ≤ a) (haN : a ≤ N) :
    (N : ℝ) / 2 ≤ (a : ℝ) * ((N / a : ℕ) : ℝ) := by
  have ha_pos : 0 < a := by omega
  have h_div_real : (N : ℝ) = (a : ℝ) * ((N / a : ℕ) : ℝ) + ((N % a : ℕ) : ℝ) := by
    have := Nat.div_add_mod N a
    have h2 : (N : ℝ) = ((a * (N / a) + N % a : ℕ) : ℝ) := by exact_mod_cast this.symm
    push_cast at h2
    exact h2
  have h_mod_lt : ((N % a : ℕ) : ℝ) ≤ (a : ℝ) := by
    have := Nat.mod_lt N ha_pos
    exact_mod_cast (Nat.le_of_lt this)
  by_cases h : (a : ℝ) ≤ (N : ℝ) / 2
  · linarith
  · have h_gt : (N : ℝ) / 2 < (a : ℝ) := lt_of_not_ge h
    have h_div_one : N / a = 1 := by
      have : a * 2 > N := by
        by_contra hc
        have : (a * 2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (not_lt.mp hc)
        linarith
      have : N / a < 2 := Nat.div_lt_of_lt_mul (by omega)
      have : 1 ≤ N / a := Nat.div_pos haN ha_pos
      omega
    rw [h_div_one]
    push_cast
    linarith

lemma sum_inv_mul_div_le_two (N : ℕ) (hN : 1 ≤ N) :
    ∑ a ∈ Icc 1 N, (1 / ((a : ℝ) * ((N / a : ℕ) : ℝ))) ≤ 2 := by
  have hN_pos : 0 < (N : ℝ) := by positivity
  calc
    ∑ a ∈ Icc 1 N, (1 / ((a : ℝ) * ((N / a : ℕ) : ℝ))) ≤ ∑ a ∈ Icc 1 N, (2 / (N : ℝ)) := by
      apply sum_le_sum
      intro a ha
      rw [mem_Icc] at ha
      have h_half := mul_div_ge_half N a ha.1 ha.2
      have h_pos : 0 < (a : ℝ) * ((N / a : ℕ) : ℝ) := by
        have : 0 < (N : ℝ) / 2 := by positivity
        linarith
      have : (N : ℝ) / 2 ≤ (a : ℝ) * ((N / a : ℕ) : ℝ) := h_half
      rw [div_le_iff₀ h_pos]
      have : 1 ≤ (2 / (N : ℝ)) * ((N : ℝ) / 2) := by
        rw [div_mul_div_comm, mul_comm, div_self (by positivity)]
      calc
        1 ≤ (2 / (N : ℝ)) * ((N : ℝ) / 2) := this
        _ ≤ (2 / (N : ℝ)) * ((a : ℝ) * ((N / a : ℕ) : ℝ)) := by
          have : 0 ≤ 2 / (N : ℝ) := by positivity
          nlinarith
    _ = (N : ℝ) * (2 / (N : ℝ)) := by
      rw [sum_const, nsmul_eq_mul, Nat.card_Icc]
      have : N + 1 - 1 = N := by omega
      rw [this]
    _ = 2 := mul_div_cancel₀ 2 (ne_of_gt hN_pos)

lemma sum_harmonic_sub_log_div_le (N : ℕ) (hN : 1 ≤ N) :
    abs (∑ a ∈ Icc 1 N, (1 / (a : ℝ)) * ((harmonic (N / a) : ℝ) - (Real.log ((N : ℝ) / (a : ℝ)) + Real.eulerMascheroniConstant))) ≤ 2 := by
  calc
    abs (∑ a ∈ Icc 1 N, (1 / (a : ℝ)) * ((harmonic (N / a) : ℝ) - (Real.log ((N : ℝ) / (a : ℝ)) + Real.eulerMascheroniConstant)))
      ≤ ∑ a ∈ Icc 1 N, abs ((1 / (a : ℝ)) * ((harmonic (N / a) : ℝ) - (Real.log ((N : ℝ) / (a : ℝ)) + Real.eulerMascheroniConstant))) :=
        abs_sum_le_sum_abs _ _
    _ = ∑ a ∈ Icc 1 N, (1 / (a : ℝ)) * abs ((harmonic (N / a) : ℝ) - (Real.log ((N : ℝ) / (a : ℝ)) + Real.eulerMascheroniConstant)) := by
      apply sum_congr rfl
      intro a ha
      rw [mem_Icc] at ha
      have : 0 < (a : ℝ) := by
        have : 1 ≤ a := ha.1; positivity
      rw [abs_mul, abs_of_pos (by positivity)]
    _ ≤ ∑ a ∈ Icc 1 N, (1 / (a : ℝ)) * (1 / ((N / a : ℕ) : ℝ)) := by
      apply sum_le_sum
      intro a ha
      rw [mem_Icc] at ha
      have := harmonic_div_sub_log_div_le N a ha.1 ha.2
      have : 0 ≤ 1 / (a : ℝ) := by
        have : 1 ≤ a := ha.1; positivity
      nlinarith
    _ = ∑ a ∈ Icc 1 N, (1 / ((a : ℝ) * ((N / a : ℕ) : ℝ))) := by
      apply sum_congr rfl
      intro a ha
      ring
    _ ≤ 2 := sum_inv_mul_div_le_two N hN

lemma sum_log_div_add_gamma_eq (N : ℕ) (hN : 1 ≤ N) :
    ∑ a ∈ Icc 1 N, (1 / (a : ℝ)) * (Real.log ((N : ℝ) / (a : ℝ)) + Real.eulerMascheroniConstant) =
    (Real.log N + Real.eulerMascheroniConstant) * (harmonic N : ℝ) -
    ∑ a ∈ Icc 1 N, (Real.log a / (a : ℝ)) := by
  have h_term : ∀ a ∈ Icc 1 N, (1 / (a : ℝ)) * (Real.log ((N : ℝ) / (a : ℝ)) + Real.eulerMascheroniConstant) =
      (Real.log N + Real.eulerMascheroniConstant) * (1 / (a : ℝ)) - Real.log a / (a : ℝ) := by
    intro a ha
    rw [mem_Icc] at ha
    have ha_pos : 0 < (a : ℝ) := by
      have : 1 ≤ a := ha.1; positivity
    have hN_pos : 0 < (N : ℝ) := by
      have : 1 ≤ N := hN; positivity
    have h_log : Real.log ((N : ℝ) / (a : ℝ)) = Real.log N - Real.log a := by
      rw [Real.log_div (ne_of_gt hN_pos) (ne_of_gt ha_pos)]
    rw [h_log]
    ring
  rw [sum_congr rfl h_term, sum_sub_distrib, ← mul_sum]
  congr 1
  rw [harmonic_eq_sum_Icc]
  push_cast
  simp_rw [one_div]

lemma target_sub_identity (L gamma H S : ℝ) :
    (L + gamma) * H - S - (L ^ 2 / 2 + 2 * gamma * L) =
    (L + gamma) * (H - L - gamma) + gamma ^ 2 + (L ^ 2 / 2 - S) := by
  ring

lemma inv_sq_le_tele (a : ℕ) (ha : 2 ≤ a) :
    1 / ((a : ℝ) ^ 2) ≤ 1 / ((a : ℝ) - 1) - 1 / (a : ℝ) := by
  have ha_pos : 0 < (a : ℝ) := by
    have : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  have ha1_pos : 0 < (a : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  have h_div : 1 / ((a : ℝ) - 1) - 1 / (a : ℝ) = 1 / ((a : ℝ) * ((a : ℝ) - 1)) := by
    field_simp
    ring
  rw [h_div]
  have h_mul_pos : 0 < (a : ℝ) * ((a : ℝ) - 1) := by positivity
  rw [one_div_le_one_div (by positivity) h_mul_pos]
  have : (a : ℝ) * ((a : ℝ) - 1) = (a : ℝ) ^ 2 - (a : ℝ) := by ring
  linarith

lemma sum_tele_inv (N : ℕ) (hN : 2 ≤ N) :
    ∑ a ∈ Ico 2 N, (1 / ((a : ℝ) - 1) - 1 / (a : ℝ)) = 1 - 1 / ((N : ℝ) - 1) := by
  have h_sub := sum_Ico_sub (fun x : ℕ => - (1 / ((x : ℝ) - 1))) hN
  have h_term : ∀ x ∈ Ico 2 N, 1 / ((x : ℝ) - 1) - 1 / (x : ℝ) =
      - (1 / (((x + 1 : ℕ) : ℝ) - 1)) - (- (1 / ((x : ℝ) - 1))) := by
    intro x hx
    push_cast
    have : (x : ℝ) + 1 - 1 = (x : ℝ) := by ring
    rw [this]
    ring
  rw [sum_congr rfl h_term, h_sub]
  have : - (1 / (((2 : ℕ) : ℝ) - 1)) = -1 := by norm_num
  rw [this]
  ring

lemma sum_inv_sq_le_two (N : ℕ) :
    ∑ a ∈ Ico 1 N, (1 / ((a : ℝ) ^ 2)) ≤ 2 := by
  by_cases hN : N ≤ 2
  · interval_cases N
    · simp
    · simp
    · have : Ico 1 2 = {1} := rfl
      rw [this, sum_singleton]
      norm_num
  · have hN2 : 2 < N := not_le.mp hN
    have h_decomp : Ico 1 N = insert 1 (Ico 2 N) := by
      ext x; simp only [mem_Ico, mem_insert]; omega
    have h1_nin : 1 ∉ Ico 2 N := by simp [mem_Ico]
    rw [h_decomp, sum_insert h1_nin]
    have h1 : 1 / (((1 : ℕ) : ℝ) ^ 2) = 1 := by norm_num
    rw [h1]
    have h_tele : ∑ a ∈ Ico 2 N, (1 / ((a : ℝ) ^ 2)) ≤ 1 := by
      calc
        ∑ a ∈ Ico 2 N, (1 / ((a : ℝ) ^ 2)) ≤
            ∑ a ∈ Ico 2 N, (1 / ((a : ℝ) - 1) - 1 / (a : ℝ)) := by
          apply sum_le_sum
          intro a ha
          rw [mem_Ico] at ha
          exact inv_sq_le_tele a ha.1
        _ = 1 - 1 / ((N : ℝ) - 1) := sum_tele_inv N (by omega)
        _ ≤ 1 := by
          have hN_gt1 : 1 < (N : ℝ) := by
            have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 2 ≤ N)
            linarith
          have : 0 ≤ 1 / ((N : ℝ) - 1) := by
            have : 0 < (N : ℝ) - 1 := by linarith
            positivity
          linarith
    linarith

lemma sum_log_div_tele (N : ℕ) (hN : 1 ≤ N) :
    Real.log N ^ 2 / 2 =
    ∑ a ∈ Ico 1 N, (Real.log ((a : ℝ) + 1) ^ 2 / 2 - Real.log (a : ℝ) ^ 2 / 2) := by
  have h := sum_Ico_sub (fun x : ℕ => Real.log (x : ℝ) ^ 2 / 2) hN
  push_cast at h
  rw [Real.log_one, zero_pow (by norm_num), zero_div, sub_zero] at h
  exact h.symm

lemma log_sq_diff_upper (a : ℕ) (ha : 1 ≤ a) :
    Real.log ((a : ℝ) + 1) ^ 2 / 2 - Real.log (a : ℝ) ^ 2 / 2 ≤
    Real.log (a : ℝ) / (a : ℝ) + 1 / (2 * (a : ℝ) ^ 2) := by
  have ha_pos : 0 < (a : ℝ) := by positivity
  have ha1_pos : 0 < (a : ℝ) + 1 := by positivity
  have h_diff : Real.log ((a : ℝ) + 1) ^ 2 - Real.log (a : ℝ) ^ 2 =
      (Real.log ((a : ℝ) + 1) - Real.log (a : ℝ)) * (Real.log ((a : ℝ) + 1) + Real.log (a : ℝ)) := by ring
  have h_le := Real.log_le_sub_one_of_pos (x := ((a : ℝ) + 1) / (a : ℝ)) (by positivity)
  have h_div_sub : ((a : ℝ) + 1) / (a : ℝ) - 1 = 1 / (a : ℝ) := by
    rw [div_sub_one (ne_of_gt ha_pos)]
    ring
  have h_log_div : Real.log (((a : ℝ) + 1) / (a : ℝ)) = Real.log ((a : ℝ) + 1) - Real.log (a : ℝ) := by
    rw [Real.log_div (ne_of_gt ha1_pos) (ne_of_gt ha_pos)]
  have hd_le : Real.log ((a : ℝ) + 1) - Real.log (a : ℝ) ≤ 1 / (a : ℝ) := by
    linarith [h_le, h_div_sub, h_log_div]
  have hd_nonneg : 0 ≤ Real.log ((a : ℝ) + 1) - Real.log (a : ℝ) := by
    have : (a : ℝ) ≤ (a : ℝ) + 1 := by linarith
    have := Real.log_le_log ha_pos this
    linarith
  have h_plus : Real.log ((a : ℝ) + 1) + Real.log (a : ℝ) =
      2 * Real.log (a : ℝ) + (Real.log ((a : ℝ) + 1) - Real.log (a : ℝ)) := by ring
  have h_step : (Real.log ((a : ℝ) + 1) - Real.log (a : ℝ)) * (Real.log ((a : ℝ) + 1) + Real.log (a : ℝ)) ≤
      (1 / (a : ℝ)) * (2 * Real.log (a : ℝ) + 1 / (a : ℝ)) := by
    have h1 : Real.log ((a : ℝ) + 1) + Real.log (a : ℝ) ≤ 2 * Real.log (a : ℝ) + 1 / (a : ℝ) := by linarith
    have h2 : 0 ≤ 2 * Real.log (a : ℝ) + 1 / (a : ℝ) := by
      have : 0 ≤ Real.log (a : ℝ) := by
        have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
        exact Real.log_nonneg this
      positivity
    nlinarith
  have h_alg1 : Real.log ((a : ℝ) + 1) ^ 2 / 2 - Real.log (a : ℝ) ^ 2 / 2 =
      ((Real.log ((a : ℝ) + 1) - Real.log (a : ℝ)) * (Real.log ((a : ℝ) + 1) + Real.log (a : ℝ))) / 2 := by ring
  have h_alg2 : (1 / (a : ℝ)) * (2 * Real.log (a : ℝ) + 1 / (a : ℝ)) / 2 =
      Real.log (a : ℝ) / (a : ℝ) + 1 / (2 * (a : ℝ) ^ 2) := by ring
  linarith

lemma log_sq_half_sub_sum_le_one_sub (N : ℕ) (hN : 1 ≤ N) :
    Real.log N ^ 2 / 2 - ∑ a ∈ Icc 1 N, (Real.log a / (a : ℝ)) ≤ 1 - Real.log N / (N : ℝ) := by
  have h_tele := sum_log_div_tele N hN
  have h_le : ∑ a ∈ Ico 1 N, (Real.log ((a : ℝ) + 1) ^ 2 / 2 - Real.log (a : ℝ) ^ 2 / 2) ≤
      ∑ a ∈ Ico 1 N, (Real.log (a : ℝ) / (a : ℝ) + 1 / (2 * (a : ℝ) ^ 2)) := by
    apply sum_le_sum
    intro a ha
    rw [mem_Ico] at ha
    exact log_sq_diff_upper a ha.1
  have h_split : ∑ a ∈ Ico 1 N, (Real.log (a : ℝ) / (a : ℝ) + 1 / (2 * (a : ℝ) ^ 2)) =
      (∑ a ∈ Ico 1 N, (Real.log (a : ℝ) / (a : ℝ))) + (1 / 2) * ∑ a ∈ Ico 1 N, (1 / ((a : ℝ) ^ 2)) := by
    rw [sum_add_distrib]
    congr 1
    have h_term : ∀ a ∈ Ico 1 N, 1 / (2 * (a : ℝ) ^ 2) = (1 / 2) * (1 / (a : ℝ) ^ 2) := by
      intro a _; ring
    rw [sum_congr rfl h_term, ← mul_sum]
  have h_inv_le := sum_inv_sq_le_two N
  have h_sum_le : (1 / 2 : ℝ) * ∑ a ∈ Ico 1 N, (1 / ((a : ℝ) ^ 2)) ≤ 1 := by
    linarith
  have h_shift : ∑ a ∈ Icc 1 N, (Real.log a / (a : ℝ)) =
      (∑ a ∈ Ico 1 N, (Real.log (a : ℝ) / (a : ℝ))) + Real.log N / (N : ℝ) := by
    have : Icc 1 N = insert N (Ico 1 N) := by
      ext x; simp only [mem_Icc, mem_insert, mem_Ico]; omega
    have hN_nin : N ∉ Ico 1 N := by simp [mem_Ico]
    rw [this, sum_insert hN_nin, add_comm]
  rw [h_shift]
  linarith

lemma log_div_self_le_sq_diff_simple (k : ℕ) (hk : 1 ≤ k) :
    Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1) ≤
    (Real.log ((k : ℝ) + 1) ^ 2 / 2 - Real.log (k : ℝ) ^ 2 / 2) + 1 / (2 * (k : ℝ) ^ 2) := by
  have hk_pos : 0 < (k : ℝ) := by positivity
  have hk1_pos : 0 < (k : ℝ) + 1 := by positivity
  set d := Real.log ((k : ℝ) + 1) - Real.log (k : ℝ) with hd_def
  have hd_low : 1 / ((k : ℝ) + 1) ≤ d := by
    have h_le := Real.log_le_sub_one_of_pos (x := (k : ℝ) / ((k : ℝ) + 1)) (by positivity)
    have h_sub : (k : ℝ) / ((k : ℝ) + 1) - 1 = - (1 / ((k : ℝ) + 1)) := by
      rw [div_sub_one (ne_of_gt hk1_pos)]
      have : (k : ℝ) - ((k : ℝ) + 1) = -1 := by ring
      rw [this, neg_div]
    have h_log : Real.log ((k : ℝ) / ((k : ℝ) + 1)) = - d := by
      dsimp [d]
      rw [Real.log_div (ne_of_gt hk_pos) (ne_of_gt hk1_pos)]
      ring
    linarith
  have hd_up : d ≤ 1 / (k : ℝ) := by
    have h_le := Real.log_le_sub_one_of_pos (x := ((k : ℝ) + 1) / (k : ℝ)) (by positivity)
    have h_sub : ((k : ℝ) + 1) / (k : ℝ) - 1 = 1 / (k : ℝ) := by
      rw [div_sub_one (ne_of_gt hk_pos)]
      ring
    have h_log : Real.log (((k : ℝ) + 1) / (k : ℝ)) = d := by
      dsimp [d]
      rw [Real.log_div (ne_of_gt hk1_pos) (ne_of_gt hk_pos)]
    linarith
  have h_diff : Real.log ((k : ℝ) + 1) ^ 2 / 2 - Real.log (k : ℝ) ^ 2 / 2 =
      d * Real.log ((k : ℝ) + 1) - d ^ 2 / 2 := by
    dsimp [d]
    ring
  have h_log1_nonneg : 0 ≤ Real.log ((k : ℝ) + 1) := by
    have : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
    exact Real.log_nonneg this
  have h_d_log : (1 / ((k : ℝ) + 1)) * Real.log ((k : ℝ) + 1) ≤ d * Real.log ((k : ℝ) + 1) := by
    nlinarith
  have hd_nonneg : 0 ≤ d := by
    have : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
    have := Real.log_le_log hk_pos this
    dsimp [d]
    linarith
  have h_d_sq : d ^ 2 / 2 ≤ 1 / (2 * (k : ℝ) ^ 2) := by
    have : d ^ 2 ≤ (1 / (k : ℝ)) ^ 2 := by nlinarith
    have : (1 / (k : ℝ)) ^ 2 / 2 = 1 / (2 * (k : ℝ) ^ 2) := by ring
    linarith
  have : Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1) = (1 / ((k : ℝ) + 1)) * Real.log ((k : ℝ) + 1) := by ring
  linarith

lemma sum_log_div_self_le_sq_half_add_one (N : ℕ) (hN : 1 ≤ N) :
    ∑ a ∈ Icc 1 N, (Real.log a / (a : ℝ)) ≤ Real.log N ^ 2 / 2 + 1 := by
  have h_shift : ∑ a ∈ Icc 1 N, (Real.log a / (a : ℝ)) =
      ∑ k ∈ Ico 1 N, (Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1)) := by
    have h_add := sum_Ico_add (fun x : ℕ => Real.log (x : ℝ) / (x : ℝ)) 1 N 1
    have h_comm : ∀ k : ℕ, Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1) =
        Real.log ((1 + k : ℕ) : ℝ) / ((1 + k : ℕ) : ℝ) := by
      intro k; push_cast; ring_nf
    rw [sum_congr rfl (fun k _ => h_comm k), h_add]
    have h11 : 1 + 1 = 2 := rfl
    have Ico_add_one_eq_Icc (a b : ℕ) : Ico a (b + 1) = Icc a b := by
      ext x; simp only [mem_Ico, mem_Icc]; omega
    rw [h11, Ico_add_one_eq_Icc]
    by_cases hN1 : N = 1
    · subst hN1; simp
    · have h_decomp : (Icc 1 N) = insert 1 (Icc 2 N) := by
        ext x; simp only [mem_Icc, mem_insert]; omega
      have h1_nin : 1 ∉ Icc 2 N := by simp [mem_Icc]
      rw [h_decomp, sum_insert h1_nin]
      have : Real.log ((1 : ℕ) : ℝ) / (((1 : ℕ) : ℝ)) = 0 := by
        push_cast; rw [Real.log_one, zero_div]
      rw [this, zero_add]
  rw [h_shift]
  have h_le : ∑ k ∈ Ico 1 N, (Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1)) ≤
      ∑ k ∈ Ico 1 N, ((Real.log ((k : ℝ) + 1) ^ 2 / 2 - Real.log (k : ℝ) ^ 2 / 2) + 1 / (2 * (k : ℝ) ^ 2)) := by
    apply sum_le_sum
    intro k hk
    rw [mem_Ico] at hk
    exact log_div_self_le_sq_diff_simple k hk.1
  have h_split : ∑ k ∈ Ico 1 N, ((Real.log ((k : ℝ) + 1) ^ 2 / 2 - Real.log (k : ℝ) ^ 2 / 2) + 1 / (2 * (k : ℝ) ^ 2)) =
      (∑ k ∈ Ico 1 N, (Real.log ((k : ℝ) + 1) ^ 2 / 2 - Real.log (k : ℝ) ^ 2 / 2)) +
      (1 / 2) * ∑ k ∈ Ico 1 N, (1 / ((k : ℝ) ^ 2)) := by
    rw [sum_add_distrib]
    congr 1
    have h_term : ∀ a ∈ Ico 1 N, 1 / (2 * (a : ℝ) ^ 2) = (1 / 2) * (1 / (a : ℝ) ^ 2) := by
      intro a _; ring
    rw [sum_congr rfl h_term, ← mul_sum]
  have h_tele := sum_log_div_tele N hN
  have h_inv_le := sum_inv_sq_le_two N
  have h_sum_le : (1 / 2 : ℝ) * ∑ k ∈ Ico 1 N, (1 / ((k : ℝ) ^ 2)) ≤ 1 := by linarith
  linarith

-- ============================================================================
-- Theorem 2: sum_card_divisors_div_sub_le
-- ============================================================================

theorem sum_card_divisors_div_sub_le (N : Nat) (hN : 1 <= N) :
    abs ((Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real) / n) - Real.log N ^ 2 / 2 -
        2 * Real.eulerMascheroniConstant * Real.log N) <= 4 := by
  have h_div_harm := sum_div_card_divisors_eq_harmonic N
  set approx := ∑ a ∈ Icc 1 N, (1 / (a : ℝ)) * (Real.log ((N : ℝ) / (a : ℝ)) + Real.eulerMascheroniConstant) with happrox_def
  have h_diff1 : abs ((Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real) / n) - approx) ≤ 2 := by
    rw [h_div_harm]
    dsimp [approx]
    have h_sub_dist : ∑ a ∈ Icc 1 N, (1 / (a : ℝ)) * (harmonic (N / a) : ℝ) -
        ∑ a ∈ Icc 1 N, (1 / (a : ℝ)) * (Real.log ((N : ℝ) / (a : ℝ)) + Real.eulerMascheroniConstant) =
        ∑ a ∈ Icc 1 N, (1 / (a : ℝ)) * ((harmonic (N / a) : ℝ) - (Real.log ((N : ℝ) / (a : ℝ)) + Real.eulerMascheroniConstant)) := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro a _
      ring
    rw [h_sub_dist]
    exact sum_harmonic_sub_log_div_le N hN
  have h_approx_eq := sum_log_div_add_gamma_eq N hN
  set Z := (Real.log N + Real.eulerMascheroniConstant) * (harmonic N : ℝ) -
      (∑ a ∈ Icc 1 N, (Real.log a / (a : ℝ))) - (Real.log N ^ 2 / 2 + 2 * Real.eulerMascheroniConstant * Real.log N) with hZ_def
  have h_id := target_sub_identity (Real.log N) Real.eulerMascheroniConstant (harmonic N : ℝ) (∑ a ∈ Icc 1 N, (Real.log a / (a : ℝ)))
  have hZ_eq : Z = (Real.log N + Real.eulerMascheroniConstant) * ((harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant) +
      Real.eulerMascheroniConstant ^ 2 + (Real.log N ^ 2 / 2 - ∑ a ∈ Icc 1 N, (Real.log a / (a : ℝ))) := h_id
  have hZ_le : Z ≤ 2 := by
    by_cases hN2 : 2 ≤ N
    · have h1 := harmonic_sub_log_sub_gamma_le N hN
      have h2 := log_sq_half_sub_sum_le_one_sub N hN
      have hN_pos : 0 < (N : ℝ) := by positivity
      have h_prod_le : (Real.log N + Real.eulerMascheroniConstant) * ((harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant) ≤
          (Real.log N + Real.eulerMascheroniConstant) / (N : ℝ) := by
        have : 0 ≤ Real.log N + Real.eulerMascheroniConstant := by
          have : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
          have : 0 ≤ Real.eulerMascheroniConstant := by
            have := Real.one_half_lt_eulerMascheroniConstant; linarith
          linarith
        calc
          (Real.log N + Real.eulerMascheroniConstant) * ((harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant) ≤
              (Real.log N + Real.eulerMascheroniConstant) * (1 / (N : ℝ)) := by nlinarith
          _ = (Real.log N + Real.eulerMascheroniConstant) / (N : ℝ) := by ring
      have h_cancel : (Real.log N + Real.eulerMascheroniConstant) / (N : ℝ) + (1 - Real.log N / (N : ℝ)) =
          1 + Real.eulerMascheroniConstant / (N : ℝ) := by
        calc
          (Real.log N + Real.eulerMascheroniConstant) / (N : ℝ) + (1 - Real.log N / (N : ℝ)) =
              Real.log N / (N : ℝ) + Real.eulerMascheroniConstant / (N : ℝ) + 1 - Real.log N / (N : ℝ) := by
            rw [add_div]
            ring
          _ = 1 + Real.eulerMascheroniConstant / (N : ℝ) := by ring
      have h_gam_le : Real.eulerMascheroniConstant ≤ 2 / 3 := by
        have := Real.eulerMascheroniConstant_lt_two_thirds
        linarith
      have h_gam_pos : 0 ≤ Real.eulerMascheroniConstant := by
        have := Real.one_half_lt_eulerMascheroniConstant; linarith
      have h_gam_div : Real.eulerMascheroniConstant / (N : ℝ) ≤ 1 / 3 := by
        have hN2_real : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
        have : Real.eulerMascheroniConstant / (N : ℝ) ≤ (2 / 3 : ℝ) / (2 : ℝ) := by
          have : 0 ≤ Real.eulerMascheroniConstant := h_gam_pos
          have : 0 < (N : ℝ) := by positivity
          have : 0 < (2 : ℝ) := by norm_num
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        have h_three : (2 / 3 : ℝ) / 2 = 1 / 3 := by norm_num
        linarith
      have h_gam_sq : Real.eulerMascheroniConstant ^ 2 ≤ 4 / 9 := by
        nlinarith
      rw [hZ_eq]
      have h_sum_AB : (Real.log N + Real.eulerMascheroniConstant) * ((harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant) +
          (Real.log N ^ 2 / 2 - ∑ a ∈ Icc 1 N, (Real.log a / (a : ℝ))) ≤ 1 + Real.eulerMascheroniConstant / (N : ℝ) := by
        linarith [h_prod_le, h2, h_cancel]
      linarith [h_sum_AB, h_gam_div, h_gam_sq]
    · have hN1 : N = 1 := by omega
      subst hN1
      have h_harm : (harmonic 1 : ℝ) = 1 := by
        rw [harmonic_succ, harmonic_zero]
        push_cast; ring
      have h_log1 : Real.log ((1 : ℕ) : ℝ) = 0 := by
        push_cast
        exact Real.log_one
      have h_sum_zero : ∑ a ∈ Icc (1 : ℕ) 1, (Real.log (a : ℝ) / (a : ℝ)) = 0 := by
        have : Icc (1 : ℕ) 1 = {1} := rfl
        rw [this, sum_singleton]
        push_cast
        rw [Real.log_one, zero_div]
      rw [hZ_eq, h_harm, h_log1, h_sum_zero]
      have h_gam_le : Real.eulerMascheroniConstant ≤ 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds.le
      have : (0 + Real.eulerMascheroniConstant) * (1 - 0 - Real.eulerMascheroniConstant) + Real.eulerMascheroniConstant ^ 2 + (0 ^ 2 / 2 - 0) =
          Real.eulerMascheroniConstant := by ring
      rw [this]
      linarith
  have hZ_ge : -2 ≤ Z := by
    rw [hZ_eq]
    have h1 := harmonic_sub_log_sub_gamma_nonneg N hN
    have h_gam_pos : 0 ≤ Real.eulerMascheroniConstant := by
      have := Real.one_half_lt_eulerMascheroniConstant; linarith
    have h_log_pos : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    have h_prod_nonneg : 0 ≤ (Real.log N + Real.eulerMascheroniConstant) * ((harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant) := by
      have : 0 ≤ Real.log N + Real.eulerMascheroniConstant := by linarith
      positivity
    have h_gam_sq_nonneg : 0 ≤ Real.eulerMascheroniConstant ^ 2 := by positivity
    have h_sum_le := sum_log_div_self_le_sq_half_add_one N hN
    linarith
  have hZ_abs : abs Z ≤ 2 := abs_le.mpr ⟨hZ_ge, hZ_le⟩
  have h_total : (Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real) / n) - Real.log N ^ 2 / 2 -
      2 * Real.eulerMascheroniConstant * Real.log N =
      ((Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real) / n) - approx) + Z := by
    dsimp [Z]
    rw [← h_approx_eq]
    ring
  rw [h_total]
  calc
    abs (((Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real) / n) - approx) + Z) ≤
        abs ((Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real) / n) - approx) + abs Z := abs_add_le _ _
    _ ≤ 2 + 2 := by linarith
    _ = 4 := by norm_num

-- ============================================================================
-- Section 4: Helpers and Proof for Theorem 3: tendsto_sum_card_divisors
-- ============================================================================

lemma tendsto_four_div_sqrt :
    Filter.Tendsto (fun N : ℕ => 4 / Real.sqrt N) Filter.atTop (nhds 0) := by
  have h_sqrt : Filter.Tendsto (fun N : ℕ => Real.sqrt N) Filter.atTop Filter.atTop := by
    apply Filter.Tendsto.comp Real.tendsto_sqrt_atTop
    exact tendsto_natCast_atTop_atTop
  have h_inv : Filter.Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp h_sqrt
  have h_mul : Filter.Tendsto (fun N : ℕ => 4 * (Real.sqrt N)⁻¹) Filter.atTop (nhds (4 * 0)) :=
    Filter.Tendsto.const_mul 4 h_inv
  rw [mul_zero] at h_mul
  have : (fun N : ℕ => 4 / Real.sqrt N) = (fun N : ℕ => 4 * (Real.sqrt N)⁻¹) := by
    ext N
    rw [div_eq_mul_inv]
  rwa [this]

lemma four_sqrt_div_self (N : ℕ) (hN : 1 ≤ N) :
    4 * Real.sqrt N / (N : ℝ) = 4 / Real.sqrt N := by
  have hN_pos : 0 < (N : ℝ) := by positivity
  have h_sqrt_pos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN_pos
  have h_sq : (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt (by positivity)).symm
  nth_rw 2 [h_sq]
  rw [div_mul_eq_div_div, mul_div_cancel_right₀ _ (ne_of_gt h_sqrt_pos)]

lemma tendsto_div_sub_of_bound (D : ℕ → ℝ) (L : ℝ)
    (h_bound : ∀ N ≥ 1, abs (D N - (N : ℝ) * Real.log N - L * N) ≤ 4 * Real.sqrt N) :
    Filter.Tendsto (fun N : ℕ => (D N - (N : ℝ) * Real.log N) / (N : ℝ)) Filter.atTop (nhds L) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [Real.norm_eq_abs]
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => abs_nonneg _) ?_ tendsto_four_div_sqrt
  rw [Filter.eventually_atTop]
  refine ⟨1, fun N hN => ?_⟩
  have hN_pos : 0 < (N : ℝ) := by
    have : 1 ≤ N := hN
    positivity
  have h_eq : (D N - (N : ℝ) * Real.log N) / (N : ℝ) - L =
      (D N - (N : ℝ) * Real.log N - L * (N : ℝ)) / (N : ℝ) := by
    have : (D N - (N : ℝ) * Real.log N - L * (N : ℝ)) / (N : ℝ) =
        (D N - (N : ℝ) * Real.log N) / (N : ℝ) - L * (N : ℝ) / (N : ℝ) := sub_div _ _ _
    rw [this, mul_div_cancel_right₀ _ (ne_of_gt hN_pos)]
  rw [h_eq, abs_div, abs_of_pos hN_pos]
  have h_le := h_bound N hN
  have h_div : abs (D N - (N : ℝ) * Real.log N - L * (N : ℝ)) / (N : ℝ) ≤ 4 * Real.sqrt N / (N : ℝ) :=
    (div_le_div_iff_of_pos_right hN_pos).mpr h_le
  rw [four_sqrt_div_self N hN] at h_div
  exact h_div

theorem tendsto_sum_card_divisors :
    Filter.Tendsto (fun N : Nat => ((Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real)) -
        (N : Real) * Real.log N) / N) Filter.atTop
      (nhds (2 * Real.eulerMascheroniConstant - 1)) := by
  apply tendsto_div_sub_of_bound
  intro N hN
  exact sum_card_divisors_sub_le N hN

-- ============================================================================
-- Section 5: Helpers and Proof for Theorem 4: tendsto_sum_card_divisors_sub_log
-- ============================================================================

lemma Ico_add_one_eq_Icc (a b : ℕ) : Ico a (b + 1) = Icc a b := by
  ext x
  simp only [mem_Ico, mem_Icc]
  omega

lemma sum_log_shift (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Ico 1 N, Real.log ((k : ℝ) + 1) = ∑ n ∈ Icc 1 N, Real.log n := by
  have h_add := sum_Ico_add (fun x : ℕ => Real.log (x : ℝ)) 1 N 1
  have h_comm : ∀ k : ℕ, Real.log ((k : ℝ) + 1) = Real.log ((1 + k : ℕ) : ℝ) := by
    intro k; push_cast; ring_nf
  rw [sum_congr rfl (fun k _ => h_comm k), h_add]
  have h11 : 1 + 1 = 2 := rfl
  rw [h11, Ico_add_one_eq_Icc]
  by_cases hN1 : N = 1
  · subst hN1
    simp
  · have h_decomp : (Icc 1 N) = insert 1 (Icc 2 N) := by
      ext x
      simp only [mem_Icc, mem_insert]
      omega
    have h1_nin : 1 ∉ Icc 2 N := by simp [mem_Icc]
    rw [h_decomp, sum_insert h1_nin]
    have : Real.log ((1 : ℕ) : ℝ) = 0 := by
      push_cast
      exact Real.log_one
    rw [this, zero_add]

lemma sum_log_telescoping (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * Real.log N - ∑ n ∈ Icc 1 N, Real.log n =
    ∑ k ∈ Ico 1 N, ((k : ℝ) * (Real.log ((k : ℝ) + 1) - Real.log k)) := by
  have h_term : ∀ k : ℕ, (k : ℝ) * (Real.log ((k : ℝ) + 1) - Real.log k) =
      (((k + 1 : ℝ) * Real.log (k + 1 : ℝ) - (k : ℝ) * Real.log k)) - Real.log ((k : ℝ) + 1) := by
    intro k
    ring
  have h_split : ∑ k ∈ Ico 1 N, ((k : ℝ) * (Real.log ((k : ℝ) + 1) - Real.log k)) =
      (∑ k ∈ Ico 1 N, (((k + 1 : ℝ) * Real.log (k + 1 : ℝ) - (k : ℝ) * Real.log k))) -
      ∑ k ∈ Ico 1 N, Real.log ((k : ℝ) + 1) := by
    rw [sum_congr rfl (fun k _ => h_term k), sum_sub_distrib]
  rw [h_split]
  have h_tele : ∑ k ∈ Ico 1 N, (((k + 1 : ℝ) * Real.log (k + 1 : ℝ) - (k : ℝ) * Real.log k)) =
      (N : ℝ) * Real.log N := by
    have h := sum_Ico_sub (fun x : ℕ => (x : ℝ) * Real.log x) hN
    push_cast at h
    rw [Real.log_one, mul_zero, sub_zero] at h
    exact h
  have h_shift := sum_log_shift N hN
  rw [h_tele, h_shift]

lemma log_diff_lower (k : ℕ) (hk : 1 ≤ k) :
    1 - 1 / ((k : ℝ) + 1) ≤ (k : ℝ) * (Real.log ((k : ℝ) + 1) - Real.log k) := by
  have hk_pos : 0 < (k : ℝ) := by positivity
  have hk1_pos : 0 < (k : ℝ) + 1 := by positivity
  have h_le := Real.log_le_sub_one_of_pos (x := (k : ℝ) / ((k : ℝ) + 1)) (by positivity)
  have h_sub : (k : ℝ) / ((k : ℝ) + 1) - 1 = - (1 / ((k : ℝ) + 1)) := by
    rw [div_sub_one (ne_of_gt hk1_pos)]
    have : (k : ℝ) - ((k : ℝ) + 1) = -1 := by ring
    rw [this, neg_div]
  have h_log : Real.log ((k : ℝ) / ((k : ℝ) + 1)) = - (Real.log ((k : ℝ) + 1) - Real.log k) := by
    rw [Real.log_div (ne_of_gt hk_pos) (ne_of_gt hk1_pos)]
    ring
  have h_step : 1 / ((k : ℝ) + 1) ≤ Real.log ((k : ℝ) + 1) - Real.log k := by
    linarith [h_le, h_sub, h_log]
  have : (k : ℝ) * (1 / ((k : ℝ) + 1)) ≤ (k : ℝ) * (Real.log ((k : ℝ) + 1) - Real.log k) := by
    nlinarith
  have h_alg : 1 - 1 / ((k : ℝ) + 1) = (k : ℝ) * (1 / ((k : ℝ) + 1)) := by
    have : (1 : ℝ) = ((k : ℝ) + 1) / ((k : ℝ) + 1) := (div_self (ne_of_gt hk1_pos)).symm
    nth_rw 1 [this]
    rw [← sub_div]
    ring
  linarith

lemma log_diff_upper (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) * (Real.log ((k : ℝ) + 1) - Real.log k) ≤ 1 := by
  have hk_pos : 0 < (k : ℝ) := by positivity
  have hk1_pos : 0 < (k : ℝ) + 1 := by positivity
  have h_le := Real.log_le_sub_one_of_pos (x := ((k : ℝ) + 1) / (k : ℝ)) (by positivity)
  have h_sub : ((k : ℝ) + 1) / (k : ℝ) - 1 = 1 / (k : ℝ) := by
    rw [div_sub_one (ne_of_gt hk_pos)]
    ring
  have h_log : Real.log (((k : ℝ) + 1) / (k : ℝ)) = Real.log ((k : ℝ) + 1) - Real.log k := by
    rw [Real.log_div (ne_of_gt hk1_pos) (ne_of_gt hk_pos)]
  have : Real.log ((k : ℝ) + 1) - Real.log k ≤ 1 / (k : ℝ) := by
    linarith [h_le, h_sub, h_log]
  have : (k : ℝ) * (Real.log ((k : ℝ) + 1) - Real.log k) ≤ (k : ℝ) * (1 / (k : ℝ)) := by
    nlinarith
  have h_cancel : (k : ℝ) * (1 / (k : ℝ)) = 1 := mul_one_div_cancel (ne_of_gt hk_pos)
  linarith

lemma card_Ico_one_eq_sub (N : ℕ) (hN : 1 ≤ N) :
    ((Finset.Ico 1 N).card : ℝ) = (N : ℝ) - 1 := by
  rw [Nat.card_Ico]
  push_cast [hN]
  ring

lemma sum_inv_shift (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Ico 1 N, (1 / ((k : ℝ) + 1)) = (harmonic N : ℝ) - 1 := by
  have h_add := sum_Ico_add (fun x : ℕ => 1 / (x : ℝ)) 1 N 1
  have h_comm : ∀ k : ℕ, 1 / ((k : ℝ) + 1) = 1 / ((1 + k : ℕ) : ℝ) := by
    intro k; push_cast; ring_nf
  rw [sum_congr rfl (fun k _ => h_comm k), h_add]
  have h11 : 1 + 1 = 2 := rfl
  rw [h11, Ico_add_one_eq_Icc]
  by_cases hN1 : N = 1
  · subst hN1; simp [harmonic_succ, harmonic_zero]
  · have h_decomp : (Icc 1 N) = insert 1 (Icc 2 N) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    have h1_nin : 1 ∉ Icc 2 N := by simp [mem_Icc]
    have h_harm : (harmonic N : ℝ) = ∑ n ∈ Icc 1 N, (1 / (n : ℝ)) := by
      rw [harmonic_eq_sum_Icc]; push_cast; simp_rw [one_div]
    rw [h_harm, h_decomp, sum_insert h1_nin]
    push_cast
    ring

lemma sum_log_diff_lower (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) - (harmonic N : ℝ) ≤ ∑ k ∈ Ico 1 N, ((k : ℝ) * (Real.log ((k : ℝ) + 1) - Real.log k)) := by
  have h_le : ∑ k ∈ Ico 1 N, (1 - 1 / ((k : ℝ) + 1)) ≤
      ∑ k ∈ Ico 1 N, ((k : ℝ) * (Real.log ((k : ℝ) + 1) - Real.log k)) := by
    apply sum_le_sum
    intro k hk
    rw [mem_Ico] at hk
    exact log_diff_lower k hk.1
  have h_sum1 : ∑ k ∈ Ico 1 N, (1 : ℝ) = (N : ℝ) - 1 := by
    rw [sum_const, nsmul_eq_mul, mul_one, card_Ico_one_eq_sub N hN]
  have h_inv : ∑ k ∈ Ico 1 N, (1 / ((k : ℝ) + 1)) = (harmonic N : ℝ) - 1 := sum_inv_shift N hN
  have h_split : ∑ k ∈ Ico 1 N, (1 - 1 / ((k : ℝ) + 1)) =
      ∑ k ∈ Ico 1 N, (1 : ℝ) - ∑ k ∈ Ico 1 N, (1 / ((k : ℝ) + 1)) := by rw [sum_sub_distrib]
  rw [h_split, h_sum1, h_inv] at h_le
  linarith

lemma sum_log_diff_upper (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Ico 1 N, ((k : ℝ) * (Real.log ((k : ℝ) + 1) - Real.log k)) ≤ (N : ℝ) := by
  calc
    ∑ k ∈ Ico 1 N, ((k : ℝ) * (Real.log ((k : ℝ) + 1) - Real.log k)) ≤ ∑ k ∈ Ico 1 N, (1 : ℝ) := by
      apply sum_le_sum
      intro k hk
      rw [mem_Ico] at hk
      exact log_diff_upper k hk.1
    _ = (N : ℝ) - 1 := by
      rw [sum_const, nsmul_eq_mul, mul_one, card_Ico_one_eq_sub N hN]
    _ ≤ (N : ℝ) := by linarith

lemma tendsto_log_div_nat :
    Filter.Tendsto (fun N : ℕ => Real.log N / (N : ℝ)) Filter.atTop (nhds 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)).comp tendsto_natCast_atTop_atTop
  simp only [Function.comp_def, pow_one, one_mul, add_zero] at h
  exact h

lemma tendsto_one_div_nat :
    Filter.Tendsto (fun N : ℕ => 1 / (N : ℝ)) Filter.atTop (nhds 0) := by
  have h_nat : Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have h_inv : Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have h := h_inv.comp h_nat
  simp only [Function.comp_def] at h
  have : (fun N : ℕ => 1 / (N : ℝ)) = (fun N : ℕ => ((N : ℝ))⁻¹) := by
    ext N
    rw [one_div]
  rwa [this]

lemma tendsto_one_add_log_div_nat :
    Filter.Tendsto (fun N : ℕ => (1 + Real.log N) / (N : ℝ)) Filter.atTop (nhds 0) := by
  have h : (fun N : ℕ => (1 + Real.log N) / (N : ℝ)) =
      (fun N : ℕ => 1 / (N : ℝ) + Real.log N / (N : ℝ)) := by
    ext N
    rw [add_div]
  rw [h]
  have h_add := Filter.Tendsto.add tendsto_one_div_nat tendsto_log_div_nat
  rw [add_zero] at h_add
  exact h_add

lemma tendsto_log_sum_ratio :
    Filter.Tendsto (fun N : ℕ => ((N : ℝ) * Real.log N - ∑ n ∈ Icc 1 N, Real.log n) / (N : ℝ))
      Filter.atTop (nhds 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [Real.norm_eq_abs]
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => abs_nonneg _) ?_ tendsto_one_add_log_div_nat
  rw [Filter.eventually_atTop]
  refine ⟨1, fun N hN => ?_⟩
  have hN_pos : 0 < (N : ℝ) := by
    have : 1 ≤ N := hN
    positivity
  let f := (N : ℝ) * Real.log N - ∑ n ∈ Icc 1 N, Real.log n
  have h_eq : f / (N : ℝ) - 1 = (f - (N : ℝ)) / (N : ℝ) := by
    have : (f - (N : ℝ)) / (N : ℝ) = f / (N : ℝ) - 1 := by
      rw [sub_div, div_self (ne_of_gt hN_pos)]
    exact this.symm
  rw [h_eq, abs_div, abs_of_pos hN_pos]
  have h_tele := sum_log_telescoping N hN
  have h_low_diff := sum_log_diff_lower N hN
  have h_up_diff := sum_log_diff_upper N hN
  have h_harm_le := harmonic_le_one_add_log N
  have h_low : (N : ℝ) - (1 + Real.log N) ≤ f := by
    dsimp [f]
    rw [h_tele]
    linarith
  have h_up : f ≤ (N : ℝ) := by
    dsimp [f]
    rw [h_tele]
    exact h_up_diff
  have h1 : f - (N : ℝ) ≤ 0 := by linarith
  have h2 : - (1 + Real.log N) ≤ f - (N : ℝ) := by linarith
  have h_log_pos : 0 ≤ Real.log (N : ℝ) := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    exact Real.log_nonneg this
  have h_abs : abs (f - (N : ℝ)) ≤ 1 + Real.log N := by
    rw [abs_le]
    exact ⟨h2, by linarith⟩
  exact (div_le_div_iff_of_pos_right hN_pos).mpr h_abs

theorem tendsto_sum_card_divisors_sub_log :
    Filter.Tendsto (fun N : Nat => (Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real) -
        Real.log n) / N) Filter.atTop (nhds (2 * Real.eulerMascheroniConstant)) := by
  have h_add := Filter.Tendsto.add tendsto_sum_card_divisors tendsto_log_sum_ratio
  have h_lim : (2 * Real.eulerMascheroniConstant - 1) + 1 = 2 * Real.eulerMascheroniConstant := by ring
  rw [h_lim] at h_add
  apply Filter.Tendsto.congr' _ h_add
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  refine ⟨1, fun N hN => ?_⟩
  rw [← add_div, sum_sub_distrib]
  ring

-- ============================================================================
-- Section 6: Helpers and Proof for Theorem 5: tendsto_sum_sum_card_divisors
-- ============================================================================

lemma sum_mul_log_shift (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Ico 1 N, ((k + 1 : ℝ) * Real.log ((k : ℝ) + 1)) = ∑ n ∈ Icc 1 N, ((n : ℝ) * Real.log n) := by
  have h_add := sum_Ico_add (fun x : ℕ => (x : ℝ) * Real.log (x : ℝ)) 1 N 1
  have h_comm : ∀ k : ℕ, (k + 1 : ℝ) * Real.log ((k : ℝ) + 1) = ((1 + k : ℕ) : ℝ) * Real.log ((1 + k : ℕ) : ℝ) := by
    intro k; push_cast; ring_nf
  rw [sum_congr rfl (fun k _ => h_comm k), h_add]
  have h11 : 1 + 1 = 2 := rfl
  rw [h11, Ico_add_one_eq_Icc]
  by_cases hN1 : N = 1
  · subst hN1
    simp
  · have h_decomp : (Icc 1 N) = insert 1 (Icc 2 N) := by
      ext x
      simp only [mem_Icc, mem_insert]
      omega
    have h1_nin : 1 ∉ Icc 2 N := by simp [mem_Icc]
    rw [h_decomp, sum_insert h1_nin]
    have : ((1 : ℕ) : ℝ) * Real.log ((1 : ℕ) : ℝ) = 0 := by
      push_cast
      rw [Real.log_one, mul_zero]
    rw [this, zero_add]

lemma sum_sq_log_telescoping (N : ℕ) (hN : 1 ≤ N) :
    2 * (∑ n ∈ Icc 1 N, (n : ℝ) * Real.log n) - (∑ n ∈ Icc 1 N, Real.log n) +
    (∑ k ∈ Ico 1 N, ((k : ℝ) ^ 2 * (Real.log ((k : ℝ) + 1) - Real.log k))) =
    (N : ℝ) ^ 2 * Real.log N := by
  have h_term : ∀ k : ℕ, ((k + 1 : ℝ) ^ 2 * Real.log ((k : ℝ) + 1) - (k : ℝ) ^ 2 * Real.log k) =
      2 * ((k + 1 : ℝ) * Real.log ((k : ℝ) + 1)) - Real.log ((k : ℝ) + 1) +
      (k : ℝ) ^ 2 * (Real.log ((k : ℝ) + 1) - Real.log k) := by
    intro k; ring
  have h_split : ∑ k ∈ Ico 1 N, (((k + 1 : ℝ) ^ 2 * Real.log ((k : ℝ) + 1) - (k : ℝ) ^ 2 * Real.log k)) =
      2 * (∑ k ∈ Ico 1 N, ((k + 1 : ℝ) * Real.log ((k : ℝ) + 1))) -
      (∑ k ∈ Ico 1 N, Real.log ((k : ℝ) + 1)) +
      (∑ k ∈ Ico 1 N, ((k : ℝ) ^ 2 * (Real.log ((k : ℝ) + 1) - Real.log k))) := by
    rw [sum_congr rfl (fun k _ => h_term k)]
    rw [sum_add_distrib, sum_sub_distrib, ← mul_sum]
  have h_tele : ∑ k ∈ Ico 1 N, (((k + 1 : ℝ) ^ 2 * Real.log ((k : ℝ) + 1) - (k : ℝ) ^ 2 * Real.log k)) =
      (N : ℝ) ^ 2 * Real.log N := by
    have h := sum_Ico_sub (fun x : ℕ => (x : ℝ) ^ 2 * Real.log x) hN
    push_cast at h
    rw [Real.log_one, mul_zero, sub_zero] at h
    exact h
  rw [sum_mul_log_shift N hN, sum_log_shift N hN] at h_split
  linarith

lemma sq_log_diff_lower (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) - 1 ≤ (k : ℝ) ^ 2 * (Real.log ((k : ℝ) + 1) - Real.log k) := by
  have h_low := log_diff_lower k hk
  have hk_pos : 0 < (k : ℝ) := by positivity
  have hk1_pos : 0 < (k : ℝ) + 1 := by positivity
  have h_mul : (k : ℝ) * (1 - 1 / ((k : ℝ) + 1)) ≤ (k : ℝ) * ((k : ℝ) * (Real.log ((k : ℝ) + 1) - Real.log k)) := by
    nlinarith
  have h_k_le : (k : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
    rw [div_le_one₀ hk1_pos]
    linarith
  have : (k : ℝ) - 1 ≤ (k : ℝ) * (1 - 1 / ((k : ℝ) + 1)) := by
    calc
      (k : ℝ) - 1 ≤ (k : ℝ) - (k : ℝ) / ((k : ℝ) + 1) := by linarith
      _ = (k : ℝ) * (1 - 1 / ((k : ℝ) + 1)) := by ring
  have h_sq : (k : ℝ) * ((k : ℝ) * (Real.log ((k : ℝ) + 1) - Real.log k)) =
      (k : ℝ) ^ 2 * (Real.log ((k : ℝ) + 1) - Real.log k) := by ring
  linarith

lemma sq_log_diff_upper (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) ^ 2 * (Real.log ((k : ℝ) + 1) - Real.log k) ≤ (k : ℝ) := by
  have h_up := log_diff_upper k hk
  have hk_pos : 0 < (k : ℝ) := by positivity
  have : (k : ℝ) * ((k : ℝ) * (Real.log ((k : ℝ) + 1) - Real.log k)) ≤ (k : ℝ) * 1 := by
    nlinarith
  have h_sq : (k : ℝ) * ((k : ℝ) * (Real.log ((k : ℝ) + 1) - Real.log k)) =
      (k : ℝ) ^ 2 * (Real.log ((k : ℝ) + 1) - Real.log k) := by ring
  linarith

lemma tendsto_inv_two_mul_nat :
    Filter.Tendsto (fun N : ℕ => 1 / (2 * (N : ℝ))) Filter.atTop (nhds 0) := by
  have h_nat : Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have h_mul : Filter.Tendsto (fun N : ℕ => 2 * (N : ℝ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) h_nat
  have : (fun N : ℕ => 1 / (2 * (N : ℝ))) = (fun x : ℝ => x⁻¹) ∘ (fun N : ℕ => 2 * (N : ℝ)) := by
    ext N; rw [Function.comp_apply, one_div]
  rw [this]
  exact tendsto_inv_atTop_zero.comp h_mul

lemma tendsto_sub_one_div_sq :
    Filter.Tendsto (fun N : ℕ => ((N : ℝ) - 1) / (N : ℝ) ^ 2) Filter.atTop (nhds 0) := by
  have h_eq : ∀ N : ℕ, 1 ≤ N → ((N : ℝ) - 1) / (N : ℝ) ^ 2 = 1 / (N : ℝ) - 1 / (N : ℝ) ^ 2 := by
    intro N hN
    have hN_pos : (N : ℝ) ≠ 0 := by
      have : 1 ≤ N := hN; positivity
    calc
      ((N : ℝ) - 1) / (N : ℝ) ^ 2 = (N : ℝ) / (N : ℝ) ^ 2 - 1 / (N : ℝ) ^ 2 := by rw [sub_div]
      _ = 1 / (N : ℝ) - 1 / (N : ℝ) ^ 2 := by
        rw [sq]
        have : (N : ℝ) / ((N : ℝ) * (N : ℝ)) = ((N : ℝ) * 1) / ((N : ℝ) * (N : ℝ)) := by ring
        rw [this, mul_div_mul_left _ _ hN_pos]
  have h_lim1 : Filter.Tendsto (fun N : ℕ => 1 / (N : ℝ)) Filter.atTop (nhds 0) := tendsto_one_div_nat
  have h_lim2 : Filter.Tendsto (fun N : ℕ => 1 / (N : ℝ) ^ 2) Filter.atTop (nhds 0) := by
    have h := h_lim1.mul h_lim1
    rw [mul_zero] at h
    have : (fun N : ℕ => 1 / (N : ℝ) ^ 2) = (fun N : ℕ => (1 / (N : ℝ)) * (1 / (N : ℝ))) := by
      ext N; ring
    rwa [this]
  have h_sub := Filter.Tendsto.sub h_lim1 h_lim2
  rw [sub_zero] at h_sub
  apply Filter.Tendsto.congr' _ h_sub
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  refine ⟨1, fun N hN => (h_eq N hN).symm⟩

lemma tendsto_sum_Ico_div_sq :
    Filter.Tendsto (fun N : ℕ => (((N : ℝ) - 1) * (N : ℝ) / 2) / (N : ℝ) ^ 2) Filter.atTop (nhds (1 / 2)) := by
  have h_eq : ∀ N : ℕ, 1 ≤ N → (((N : ℝ) - 1) * (N : ℝ) / 2) / (N : ℝ) ^ 2 = 1 / 2 - 1 / (2 * (N : ℝ)) := by
    intro N hN
    have hN_pos : (N : ℝ) ≠ 0 := by
      have : 1 ≤ N := hN; positivity
    calc
      (((N : ℝ) - 1) * (N : ℝ) / 2) / (N : ℝ) ^ 2 = ((N : ℝ) - 1) / (2 * (N : ℝ)) := by
        rw [sq]
        have : (((N : ℝ) - 1) * (N : ℝ) / 2) / ((N : ℝ) * (N : ℝ)) =
            (((N : ℝ) - 1) * (N : ℝ)) / (2 * (N : ℝ) * (N : ℝ)) := by ring
        rw [this, mul_div_mul_right _ _ hN_pos]
      _ = 1 / 2 - 1 / (2 * (N : ℝ)) := by
        rw [sub_div]
        have : (N : ℝ) / (2 * (N : ℝ)) = 1 / 2 := by
          have : (N : ℝ) / (2 * (N : ℝ)) = ((N : ℝ) * 1) / ((N : ℝ) * 2) := by ring
          rw [this, mul_div_mul_left _ _ hN_pos]
        rw [this]
  have h_lim := Filter.Tendsto.sub (tendsto_const_nhds (x := (1 / 2 : ℝ))) tendsto_inv_two_mul_nat
  rw [sub_zero] at h_lim
  apply Filter.Tendsto.congr' _ h_lim
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  refine ⟨1, fun N hN => (h_eq N hN).symm⟩

lemma tendsto_sum_Ico_sub_one_div_sq :
    Filter.Tendsto (fun N : ℕ => (((N : ℝ) - 1) * (N : ℝ) / 2 - ((N : ℝ) - 1)) / (N : ℝ) ^ 2)
      Filter.atTop (nhds (1 / 2)) := by
  have h_split : (fun N : ℕ => (((N : ℝ) - 1) * (N : ℝ) / 2 - ((N : ℝ) - 1)) / (N : ℝ) ^ 2) =
      (fun N : ℕ => (((N : ℝ) - 1) * (N : ℝ) / 2) / (N : ℝ) ^ 2 - ((N : ℝ) - 1) / (N : ℝ) ^ 2) := by
    ext N; rw [sub_div]
  rw [h_split]
  have h_sub := Filter.Tendsto.sub tendsto_sum_Ico_div_sq tendsto_sub_one_div_sq
  rw [sub_zero] at h_sub
  exact h_sub

lemma sum_log_le_mul_log (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, Real.log n ≤ (N : ℝ) * Real.log N := by
  have h_le : ∀ n ∈ Icc 1 N, Real.log (n : ℝ) ≤ Real.log (N : ℝ) := by
    intro n hn
    rw [mem_Icc] at hn
    have hn_pos : 0 < (n : ℝ) := by
      have : 1 ≤ n := hn.1; positivity
    apply Real.log_le_log hn_pos
    exact_mod_cast hn.2
  calc
    ∑ n ∈ Icc 1 N, Real.log (n : ℝ) ≤ ∑ n ∈ Icc 1 N, Real.log (N : ℝ) := sum_le_sum h_le
    _ = (N : ℝ) * Real.log (N : ℝ) := by
      rw [sum_const, nsmul_eq_mul, Nat.card_Icc]
      have : N + 1 - 1 = N := by omega
      rw [this]

lemma sum_log_nonneg (N : ℕ) :
    0 ≤ ∑ n ∈ Icc 1 N, Real.log n := by
  apply sum_nonneg
  intro n hn
  rw [mem_Icc] at hn
  have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
  exact Real.log_nonneg this

lemma tendsto_sum_log_div_sq :
    Filter.Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, Real.log n) / (N : ℝ) ^ 2) Filter.atTop (nhds 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [Real.norm_eq_abs, sub_zero]
  have h_bound : ∀ᶠ N : ℕ in Filter.atTop,
      abs ((∑ n ∈ Icc 1 N, Real.log n) / (N : ℝ) ^ 2) ≤ Real.log N / (N : ℝ) := by
    rw [Filter.eventually_atTop]
    refine ⟨1, fun N hN => ?_⟩
    have hN_pos : 0 < (N : ℝ) := by
      have : 1 ≤ N := hN; positivity
    have h_nonneg : 0 ≤ (∑ n ∈ Icc 1 N, Real.log n) / (N : ℝ) ^ 2 := by
      have : 0 ≤ ∑ n ∈ Icc 1 N, Real.log n := sum_log_nonneg N
      positivity
    rw [abs_of_nonneg h_nonneg]
    have h_up := sum_log_le_mul_log N hN
    have h_div : (∑ n ∈ Icc 1 N, Real.log n) / (N : ℝ) ^ 2 ≤ ((N : ℝ) * Real.log N) / (N : ℝ) ^ 2 :=
      (div_le_div_iff_of_pos_right (by positivity)).mpr h_up
    have h_cancel : ((N : ℝ) * Real.log N) / (N : ℝ) ^ 2 = Real.log N / (N : ℝ) := by
      rw [sq]
      calc
        ((N : ℝ) * Real.log N) / ((N : ℝ) * (N : ℝ)) =
            ((N : ℝ) * Real.log N) / (N : ℝ) / (N : ℝ) := by rw [div_mul_eq_div_div]
        _ = Real.log N / (N : ℝ) := by rw [mul_div_cancel_left₀ _ (ne_of_gt hN_pos)]
    rwa [h_cancel] at h_div
  have h_tendsto := tendsto_log_div_nat
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => abs_nonneg _) h_bound h_tendsto

lemma tendsto_sum_id_div_sq :
    Filter.Tendsto (fun N : ℕ => ((Finset.Icc 1 N).sum (fun n => (n : ℝ))) / (N : ℝ) ^ 2)
      Filter.atTop (nhds (1 / 2)) := by
  have h_sum : ∀ N : ℕ, 1 ≤ N → (Finset.Icc 1 N).sum (fun n => (n : ℝ)) = (N : ℝ) * ((N : ℝ) + 1) / 2 := by
    intro N hN
    have : (Finset.Icc 1 N).sum (fun n => (n : ℝ)) = (Finset.range (N + 1)).sum (fun n => (n : ℝ)) := by
      have : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
        ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [this, Finset.sum_insert (by simp [Finset.mem_Icc])]
      push_cast; ring
    rw [this]
    have h_nat := Finset.sum_range_id_mul_two (N + 1)
    have : (N + 1) * (N + 1 - 1) = N * (N + 1) := by
      have : N + 1 - 1 = N := by omega
      rw [this, mul_comm]
    rw [this] at h_nat
    have h_cast : (((Finset.range (N + 1)).sum (fun n => n) * 2 : ℕ) : ℝ) = (((N * (N + 1) : ℕ) : ℝ)) := by
      exact_mod_cast h_nat
    push_cast at h_cast
    linarith
  have h_div : ∀ N : ℕ, 1 ≤ N → ((N : ℝ) * ((N : ℝ) + 1) / 2) / (N : ℝ) ^ 2 =
      1 / 2 + 1 / (2 * (N : ℝ)) := by
    intro N hN
    have hN_pos : (N : ℝ) ≠ 0 := by
      have : 1 ≤ N := hN; positivity
    calc
      ((N : ℝ) * ((N : ℝ) + 1) / 2) / (N : ℝ) ^ 2 = ((N : ℝ) * ((N : ℝ) + 1)) / (2 * (N : ℝ) ^ 2) := by ring
      _ = ((N : ℝ) + 1) / (2 * (N : ℝ)) := by
        rw [sq]
        have : (N : ℝ) * ((N : ℝ) + 1) / (2 * ((N : ℝ) * (N : ℝ))) =
            ((N : ℝ) * ((N : ℝ) + 1)) / ((N : ℝ) * (2 * (N : ℝ))) := by ring
        rw [this, mul_div_mul_left _ _ hN_pos]
      _ = 1 / 2 + 1 / (2 * (N : ℝ)) := by
        rw [add_div]
        have : (N : ℝ) / (2 * (N : ℝ)) = 1 / 2 := by
          have : (N : ℝ) / (2 * (N : ℝ)) = ((N : ℝ) * 1) / ((N : ℝ) * 2) := by ring
          rw [this, mul_div_mul_left _ _ hN_pos]
        rw [this]
  have h_lim : Filter.Tendsto (fun N : ℕ => 1 / 2 + 1 / (2 * (N : ℝ))) Filter.atTop (nhds (1 / 2)) := by
    have h_nat : Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop
    have h_mul : Filter.Tendsto (fun N : ℕ => 2 * (N : ℝ)) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num) h_nat
    have h_inv := tendsto_inv_two_mul_nat
    have := Filter.Tendsto.const_add (1 / 2) h_inv
    rw [add_zero] at this
    exact this
  apply Filter.Tendsto.congr' _ h_lim
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  refine ⟨1, fun N hN => ?_⟩
  rw [h_sum N hN, h_div N hN]

lemma tendsto_sum_rem_div_sq (R : ℕ → ℝ)
    (hR : ∀ (n : ℕ), 1 ≤ n → abs (R n) ≤ 4 * Real.sqrt n) :
    Filter.Tendsto (fun N : ℕ => (Finset.Icc 1 N).sum R / (N : ℝ) ^ 2) Filter.atTop (nhds 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [Real.norm_eq_abs, sub_zero]
  have h_bound : ∀ᶠ N : ℕ in Filter.atTop,
      abs ((Finset.Icc 1 N).sum R / (N : ℝ) ^ 2) ≤ 4 / Real.sqrt N := by
    rw [Filter.eventually_atTop]
    refine ⟨1, fun N hN => ?_⟩
    have hN_pos : 0 < (N : ℝ) := by
      have : 1 ≤ N := hN; positivity
    have hN2_pos : 0 < (N : ℝ) ^ 2 := by positivity
    rw [abs_div, abs_of_pos hN2_pos]
    have h_sum_le : abs ((Finset.Icc 1 N).sum R) ≤ (N : ℝ) * (4 * Real.sqrt N) := by
      calc
        abs ((Finset.Icc 1 N).sum R) ≤ ∑ n ∈ Finset.Icc 1 N, abs (R n) := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ Finset.Icc 1 N, 4 * Real.sqrt n := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_Icc] at hn
          exact hR n hn.1
        _ ≤ ∑ n ∈ Finset.Icc 1 N, 4 * Real.sqrt N := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_Icc] at hn
          have hn_pos : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn.2
          have : Real.sqrt n ≤ Real.sqrt N := Real.sqrt_le_sqrt hn_pos
          linarith
        _ = (N : ℝ) * (4 * Real.sqrt N) := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
          have : N + 1 - 1 = N := by omega
          rw [this]
    have h_div : abs ((Finset.Icc 1 N).sum R) / (N : ℝ) ^ 2 ≤
        ((N : ℝ) * (4 * Real.sqrt N)) / (N : ℝ) ^ 2 :=
      (div_le_div_iff_of_pos_right hN2_pos).mpr h_sum_le
    have h_cancel : ((N : ℝ) * (4 * Real.sqrt N)) / (N : ℝ) ^ 2 = (4 * Real.sqrt N) / (N : ℝ) := by
      rw [sq]
      have : (N : ℝ) * (4 * Real.sqrt N) / ((N : ℝ) * (N : ℝ)) =
          (4 * Real.sqrt N) / (N : ℝ) := by
        rw [mul_div_mul_left _ _ (ne_of_gt hN_pos)]
      exact this
    rw [h_cancel, four_sqrt_div_self N hN] at h_div
    exact h_div
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => abs_nonneg _) h_bound tendsto_four_div_sqrt

lemma sum_Ico_id (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Ico 1 N, (k : ℝ) = ((N : ℝ) - 1) * (N : ℝ) / 2 := by
  have : (Finset.Ico 1 N).sum (fun k => (k : ℝ)) = (Finset.range N).sum (fun k => (k : ℝ)) := by
    have : Finset.range N = insert 0 (Finset.Ico 1 N) := by
      ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
    rw [this, Finset.sum_insert (by simp [Finset.mem_Ico])]
    push_cast; ring
  rw [this]
  have h_nat := Finset.sum_range_id_mul_two N
  have h_cast : (((Finset.range N).sum (fun n => n) * 2 : ℕ) : ℝ) = (((N * (N - 1) : ℕ) : ℝ)) := by
    exact_mod_cast h_nat
  push_cast [hN] at h_cast
  linarith

lemma sum_Ico_id_sub_one (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Ico 1 N, ((k : ℝ) - 1) = ((N : ℝ) - 1) * (N : ℝ) / 2 - ((N : ℝ) - 1) := by
  rw [sum_sub_distrib, sum_Ico_id N hN]
  have : ∑ k ∈ Ico 1 N, (1 : ℝ) = (N : ℝ) - 1 := by
    rw [sum_const, nsmul_eq_mul, mul_one, Nat.card_Ico]
    push_cast [hN]
    ring
  rw [this]

lemma tendsto_sum_sq_log_diff_div_sq :
    Filter.Tendsto (fun N : ℕ => (∑ k ∈ Ico 1 N, (k : ℝ) ^ 2 * (Real.log ((k : ℝ) + 1) - Real.log k)) / (N : ℝ) ^ 2)
      Filter.atTop (nhds (1 / 2)) := by
  have h_low_ev : ∀ᶠ N : ℕ in Filter.atTop,
      (((N : ℝ) - 1) * (N : ℝ) / 2 - ((N : ℝ) - 1)) / (N : ℝ) ^ 2 ≤
      (∑ k ∈ Ico 1 N, (k : ℝ) ^ 2 * (Real.log ((k : ℝ) + 1) - Real.log k)) / (N : ℝ) ^ 2 := by
    rw [Filter.eventually_atTop]
    refine ⟨1, fun N hN => ?_⟩
    have hN2_pos : 0 < (N : ℝ) ^ 2 := by
      have : 1 ≤ N := hN; positivity
    apply (div_le_div_iff_of_pos_right hN2_pos).mpr
    rw [← sum_Ico_id_sub_one N hN]
    apply sum_le_sum
    intro k hk
    rw [mem_Ico] at hk
    exact sq_log_diff_lower k hk.1
  have h_up_ev : ∀ᶠ N : ℕ in Filter.atTop,
      (∑ k ∈ Ico 1 N, (k : ℝ) ^ 2 * (Real.log ((k : ℝ) + 1) - Real.log k)) / (N : ℝ) ^ 2 ≤
      (((N : ℝ) - 1) * (N : ℝ) / 2) / (N : ℝ) ^ 2 := by
    rw [Filter.eventually_atTop]
    refine ⟨1, fun N hN => ?_⟩
    have hN2_pos : 0 < (N : ℝ) ^ 2 := by
      have : 1 ≤ N := hN; positivity
    apply (div_le_div_iff_of_pos_right hN2_pos).mpr
    rw [← sum_Ico_id N hN]
    apply sum_le_sum
    intro k hk
    rw [mem_Ico] at hk
    exact sq_log_diff_upper k hk.1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_sum_Ico_sub_one_div_sq tendsto_sum_Ico_div_sq h_low_ev h_up_ev

lemma tendsto_n_log_n_div_sq :
    Filter.Tendsto (fun N : ℕ => ((∑ n ∈ Icc 1 N, (n : ℝ) * Real.log n) - (N : ℝ) ^ 2 * Real.log N / 2) / (N : ℝ) ^ 2)
      Filter.atTop (nhds (- (1 / 4))) := by
  have h_log := tendsto_sum_log_div_sq
  have h_sq := tendsto_sum_sq_log_diff_div_sq
  have h_comb := Filter.Tendsto.sub (Filter.Tendsto.const_mul (1 / 2) h_log) (Filter.Tendsto.const_mul (1 / 2) h_sq)
  have h_lim : (1 / 2 : ℝ) * 0 - (1 / 2) * (1 / 2) = - (1 / 4) := by ring
  rw [h_lim] at h_comb
  apply Filter.Tendsto.congr' _ h_comb
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  refine ⟨1, fun N hN => ?_⟩
  have h_tele := sum_sq_log_telescoping N hN
  have h_alg : (∑ n ∈ Icc 1 N, (n : ℝ) * Real.log n) - (N : ℝ) ^ 2 * Real.log N / 2 =
      (1 / 2) * (∑ n ∈ Icc 1 N, Real.log n) - (1 / 2) * (∑ k ∈ Ico 1 N, ((k : ℝ) ^ 2 * (Real.log ((k : ℝ) + 1) - Real.log k))) := by
    linarith
  calc
    (1 / 2) * ((∑ n ∈ Icc 1 N, Real.log n) / (N : ℝ) ^ 2) -
        (1 / 2) * ((∑ k ∈ Ico 1 N, ((k : ℝ) ^ 2 * (Real.log ((k : ℝ) + 1) - Real.log k))) / (N : ℝ) ^ 2) =
      ((1 / 2) * (∑ n ∈ Icc 1 N, Real.log n) - (1 / 2) * (∑ k ∈ Ico 1 N, ((k : ℝ) ^ 2 * (Real.log ((k : ℝ) + 1) - Real.log k)))) / (N : ℝ) ^ 2 := by ring
    _ = ((∑ n ∈ Icc 1 N, (n : ℝ) * Real.log n) - (N : ℝ) ^ 2 * Real.log N / 2) / (N : ℝ) ^ 2 := by rw [h_alg]

-- ============================================================================
-- Theorem 5: tendsto_sum_sum_card_divisors
-- ============================================================================

theorem tendsto_sum_sum_card_divisors :
    Filter.Tendsto (fun N : Nat => ((Finset.Icc 1 N).sum (fun n =>
        (Finset.Icc 1 n).sum (fun m => (m.divisors.card : Real))) -
        (N : Real) ^ 2 * Real.log N / 2) / (N : Real) ^ 2) Filter.atTop
      (nhds (Real.eulerMascheroniConstant - 3 / 4)) := by
  let R : ℕ → ℝ := fun n => (Finset.Icc 1 n).sum (fun m => (m.divisors.card : Real)) - (n : ℝ) * Real.log n - (2 * Real.eulerMascheroniConstant - 1) * (n : ℝ)
  have hR : ∀ (n : ℕ), 1 ≤ n → abs (R n) ≤ 4 * Real.sqrt n := by
    intro n hn
    exact sum_card_divisors_sub_le n hn
  have h_rem := tendsto_sum_rem_div_sq R hR
  have h_id := tendsto_sum_id_div_sq
  have h_id_mul := Filter.Tendsto.const_mul (2 * Real.eulerMascheroniConstant - 1) h_id
  have h_nlogn := tendsto_n_log_n_div_sq
  have h_main := Filter.Tendsto.add h_nlogn h_id_mul
  have h_all := Filter.Tendsto.add h_main h_rem
  have h_lim : - (1 / 4) + (2 * Real.eulerMascheroniConstant - 1) * (1 / 2) + 0 = Real.eulerMascheroniConstant - 3 / 4 := by ring
  rw [h_lim] at h_all
  apply Filter.Tendsto.congr' _ h_all
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  refine ⟨1, fun N hN => ?_⟩
  have h_sum_decomp : (Finset.Icc 1 N).sum (fun n => (Finset.Icc 1 n).sum (fun m => (m.divisors.card : Real))) =
      (∑ n ∈ Icc 1 N, (n : ℝ) * Real.log n) +
      (2 * Real.eulerMascheroniConstant - 1) * (∑ n ∈ Icc 1 N, (n : ℝ)) +
      (∑ n ∈ Icc 1 N, R n) := by
    have h_term : ∀ n ∈ Icc 1 N, (Finset.Icc 1 n).sum (fun m => (m.divisors.card : Real)) =
        (n : ℝ) * Real.log n + (2 * Real.eulerMascheroniConstant - 1) * (n : ℝ) + R n := by
      intro n _
      dsimp [R]
      ring
    rw [sum_congr rfl h_term]
    simp_rw [add_assoc, sum_add_distrib, ← mul_sum]
  rw [h_sum_decomp]
  ring

end TuringTask
