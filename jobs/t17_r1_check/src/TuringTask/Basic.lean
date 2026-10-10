import Mathlib

open scoped ArithmeticFunction.Moebius
open scoped LSeries.notation
open Complex LSeries

lemma test_moebius_sum : HasSum (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2) (6 / Real.pi ^ 2) := by
  have hs : (1 : ℝ) < (2 : ℂ).re := by simp
  have h1 := LSeries_one_mul_Lseries_moebius hs
  have h2 := LSeries_one_eq_riemannZeta hs
  have h3 : riemannZeta 2 = (Real.pi : ℂ) ^ 2 / 6 := riemannZeta_two
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have h_val : L ↗μ 2 = 6 / (Real.pi : ℂ) ^ 2 := by
    have h_mul : ((Real.pi : ℂ) ^ 2 / 6) * L ↗μ 2 = 1 := by
      rwa [h2, h3] at h1
    have h_pi6 : (Real.pi : ℂ) ^ 2 / 6 ≠ 0 := by
      simp [hpi]
    exact (eq_one_div_of_mul_eq_one_right h_mul).trans (by ring)
  have h_sum : LSeriesSummable ↗μ 2 := by
    rw [ArithmeticFunction.LSeriesSummable_moebius_iff]
    exact hs
  have h_has : HasSum (term ↗μ 2) (6 / (Real.pi : ℂ) ^ 2) := by
    rw [← h_val]
    exact h_sum.LSeriesHasSum
  have h_re := Complex.hasSum_re h_has
  have h_term_re : (fun n : ℕ => (term ↗μ 2 n).re) = (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2) := by
    ext (_ | n)
    · simp [term]
    · simp only [term_of_ne_zero n.succ_ne_zero, cpow_two]
      have : (↑(μ n.succ) : ℂ) / (↑n.succ : ℂ) ^ 2 = ((((ArithmeticFunction.moebius n.succ : ℝ) / ((n.succ : ℝ) ^ 2)) : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [this, ofReal_re]
  have h_const_re : (6 / (Real.pi : ℂ) ^ 2).re = 6 / Real.pi ^ 2 := by
    have : (6 / (Real.pi : ℂ) ^ 2) = (((6 / Real.pi ^ 2 : ℝ) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [this, ofReal_re]
  rwa [h_term_re, h_const_re] at h_re

lemma sum_range_inv_sq_le (K : ℕ) (hK : 1 ≤ K) (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 : ℝ) / (i + K + 1 : ℝ) ^ 2 ≤ 1 / (K : ℝ) := by
  have hK_pos : 0 < (K : ℝ) := by positivity
  let g : ℕ → ℝ := fun x => 1 / (x + K : ℝ)
  have h_tel : ∑ i ∈ Finset.range n, (g i - g (i + 1)) = g 0 - g n := by
    have h := Finset.sum_range_sub (fun x => - g x) n
    simp only [neg_sub_neg] at h
    exact h
  have h_le : ∑ i ∈ Finset.range n, (1 : ℝ) / (i + K + 1 : ℝ) ^ 2 ≤
      ∑ i ∈ Finset.range n, (g i - g (i + 1)) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hi1 : 0 < (i + K : ℝ) := by positivity
    have hi2 : 0 < (i + K + 1 : ℝ) := by positivity
    have h_diff : g i - g (i + 1) = 1 / ((i + K : ℝ) * (i + K + 1 : ℝ)) := by
      dsimp [g]
      push_cast
      field_simp
      ring
    rw [h_diff]
    rw [one_div_le_one_div (by positivity) (by positivity)]
    nlinarith
  refine h_le.trans ?_
  rw [h_tel]
  dsimp [g]
  push_cast
  simp only [zero_add]
  have : 0 ≤ 1 / (n + K : ℝ) := by positivity
  linarith

lemma tsum_inv_sq_le (K : ℕ) (hK : 1 ≤ K) :
    ∑' i : ℕ, (1 : ℝ) / (i + K + 1 : ℝ) ^ 2 ≤ 1 / (K : ℝ) := by
  apply Real.tsum_le_of_sum_range_le (fun i => by positivity)
  exact sum_range_inv_sq_le K hK

lemma abs_sum_moebius_div_sq_sub_le (K : ℕ) (hK : 1 ≤ K) :
    |∑ d ∈ Finset.Icc 1 K, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2| ≤ 1 / (K : ℝ) := by
  set F : ℕ → ℝ := fun n => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2
  have hF_has := test_moebius_sum
  have hF_sum : Summable F := hF_has.summable
  have hF_tsum : ∑' n, F n = 6 / Real.pi ^ 2 := hF_has.tsum_eq
  have h_split := ((summable_nat_add_iff (K + 1)).mpr hF_sum).sum_add_tsum_nat_add' (f := F)
  have h_range : ∑ i ∈ Finset.range (K + 1), F i = ∑ d ∈ Finset.Icc 1 K, F d := by
    have h_r0 : Finset.range (K + 1) = insert 0 (Finset.Icc 1 K) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [h_r0, Finset.sum_insert (by simp)]
    have : F 0 = 0 := by simp [F]
    rw [this, zero_add]
  rw [h_range, hF_tsum] at h_split
  have h_assoc : (fun i : ℕ => F (i + (K + 1))) = (fun i : ℕ => F (i + K + 1)) := by
    ext i
    congr 1
  have h_diff : ∑ d ∈ Finset.Icc 1 K, F d - 6 / Real.pi ^ 2 = - ∑' i : ℕ, F (i + K + 1) := by
    calc ∑ d ∈ Finset.Icc 1 K, F d - 6 / Real.pi ^ 2
         _ = ∑ d ∈ Finset.Icc 1 K, F d - (∑ d ∈ Finset.Icc 1 K, F d + ∑' i : ℕ, F (i + (K + 1))) := by rw [h_split]
         _ = - ∑' i : ℕ, F (i + K + 1) := by
           rw [h_assoc]
           ring
  rw [h_diff, abs_neg]
  have h_summable : Summable (fun i : ℕ => 1 / (i + K + 1 : ℝ) ^ 2) := by
    apply summable_of_sum_range_le (fun i => by positivity)
    exact sum_range_inv_sq_le K hK
  have h_term_le : ∀ i : ℕ, ‖F (i + K + 1)‖ ≤ 1 / (i + K + 1 : ℝ) ^ 2 := by
    intro i
    dsimp [F]
    push_cast
    rw [abs_div, abs_pow]
    have : 0 < (i + K + 1 : ℝ) := by positivity
    rw [abs_of_pos this]
    have h_moeb : |(ArithmeticFunction.moebius (i + K + 1) : ℝ)| ≤ 1 := by
      norm_cast
      exact ArithmeticFunction.abs_moebius_le_one
    gcongr
  have h_norm_sum : Summable (fun i : ℕ => ‖F (i + K + 1)‖) :=
    h_summable.of_nonneg_of_le (fun i => norm_nonneg _) h_term_le
  have h_norm_le := norm_tsum_le_tsum_norm h_norm_sum
  rw [Real.norm_eq_abs] at h_norm_le
  refine h_norm_le.trans ?_
  have h_tsum_le : ∑' i : ℕ, ‖F (i + K + 1)‖ ≤ ∑' i : ℕ, 1 / (i + K + 1 : ℝ) ^ 2 :=
    h_norm_sum.tsum_mono h_summable h_term_le
  exact h_tsum_le.trans (tsum_inv_sq_le K hK)

lemma abs_cast_div_sub_le (m n : ℕ) (hn : 0 < n) :
    |((m / n : ℕ) : ℝ) - (m : ℝ) / (n : ℝ)| ≤ 1 := by
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have h1 : ((m / n : ℕ) : ℝ) ≤ (m : ℝ) / (n : ℝ) := Nat.cast_div_le
  have h2 : (m : ℝ) / (n : ℝ) - 1 ≤ ((m / n : ℕ) : ℝ) := by
    rw [sub_le_iff_le_add]
    rw [div_le_iff₀ hn_pos]
    have h_mod : m = n * (m / n) + m % n := (Nat.div_add_mod m n).symm
    have h_mod_lt : m % n < n := Nat.mod_lt m hn
    have : (m : ℝ) < (((m / n : ℕ) : ℝ) + 1) * (n : ℝ) := by
      calc (m : ℝ) = ((n * (m / n) + m % n : ℕ) : ℝ) := by rw [← h_mod]
           _ = (n : ℝ) * ((m / n : ℕ) : ℝ) + ((m % n : ℕ) : ℝ) := by push_cast; rfl
           _ < (n : ℝ) * ((m / n : ℕ) : ℝ) + (n : ℝ) := by gcongr
           _ = (((m / n : ℕ) : ℝ) + 1) * (n : ℝ) := by ring
    exact this.le
  rw [abs_le]
  constructor <;> linarith

lemma abs_cast_div_sq_sub_le (m n : ℕ) (hn : 0 < n) :
    |((m / n : ℕ) : ℝ) ^ 2 - ((m : ℝ) / (n : ℝ)) ^ 2| ≤ 2 * ((m : ℝ) / (n : ℝ)) := by
  have h_le1 := abs_cast_div_sub_le m n hn
  have hy_nonneg : 0 ≤ ((m / n : ℕ) : ℝ) := by positivity
  have hx_nonneg : 0 ≤ (m : ℝ) / (n : ℝ) := by positivity
  have hy_le_x : ((m / n : ℕ) : ℝ) ≤ (m : ℝ) / (n : ℝ) := Nat.cast_div_le
  have h_sq : ((m : ℝ) / (n : ℝ)) ^ 2 - ((m / n : ℕ) : ℝ) ^ 2 =
      ((m : ℝ) / (n : ℝ) - ((m / n : ℕ) : ℝ)) * ((m : ℝ) / (n : ℝ) + ((m / n : ℕ) : ℝ)) := by ring
  rw [abs_sub_comm, abs_of_nonneg (by nlinarith), h_sq]
  have h_sub_le : (m : ℝ) / (n : ℝ) - ((m / n : ℕ) : ℝ) ≤ 1 := by
    rw [abs_le] at h_le1
    linarith
  have h_add_le : (m : ℝ) / (n : ℝ) + ((m / n : ℕ) : ℝ) ≤ 2 * ((m : ℝ) / (n : ℝ)) := by linarith
  nlinarith

lemma dvd_of_sq_dvd_sq_mul {d b a : ℕ} (ha : Squarefree a) (hb : b ≠ 0) (hd : d ^ 2 ∣ b ^ 2 * a) : d ∣ b := by
  have ha0 : a ≠ 0 := ha.ne_zero
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp [ha0, hb] at hd
  rw [← Nat.factorization_le_iff_dvd hd0 hb, Finsupp.le_def]
  intro p
  have h_dvd := (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hd0) (mul_ne_zero (pow_ne_zero 2 hb) ha0)).mpr hd
  rw [Finsupp.le_def] at h_dvd
  have hp := h_dvd p
  simp only [Nat.factorization_pow, Nat.factorization_mul (pow_ne_zero 2 hb) ha0,
    Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul] at hp
  have h_le1 := ha.natFactorization_le_one p
  omega

lemma sum_moebius_divisors (b : ℕ) : ∑ d ∈ b.divisors, (ArithmeticFunction.moebius d : ℝ) = if b = 1 then 1 else 0 := by
  have h := @ArithmeticFunction.coe_mul_zeta_apply ℝ _ ArithmeticFunction.moebius b
  rw [ArithmeticFunction.coe_moebius_mul_coe_zeta, ArithmeticFunction.one_apply] at h
  exact h.symm

lemma card_Icc_filter_dvd (N d : ℕ) (hd : 0 < d) :
    ((Finset.Icc 1 N).filter (fun n => d ∣ n)).card = N / d := by
  have hd_inj : Function.Injective (fun k => d * k) := fun a b h => Nat.eq_of_mul_eq_mul_left hd h
  have : (Finset.Icc 1 N).filter (fun n => d ∣ n) = (Finset.Icc 1 (N / d)).map ⟨fun k => d * k, hd_inj⟩ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨k, rfl⟩⟩
      refine ⟨k, ⟨?_, ?_⟩, rfl⟩
      · have : 0 < k := by
          by_contra hk
          have : k = 0 := by omega
          subst this
          omega
        omega
      · rw [mul_comm] at h2
        exact (Nat.le_div_iff_mul_le hd).mpr h2
    · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ⟨k, rfl⟩⟩
      · have : 1 ≤ d * k := by nlinarith
        exact this
      · rw [mul_comm]
        exact (Nat.le_div_iff_mul_le hd).mp h2
  rw [this, Finset.card_map, Nat.card_Icc, Nat.add_sub_cancel_right]

lemma squarefree_eq_sum_moebius_sq {N : ℕ} (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
    (if Squarefree n then (1 : ℝ) else 0) =
    ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), if d ^ 2 ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0 := by
  rw [Finset.mem_Icc] at hn
  obtain ⟨a, b, ha_pos, hb_pos, h_eq, ha_sq⟩ := Nat.sq_mul_squarefree_of_pos (n := n) (by linarith [hn.1])
  have h_sq_iff : Squarefree n ↔ b = 1 := by
    constructor
    · intro hn_sq
      have hdvd : b * b ∣ n := by rw [← sq, ← h_eq]; exact dvd_mul_right (b ^ 2) a
      have : b = 1 := Nat.isUnit_iff.mp (hn_sq b hdvd)
      exact this
    · rintro rfl
      rw [← h_eq, one_pow, one_mul]
      exact ha_sq
  have hb_le : b ≤ Nat.sqrt N := by
    have : b * b ≤ N := by
      rw [← sq]
      calc b ^ 2 ≤ b ^ 2 * a := by
             have : 1 ≤ a := ha_pos
             nlinarith
           _ = n := h_eq
           _ ≤ N := hn.2
    exact Nat.le_sqrt.mpr this
  have h_set : (Finset.Icc 1 (Nat.sqrt N)).filter (fun d => d ^ 2 ∣ n) = b.divisors := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hd1, _⟩, hd_sq⟩
      have hd_dvd : d ∣ b := by
        rw [← h_eq] at hd_sq
        exact dvd_of_sq_dvd_sq_mul ha_sq hb_pos.ne' hd_sq
      exact ⟨hd_dvd, hb_pos.ne'⟩
    · rintro ⟨hd_dvd, _⟩
      have hd_pos : 1 ≤ d := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr ⟨hd_dvd, hb_pos.ne'⟩)
      have hd_le : d ≤ Nat.sqrt N := (Nat.le_of_dvd hb_pos hd_dvd).trans hb_le
      have hd_sq : d ^ 2 ∣ n := by
        rw [← h_eq]
        have : d ^ 2 ∣ b ^ 2 := pow_dvd_pow_of_dvd hd_dvd 2
        exact dvd_mul_of_dvd_left this a
      exact ⟨⟨hd_pos, hd_le⟩, hd_sq⟩
  rw [← Finset.sum_filter]
  rw [h_set, sum_moebius_divisors b]
  by_cases hb1 : b = 1
  · simp [hb1, h_sq_iff.mpr hb1]
  · simp [hb1, (h_sq_iff.not.mpr hb1)]

lemma card_squarefree_eq_sum (N : ℕ) :
    ((((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : Real)) =
    ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ArithmeticFunction.moebius d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ) := by
  have h_card : ((((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : Real)) =
      ∑ n ∈ Finset.Icc 1 N, if Squarefree n then (1 : ℝ) else (0 : ℝ) := by
    have : ((((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : Real)) =
        ∑ n ∈ (Finset.Icc 1 N).filter (fun n : Nat => Squarefree n), (1 : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [this, Finset.sum_filter]
  rw [h_card]
  have h_step : (∑ n ∈ Finset.Icc 1 N, if Squarefree n then (1 : ℝ) else (0 : ℝ)) =
      ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 (Nat.sqrt N),
      if d ^ 2 ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0 := by
    refine Finset.sum_congr rfl fun n hn => ?_
    exact squarefree_eq_sum_moebius_sq n hn
  rw [h_step, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  have hd_sq_pos : 0 < d ^ 2 := by
    have : 0 < d := by omega
    positivity
  rw [← Finset.sum_filter, Finset.sum_const]
  rw [card_Icc_filter_dvd N (d ^ 2) hd_sq_pos]
  simp [nsmul_eq_mul]
  ring

lemma sqrt_bounds (N : ℕ) (hN : 1 ≤ N) :
    let K := Nat.sqrt N
    (K : ℝ) ≤ Real.sqrt N ∧ (N : ℝ) / (K : ℝ) ≤ 2 * Real.sqrt N := by
  intro K
  have hK : 1 ≤ K := Nat.le_sqrt.mpr (by omega)
  have hK_pos : 0 < (K : ℝ) := Nat.cast_pos.mpr (by omega)
  have h1 : (K : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  have h_lt : Real.sqrt N < (K : ℝ) + 1 := Real.real_sqrt_lt_nat_sqrt_succ
  have hK_cast : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have h_sqrt_le_2K : Real.sqrt N ≤ 2 * (K : ℝ) := by linarith
  have h2 : (N : ℝ) / (K : ℝ) ≤ 2 * Real.sqrt N := by
    rw [div_le_iff₀ hK_pos]
    have hN_eq : (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt (by positivity)).symm
    nth_rw 1 [hN_eq]
    calc Real.sqrt N * Real.sqrt N
         _ ≤ Real.sqrt N * (2 * (K : ℝ)) := by
           gcongr
         _ = 2 * Real.sqrt N * (K : ℝ) := by ring
  exact ⟨h1, h2⟩

lemma card_coprime_eq_sum (N : ℕ) :
    ((((Finset.product (Finset.Icc 1 N) (Finset.Icc 1 N)).filter
        (fun p : Prod Nat Nat => Nat.Coprime p.1 p.2)).card : Real)) =
    ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) * ((N / d : ℕ) : ℝ) ^ 2 := by
  have h_card : ((((Finset.product (Finset.Icc 1 N) (Finset.Icc 1 N)).filter
        (fun p : Prod Nat Nat => Nat.Coprime p.1 p.2)).card : Real)) =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, if Nat.Coprime a b then (1 : ℝ) else (0 : ℝ) := by
    have : (((Finset.product (Finset.Icc 1 N) (Finset.Icc 1 N)).filter
          (fun p : Prod Nat Nat => Nat.Coprime p.1 p.2)).card : Real) =
        ∑ p ∈ Finset.product (Finset.Icc 1 N) (Finset.Icc 1 N), if Nat.Coprime p.1 p.2 then (1 : ℝ) else (0 : ℝ) := by
      rw [Finset.card_filter]
      push_cast
      rfl
    rw [this, Finset.product_eq_sprod, Finset.sum_product]
  rw [h_card]
  have h_coprime : ∀ a ∈ Finset.Icc 1 N, ∀ b ∈ Finset.Icc 1 N,
      (if Nat.Coprime a b then (1 : ℝ) else (0 : ℝ)) =
      ∑ d ∈ Finset.Icc 1 N, if d ∣ a ∧ d ∣ b then (ArithmeticFunction.moebius d : ℝ) else (0 : ℝ) := by
    intro a ha b hb
    rw [Finset.mem_Icc] at ha hb
    have : (if Nat.Coprime a b then (1 : ℝ) else (0 : ℝ)) =
        if Nat.gcd a b = 1 then (1 : ℝ) else (0 : ℝ) := rfl
    rw [this, ← sum_moebius_divisors (Nat.gcd a b)]
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc, Nat.dvd_gcd_iff]
    have h_gcd_pos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b (by omega)
    constructor
    · rintro ⟨⟨hda, hdb⟩, _⟩
      have hd_pos : 1 ≤ d := Nat.pos_of_dvd_of_pos hda (by omega)
      have hd_le : d ≤ N := (Nat.le_of_dvd (by omega) hda).trans ha.2
      exact ⟨⟨hd_pos, hd_le⟩, ⟨hda, hdb⟩⟩
    · rintro ⟨⟨hd1, _⟩, ⟨hda, hdb⟩⟩
      exact ⟨⟨hda, hdb⟩, h_gcd_pos.ne'⟩
  have h_step1 : ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, (if Nat.Coprime a b then (1 : ℝ) else (0 : ℝ)) =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
      ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) * (if d ∣ a then 1 else 0) * (if d ∣ b then 1 else 0) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [h_coprime a ha b hb]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases h1 : d ∣ a <;> by_cases h2 : d ∣ b <;> simp [h1, h2]
  rw [h_step1]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  have hd_pos : 0 < d := by omega
  have h_sum_d : (∑ a ∈ Finset.Icc 1 N, if d ∣ a then (1 : ℝ) else 0) = ((N / d : ℕ) : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, card_Icc_filter_dvd N d hd_pos]
    simp
  calc ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
       (ArithmeticFunction.moebius d : ℝ) * (if d ∣ a then 1 else 0) * (if d ∣ b then 1 else 0)
       _ = ∑ a ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℝ) * (if d ∣ a then 1 else 0)) *
           ∑ b ∈ Finset.Icc 1 N, (if d ∣ b then 1 else 0) := by
         refine Finset.sum_congr rfl fun a _ => ?_
         rw [← Finset.mul_sum]
       _ = (∑ a ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) * (if d ∣ a then 1 else 0)) *
           ∑ b ∈ Finset.Icc 1 N, (if d ∣ b then 1 else 0) := by rw [Finset.sum_mul]
       _ = ((ArithmeticFunction.moebius d : ℝ) * ∑ a ∈ Finset.Icc 1 N, (if d ∣ a then 1 else 0)) *
           ∑ b ∈ Finset.Icc 1 N, (if d ∣ b then 1 else 0) := by rw [← Finset.mul_sum]
       _ = (ArithmeticFunction.moebius d : ℝ) * ((N / d : ℕ) : ℝ) ^ 2 := by
         rw [h_sum_d]
         ring

lemma sum_Icc_one_div_le_log_add_one (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) ≤ Real.log N + 1 := by
  have h := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at h
  have h_cast : (∑ i ∈ Finset.Icc 1 N, (↑i : ℚ)⁻¹ : ℝ) = ∑ i ∈ Finset.Icc 1 N, (1 : ℝ) / (i : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl fun x _ => by ring
  rw [← h_cast]
  exact_mod_cast h.trans (by linarith)

lemma sum_coprime_eq_totient (b : ℕ) (hb : 1 ≤ b) :
    ∑ a ∈ Finset.Icc 1 b, (if a < b ∧ Nat.Coprime a b then (1 : ℝ) else 0) =
    (Nat.totient b : ℝ) - if b = 1 then 1 else 0 := by
  rcases eq_or_lt_of_le hb with rfl | hb2
  · simp
  · have hb_ne1 : b ≠ 1 := hb2.ne'
    simp only [if_neg hb_ne1, sub_zero]
    have h_split : Finset.Icc 1 b = insert b (Finset.Ico 1 b) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
    rw [h_split, Finset.sum_insert (by simp)]
    have : (if b < b ∧ Nat.Coprime b b then (1 : ℝ) else 0) = 0 := by simp
    rw [this, zero_add]
    have h_range : Finset.range b = insert 0 (Finset.Ico 1 b) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    have h_tot : (Nat.totient b : ℝ) = ∑ a ∈ Finset.range b, (if Nat.Coprime a b then (1 : ℝ) else 0) := by
      rw [Nat.totient_eq_card_coprime]
      simp only [Finset.sum_boole, Nat.coprime_comm]
    rw [h_tot, h_range, Finset.sum_insert (by simp)]
    have h0 : (if Nat.Coprime 0 b then (1 : ℝ) else 0) = 0 := by
      have : ¬ Nat.Coprime 0 b := by
        intro hc
        have : Nat.gcd 0 b = 1 := hc
        rw [Nat.gcd_zero_left] at this
        subst this
        omega
      simp [this]
    rw [h0, zero_add]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_Ico] at ha
    simp [ha.2]

lemma card_coprime_eq_two_sum_totient_sub_one (N : ℕ) (hN : 1 ≤ N) :
    ((((Finset.product (Finset.Icc 1 N) (Finset.Icc 1 N)).filter
        (fun p : Prod Nat Nat => Nat.Coprime p.1 p.2)).card : Real)) =
    2 * (∑ n ∈ Finset.Icc 1 N, (Nat.totient n : ℝ)) - 1 := by
  have h_card : ((((Finset.product (Finset.Icc 1 N) (Finset.Icc 1 N)).filter
        (fun p : Prod Nat Nat => Nat.Coprime p.1 p.2)).card : Real)) =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, if Nat.Coprime a b then (1 : ℝ) else (0 : ℝ) := by
    have : (((Finset.product (Finset.Icc 1 N) (Finset.Icc 1 N)).filter
          (fun p : Prod Nat Nat => Nat.Coprime p.1 p.2)).card : Real) =
        ∑ p ∈ Finset.product (Finset.Icc 1 N) (Finset.Icc 1 N), if Nat.Coprime p.1 p.2 then (1 : ℝ) else (0 : ℝ) := by
      rw [Finset.card_filter]
      push_cast
      rfl
    rw [this, Finset.product_eq_sprod, Finset.sum_product]
  rw [h_card]
  have h_decomp : ∀ a b : ℕ, (if Nat.Coprime a b then (1 : ℝ) else 0) =
      (if a = b ∧ a = 1 then (1 : ℝ) else 0) +
      (if a < b ∧ Nat.Coprime a b then (1 : ℝ) else 0) +
      (if b < a ∧ Nat.Coprime a b then (1 : ℝ) else 0) := by
    intro a b
    rcases lt_trichotomy a b with hlt | heq | hgt
    · have : ¬ a = b := hlt.ne
      have : ¬ b < a := hlt.not_gt
      by_cases hc : Nat.Coprime a b <;> simp [*]
    · subst heq
      have : ¬ a < a := lt_irrefl a
      have : Nat.Coprime a a ↔ a = 1 := by
        constructor
        · intro h
          have : Nat.gcd a a = a := Nat.gcd_self a
          omega
        · rintro rfl; exact Nat.coprime_one_left 1
      by_cases ha1 : a = 1 <;> simp [*]
    · have : ¬ a = b := hgt.ne'
      have : ¬ a < b := hgt.not_gt
      by_cases hc : Nat.Coprime a b <;> simp [*]
  have h_split : (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, if Nat.Coprime a b then (1 : ℝ) else 0) =
      (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, if a = b ∧ a = 1 then (1 : ℝ) else 0) +
      (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, if a < b ∧ Nat.Coprime a b then (1 : ℝ) else 0) +
      (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, if b < a ∧ Nat.Coprime a b then (1 : ℝ) else 0) := by
    simp_rw [h_decomp, Finset.sum_add_distrib]
  rw [h_split]
  have h_one : (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, if a = b ∧ a = 1 then (1 : ℝ) else 0) = 1 := by
    have : (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, if a = b ∧ a = 1 then (1 : ℝ) else 0) =
        ∑ a ∈ Finset.Icc 1 N, if a = 1 then (1 : ℝ) else 0 := by
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.mem_Icc] at ha
      have : (∑ b ∈ Finset.Icc 1 N, if a = b ∧ a = 1 then (1 : ℝ) else 0) =
          if a = 1 then (1 : ℝ) else 0 := by
        by_cases ha1 : a = 1
        · subst ha1
          have h1_mem : 1 ∈ Finset.Icc 1 N := Finset.left_mem_Icc.mpr hN
          rw [Finset.sum_eq_single 1]
          · simp
          · intro b hb hne
            simp [hne.symm]
          · intro h; exact (h h1_mem).elim
        · have : ∀ b ∈ Finset.Icc 1 N, (if a = b ∧ a = 1 then (1 : ℝ) else 0) = 0 := by
            intro b _; simp [ha1]
          rw [Finset.sum_congr rfl this, Finset.sum_const_zero, if_neg ha1]
      exact this
    rw [this]
    have h1_mem : 1 ∈ Finset.Icc 1 N := Finset.left_mem_Icc.mpr hN
    rw [Finset.sum_eq_single 1]
    · simp
    · intro b hb hne; simp [hne]
    · intro h; exact (h h1_mem).elim
  rw [h_one]
  have h_symm : (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, if b < a ∧ Nat.Coprime a b then (1 : ℝ) else 0) =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, if a < b ∧ Nat.Coprime a b then (1 : ℝ) else 0 := by
    rw [Finset.sum_comm]
    simp_rw [Nat.coprime_comm]
  rw [h_symm]
  have h_sum_inner : (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, if a < b ∧ Nat.Coprime a b then (1 : ℝ) else 0) =
      (∑ n ∈ Finset.Icc 1 N, (Nat.totient n : ℝ)) - 1 := by
    rw [Finset.sum_comm]
    have : (∑ b ∈ Finset.Icc 1 N, ∑ a ∈ Finset.Icc 1 N, if a < b ∧ Nat.Coprime a b then (1 : ℝ) else 0) =
        ∑ b ∈ Finset.Icc 1 N, ((Nat.totient b : ℝ) - if b = 1 then 1 else 0) := by
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [Finset.mem_Icc] at hb
      have h_eq : (∑ a ∈ Finset.Icc 1 N, if a < b ∧ Nat.Coprime a b then (1 : ℝ) else 0) =
          ∑ a ∈ Finset.Icc 1 b, if a < b ∧ Nat.Coprime a b then (1 : ℝ) else 0 := by
        refine (Finset.sum_subset (Finset.Icc_subset_Icc_right hb.2) ?_).symm
        intro x hx_N hx_b
        rw [Finset.mem_Icc] at hx_N hx_b
        have : ¬ x < b := by omega
        simp [this]
      rw [h_eq, sum_coprime_eq_totient b (by omega)]
    rw [this, Finset.sum_sub_distrib]
    have h1_mem : 1 ∈ Finset.Icc 1 N := Finset.left_mem_Icc.mpr hN
    have h_sub1 : (∑ x ∈ Finset.Icc 1 N, if x = 1 then (1 : ℝ) else 0) = 1 := by
      rw [Finset.sum_eq_single 1]
      · simp
      · intro b _ hne; simp [hne]
      · intro h; exact (h h1_mem).elim
    rw [h_sub1]
  rw [h_sum_inner]
  ring

lemma totient_eq_sum_moebius (n : ℕ) (hn : 0 < n) :
    (Nat.totient n : ℝ) = ∑ x ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ) * (x.2 : ℝ) := by
  have h := @ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq ℝ _
    (fun m => (Nat.totient m : ℝ)) (fun m => (m : ℝ))
  have h_sum : ∀ (m : ℕ), m > 0 → ∑ i ∈ m.divisors, (Nat.totient i : ℝ) = (m : ℝ) := by
    intro m _hm
    norm_cast
    exact Nat.sum_totient m
  exact (h.mp h_sum n hn).symm

lemma totient_div_eq_sum_divisors (n : ℕ) (hn : 0 < n) :
    (Nat.totient n : ℝ) / n = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) := by
  have hn_pos : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [totient_eq_sum_moebius n hn]
  rw [Nat.sum_divisorsAntidiagonal fun i j => (ArithmeticFunction.moebius i : ℝ) * (j : ℝ)]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd_dvd := Nat.dvd_of_mem_divisors hd
  have hd_pos : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne'
  have hdiv : ((n / d : ℕ) : ℝ) = (n : ℝ) / (d : ℝ) := Nat.cast_div hd_dvd hd_pos
  rw [hdiv]
  field_simp

lemma sum_sum_divisors_eq {α : Type*} [AddCommMonoid α] (N : ℕ) (f : ℕ → α) :
    ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, f d =
    ∑ d ∈ Finset.Icc 1 N, (N / d) • f d := by
  have h_inner : ∀ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, f d =
      ∑ d ∈ Finset.Icc 1 N, if d ∣ n then f d else 0 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hd_dvd, hn0⟩
      have hd_pos : 1 ≤ d := (Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr ⟨hd_dvd, hn0⟩))
      have hd_le : d ≤ N := (Nat.le_of_dvd (by omega) hd_dvd).trans hn.2
      exact ⟨⟨hd_pos, hd_le⟩, hd_dvd⟩
    · rintro ⟨⟨hd1, _⟩, hd_dvd⟩
      exact ⟨hd_dvd, by omega⟩
  rw [Finset.sum_congr rfl h_inner]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  rw [← Finset.sum_filter, Finset.sum_const]
  rw [card_Icc_filter_dvd N d (by omega)]

namespace TuringTask

theorem card_squarefree_sub_le (N : Nat) (hN : 1 <= N) :
    abs ((((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : Real) -
        6 / Real.pi ^ 2 * N) <= 3 * Real.sqrt N := by
  set K := Nat.sqrt N
  have hK : 1 ≤ K := Nat.le_sqrt.mpr (by omega)
  have hK_pos : 0 < (K : ℝ) := Nat.cast_pos.mpr (by omega)
  rw [card_squarefree_eq_sum N]
  have h_comm : 6 / Real.pi ^ 2 * (N : ℝ) = (N : ℝ) * (6 / Real.pi ^ 2) := by ring
  rw [h_comm]
  have h_decomp : (∑ d ∈ Finset.Icc 1 K, (ArithmeticFunction.moebius d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ)) -
      (N : ℝ) * (6 / Real.pi ^ 2) =
      (∑ d ∈ Finset.Icc 1 K, (ArithmeticFunction.moebius d : ℝ) * (((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) / (d : ℝ) ^ 2)) +
      (N : ℝ) * (∑ d ∈ Finset.Icc 1 K, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2) := by
    rw [mul_sub, Finset.mul_sum, add_sub, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_Icc] at hd
    have hd_pos : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
    ring
  rw [h_decomp]
  refine (abs_add_le _ _).trans ?_
  have h_first : |∑ d ∈ Finset.Icc 1 K, (ArithmeticFunction.moebius d : ℝ) * (((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) / (d : ℝ) ^ 2)| ≤
      (K : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h_le_each : ∀ d ∈ Finset.Icc 1 K,
        |(ArithmeticFunction.moebius d : ℝ) * (((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) / (d : ℝ) ^ 2)| ≤ 1 := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      rw [abs_mul]
      have h_moeb : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        norm_cast; exact ArithmeticFunction.abs_moebius_le_one
      have hd_sq_pos : 0 < d ^ 2 := by
        have : 0 < d := by omega
        positivity
      have h_floor := abs_cast_div_sub_le N (d ^ 2) hd_sq_pos
      push_cast at h_floor
      have : |(ArithmeticFunction.moebius d : ℝ)| * |((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) / (d : ℝ) ^ 2| ≤ 1 * 1 := by
        gcongr
      linarith
    have h_sum_le := Finset.sum_le_sum h_le_each
    rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h_sum_le
    have h_card_K : (Finset.Icc 1 K).card = K := by
      rw [Nat.card_Icc, Nat.add_sub_cancel_right]
    rw [h_card_K] at h_sum_le
    exact h_sum_le
  have h_second : |(N : ℝ) * (∑ d ∈ Finset.Icc 1 K, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2)| ≤
      (N : ℝ) / (K : ℝ) := by
    rw [abs_mul, abs_of_pos (Nat.cast_pos.mpr (by omega))]
    have h_tail := abs_sum_moebius_div_sq_sub_le K hK
    have : (N : ℝ) * |∑ d ∈ Finset.Icc 1 K, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2| ≤
        (N : ℝ) * (1 / (K : ℝ)) := by
      gcongr
    refine this.trans ?_
    have : (N : ℝ) * (1 / (K : ℝ)) = (N : ℝ) / (K : ℝ) := by ring
    rw [this]
  have h_bounds := sqrt_bounds N hN
  linarith [h_first, h_second, h_bounds.1, h_bounds.2]

theorem card_coprime_sub_le (N : Nat) (hN : 1 <= N) :
    abs ((((Finset.product (Finset.Icc 1 N) (Finset.Icc 1 N)).filter
        (fun p : Prod Nat Nat => Nat.Coprime p.1 p.2)).card : Real) - 6 / Real.pi ^ 2 * N ^ 2) <=
      6 * N * (Real.log N + 1) := by
  rw [card_coprime_eq_sum N]
  have h_comm : 6 / Real.pi ^ 2 * (N : ℝ) ^ 2 = (N : ℝ) ^ 2 * (6 / Real.pi ^ 2) := by ring
  rw [h_comm]
  have h_decomp : (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) * ((N / d : ℕ) : ℝ) ^ 2) -
      (N : ℝ) ^ 2 * (6 / Real.pi ^ 2) =
      (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) * (((N / d : ℕ) : ℝ) ^ 2 - ((N : ℝ) / (d : ℝ)) ^ 2)) +
      (N : ℝ) ^ 2 * (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2) := by
    rw [mul_sub, Finset.mul_sum, add_sub, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_Icc] at hd
    have hd_pos : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
    ring
  rw [h_decomp]
  refine (abs_add_le _ _).trans ?_
  have h_first : |∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) * (((N / d : ℕ) : ℝ) ^ 2 - ((N : ℝ) / (d : ℝ)) ^ 2)| ≤
      2 * (N : ℝ) * (Real.log N + 1) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h_le_each : ∀ d ∈ Finset.Icc 1 N,
        |(ArithmeticFunction.moebius d : ℝ) * (((N / d : ℕ) : ℝ) ^ 2 - ((N : ℝ) / (d : ℝ)) ^ 2)| ≤
        2 * (N : ℝ) / (d : ℝ) := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      rw [abs_mul]
      have h_moeb : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        norm_cast; exact ArithmeticFunction.abs_moebius_le_one
      have h_sq := abs_cast_div_sq_sub_le N d (by omega)
      have : |(ArithmeticFunction.moebius d : ℝ)| * |((N / d : ℕ) : ℝ) ^ 2 - ((N : ℝ) / (d : ℝ)) ^ 2| ≤
          1 * (2 * ((N : ℝ) / (d : ℝ))) := by
        gcongr
      have h_arith : 1 * (2 * ((N : ℝ) / (d : ℝ))) = 2 * (N : ℝ) / (d : ℝ) := by ring
      linarith
    have h_sum_le := Finset.sum_le_sum h_le_each
    have h_factor : (∑ d ∈ Finset.Icc 1 N, 2 * (N : ℝ) / (d : ℝ)) = 2 * (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => by ring
    rw [h_factor] at h_sum_le
    have h_log := sum_Icc_one_div_le_log_add_one N
    have h_2N_nonneg : 0 ≤ 2 * (N : ℝ) := by positivity
    nlinarith
  have h_second : |(N : ℝ) ^ 2 * (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2)| ≤ (N : ℝ) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    have h_tail := abs_sum_moebius_div_sq_sub_le N hN
    have : (N : ℝ) ^ 2 * |∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2| ≤
        (N : ℝ) ^ 2 * (1 / (N : ℝ)) := by
      gcongr
    refine this.trans ?_
    have hN_pos : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have : (N : ℝ) ^ 2 * (1 / (N : ℝ)) = (N : ℝ) := by
      field_simp
    rw [this]
  have h_N_le : (N : ℝ) ≤ 4 * (N : ℝ) * (Real.log N + 1) := by
    have h_log_nonneg : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have hN_ge1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  linarith

theorem sum_totient_sub_le (N : Nat) (hN : 1 <= N) :
    abs ((Finset.Icc 1 N).sum (fun n => (Nat.totient n : Real)) - 3 / Real.pi ^ 2 * N ^ 2) <=
      4 * N * (Real.log N + 1) := by
  have h_coprime := card_coprime_sub_le N hN
  have h_rel := card_coprime_eq_two_sum_totient_sub_one N hN
  have h_id : (Finset.Icc 1 N).sum (fun n => (Nat.totient n : Real)) - 3 / Real.pi ^ 2 * (N : ℝ) ^ 2 =
      (1 / 2) * (((((Finset.product (Finset.Icc 1 N) (Finset.Icc 1 N)).filter
        (fun p : Prod Nat Nat => Nat.Coprime p.1 p.2)).card : Real) - 6 / Real.pi ^ 2 * (N : ℝ) ^ 2) + 1) := by
    rw [h_rel]
    ring
  rw [h_id, abs_mul, abs_of_pos (by norm_num)]
  have h_abs_add : |((((Finset.product (Finset.Icc 1 N) (Finset.Icc 1 N)).filter
        (fun p : Prod Nat Nat => Nat.Coprime p.1 p.2)).card : Real) - 6 / Real.pi ^ 2 * (N : ℝ) ^ 2) + 1| ≤
      6 * (N : ℝ) * (Real.log N + 1) + 1 := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_one]
    linarith [h_coprime]
  have h_half_le : (1 / 2 : ℝ) * (6 * (N : ℝ) * (Real.log N + 1) + 1) ≤ 4 * (N : ℝ) * (Real.log N + 1) := by
    have hN_ge1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
    have h_log_nonneg : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    nlinarith
  linarith [h_abs_add]

theorem sum_totient_div_sub_le (N : Nat) (hN : 1 <= N) :
    abs ((Finset.Icc 1 N).sum (fun n => (Nat.totient n : Real) / n) - 6 / Real.pi ^ 2 * N) <=
      Real.log N + 2 := by
  have hN_pos : 0 < N := by omega
  have h_tot_sum : (Finset.Icc 1 N).sum (fun n => (Nat.totient n : Real) / n) =
      ∑ d ∈ Finset.Icc 1 N, ((N / d : ℕ) : ℝ) * ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) := by
    have h1 : (Finset.Icc 1 N).sum (fun n => (Nat.totient n : Real) / n) =
        ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_Icc] at hn
      exact totient_div_eq_sum_divisors n (by omega)
    rw [h1, sum_sum_divisors_eq]
    refine Finset.sum_congr rfl fun d _ => by simp [nsmul_eq_mul]
  rw [h_tot_sum]
  have h_comm : 6 / Real.pi ^ 2 * (N : ℝ) = (N : ℝ) * (6 / Real.pi ^ 2) := by ring
  rw [h_comm]
  have h_decomp : (∑ d ∈ Finset.Icc 1 N, ((N / d : ℕ) : ℝ) * ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ))) -
      (N : ℝ) * (6 / Real.pi ^ 2) =
      (∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) * (((N / d : ℕ) : ℝ) - (N : ℝ) / (d : ℝ))) +
      (N : ℝ) * (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2) := by
    rw [mul_sub, Finset.mul_sum, add_sub, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_Icc] at hd
    have hd_pos : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
    ring
  rw [h_decomp]
  refine (abs_add_le _ _).trans ?_
  have h_first : |∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) * (((N / d : ℕ) : ℝ) - (N : ℝ) / (d : ℝ))| ≤
      Real.log N + 1 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h_le_each : ∀ d ∈ Finset.Icc 1 N,
        |((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) * (((N / d : ℕ) : ℝ) - (N : ℝ) / (d : ℝ))| ≤
        1 / (d : ℝ) := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      rw [abs_mul, abs_div]
      have hd_pos : 0 < (d : ℝ) := Nat.cast_pos.mpr (by omega)
      rw [abs_of_pos hd_pos]
      have h_moeb : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        norm_cast; exact ArithmeticFunction.abs_moebius_le_one
      have h_floor : |((N / d : ℕ) : ℝ) - (N : ℝ) / (d : ℝ)| ≤ 1 := abs_cast_div_sub_le N d (by omega)
      have : |(ArithmeticFunction.moebius d : ℝ)| / (d : ℝ) * |((N / d : ℕ) : ℝ) - (N : ℝ) / (d : ℝ)| ≤
          1 / (d : ℝ) * 1 := by
        gcongr
      linarith
    have h_sum_le := Finset.sum_le_sum h_le_each
    exact h_sum_le.trans (sum_Icc_one_div_le_log_add_one N)
  have h_second : |(N : ℝ) * (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2)| ≤ 1 := by
    rw [abs_mul, abs_of_pos (Nat.cast_pos.mpr (by omega))]
    have h_tail := abs_sum_moebius_div_sq_sub_le N hN
    have : (N : ℝ) * |∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2| ≤
        (N : ℝ) * (1 / (N : ℝ)) := by
      gcongr
    refine this.trans ?_
    have : (N : ℝ) * (1 / (N : ℝ)) = 1 := by
      field_simp
    rw [this]
  linarith

theorem tendsto_card_squarefree_div :
    Filter.Tendsto (fun N : Nat => (((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card :
        Real) / N) Filter.atTop (nhds (6 / Real.pi ^ 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [Real.norm_eq_abs]
  have h_lim : Filter.Tendsto (fun N : ℕ => 3 / Real.sqrt N) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have h2 : Filter.Tendsto (fun N : ℕ => 3 * (Real.sqrt N)⁻¹) Filter.atTop (nhds (3 * 0)) :=
      h1.const_mul 3
    rw [mul_zero] at h2
    have : (fun N : ℕ => 3 / Real.sqrt N) = (fun N : ℕ => 3 * (Real.sqrt N)⁻¹) := by
      ext N; ring
    rwa [this]
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => abs_nonneg _) ?_ h_lim
  rw [Filter.eventually_atTop]
  refine ⟨1, fun N hN => ?_⟩
  have hN_pos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have h_bound := card_squarefree_sub_le N hN
  have h_div : (((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : Real) / (N : ℝ) - 6 / Real.pi ^ 2 =
      ((((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : Real) - 6 / Real.pi ^ 2 * (N : ℝ)) / (N : ℝ) := by
    field_simp
  rw [h_div, abs_div, abs_of_pos hN_pos]
  have h_le : |(((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : Real) - 6 / Real.pi ^ 2 * (N : ℝ)| / (N : ℝ) ≤
      3 * Real.sqrt N / (N : ℝ) := by
    gcongr
  refine h_le.trans_eq ?_
  have hN_sqrt : (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt (by positivity)).symm
  nth_rw 2 [hN_sqrt]
  have h_sqrt_pos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN_pos
  exact mul_div_mul_right 3 (Real.sqrt N) h_sqrt_pos.ne'

end TuringTask
