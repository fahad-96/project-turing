import Mathlib

namespace TuringTask

noncomputable def ex (x : Real) : Complex :=
  Complex.exp (2 * (Real.pi : Complex) * Complex.I * (x : Complex))

noncomputable def rt (n : Nat) : Complex :=
  if n % 4 = 1 then ((Real.sqrt (n : Real) : Real) : Complex)
  else Complex.I * ((Real.sqrt (n : Real) : Real) : Complex)

/-!
### Helper Lemmas for Exponential and Chinese Remainder Theorem
-/

lemma ex_add (x y : Real) : ex (x + y) = ex x * ex y := by
  dsimp [ex]
  push_cast
  have : 2 * (Real.pi : Complex) * Complex.I * (↑x + ↑y) =
      2 * (Real.pi : Complex) * Complex.I * ↑x + 2 * (Real.pi : Complex) * Complex.I * ↑y := by ring
  rw [this, Complex.exp_add]

lemma ex_int (n : Int) : ex n = 1 := by
  dsimp [ex]
  have : 2 * (Real.pi : Complex) * Complex.I * (n : Complex) =
      (n : Complex) * (2 * (Real.pi : Complex) * Complex.I) := by ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma ex_add_int (x : Real) (n : Int) : ex (x + n) = ex x := by
  have : ex (x + (n : Real)) = ex x * ex (n : Real) := ex_add x (n : Real)
  rw [this, ex_int n, mul_one]

lemma ex_sub_int (x : Real) (n : Int) : ex (x - n) = ex x := by
  have : x - (n : Real) = x + (-n : Real) := by ring
  rw [this, ← Int.cast_neg]
  exact ex_add_int x (-n)

lemma ex_sq_mod (m : Nat) (hm : m ≠ 0) (x : Nat) :
    ex (((x : Real) ^ 2) / (m : Real)) = ex ((((x % m : Nat) : Real) ^ 2) / (m : Real)) := by
  have hmR : (m : Real) ≠ 0 := Nat.cast_ne_zero.mpr hm
  set q := x / m
  set r := x % m
  have hx : (x : Real) = (m : Real) * (q : Real) + (r : Real) := by
    have := (Nat.div_add_mod x m).symm
    exact_mod_cast this
  have h_alg : (x : Real) ^ 2 / (m : Real) =
      (r : Real) ^ 2 / (m : Real) + ((m : Real) * (q : Real) ^ 2 + 2 * (q : Real) * (r : Real)) := by
    rw [hx]
    field_simp
    ring
  rw [h_alg]
  have h_int : ((m : Real) * (q : Real) ^ 2 + 2 * (q : Real) * (r : Real)) =
      (((m * q ^ 2 + 2 * q * r : Nat) : Int) : Real) := by push_cast; rfl
  rw [h_int]
  exact ex_add_int _ _

lemma frac_decomp (p q : Real) (j k : Real) (hp : p ≠ 0) (hq : q ≠ 0) :
    q * j ^ 2 / p + p * k ^ 2 / q = (q * j + p * k) ^ 2 / (p * q) - 2 * j * k := by
  have hpq : p * q ≠ 0 := mul_ne_zero hp hq
  field_simp
  ring

lemma ex_frac_decomp (p q : Nat) (j k : Nat) (hp : p ≠ 0) (hq : q ≠ 0) :
    ex ((q : Real) * (j : Real) ^ 2 / (p : Real) + (p : Real) * (k : Real) ^ 2 / (q : Real)) =
    ex (((((q * j + p * k : Nat) : Real) ^ 2)) / ((p * q : Nat) : Real)) := by
  have hpR : (p : Real) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hqR : (q : Real) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have h_alg := frac_decomp (p : Real) (q : Real) (j : Real) (k : Real) hpR hqR
  have h_cast : ((q * j + p * k : Nat) : Real) = (q : Real) * (j : Real) + (p : Real) * (k : Real) := by push_cast; rfl
  have h_cast_mul : ((p * q : Nat) : Real) = (p : Real) * (q : Real) := by push_cast; rfl
  rw [h_cast, h_cast_mul, h_alg]
  have h_int : 2 * (j : Real) * (k : Real) = (((2 * j * k : Nat) : Int) : Real) := by push_cast; rfl
  rw [h_int]
  exact ex_sub_int _ _

lemma lin_bounded_dvd (p : Int) (hp : 0 < p) (j1 j2 : Int) (hj1 : 0 ≤ j1) (hj1' : j1 < p)
    (hj2 : 0 ≤ j2) (hj2' : j2 < p) (c : Int) (h : j1 - j2 = p * c) : j1 = j2 := by
  rcases lt_trichotomy c 0 with hneg | rfl | hpos
  · have : p * c ≤ -p := by nlinarith
    linarith
  · linarith
  · have : p * c ≥ p := by nlinarith
    linarith

lemma prime_dvd_mul_cancel (p q : Nat) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (d : Int) (h : (p : Int) ∣ (q : Int) * d) : (p : Int) ∣ d := by
  have hp_prime : Prime (p : Int) := Nat.prime_iff_prime_int.mp hp
  have hor := hp_prime.dvd_mul.mp h
  rcases hor with h1 | h2
  · have h_dvd_nat : p ∣ q := by exact Int.natCast_dvd_natCast.mp h1
    have : p = 1 ∨ p = q := (Nat.dvd_prime hq).mp h_dvd_nat
    rcases this with rfl | rfl
    · exfalso; exact Nat.Prime.ne_one hp rfl
    · exfalso; exact hpq rfl
  · exact h2

lemma crt_map_inj (p q : Nat) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    ∀ (j1 k1 j2 k2 : Nat), j1 < p → j2 < p → k1 < q → k2 < q →
      (q * j1 + p * k1) % (p * q) = (q * j2 + p * k2) % (p * q) → j1 = j2 ∧ k1 = k2 := by
  intro j1 k1 j2 k2 hj1 hj2 hk1 hk2 h
  have hp_pos : (0 : Int) < (p : Int) := by exact_mod_cast hp.pos
  have hq_pos : (0 : Int) < (q : Int) := by exact_mod_cast hq.pos
  have h_modeq : (q * j1 + p * k1) ≡ (q * j2 + p * k2) [MOD p * q] := h
  have hdvd : (p * q : Int) ∣ ((q * j1 + p * k1 : Int) - (q * j2 + p * k2 : Int)) :=
    Nat.ModEq.dvd h_modeq.symm
  have h_split : ((q * j1 + p * k1 : Int) - (q * j2 + p * k2 : Int)) =
      (q : Int) * ((j1 : Int) - (j2 : Int)) + (p : Int) * ((k1 : Int) - (k2 : Int)) := by ring
  rw [h_split] at hdvd
  have hdvd_p : (p : Int) ∣ (q : Int) * ((j1 : Int) - (j2 : Int)) + (p : Int) * ((k1 : Int) - (k2 : Int)) := by
    have : (p : Int) ∣ (p * q : Int) := dvd_mul_right (p : Int) (q : Int)
    exact dvd_trans this hdvd
  have hdvd_p' : (p : Int) ∣ (q : Int) * ((j1 : Int) - (j2 : Int)) := by
    have : (p : Int) ∣ (p : Int) * ((k1 : Int) - (k2 : Int)) := dvd_mul_right (p : Int) _
    exact (dvd_add_left this).mp hdvd_p
  have hdvd_j : (p : Int) ∣ ((j1 : Int) - (j2 : Int)) := prime_dvd_mul_cancel p q hp hq hpq _ hdvd_p'
  obtain ⟨cj, hcj⟩ := hdvd_j
  have hj_eq : j1 = j2 := by
    have hj1_int : (j1 : Int) < (p : Int) := by exact_mod_cast hj1
    have hj2_int : (j2 : Int) < (p : Int) := by exact_mod_cast hj2
    have hj1_ge : 0 ≤ (j1 : Int) := by exact_mod_cast Nat.zero_le j1
    have hj2_ge : 0 ≤ (j2 : Int) := by exact_mod_cast Nat.zero_le j2
    exact Nat.cast_injective (lin_bounded_dvd (p : Int) hp_pos (j1 : Int) (j2 : Int) hj1_ge hj1_int hj2_ge hj2_int cj hcj)

  have hdvd_q : (q : Int) ∣ (q : Int) * ((j1 : Int) - (j2 : Int)) + (p : Int) * ((k1 : Int) - (k2 : Int)) := by
    have : (q : Int) ∣ (p * q : Int) := by rw [mul_comm]; exact dvd_mul_right (q : Int) (p : Int)
    exact dvd_trans this hdvd
  have hdvd_q' : (q : Int) ∣ (p : Int) * ((k1 : Int) - (k2 : Int)) := by
    have : (q : Int) ∣ (q : Int) * ((j1 : Int) - (j2 : Int)) := dvd_mul_right (q : Int) _
    exact (dvd_add_right this).mp hdvd_q
  have hdvd_k : (q : Int) ∣ ((k1 : Int) - (k2 : Int)) := prime_dvd_mul_cancel q p hq hp hpq.symm _ hdvd_q'
  obtain ⟨ck, hck⟩ := hdvd_k
  have hk_eq : k1 = k2 := by
    have hk1_int : (k1 : Int) < (q : Int) := by exact_mod_cast hk1
    have hk2_int : (k2 : Int) < (q : Int) := by exact_mod_cast hk2
    have hk1_ge : 0 ≤ (k1 : Int) := by exact_mod_cast Nat.zero_le k1
    have hk2_ge : 0 ≤ (k2 : Int) := by exact_mod_cast Nat.zero_le k2
    exact Nat.cast_injective (lin_bounded_dvd (q : Int) hq_pos (k1 : Int) (k2 : Int) hk1_ge hk1_int hk2_ge hk2_int ck hck)

  exact ⟨hj_eq, hk_eq⟩

/-!
### Main Theorems
-/

theorem sum_sq (n : Nat) (hn : n % 2 = 1) :
    Finset.sum (Finset.range n) (fun k : Nat => ex ((k : Real) ^ 2 / (n : Real))) = rt n := by
  sorry

theorem sum_tri (n : Nat) (hn : n % 2 = 1) :
    Finset.sum (Finset.range n) (fun k : Nat =>
        ex ((k : Real) * ((k : Real) + 1) / (2 * (n : Real)))) =
      ex (((n : Real) - 1) / (8 * (n : Real))) * ((Real.sqrt (n : Real) : Real) : Complex) := by
  sorry

theorem sum_legendre (p : Nat) [Fact p.Prime] (hp : p % 2 = 1) (a : Int) :
    Finset.sum (Finset.range p) (fun k : Nat =>
        ((legendreSym p (k : Int) : Int) : Complex) *
          ex ((a : Real) * (k : Real) / (p : Real))) =
      ((legendreSym p a : Int) : Complex) * rt p := by
  sorry

theorem sum_sq_mul (p q : Nat) [Fact p.Prime] [Fact q.Prime]
    (hp : p % 2 = 1) (hq : q % 2 = 1) (hpq : Not (p = q)) :
    Finset.sum (Finset.range p) (fun j : Nat =>
        ex ((q : Real) * (j : Real) ^ 2 / (p : Real))) *
      Finset.sum (Finset.range q) (fun k : Nat =>
        ex ((p : Real) * (k : Real) ^ 2 / (q : Real))) = rt (p * q) := by
  have hp_prime : Nat.Prime p := Fact.out
  have hq_prime : Nat.Prime q := Fact.out
  have hp_pos : p ≠ 0 := hp_prime.ne_zero
  have hq_pos : q ≠ 0 := hq_prime.ne_zero
  have hpq_pos : p * q ≠ 0 := mul_ne_zero hp_pos hq_pos
  -- Rewrite LHS as sum over product
  rw [Finset.sum_mul_sum]
  have h_prod : (∑ j ∈ Finset.range p, ∑ k ∈ Finset.range q,
      ex ((q : Real) * (j : Real) ^ 2 / (p : Real)) * ex ((p : Real) * (k : Real) ^ 2 / (q : Real))) =
      ∑ jk ∈ Finset.range p ×ˢ Finset.range q,
      ex ((q : Real) * (jk.1 : Real) ^ 2 / (p : Real)) * ex ((p : Real) * (jk.2 : Real) ^ 2 / (q : Real)) := by
    rw [Finset.sum_product]
  rw [h_prod]
  -- Set up the embedding
  let F_fun : Nat × Nat → Nat := fun ⟨j, k⟩ => (q * j + p * k) % (p * q)
  have hF_inj : ∀ x ∈ Finset.range p ×ˢ Finset.range q,
                ∀ y ∈ Finset.range p ×ˢ Finset.range q,
                F_fun x = F_fun y → x = y := by
    rintro ⟨j1, k1⟩ hj1 ⟨j2, k2⟩ hj2 hF
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hj1 hj2
    have ⟨eq1, eq2⟩ := crt_map_inj p q hp_prime hq_prime hpq j1 k1 j2 k2 hj1.1 hj2.1 hj1.2 hj2.2 hF
    rw [eq1, eq2]
  let F : { x // x ∈ Finset.range p ×ˢ Finset.range q } ↪ Nat :=
    ⟨fun x => F_fun x.val, fun x y h => Subtype.ext (hF_inj x.val x.property y.val y.property h)⟩
  -- Show image of map is range (p * q)
  have h_subset : (Finset.range p ×ˢ Finset.range q).attach.map F ⊆ Finset.range (p * q) := by
    intro x hx
    rw [Finset.mem_map] at hx
    rcases hx with ⟨⟨⟨j, k⟩, hjk⟩, _, rfl⟩
    exact Finset.mem_range.mpr (Nat.mod_lt _ (Nat.pos_of_ne_zero hpq_pos))
  have h_card_map : ((Finset.range p ×ˢ Finset.range q).attach.map F).card = p * q := by
    rw [Finset.card_map, Finset.card_attach, Finset.card_product, Finset.card_range, Finset.card_range]
  have h_card_range : (Finset.range (p * q)).card = p * q := Finset.card_range (p * q)
  have h_eq : (Finset.range p ×ˢ Finset.range q).attach.map F = Finset.range (p * q) :=
    Finset.eq_of_subset_of_card_le h_subset (by rw [h_card_map, h_card_range])
  -- Now compute sum
  have h_sum_reindex :
      ∑ x ∈ Finset.range (p * q), ex ((x : Real) ^ 2 / ((p * q : Nat) : Real)) =
      ∑ jk ∈ Finset.range p ×ˢ Finset.range q,
        ex (((F_fun jk : Real) ^ 2) / ((p * q : Nat) : Real)) := by
    conv_lhs => rw [← h_eq]
    rw [Finset.sum_map]
    exact Finset.sum_attach (Finset.range p ×ˢ Finset.range q) (fun x => ex (((F_fun x : Real) ^ 2) / ((p * q : Nat) : Real)))
  have h_sum_mod_eq :
      ∑ jk ∈ Finset.range p ×ˢ Finset.range q,
        ex (((F_fun jk : Real) ^ 2) / ((p * q : Nat) : Real)) =
      ∑ jk ∈ Finset.range p ×ˢ Finset.range q,
        ex ((q : Real) * (jk.1 : Real) ^ 2 / (p : Real)) *
        ex ((p : Real) * (jk.2 : Real) ^ 2 / (q : Real)) := by
    apply Finset.sum_congr rfl
    rintro ⟨j, k⟩ _
    dsimp [F_fun]
    rw [← ex_sq_mod (p * q) hpq_pos (q * j + p * k)]
    rw [← ex_frac_decomp p q j k hp_pos hq_pos]
    exact ex_add _ _
  rw [h_sum_mod_eq] at h_sum_reindex
  -- Now connect with sum_sq (p * q)
  have hpq_odd : (p * q) % 2 = 1 := by
    rw [Nat.mul_mod, hp, hq]
  rw [← h_sum_reindex]
  exact sum_sq (p * q) hpq_odd

theorem sum_cot (p : Nat) [Fact p.Prime] (hp : p % 4 = 3) :
    Real.sqrt (p : Real) * Finset.sum (Finset.range p) (fun k : Nat =>
        ((legendreSym p (k : Int) : Int) : Real) *
          Real.cot (Real.pi * (k : Real) / (p : Real))) =
      -2 * Finset.sum (Finset.range p) (fun k : Nat =>
        (k : Real) * ((legendreSym p (k : Int) : Int) : Real)) := by
  sorry

end TuringTask
