import Mathlib

/-!
# Binary cyclotomic polynomials: the Lam-Leung expansion

Let `p ≠ q` be primes and `u < q`, `v < p` with `u p ≡ 1 (mod q)`, `v q ≡ 1 (mod p)`.
* `uv_eq`: `u p + v q = p q + 1`.
* `cyc_mul`: `Φ_{pq} (X^p - 1)(X^q - 1) = (X^{pq} - 1)(X - 1)`.
* `lam_leung`: `Φ_{pq} = ∑_{α < u, β < v} X^{αp + βq} - ∑_{u ≤ α < q, v ≤ β < p} X^{αp + βq - pq}`.
* Coordinates: `alp m = m u mod q` and `bet m = m v mod p`. Every `m` satisfies
  `alp m · p + bet m · q ≡ m (mod pq)`, and `(α, β) ↦ αp + βq` is injective on `[0, q) × [0, p)`.
* `coeff_binary`: for `m < pq` the coefficient is `1` if `alp m < u` and `bet m < v`, `-1` if
  `alp m ≥ u` and `bet m ≥ v`, and `0` otherwise; it vanishes for `m ≥ pq`.
-/

namespace TuringTask

open Polynomial Finset

/-- The first coordinate `m u mod q`. -/
def alp (q u m : ℕ) : ℕ := m * u % q

/-- The second coordinate `m v mod p`. -/
def bet (p v m : ℕ) : ℕ := m * v % p

section

variable {p q u v : ℕ} (hp : p.Prime) (hq : q.Prime) (hu : u * p % q = 1) (hv : v * q % p = 1)
  (huq : u < q) (hvp : v < p)

include hu in
lemma ne_of_inv : p ≠ q := by
  rintro rfl
  rw [Nat.mul_mod_left] at hu
  exact absurd hu (by norm_num)

include hp hq hu in
lemma coprime_pq : Nat.Coprime p q :=
  (Nat.coprime_primes hp hq).mpr (ne_of_inv hu)

include hp hq hu hv huq hvp in
lemma uv_eq : u * p + v * q = p * q + 1 := by
  have hcop := coprime_pq hp hq hu
  have h1 : u * p + v * q ≡ 1 [MOD q] := by
    unfold Nat.ModEq
    rw [Nat.add_mul_mod_self_right, hu, Nat.mod_eq_of_lt hq.one_lt]
  have h2 : u * p + v * q ≡ 1 [MOD p] := by
    unfold Nat.ModEq
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, hv, Nat.mod_eq_of_lt hp.one_lt]
  have h3 : u * p + v * q ≡ 1 [MOD p * q] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h2, h1⟩
  have hu0 : 0 < u := by
    rcases Nat.eq_zero_or_pos u with h | h
    · rw [h, zero_mul, Nat.zero_mod] at hu; exact absurd hu (by norm_num)
    · exact h
  have hv0 : 0 < v := by
    rcases Nat.eq_zero_or_pos v with h | h
    · rw [h, zero_mul, Nat.zero_mod] at hv; exact absurd hv (by norm_num)
    · exact h
  have hlt1 : u * p < p * q := by rw [mul_comm p q]; exact Nat.mul_lt_mul_of_pos_right huq hp.pos
  have hlt2 : v * q < p * q := Nat.mul_lt_mul_of_pos_right hvp hq.pos
  have hge : p + q ≤ u * p + v * q := by nlinarith
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hpq2 : 4 ≤ p * q := by nlinarith
  unfold Nat.ModEq at h3
  rw [Nat.mod_eq_of_lt (show 1 < p * q by omega)] at h3
  have hma := Nat.mod_add_div (u * p + v * q) (p * q)
  rw [h3] at hma
  generalize hM : p * q = M at *
  generalize hA : u * p = A at *
  generalize hB : v * q = B at *
  have hd2 : (A + B) / M < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hd2) with h0 | h0
  · rw [h0, mul_zero] at hma; omega
  · rw [h0, mul_one] at hma; omega

include hp in
lemma cyc_prime_mul :
    cyclotomic p ℤ * (X - 1) = X ^ p - 1 := by
  haveI := Fact.mk hp
  exact cyclotomic_prime_mul_X_sub_one ℤ p

include hp hq hu in
lemma cyc_mul : cyclotomic (p * q) ℤ * (X ^ p - 1) * (X ^ q - 1) =
    (X ^ (p * q) - 1) * (X - 1) := by
  have hne := ne_of_inv hu
  have hdiv : ¬ q ∣ p := fun h => hne ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm
  have h1 := cyclotomic_expand_eq_cyclotomic_mul hq hdiv ℤ
  have h2 := cyc_prime_mul hp
  have h3 : expand ℤ q (cyclotomic p ℤ) * (X ^ q - 1) = X ^ (p * q) - 1 := by
    have := congrArg (expand ℤ q) h2
    simp only [map_mul, map_sub, map_pow, expand_X, map_one] at this
    rw [this, ← pow_mul, mul_comm]
  calc cyclotomic (p * q) ℤ * (X ^ p - 1) * (X ^ q - 1)
      = cyclotomic (p * q) ℤ * (cyclotomic p ℤ * (X - 1)) * (X ^ q - 1) := by rw [h2]
    _ = (cyclotomic (p * q) ℤ * cyclotomic p ℤ) * (X ^ q - 1) * (X - 1) := by ring
    _ = (X ^ (p * q) - 1) * (X - 1) := by rw [← h1, h3]

include hq hu in
lemma alp_rep {α β : ℕ} (hα : α < q) : alp q u (α * p + β * q) = α := by
  unfold alp
  have hu' : u * p ≡ 1 [MOD q] := by unfold Nat.ModEq; rw [hu, Nat.mod_eq_of_lt hq.one_lt]
  have : (α * p + β * q) * u ≡ α [MOD q] := by
    calc (α * p + β * q) * u = α * (u * p) + q * (β * u) := by ring
      _ ≡ α * 1 + 0 [MOD q] := Nat.ModEq.add (Nat.ModEq.mul_left _ hu')
          (by unfold Nat.ModEq; simp [Nat.mul_mod_right])
      _ = α := by ring
  rw [this, Nat.mod_eq_of_lt hα]

include hp hv in
lemma bet_rep {α β : ℕ} (hβ : β < p) : bet p v (α * p + β * q) = β := by
  unfold bet
  have hv' : v * q ≡ 1 [MOD p] := by unfold Nat.ModEq; rw [hv, Nat.mod_eq_of_lt hp.one_lt]
  have : (α * p + β * q) * v ≡ β [MOD p] := by
    calc (α * p + β * q) * v = β * (v * q) + p * (α * v) := by ring
      _ ≡ β * 1 + 0 [MOD p] := Nat.ModEq.add (Nat.ModEq.mul_left _ hv')
          (by unfold Nat.ModEq; simp [Nat.mul_mod_right])
      _ = β := by ring
  rw [this, Nat.mod_eq_of_lt hβ]

include hp hq hu hv in
lemma E_mod (m : ℕ) : alp q u m * p + bet p v m * q ≡ m [MOD p * q] := by
  have hcop := coprime_pq hp hq hu
  have hu' : u * p ≡ 1 [MOD q] := by unfold Nat.ModEq; rw [hu, Nat.mod_eq_of_lt hq.one_lt]
  have hv' : v * q ≡ 1 [MOD p] := by unfold Nat.ModEq; rw [hv, Nat.mod_eq_of_lt hp.one_lt]
  apply (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
  constructor
  · unfold alp bet
    calc m * u % q * p + m * v % p * q ≡ 0 + m * v * q [MOD p] :=
          Nat.ModEq.add (by unfold Nat.ModEq; simp [Nat.mul_mod_left])
            (Nat.ModEq.mul_right _ (Nat.mod_modEq _ _))
      _ = m * (v * q) := by ring
      _ ≡ m * 1 [MOD p] := Nat.ModEq.mul_left _ hv'
      _ = m := by ring
  · unfold alp bet
    calc m * u % q * p + m * v % p * q ≡ m * u * p + 0 [MOD q] :=
          Nat.ModEq.add (Nat.ModEq.mul_right _ (Nat.mod_modEq _ _))
            (by unfold Nat.ModEq; simp [Nat.mul_mod_left])
      _ = m * (u * p) := by ring
      _ ≡ m * 1 [MOD q] := Nat.ModEq.mul_left _ hu'
      _ = m := by ring

include hp hq hu hv huq hvp in
lemma E_pos_lt {m : ℕ} (ha : alp q u m < u) (hb : bet p v m < v) :
    alp q u m * p + bet p v m * q + p + q ≤ p * q + 1 := by
  have h := uv_eq hp hq hu hv huq hvp
  have h1 : (alp q u m + 1) * p ≤ u * p := Nat.mul_le_mul_right _ ha
  have h2 : (bet p v m + 1) * q ≤ v * q := Nat.mul_le_mul_right _ hb
  nlinarith

include hp hq hu hv huq hvp in
lemma E_eq_of_pos {m : ℕ} (hm : m < p * q) (ha : alp q u m < u) (hb : bet p v m < v) :
    alp q u m * p + bet p v m * q = m := by
  have h := E_pos_lt hp hq hu hv huq hvp ha hb
  have := hp.two_le
  exact Nat.ModEq.eq_of_lt_of_lt (E_mod hp hq hu hv m) (by omega) hm

include hp hq hu hv huq hvp in
lemma E_eq_of_neg {m : ℕ} (hm : m < p * q) (ha : u ≤ alp q u m) (hb : v ≤ bet p v m) :
    alp q u m * p + bet p v m * q = m + p * q := by
  have h := uv_eq hp hq hu hv huq hvp
  have h1 : u * p ≤ alp q u m * p := Nat.mul_le_mul_right _ ha
  have h2 : v * q ≤ bet p v m * q := Nat.mul_le_mul_right _ hb
  have ha' : alp q u m < q := Nat.mod_lt _ hq.pos
  have hb' : bet p v m < p := Nat.mod_lt _ hp.pos
  have h3 : alp q u m * p + p ≤ q * p := by nlinarith
  have h4 : bet p v m * q + q ≤ p * q := by nlinarith
  have hmod := E_mod hp hq hu hv m
  have hge : p * q ≤ alp q u m * p + bet p v m * q := by omega
  have h5 : alp q u m * p + bet p v m * q - p * q ≡ m [MOD p * q] := by
    unfold Nat.ModEq
    rw [← Nat.add_mod_right (alp q u m * p + bet p v m * q - p * q) (p * q),
      Nat.sub_add_cancel hge]
    exact hmod
  have : alp q u m * p + bet p v m * q - p * q = m :=
    Nat.ModEq.eq_of_lt_of_lt h5 (by rw [mul_comm q p] at h3; omega) hm
  omega

/-- The double sum of an indicator. -/
lemma sum_sum_ite (S T : Finset ℕ) (a0 b0 : ℕ) (c : Prop) [Decidable c] :
    (∑ α ∈ S, ∑ β ∈ T, if α = a0 ∧ β = b0 ∧ c then (1 : ℤ) else 0) =
      if a0 ∈ S ∧ b0 ∈ T ∧ c then 1 else 0 := by
  by_cases ha : a0 ∈ S
  · rw [sum_eq_single a0]
    · by_cases hb : b0 ∈ T
      · rw [sum_eq_single b0]
        · simp [ha, hb]
        · intro b _ hb'; simp [hb']
        · intro h; exact absurd hb h
      · rw [sum_eq_zero]
        · simp [hb]
        · intro b hbT; have : b ≠ b0 := fun h => hb (h ▸ hbT); simp [this]
    · intro a _ ha'; apply sum_eq_zero; intro b _; simp [ha']
    · intro h; exact absurd ha h
  · rw [sum_eq_zero]
    · simp [ha]
    · intro a haS
      apply sum_eq_zero
      intro b _
      have : a ≠ a0 := fun h => ha (h ▸ haS)
      simp [this]

/-- The positive part of the Lam-Leung expansion. -/
noncomputable def lamPos (p q u v : ℕ) : ℤ[X] :=
  ∑ α ∈ range u, ∑ β ∈ range v, X ^ (α * p + β * q)

/-- The negative part of the Lam-Leung expansion. -/
noncomputable def lamNeg (p q u v : ℕ) : ℤ[X] :=
  ∑ α ∈ Ico u q, ∑ β ∈ Ico v p, X ^ (α * p + β * q - p * q)

include hp hq hu hv huq hvp in
theorem lam_leung : cyclotomic (p * q) ℤ = lamPos p q u v - lamNeg p q u v := by
  have huv := uv_eq hp hq hu hv huq hvp
  have hgp : ∀ n : ℕ, (∑ α ∈ range n, (X : ℤ[X]) ^ (α * p)) * (X ^ p - 1) = X ^ (n * p) - 1 := by
    intro n
    have := geom_sum_mul ((X : ℤ[X]) ^ p) n
    simp only [← pow_mul] at this
    rw [show n * p = p * n by ring]
    convert this using 2
    apply sum_congr rfl; intro α _; rw [mul_comm]
  have hgq : ∀ n : ℕ, (∑ β ∈ range n, (X : ℤ[X]) ^ (β * q)) * (X ^ q - 1) = X ^ (n * q) - 1 := by
    intro n
    have := geom_sum_mul ((X : ℤ[X]) ^ q) n
    simp only [← pow_mul] at this
    rw [show n * q = q * n by ring]
    convert this using 2
    apply sum_congr rfl; intro β _; rw [mul_comm]
  have hpos : lamPos p q u v * (X ^ p - 1) * (X ^ q - 1) =
      (X ^ (u * p) - 1) * (X ^ (v * q) - 1) := by
    unfold lamPos
    have : (∑ α ∈ range u, ∑ β ∈ range v, (X : ℤ[X]) ^ (α * p + β * q)) =
        (∑ α ∈ range u, X ^ (α * p)) * (∑ β ∈ range v, X ^ (β * q)) := by
      rw [sum_mul_sum]; apply sum_congr rfl; intro α _; apply sum_congr rfl; intro β _
      rw [pow_add]
    rw [this, ← hgp, ← hgq]; ring
  have hneg : X ^ (p * q) * lamNeg p q u v * (X ^ p - 1) * (X ^ q - 1) =
      (X ^ (q * p) - X ^ (u * p)) * (X ^ (p * q) - X ^ (v * q)) := by
    unfold lamNeg
    have : X ^ (p * q) * (∑ α ∈ Ico u q, ∑ β ∈ Ico v p, (X : ℤ[X]) ^ (α * p + β * q - p * q)) =
        (∑ α ∈ Ico u q, X ^ (α * p)) * (∑ β ∈ Ico v p, X ^ (β * q)) := by
      rw [mul_sum, sum_mul_sum]; apply sum_congr rfl; intro α hα; rw [mul_sum]
      apply sum_congr rfl; intro β hβ
      rw [mem_Ico] at hα hβ
      have h1 : u * p ≤ α * p := Nat.mul_le_mul_right _ hα.1
      have h2 : v * q ≤ β * q := Nat.mul_le_mul_right _ hβ.1
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    have e1 : (∑ α ∈ Ico u q, (X : ℤ[X]) ^ (α * p)) * (X ^ p - 1) = X ^ (q * p) - X ^ (u * p) := by
      rw [sum_Ico_eq_sub _ huq.le, sub_mul, hgp, hgp]; ring
    have e2 : (∑ β ∈ Ico v p, (X : ℤ[X]) ^ (β * q)) * (X ^ q - 1) = X ^ (p * q) - X ^ (v * q) := by
      rw [sum_Ico_eq_sub _ hvp.le, sub_mul, hgq, hgq]; ring
    rw [this, ← e1, ← e2]; ring
  have hrel : (X : ℤ[X]) ^ (u * p) * X ^ (v * q) = X ^ (p * q) * X := by
    rw [← pow_add, huv, pow_succ]
  have hC := cyc_mul hp hq hu
  have hne : (X : ℤ[X]) ^ (p * q) * (X ^ p - 1) * (X ^ q - 1) ≠ 0 := by
    have h1 : (X : ℤ[X]) ^ p - 1 ≠ 0 := by
      have := X_pow_sub_C_ne_zero hp.pos (1 : ℤ); simpa using this
    have h2 : (X : ℤ[X]) ^ q - 1 ≠ 0 := by
      have := X_pow_sub_C_ne_zero hq.pos (1 : ℤ); simpa using this
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ X_ne_zero) h1) h2
  apply mul_right_cancel₀ hne
  have key : (lamPos p q u v - lamNeg p q u v) * (X ^ (p * q) * (X ^ p - 1) * (X ^ q - 1)) =
      X ^ (p * q) * ((X ^ (p * q) - 1) * (X - 1)) := by
    have : (lamPos p q u v - lamNeg p q u v) * (X ^ (p * q) * (X ^ p - 1) * (X ^ q - 1)) =
        X ^ (p * q) * (lamPos p q u v * (X ^ p - 1) * (X ^ q - 1)) -
          X ^ (p * q) * lamNeg p q u v * (X ^ p - 1) * (X ^ q - 1) := by ring
    rw [this, hpos, hneg, mul_comm q p]
    linear_combination (X ^ (p * q) - (1 : ℤ[X])) * hrel
  rw [key, ← hC]; ring

include hp hq hu hv huq hvp in
lemma coeff_lamPos (m : ℕ) : (lamPos p q u v).coeff m =
    if m < p * q ∧ alp q u m < u ∧ bet p v m < v then 1 else 0 := by
  unfold lamPos
  simp only [finsetSum_coeff, coeff_X_pow]
  have h : ∀ α ∈ range u, ∀ β ∈ range v, (m = α * p + β * q) ↔
      (α = alp q u m ∧ β = bet p v m ∧ alp q u m * p + bet p v m * q = m) := by
    intro α hα β hβ
    rw [mem_range] at hα hβ
    constructor
    · rintro rfl
      rw [alp_rep hq hu (by omega), bet_rep hp hv (by omega)]
      exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨rfl, rfl, h⟩; exact h.symm
  rw [sum_congr rfl (fun α hα => sum_congr rfl (fun β hβ => if_congr (h α hα β hβ) rfl rfl)),
    sum_sum_ite]
  apply if_congr _ rfl rfl
  rw [mem_range, mem_range]
  constructor
  · rintro ⟨ha, hb, hE⟩
    have := E_pos_lt hp hq hu hv huq hvp ha hb
    exact ⟨by omega, ha, hb⟩
  · rintro ⟨hm, ha, hb⟩
    exact ⟨ha, hb, E_eq_of_pos hp hq hu hv huq hvp hm ha hb⟩

lemma alp_add_mul (m : ℕ) : alp q u (m + p * q) = alp q u m := by
  unfold alp
  rw [show (m + p * q) * u = m * u + q * (p * u) by ring, Nat.add_mul_mod_self_left]

lemma bet_add_mul (m : ℕ) : bet p v (m + p * q) = bet p v m := by
  unfold bet
  rw [show (m + p * q) * v = m * v + p * (q * v) by ring, Nat.add_mul_mod_self_left]

include hp hq hu hv huq hvp in
lemma coeff_lamNeg (m : ℕ) : (lamNeg p q u v).coeff m =
    if m < p * q ∧ u ≤ alp q u m ∧ v ≤ bet p v m then 1 else 0 := by
  have huv := uv_eq hp hq hu hv huq hvp
  unfold lamNeg
  simp only [finsetSum_coeff, coeff_X_pow]
  have h : ∀ α ∈ Ico u q, ∀ β ∈ Ico v p, (m = α * p + β * q - p * q) ↔
      (α = alp q u m ∧ β = bet p v m ∧ alp q u m * p + bet p v m * q = m + p * q) := by
    intro α hα β hβ
    rw [mem_Ico] at hα hβ
    have h1 : u * p ≤ α * p := Nat.mul_le_mul_right _ hα.1
    have h2 : v * q ≤ β * q := Nat.mul_le_mul_right _ hβ.1
    constructor
    · intro hm
      have hm' : m + p * q = α * p + β * q := by omega
      rw [← alp_add_mul, ← bet_add_mul, hm', alp_rep hq hu hα.2, bet_rep hp hv hβ.2]
      exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨rfl, rfl, h⟩; omega
  rw [sum_congr rfl (fun α hα => sum_congr rfl (fun β hβ => if_congr (h α hα β hβ) rfl rfl)),
    sum_sum_ite]
  apply if_congr _ rfl rfl
  rw [mem_Ico, mem_Ico]
  have ha' : alp q u m < q := Nat.mod_lt _ hq.pos
  have hb' : bet p v m < p := Nat.mod_lt _ hp.pos
  constructor
  · rintro ⟨⟨ha, -⟩, ⟨hb, -⟩, hE⟩
    have h3 : alp q u m * p + p ≤ q * p := by nlinarith
    have h4 : bet p v m * q + q ≤ p * q := by nlinarith
    rw [mul_comm q p] at h3
    exact ⟨by omega, ha, hb⟩
  · rintro ⟨hm, ha, hb⟩
    exact ⟨⟨ha, ha'⟩, ⟨hb, hb'⟩, E_eq_of_neg hp hq hu hv huq hvp hm ha hb⟩

include hp hq hu hv huq hvp in
/-- The coefficients of `Φ_{pq}` in the coordinates `alp`, `bet`. -/
theorem coeff_binary (m : ℕ) : (cyclotomic (p * q) ℤ).coeff m =
    (if m < p * q ∧ alp q u m < u ∧ bet p v m < v then 1 else 0) -
      (if m < p * q ∧ u ≤ alp q u m ∧ v ≤ bet p v m then 1 else 0) := by
  rw [lam_leung hp hq hu hv huq hvp, coeff_sub, coeff_lamPos hp hq hu hv huq hvp,
    coeff_lamNeg hp hq hu hv huq hvp]

include hp hq hu hv huq hvp in
lemma coeff_binary_eq_one_iff (m : ℕ) : (cyclotomic (p * q) ℤ).coeff m = 1 ↔
    m < p * q ∧ alp q u m < u ∧ bet p v m < v := by
  rw [coeff_binary hp hq hu hv huq hvp]
  split_ifs with h1 h2 h2 <;> omega

include hp hq hu hv huq hvp in
lemma coeff_binary_cases (m : ℕ) : (cyclotomic (p * q) ℤ).coeff m = 0 ∨
    (cyclotomic (p * q) ℤ).coeff m = 1 ∨ (cyclotomic (p * q) ℤ).coeff m = -1 := by
  rw [coeff_binary hp hq hu hv huq hvp]
  split_ifs <;> simp

include hp hq hu hv huq hvp in
lemma coeff_binary_closed {m : ℕ} (hm : m < p * q) : (cyclotomic (p * q) ℤ).coeff m =
    (if alp q u m < u then 1 else 0) + (if bet p v m < v then 1 else 0) - 1 := by
  rw [coeff_binary hp hq hu hv huq hvp]
  by_cases ha : alp q u m < u <;> by_cases hb : bet p v m < v <;> simp [hm, ha, hb]

include hp hq hu hv huq hvp in
lemma coeff_binary_of_ge {m : ℕ} (hm : p * q ≤ m) : (cyclotomic (p * q) ℤ).coeff m = 0 := by
  rw [coeff_binary hp hq hu hv huq hvp]
  simp [show ¬ m < p * q by omega]

end

end TuringTask
