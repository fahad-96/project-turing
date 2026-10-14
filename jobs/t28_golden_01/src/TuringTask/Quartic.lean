import Mathlib
import TuringTask.Core

/-!
# When is `2` a fourth power modulo `p`

* `key1` (Dirichlet): for `p = 1 (mod 8)` and `p = A^2 + B^2` with `A` odd, put `i = A / B` in
  `ZMod p`. Then `i^2 = -1` and `(A + B)^2 = 2 i B^2`, so `core_u` gives
  `(2 i) ^ ((p - 1) / 4) J(B | p) = J(A + B | p)`. Here `J(B | p) = 1` (`J_d`),
  `J(A + B | p) = J(2 | A + B)` because `2 p = (A + B)^2 + (A - B)^2`, and
  `i ^ ((p - 1) / 4) = (-1) ^ ((p - 1) / 8)`. A table modulo `16` then shows
  `2 ^ ((p - 1) / 4) = 1` exactly when `8 ∣ B`.
* `two_quartic_iff` (theorem 1): with Fermat's `p = A^2 + B^2` (`Nat.Prime.sq_add_sq`).
* `key3`: for `p = 1 (mod 8)` and `e^2 = p + 2 f^2`, `core_u` with `2 = (e / f)^2` gives
  `2 ^ ((p - 1) / 4) = J(-2 | e)`, which is `1` exactly for `e = 1, 3 (mod 8)`.
* `two_quartic_iff'` (theorem 3): for `p = 7 (mod 8)` every square is a fourth power
  (`s ^ ((p + 1) / 4)`), and the unit step `(e, f) ↦ (3 e + 4 f, 2 e + 3 f)` moves `e` into the
  classes `1, 3 (mod 8)`; for `p = 3, 5 (mod 8)` both sides fail modulo `8`.
-/

namespace TuringTask

lemma two_ne_zero_zmod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  haveI := Fact.mk hp
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
  exact hp2 this

lemma neg_one_pow_eighth {p : ℕ} (hp8 : p % 8 = 1) :
    ((-1 : ZMod p)) ^ ((p - 1) / 8) = ((if p % 16 = 1 then 1 else -1 : ℤ) : ZMod p) := by
  split_ifs with h
  · rw [Even.neg_one_pow ⟨(p - 1) / 16, by omega⟩]; simp
  · rw [Odd.neg_one_pow ⟨(p - 1) / 16, by omega⟩]; simp

lemma J_two_eq {m : ℕ} (hm : m % 2 = 1) :
    jacobiSym 2 m = if m % 8 = 1 ∨ m % 8 = 7 then 1 else -1 := by
  rw [jacobiSym.at_two (Nat.odd_iff.mpr hm), ZMod.χ₈_nat_eq_if_mod_eight]
  simp [hm]

lemma J_neg_two_eq {m : ℕ} (hm : m % 2 = 1) :
    jacobiSym (-2) m = if m % 8 = 1 ∨ m % 8 = 3 then 1 else -1 := by
  rw [jacobiSym.at_neg_two (Nat.odd_iff.mpr hm), ZMod.χ₈'_nat_eq_if_mod_eight]
  simp [hm]

lemma J_two_p {p : ℕ} (hp8 : p % 8 = 1) : jacobiSym 2 p = 1 := by
  rw [J_two_eq (by omega), if_pos (Or.inl hp8)]

lemma pm_one_ite (P : Prop) [Decidable P] : ((if P then 1 else -1 : ℤ)) = 1 ∨
    ((if P then 1 else -1 : ℤ)) = -1 := by
  split_ifs <;> simp

lemma gcd_sub_add {A B : ℕ} (h : Nat.Coprime A B) (hodd : (A + B) % 2 = 1) :
    Int.gcd ((A : ℤ) - B) ((A + B : ℕ) : ℤ) = 1 := by
  set g := Int.gcd ((A : ℤ) - B) ((A + B : ℕ) : ℤ)
  have h1 : (g : ℤ) ∣ (A : ℤ) - B := Int.gcd_dvd_left _ _
  have h2 : (g : ℤ) ∣ ((A + B : ℕ) : ℤ) := Int.gcd_dvd_right _ _
  have h2n : g ∣ A + B := Int.natCast_dvd_natCast.mp h2
  have hA : g ∣ 2 * A := by
    have : (g : ℤ) ∣ ((2 * A : ℕ) : ℤ) := by
      rw [show ((2 * A : ℕ) : ℤ) = ((A : ℤ) - B) + ((A + B : ℕ) : ℤ) by push_cast; ring]
      exact dvd_add h1 h2
    exact Int.natCast_dvd_natCast.mp this
  have hB : g ∣ 2 * B := by
    have : (g : ℤ) ∣ ((2 * B : ℕ) : ℤ) := by
      rw [show ((2 * B : ℕ) : ℤ) = ((A + B : ℕ) : ℤ) - ((A : ℤ) - B) by push_cast; ring]
      exact dvd_sub h2 h1
    exact Int.natCast_dvd_natCast.mp this
  have hg2 : Nat.Coprime g 2 := by
    rw [Nat.coprime_two_right]
    rcases Nat.even_or_odd g with ⟨r, hr⟩ | ho
    · exfalso
      have : 2 ∣ A + B := (show 2 ∣ g from ⟨r, by omega⟩).trans h2n
      omega
    · exact ho
  have hgA := hg2.dvd_of_dvd_mul_left hA
  have hgB := hg2.dvd_of_dvd_mul_left hB
  exact Nat.eq_one_of_dvd_one (h ▸ Nat.dvd_gcd hgA hgB)

lemma table1 : ∀ a, a < 16 → ∀ b, b < 16 → a % 2 = 1 → (a ^ 2 + b ^ 2) % 8 = 1 →
    ((if (a ^ 2 + b ^ 2) % 16 = 1 then 1 else -1 : ℤ) *
      (if (a + b) % 8 = 1 ∨ (a + b) % 8 = 7 then 1 else -1) = 1 ↔ b % 8 = 0) := by
  decide

/-- Dirichlet's computation of `2 ^ ((p - 1) / 4)` from `p = A^2 + B^2`. -/
lemma key1 {p A B : ℕ} (hp : p.Prime) (hp8 : p % 8 = 1) (h : p = A ^ 2 + B ^ 2)
    (hA : A % 2 = 1) : (2 : ZMod p) ^ ((p - 1) / 4) = 1 ↔ B % 8 = 0 := by
  haveI := Fact.mk hp
  have hp2 : p ≠ 2 := by omega
  have hp4 : p % 4 = 1 := by omega
  have hpz : (p : ℤ) = (A : ℤ) ^ 2 + 1 * (B : ℤ) ^ 2 := by rw [h]; push_cast; ring
  have hcop : Nat.Coprime A B := coprime_of_rep hp hpz
  have hB0 : 0 < B := by
    rcases Nat.eq_zero_or_pos B with hB | hB
    · exfalso
      rw [hB] at h
      have := coprime_of_rep (c := A) (d := A) (q := 0) hp (by rw [h]; push_cast; ring)
      simp at this
      rw [this] at h
      simp at h
      exact Nat.not_prime_one (h ▸ hp)
    · exact hB
  have hBp : ((B : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    have : (p : ℤ) ∣ B := int_dvd_of_zmod hz
    have := Int.le_of_dvd (by exact_mod_cast hB0) this
    have : (A : ℤ) ^ 2 ≥ 1 := by
      have : 1 ≤ A := by omega
      exact_mod_cast Nat.one_le_pow _ _ this
    nlinarith
  have hzero : ((A : ℤ) : ZMod p) ^ 2 + ((B : ℤ) : ZMod p) ^ 2 = 0 := by
    have : ((p : ℤ) : ZMod p) = 0 := by simp
    rw [hpz] at this; push_cast at this ⊢; linear_combination this
  set i : ZMod p := ((A : ℤ) : ZMod p) / ((B : ℤ) : ZMod p)
  have hiA : ((A : ℤ) : ZMod p) = i * ((B : ℤ) : ZMod p) := by
    simp only [i]; field_simp
  have hi2 : i ^ 2 = -1 := by
    have : (i * ((B : ℤ) : ZMod p)) ^ 2 + ((B : ℤ) : ZMod p) ^ 2 = 0 := by rw [← hiA]; exact hzero
    have hB2 : ((B : ℤ) : ZMod p) ^ 2 ≠ 0 := pow_ne_zero 2 hBp
    have : (i ^ 2 + 1) * ((B : ℤ) : ZMod p) ^ 2 = 0 := by linear_combination this
    rcases mul_eq_zero.mp this with h1 | h1
    · linear_combination h1
    · exact absurd h1 hB2
  have hsq : (((A + B : ℕ) : ℤ) : ZMod p) ^ 2 = (2 * i) * ((B : ℤ) : ZMod p) ^ 2 := by
    push_cast
    rw [show ((A : ZMod p) + B) ^ 2 = (A : ZMod p) ^ 2 + B ^ 2 + 2 * A * B by ring]
    have hz' : (A : ZMod p) ^ 2 + (B : ZMod p) ^ 2 = 0 := by exact_mod_cast hzero
    have hiA' : (A : ZMod p) = i * B := by exact_mod_cast hiA
    rw [hz', hiA']; ring
  have hcore := core_u hp hp4 hsq
  -- `J(B | p) = 1`
  obtain ⟨v, B₀, hB₀, hBv⟩ := Nat.exists_eq_two_pow_mul_odd hB0.ne'
  have hJB : jacobiSym (B : ℤ) p = 1 := by
    rw [J_d hp4 hpz hcop hBv (Nat.odd_iff.mp hB₀), J_two_p hp8, one_pow]
  -- `J(A + B | p) = J(2 | A + B)`
  have hAB : (A + B) % 2 = 1 := by
    have : B % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one B with hb | hb
      · exact hb
      · exfalso
        have h1 : A ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hA]
        have h2 : B ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hb]
        omega
    omega
  have hJAB : jacobiSym ((A + B : ℕ) : ℤ) p = jacobiSym 2 (A + B) := by
    rw [← jacobiSym.quadratic_reciprocity_one_mod_four hp4 (Nat.odd_iff.mpr hAB)]
    have h2p : jacobiSym (2 * p) (A + B) = 1 := by
      rw [jacobiSym.mod_left' (a₂ := ((A : ℤ) - B) ^ 2) (by
        rw [show (2 * (p : ℤ)) = ((A : ℤ) - B) ^ 2 + ((A + B : ℕ) : ℤ) * (A + B) by
          rw [h]; push_cast; ring, Int.add_mul_emod_self_left])]
      exact jacobiSym.sq_one' (gcd_sub_add hcop hAB)
    rw [jacobiSym.mul_left] at h2p
    have hsq2 : jacobiSym 2 (A + B) ^ 2 = 1 := by
      apply jacobiSym.sq_one
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, Int.gcd_natCast_natCast]
      exact Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hAB)
    calc jacobiSym (p : ℤ) (A + B) = jacobiSym 2 (A + B) ^ 2 * jacobiSym (p : ℤ) (A + B) := by
          rw [hsq2, one_mul]
      _ = jacobiSym 2 (A + B) := by rw [sq, mul_assoc, h2p, mul_one]
  have hik : i ^ ((p - 1) / 4) = (-1 : ZMod p) ^ ((p - 1) / 8) := by
    rw [show (p - 1) / 4 = 2 * ((p - 1) / 8) by omega, pow_mul, hi2]
  rw [hJB, hJAB, mul_pow, hik, neg_one_pow_eighth hp8] at hcore
  push_cast at hcore
  have hs := pm_one_ite (p % 16 = 1)
  have h2 : (2 : ZMod p) ^ ((p - 1) / 4) =
      (((if p % 16 = 1 then 1 else -1 : ℤ) * jacobiSym 2 (A + B) : ℤ) : ZMod p) := by
    push_cast
    rw [← hcore]
    have : ((if p % 16 = 1 then (1 : ZMod p) else -1)) ^ 2 = 1 := by split_ifs <;> simp
    linear_combination (-(2 : ZMod p) ^ ((p - 1) / 4)) * this
  rw [h2, cast_pm_one hp hp2 (by
    rw [J_two_eq hAB]; rcases hs with h1 | h1 <;> rw [h1] <;> split_ifs <;> simp)]
  rw [J_two_eq hAB]
  have hp16 : p % 16 = ((A % 16) ^ 2 + (B % 16) ^ 2) % 16 := by
    rw [h, Nat.add_mod, Nat.pow_mod, Nat.pow_mod (B)]
    omega
  have hab8 : (A + B) % 8 = (A % 16 + B % 16) % 8 := by omega
  have hb8 : B % 8 = B % 16 % 8 := by omega
  have hA16 : (A % 16) % 2 = 1 := by omega
  have hp8' : ((A % 16) ^ 2 + (B % 16) ^ 2) % 8 = 1 := by
    have : p % 8 = p % 16 % 8 := by omega
    rw [hp16] at this; omega
  rw [hp16, hab8, hb8]
  exact table1 _ (Nat.mod_lt A (by norm_num)) _ (Nat.mod_lt B (by norm_num)) hA16 hp8'

lemma sq_mod8 (n : ℕ) : n ^ 2 % 8 = 0 ∨ n ^ 2 % 8 = 1 ∨ n ^ 2 % 8 = 4 := by
  rw [Nat.pow_mod]
  have := Nat.mod_lt n (show 8 > 0 by norm_num)
  generalize n % 8 = r at *
  interval_cases r <;> simp

lemma sq_mod8_odd {n : ℕ} (h : n % 2 = 1) : n ^ 2 % 8 = 1 := by
  rw [Nat.pow_mod]
  have := Nat.mod_lt n (show 8 > 0 by norm_num)
  have h' : n % 8 % 2 = 1 := by omega
  generalize n % 8 = r at *
  interval_cases r <;> simp_all

lemma sq_mod16_eq (n : ℕ) : n ^ 2 % 16 = (n % 16) ^ 2 % 16 := Nat.pow_mod n 2 16

theorem two_quartic_iff {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    (∃ x : ZMod p, x ^ 4 = 2) ↔ ∃ a b : ℕ, p = a ^ 2 + 64 * b ^ 2 := by
  haveI := Fact.mk hp
  have hp2 : p ≠ 2 := by omega
  by_cases h8 : p % 8 = 1
  · rw [pow4_iff hp hp4 (two_ne_zero_zmod hp hp2)]
    constructor
    · intro h2
      obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha
      · have hb : b % 2 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one b with hb | hb
          · exfalso
            have h1 : a ^ 2 % 2 = 0 := by rw [Nat.pow_mod, ha]
            have h3 : b ^ 2 % 2 = 0 := by rw [Nat.pow_mod, hb]
            omega
          · exact hb
        have := (key1 hp h8 (by rw [← hab]; ring) hb).mp h2
        exact ⟨b, a / 8, by
          have : a = 8 * (a / 8) := by omega
          rw [← hab]; nth_rewrite 1 [this]; ring⟩
      · have := (key1 hp h8 hab.symm ha).mp h2
        exact ⟨a, b / 8, by
          have : b = 8 * (b / 8) := by omega
          rw [← hab]; nth_rewrite 1 [this]; ring⟩
    · rintro ⟨a, b, hab⟩
      have ha : a % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one a with ha | ha
        · exfalso
          have h1 : a ^ 2 % 2 = 0 := by rw [Nat.pow_mod, ha]
          omega
        · exact ha
      exact (key1 hp h8 (B := 8 * b) (by rw [hab]; ring) ha).mpr (by omega)
  · constructor
    · rintro ⟨x, hx⟩
      have : IsSquare (2 : ZMod p) := ⟨x ^ 2, by rw [← hx]; ring⟩
      have := (ZMod.exists_sq_eq_two_iff hp2).mp this
      omega
    · rintro ⟨a, b, hab⟩
      have := sq_mod8 a
      omega

/-- For `p = 1 (mod 8)` and `e^2 = p + 2 f^2`: `2 ^ ((p - 1) / 4) = J(-2 | e)`. -/
lemma key3 {p e f : ℕ} (hp : p.Prime) (hp8 : p % 8 = 1) (h : e ^ 2 = p + 2 * f ^ 2) :
    (2 : ZMod p) ^ ((p - 1) / 4) = 1 ↔ e % 8 = 1 ∨ e % 8 = 3 := by
  haveI := Fact.mk hp
  have hp2 : p ≠ 2 := by omega
  have hp4 : p % 4 = 1 := by omega
  have hpz : (p : ℤ) = (e : ℤ) ^ 2 + (-2) * (f : ℤ) ^ 2 := by
    have : ((e ^ 2 : ℕ) : ℤ) = ((p + 2 * f ^ 2 : ℕ) : ℤ) := by rw [h]
    push_cast at this; linarith
  have hcop : Nat.Coprime e f := coprime_of_rep hp hpz
  have he : e % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one e with he | he
    · exfalso
      have h1 : e ^ 2 % 2 = 0 := by rw [Nat.pow_mod, he]
      omega
    · exact he
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with hf | hf
    · exfalso
      have he1 : e = 1 := (Nat.coprime_zero_right e).mp (hf ▸ hcop)
      rw [he1, hf] at h
      have := hp.two_le
      norm_num at h
      omega
    · exact hf
  have hsq : ((e : ℤ) : ZMod p) ^ 2 = (2 : ZMod p) * ((f : ℤ) : ZMod p) ^ 2 := by
    have : ((p : ℤ) : ZMod p) = 0 := by simp
    rw [hpz] at this; push_cast at this ⊢; linear_combination this
  have hcore := core_u hp hp4 hsq
  obtain ⟨v, f₀, hf₀, hfv⟩ := Nat.exists_eq_two_pow_mul_odd hf0.ne'
  rw [J_d hp4 hpz hcop hfv (Nat.odd_iff.mp hf₀), J_two_p hp8, one_pow, J_c hp4 he hpz hcop,
    J_neg_two_eq he] at hcore
  push_cast at hcore
  rw [mul_one] at hcore
  rw [hcore]
  have hpm : (if e % 8 = 1 ∨ e % 8 = 3 then (1 : ZMod p) else -1) =
      ((if e % 8 = 1 ∨ e % 8 = 3 then 1 else -1 : ℤ) : ZMod p) := by split_ifs <;> simp
  rw [hpm, cast_pm_one hp hp2 (pm_one_ite _)]
  split_ifs with hc <;> simp [hc]

lemma unit_step {p e f : ℕ} (h : e ^ 2 = p + 2 * f ^ 2) :
    (3 * e + 4 * f) ^ 2 = p + 2 * (2 * e + 3 * f) ^ 2 := by
  have h' : (e : ℤ) ^ 2 = p + 2 * f ^ 2 := by exact_mod_cast h
  have : ((3 * e + 4 * f : ℕ) : ℤ) ^ 2 = p + 2 * ((2 * e + 3 * f : ℕ) : ℤ) ^ 2 := by
    push_cast; linear_combination h'
  exact_mod_cast this

theorem two_quartic_iff' {p : ℕ} (hp : p.Prime) (hp2 : p % 2 = 1) :
    (∃ x : ZMod p, x ^ 4 = 2) ↔ ∃ e f : ℕ, e ^ 2 = p + 2 * f ^ 2 ∧ (e % 8 = 1 ∨ e % 8 = 3) := by
  haveI := Fact.mk hp
  have hp2' : p ≠ 2 := by omega
  rcases (by omega : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7) with h8 | h8 | h8 | h8
  · rw [pow4_iff hp (by omega) (two_ne_zero_zmod hp hp2')]
    constructor
    · intro h2
      obtain ⟨e, f, hef⟩ := rep_minus_two hp ((ZMod.exists_sq_eq_two_iff hp2').mpr (Or.inl h8))
      exact ⟨e, f, hef, (key3 hp h8 hef).mp h2⟩
    · rintro ⟨e, f, hef, he⟩
      exact (key3 hp h8 hef).mpr he
  · constructor
    · rintro ⟨x, hx⟩
      have := (ZMod.exists_sq_eq_two_iff hp2').mp ⟨x ^ 2, by rw [← hx]; ring⟩
      omega
    · rintro ⟨e, f, hef, -⟩
      have h1 := sq_mod8 e
      have h2 := sq_mod8 f
      omega
  · constructor
    · rintro ⟨x, hx⟩
      have := (ZMod.exists_sq_eq_two_iff hp2').mp ⟨x ^ 2, by rw [← hx]; ring⟩
      omega
    · rintro ⟨e, f, hef, -⟩
      have h1 := sq_mod8 e
      have h2 := sq_mod8 f
      omega
  · constructor
    · intro _
      obtain ⟨e, f, hef⟩ := rep_minus_two hp ((ZMod.exists_sq_eq_two_iff hp2').mpr (Or.inr h8))
      have he : e % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one e with he | he
        · exfalso
          have h1 : e ^ 2 % 2 = 0 := by rw [Nat.pow_mod, he]
          omega
        · exact he
      have hf : f % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one f with hf | hf
        · exfalso
          have h1 := sq_mod8_odd he
          have h2 : f ^ 2 % 4 = 0 := by
            rcases (by omega : f % 4 = 0 ∨ f % 4 = 2) with h4 | h4 <;>
              rw [Nat.pow_mod, h4]
          omega
        · exact hf
      by_cases hc : e % 8 = 1 ∨ e % 8 = 3
      · exact ⟨e, f, hef, hc⟩
      · refine ⟨3 * e + 4 * f, 2 * e + 3 * f, unit_step hef, ?_⟩
        obtain ⟨m, rfl⟩ : ∃ m, f = 2 * m + 1 := ⟨f / 2, by omega⟩
        rcases (by omega : e % 8 = 5 ∨ e % 8 = 7) with h5 | h5
        · obtain ⟨k, rfl⟩ : ∃ k, e = 8 * k + 5 := ⟨e / 8, by omega⟩
          right; omega
        · obtain ⟨k, rfl⟩ : ∃ k, e = 8 * k + 7 := ⟨e / 8, by omega⟩
          left; omega
    · intro _
      obtain ⟨s, hs⟩ := (ZMod.exists_sq_eq_two_iff hp2').mpr (Or.inr h8)
      refine ⟨s ^ ((p + 1) / 4), ?_⟩
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact two_ne_zero_zmod hp hp2' (by rw [hs]; ring)
      rw [← pow_mul, show (p + 1) / 4 * 4 = (p - 1) + 2 by omega, pow_add,
        ZMod.pow_card_sub_one_eq_one hs0, hs]
      ring

end TuringTask
