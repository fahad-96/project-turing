import Mathlib
import TuringTask.Jacobi

/-!
# When is `-4` an eighth power modulo `p` (theorems 2 and 5)

* `key2`: for `p = 1 (mod 8)` and `p = c^2 + 2 d^2`, `core_u` with `-2 = (c / d)^2` gives
  `2 ^ ((p - 1) / 4) = J(2 | c)`, and
  `(-4) ^ ((p - 1) / 8) = (-1) ^ ((p - 1) / 8) 2 ^ ((p - 1) / 4)`. A table modulo `16` shows
  that this is `1` exactly when `4 ∣ d`.
* `octic_neg_four` (theorem 2): with the representation `p = c^2 + 2 d^2` from `rep_plus_two`.
* For theorem 5 fix `z` with `z^4 = -1`, so `i = z^2` is a square root of `-1` and
  `s₀ = z - z^3` is a square root of `2`. Then `(1 + z)^2 = (1 + i)(1 + s₀)` and
  `(1 + z^3)^2 = z^6 (1 + i)(1 - s₀)`, so some `1 + s` with `s^2 = 2` is a square exactly when
  `1 + i` is (`sqrt_two_side`). Since `(1 + i)^4 = -4` and every fourth root of unity
  `±1, ±i` is a square, `1 + i` is a square exactly when `-4` is an eighth power
  (`octic_side`).
-/

namespace TuringTask

lemma table2 : ∀ a, a < 16 → ∀ b, b < 16 → a % 2 = 1 → (a ^ 2 + 2 * b ^ 2) % 8 = 1 →
    ((if (a ^ 2 + 2 * b ^ 2) % 16 = 1 then 1 else -1 : ℤ) *
      (if a % 8 = 1 ∨ a % 8 = 7 then 1 else -1) = 1 ↔ b % 4 = 0) := by
  decide

/-- The eighth-power character of `-4` from `p = c^2 + 2 d^2`. -/
lemma key2 {p c d : ℕ} (hp : p.Prime) (hp8 : p % 8 = 1) (h : p = c ^ 2 + 2 * d ^ 2) :
    (-4 : ZMod p) ^ ((p - 1) / 8) = 1 ↔ d % 4 = 0 := by
  haveI := Fact.mk hp
  have hp2 : p ≠ 2 := by omega
  have hp4 : p % 4 = 1 := by omega
  have hc : c % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one c with hc | hc
    · exfalso
      have : c ^ 2 % 2 = 0 := by rw [Nat.pow_mod, hc]
      omega
    · exact hc
  have hpz : (p : ℤ) = (c : ℤ) ^ 2 + 2 * (d : ℤ) ^ 2 := by rw [h]; push_cast; ring
  have hcd : Nat.Coprime c d := coprime_of_rep hp hpz
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exfalso
      rw [h0] at hcd
      have hc1 : c = 1 := (Nat.coprime_zero_right c).mp hcd
      rw [hc1, h0] at h
      have := hp.two_le
      norm_num at h
      omega
    · exact h0
  have hsq : ((c : ℤ) : ZMod p) ^ 2 = (-2 : ZMod p) * ((d : ℤ) : ZMod p) ^ 2 := by
    have : ((p : ℤ) : ZMod p) = 0 := by simp
    rw [hpz] at this; push_cast at this ⊢; linear_combination this
  have hcore := core_u hp hp4 hsq
  obtain ⟨v, d₀, hd₀, hdv⟩ := Nat.exists_eq_two_pow_mul_odd hd0.ne'
  rw [J_d hp4 hpz hcd hdv (Nat.odd_iff.mp hd₀), J_two_p hp8, one_pow, J_c hp4 hc hpz hcd,
    J_two_eq hc] at hcore
  push_cast at hcore
  have hn := neg_one_pow_eighth hp8
  push_cast at hn
  have he : (-4 : ZMod p) ^ ((p - 1) / 8) =
      (-1 : ZMod p) ^ ((p - 1) / 8) * (-2 : ZMod p) ^ ((p - 1) / 4) := by
    rw [show (p - 1) / 4 = 2 * ((p - 1) / 8) by omega, pow_mul, ← mul_pow]
    norm_num
  have h2 : (-4 : ZMod p) ^ ((p - 1) / 8) =
      (((if p % 16 = 1 then 1 else -1 : ℤ) * (if c % 8 = 1 ∨ c % 8 = 7 then 1 else -1) : ℤ) :
        ZMod p) := by
    push_cast
    linear_combination he + (-2 : ZMod p) ^ ((p - 1) / 4) * hn +
      (if p % 16 = 1 then (1 : ZMod p) else -1) * hcore
  have hs1 := pm_one_ite (p % 16 = 1)
  have hs2 := pm_one_ite (c % 8 = 1 ∨ c % 8 = 7)
  rw [h2, cast_pm_one hp hp2 (by
    rcases hs1 with h1 | h1 <;> rcases hs2 with h3 | h3 <;> rw [h1, h3] <;> simp)]
  have hp16 : p % 16 = ((c % 16) ^ 2 + 2 * (d % 16) ^ 2) % 16 := by
    rw [h]
    simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  have hc8 : c % 8 = c % 16 % 8 := by omega
  have hd4 : d % 4 = d % 16 % 4 := by omega
  have hc16 : (c % 16) % 2 = 1 := by omega
  have hp8' : ((c % 16) ^ 2 + 2 * (d % 16) ^ 2) % 8 = 1 := by
    have : p % 8 = p % 16 % 8 := by omega
    rw [hp16] at this; omega
  rw [hp16, hc8, hd4]
  exact table2 _ (Nat.mod_lt c (by norm_num)) _ (Nat.mod_lt d (by norm_num)) hc16 hp8'

theorem octic_neg_four {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 1) :
    (∃ x : ZMod p, x ^ 8 = -4) ↔ ∃ a b : ℕ, p = a ^ 2 + 32 * b ^ 2 := by
  haveI := Fact.mk hp
  have hp2 : p ≠ 2 := by omega
  have h4 : (-4 : ZMod p) ≠ 0 := by
    rw [show (-4 : ZMod p) = -(2 * 2) by ring, neg_ne_zero]
    exact mul_ne_zero (two_ne_zero_zmod hp hp2) (two_ne_zero_zmod hp hp2)
  rw [pow8_iff hp hp8 h4]
  constructor
  · intro hx
    obtain ⟨c, d, hcd⟩ :=
      rep_plus_two hp ((ZMod.exists_sq_eq_neg_two_iff hp2).mpr (Or.inl hp8))
    have hd := (key2 hp hp8 hcd).mp hx
    refine ⟨c, d / 4, ?_⟩
    have : d = 4 * (d / 4) := by omega
    rw [hcd]
    nth_rewrite 1 [this]
    ring
  · rintro ⟨a, b, hab⟩
    exact (key2 hp hp8 (c := a) (d := 4 * b) (by rw [hab]; ring)).mpr (by omega)

lemma exists_zeta {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 1) : ∃ z : ZMod p, z ^ 4 = -1 := by
  haveI := Fact.mk hp
  rw [pow4_iff hp (by omega) (neg_ne_zero.mpr one_ne_zero)]
  exact Even.neg_one_pow ⟨(p - 1) / 8, by omega⟩

lemma zeta_ne_zero {p : ℕ} (hp : p.Prime) {z : ZMod p} (hz : z ^ 4 = -1) : z ≠ 0 := by
  haveI := Fact.mk hp
  rintro rfl
  norm_num at hz

lemma one_add_i_ne_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {z : ZMod p} (hz : z ^ 4 = -1) :
    1 + z ^ 2 ≠ 0 := by
  haveI := Fact.mk hp
  intro h0
  have : (2 : ZMod p) = 0 := by linear_combination hz - (z ^ 2 - 1) * h0
  exact two_ne_zero_zmod hp hp2 this

/-- Every fourth root of unity is a nonzero square. -/
lemma sq_of_fourth_root {p : ℕ} (hp : p.Prime) {z u : ZMod p} (hz : z ^ 4 = -1)
    (hu : u ^ 4 = 1) : ∃ r : ZMod p, r ≠ 0 ∧ u = r ^ 2 := by
  haveI := Fact.mk hp
  have hz0 := zeta_ne_zero hp hz
  have hprod : (u - 1) * (u + 1) * (u - z ^ 2) * (u + z ^ 2) = 0 := by
    linear_combination hu - (u ^ 2 - 1) * hz
  rcases mul_eq_zero.mp hprod with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact ⟨1, one_ne_zero, by linear_combination h⟩
      · exact ⟨z ^ 2, pow_ne_zero 2 hz0, by linear_combination h - hz⟩
    · exact ⟨z, hz0, by linear_combination h⟩
  · exact ⟨z ^ 3, pow_ne_zero 3 hz0, by linear_combination h - z ^ 2 * hz⟩

lemma octic_side {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {z : ZMod p} (hz : z ^ 4 = -1) :
    (∃ x : ZMod p, x ^ 8 = -4) ↔ ∃ y : ZMod p, 1 + z ^ 2 = y ^ 2 := by
  haveI := Fact.mk hp
  have hw : (1 + z ^ 2) ^ 4 = -4 := by linear_combination (z ^ 4 + 4 * z ^ 2 + 5) * hz
  have hw0 := one_add_i_ne_zero hp hp2 hz
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨r, hr0, hr⟩ := sq_of_fourth_root hp hz (u := x ^ 2 / (1 + z ^ 2)) (by
      rw [div_pow, ← pow_mul, hx, hw]
      exact div_self (neg_ne_zero.mpr (by
        rw [show (4 : ZMod p) = 2 * 2 by norm_num]
        exact mul_ne_zero (two_ne_zero_zmod hp hp2) (two_ne_zero_zmod hp hp2))))
    refine ⟨x / r, ?_⟩
    rw [div_eq_iff hw0] at hr
    rw [div_pow, eq_div_iff (pow_ne_zero 2 hr0)]
    linear_combination -hr
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [show 8 = 2 * 4 by norm_num, pow_mul, ← hy, hw]⟩

lemma sqrt_two_side {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {z : ZMod p} (hz : z ^ 4 = -1) :
    (∃ s t : ZMod p, s ^ 2 = 2 ∧ t ^ 2 = 1 + s) ↔ ∃ y : ZMod p, 1 + z ^ 2 = y ^ 2 := by
  haveI := Fact.mk hp
  have hz0 := zeta_ne_zero hp hz
  have hw0 := one_add_i_ne_zero hp hp2 hz
  have hs0 : (z - z ^ 3) ^ 2 = 2 := by linear_combination (z ^ 2 - 2) * hz
  have hid : (1 + z) ^ 2 = (1 + z ^ 2) * (1 + (z - z ^ 3)) := by linear_combination z * hz
  have hid' : (1 + z ^ 3) ^ 2 = (z ^ 3) ^ 2 * (1 + z ^ 2) * (1 + -(z - z ^ 3)) := by
    linear_combination (-z ^ 7 - z ^ 4 + 2 * z ^ 3 + 1) * hz
  constructor
  · rintro ⟨s, t, hs, ht⟩
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hs.trans hs0.symm) with rfl | rfl
    · have ht0 : t ≠ 0 := by
        rintro rfl
        have h1 : z - z ^ 3 = -1 := by linear_combination -ht
        rw [h1] at hs0
        exact one_ne_zero (by linear_combination -hs0)
      refine ⟨(1 + z) / t, ?_⟩
      rw [div_pow, eq_div_iff (pow_ne_zero 2 ht0), ht, hid]
    · have ht0 : t ≠ 0 := by
        rintro rfl
        have h1 : z - z ^ 3 = 1 := by linear_combination ht
        rw [h1] at hs0
        exact one_ne_zero (by linear_combination -hs0)
      refine ⟨(1 + z ^ 3) / (z ^ 3 * t), ?_⟩
      rw [div_pow, eq_div_iff (pow_ne_zero 2 (mul_ne_zero (pow_ne_zero 3 hz0) ht0)), mul_pow,
        ht, hid']
      ring
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hw0 (by rw [hy]; ring)
    refine ⟨z - z ^ 3, (1 + z) / y, hs0, ?_⟩
    rw [div_pow, ← hy, hid]
    field_simp

theorem sqrt_two_octic {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 1) :
    (∃ s t : ZMod p, s ^ 2 = 2 ∧ t ^ 2 = 1 + s) ↔ ∃ a b : ℕ, p = a ^ 2 + 32 * b ^ 2 := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨z, hz⟩ := exists_zeta hp hp8
  rw [sqrt_two_side hp hp2 hz, ← octic_side hp hp2 hz, octic_neg_four hp hp8]

end TuringTask
