import Mathlib

/-!
# Fourth and eighth powers modulo `p`

* `pow4_iff`: for `p = 1 (mod 4)` and `a ≠ 0` in `ZMod p`, `a` is a fourth power exactly when
  `a ^ ((p - 1) / 4) = 1`. Euler's criterion (`ZMod.euler_criterion`) makes `a = z^2`, and then
  `z ^ ((p - 1) / 2) = a ^ ((p - 1) / 4)` makes `z` a square.
* `pow8_iff`: the same for eighth powers and `p = 1 (mod 8)`.
* `euler_J`: `J(a | p) = a ^ ((p - 1) / 2)` in `ZMod p` (`legendreSym.eq_pow`).
* `J_pm_one`, `cast_pm_one`: Jacobi symbols of numbers prime to `p` are `1` or `-1`, and `1 ≠ -1`
  in `ZMod p` for odd `p`.
-/

namespace TuringTask

lemma pow4_iff {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) {a : ZMod p} (ha : a ≠ 0) :
    (∃ x : ZMod p, x ^ 4 = a) ↔ a ^ ((p - 1) / 4) = 1 := by
  haveI := Fact.mk hp
  have e2 : p / 2 = 2 * ((p - 1) / 4) := by omega
  have e4 : 4 * ((p - 1) / 4) = p - 1 := by omega
  constructor
  · rintro ⟨x, rfl⟩
    have hx : x ≠ 0 := by rintro rfl; simp at ha
    rw [← pow_mul, e4]
    exact ZMod.pow_card_sub_one_eq_one hx
  · intro h
    have hsq : IsSquare a := (ZMod.euler_criterion p ha).mpr (by rw [e2, pow_mul']; simp [h])
    obtain ⟨z, rfl⟩ := hsq
    have hz : z ≠ 0 := by rintro rfl; simp at ha
    have hz2 : IsSquare z := (ZMod.euler_criterion p hz).mpr (by
      rw [e2, pow_mul, sq, h])
    obtain ⟨y, rfl⟩ := hz2
    exact ⟨y, by ring⟩

lemma pow8_iff {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 1) {a : ZMod p} (ha : a ≠ 0) :
    (∃ x : ZMod p, x ^ 8 = a) ↔ a ^ ((p - 1) / 8) = 1 := by
  haveI := Fact.mk hp
  have e2 : p / 2 = 4 * ((p - 1) / 8) := by omega
  have e4 : (p - 1) / 4 = 2 * ((p - 1) / 8) := by omega
  have e8 : 8 * ((p - 1) / 8) = p - 1 := by omega
  constructor
  · rintro ⟨x, rfl⟩
    have hx : x ≠ 0 := by rintro rfl; simp at ha
    rw [← pow_mul, e8]
    exact ZMod.pow_card_sub_one_eq_one hx
  · intro h
    have hsq : IsSquare a := (ZMod.euler_criterion p ha).mpr (by rw [e2, pow_mul']; simp [h])
    obtain ⟨z, rfl⟩ := hsq
    have hz : z ≠ 0 := by rintro rfl; simp at ha
    obtain ⟨y, hy⟩ := (pow4_iff hp (by omega) hz).mpr (by rw [e4, pow_mul, sq, h])
    exact ⟨y, by rw [← hy]; ring⟩

lemma euler_J {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℤ) :
    ((jacobiSym a p : ℤ) : ZMod p) = (a : ZMod p) ^ ((p - 1) / 2) := by
  haveI := Fact.mk hp
  have : (p - 1) / 2 = p / 2 := by
    have := hp.eq_one_or_self_of_dvd 2
    rcases Nat.even_or_odd p with ⟨r, hr⟩ | ⟨r, hr⟩
    · exfalso
      rcases this ⟨r, by omega⟩ with h | h <;> omega
    · omega
  rw [this, ← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_pow]

lemma J_pm_one {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    jacobiSym a p = 1 ∨ jacobiSym a p = -1 := by
  apply jacobiSym.eq_one_or_neg_one
  have hp' := Nat.prime_iff_prime_int.mp hp
  rcases Int.gcd_dvd_right a p |> (fun h => (Nat.dvd_prime hp).mp (by exact_mod_cast h)) with
    h | h
  · exact h
  · exfalso
    apply ha
    have : ((a.gcd p : ℕ) : ℤ) ∣ a := Int.gcd_dvd_left a p
    rwa [h] at this

lemma one_ne_neg_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (1 : ZMod p) ≠ -1 := by
  haveI := Fact.mk hp
  intro h
  have : (2 : ZMod p) = 0 := by linear_combination h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast this
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  have := hp.two_le
  omega

/-- A sign `j = ±1` is `1` exactly when its image in `ZMod p` is `1`. -/
lemma cast_pm_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {j : ℤ} (hj : j = 1 ∨ j = -1) :
    ((j : ℤ) : ZMod p) = 1 ↔ j = 1 := by
  rcases hj with rfl | rfl
  · simp
  · simp only [Int.cast_neg, Int.cast_one]
    constructor
    · intro h; exact absurd h.symm (one_ne_neg_one hp hp2)
    · intro h; norm_num at h

end TuringTask
