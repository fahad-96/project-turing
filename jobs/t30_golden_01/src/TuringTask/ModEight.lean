import Mathlib
import TuringTask.Reciprocity

/-!
# `12 k s(h, k) ≡ k + 1 - 2 J(h | k) (mod 8)` for odd `k` (theorem 3)

Strong induction on the odd modulus `k`. Replace `h` by its residue `x` modulo `k`.
* `x` odd: reciprocity gives `x · 12 k s(x, k) = x² + k² + 1 - 3 x k - k · 12 x s(k, x)`, the
  induction hypothesis for the modulus `x < k` gives `12 x s(k, x)` modulo `8`, and Jacobi
  reciprocity links `J(x | k)` with `J(k | x)`. A table modulo `8` (`table8`) finishes, since
  `x² ≡ 1 (mod 8)`.
* `x` even: `s(x, k) = -s(k - x, k)`, `J(x | k) = χ₄(k) J(k - x | k)`, and `k - x` is odd.
-/

namespace TuringTask

open Finset

lemma int_twelve {h k : ℕ} (hhk : Nat.Coprime h k) (hk : 0 < k) :
    ∃ N : ℤ, 12 * k * dsum h k = N :=
  ⟨2 * h * (k - 1) * (2 * k - 1) - 12 * (dS2 h k : ℤ) - 3 * k * (k - 1), by
    rw [twelve_k_dsum hhk hk]; push_cast; ring⟩

lemma table8 (x k j1 j2 : ZMod 8) (hx : x = 1 ∨ x = 3 ∨ x = 5 ∨ x = 7)
    (hk : k = 1 ∨ k = 3 ∨ k = 5 ∨ k = 7) (hj2 : j2 = 1 ∨ j2 = -1)
    (hrel1 : (x = 1 ∨ x = 5 ∨ k = 1 ∨ k = 5) → j1 = j2)
    (hrel2 : (x = 3 ∨ x = 7) → (k = 3 ∨ k = 7) → j1 = -j2) :
    x * (x ^ 2 + k ^ 2 + 1 - 3 * x * k - k * (x + 1 - 2 * j2)) = k + 1 - 2 * j1 := by
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl <;>
    rcases hj2 with rfl | rfl <;> revert j1 <;> decide

lemma odd_cast8 (x : ℕ) (hx : x % 2 = 1) :
    (x : ZMod 8) = 1 ∨ (x : ZMod 8) = 3 ∨ (x : ZMod 8) = 5 ∨ (x : ZMod 8) = 7 := by
  have h : (x : ZMod 8) = ((x % 8 : ℕ) : ZMod 8) := (ZMod.natCast_mod x 8).symm
  rcases (by omega : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7) with e | e | e | e <;>
    rw [h, e] <;> simp

lemma cast8_one_mod_four (x : ℕ) (hx : x % 4 = 1) : (x : ZMod 8) = 1 ∨ (x : ZMod 8) = 5 := by
  have h : (x : ZMod 8) = ((x % 8 : ℕ) : ZMod 8) := (ZMod.natCast_mod x 8).symm
  rcases (by omega : x % 8 = 1 ∨ x % 8 = 5) with e | e <;> rw [h, e] <;> simp

lemma cast8_three_mod_four (x : ℕ) (hx : x % 4 = 3) : (x : ZMod 8) = 3 ∨ (x : ZMod 8) = 7 := by
  have h : (x : ZMod 8) = ((x % 8 : ℕ) : ZMod 8) := (ZMod.natCast_mod x 8).symm
  rcases (by omega : x % 8 = 3 ∨ x % 8 = 7) with e | e <;> rw [h, e] <;> simp

lemma not_one_five_of_three {x : ℕ} (hx : x % 4 = 3) :
    ¬ ((x : ZMod 8) = 1 ∨ (x : ZMod 8) = 5) := by
  rcases cast8_three_mod_four x hx with h | h <;> rw [h] <;> decide

lemma jacobi_pm {a : ℤ} {b : ℕ} (h : a.gcd b = 1) :
    (((jacobiSym a b : ℤ) : ZMod 8) = 1 ∨ ((jacobiSym a b : ℤ) : ZMod 8) = -1) := by
  rcases jacobiSym.eq_one_or_neg_one h with e | e <;> rw [e] <;> simp

/-- The odd step: from the modulus `x` to the modulus `k`. -/
lemma mod_eight_odd_step {x k : ℕ} (hx0 : 0 < x) (hxo : x % 2 = 1) (hko : k % 2 = 1)
    (hxk : Nat.Coprime x k) (m' : ℤ)
    (ih : 12 * x * dsum k x = x + 1 - 2 * (jacobiSym k x : ℚ) + 8 * m') :
    ∃ m : ℤ, 12 * k * dsum x k = k + 1 - 2 * (jacobiSym x k : ℚ) + 8 * m := by
  have hk0 : 0 < k := by omega
  obtain ⟨N, hN⟩ := int_twelve hxk hk0
  have hrec := reciprocity hxk hx0 hk0
  -- the integer relation `x N = x² + k² + 1 - 3 x k - k (x + 1 - 2 J(k | x) + 8 m')`
  have hint : (x : ℤ) * N = x ^ 2 + k ^ 2 + 1 - 3 * x * k -
      k * (x + 1 - 2 * jacobiSym k x + 8 * m') := by
    have : ((x : ℤ) * N : ℚ) = ((x ^ 2 + k ^ 2 + 1 - 3 * x * k -
        k * (x + 1 - 2 * jacobiSym k x + 8 * m') : ℤ) : ℚ) := by
      push_cast
      rw [← hN]
      linear_combination hrec - (k : ℚ) * ih
    exact_mod_cast this
  have h8 := congrArg (Int.cast : ℤ → ZMod 8) hint
  push_cast at h8
  have h8' : ((8 : ℤ) : ZMod 8) = 0 := by decide
  push_cast at h8'
  rw [h8', zero_mul, add_zero] at h8
  -- the table
  have hxx : (x : ZMod 8) * (x : ZMod 8) = 1 := by
    rcases odd_cast8 x hxo with h | h | h | h <;> rw [h] <;> decide
  have hgcd1 : (x : ℤ).gcd k = 1 := by rw [Int.gcd_natCast_natCast]; exact hxk
  have hgcd2 : (k : ℤ).gcd x = 1 := by rw [Int.gcd_natCast_natCast]; exact hxk.symm
  have htab := table8 (x : ZMod 8) (k : ZMod 8) ((jacobiSym x k : ℤ) : ZMod 8)
    ((jacobiSym k x : ℤ) : ZMod 8) (odd_cast8 x hxo) (odd_cast8 k hko) (jacobi_pm hgcd2)
    (by
      intro h
      rcases Nat.odd_mod_four_iff.mp hxo with hx1 | hx3
      · rw [jacobiSym.quadratic_reciprocity_one_mod_four hx1 (Nat.odd_iff.mpr hko)]
      · rcases Nat.odd_mod_four_iff.mp hko with hk1 | hk3
        · rw [jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr hxo) hk1]
        · exfalso
          rcases h with h | h | h | h
          · exact not_one_five_of_three hx3 (Or.inl h)
          · exact not_one_five_of_three hx3 (Or.inr h)
          · exact not_one_five_of_three hk3 (Or.inl h)
          · exact not_one_five_of_three hk3 (Or.inr h))
    (by
      intro hx hk
      have hx3 : x % 4 = 3 := by
        rcases Nat.odd_mod_four_iff.mp hxo with hx1 | hx3
        · exfalso
          rcases cast8_one_mod_four x hx1 with e | e <;> rw [e] at hx <;> revert hx <;> decide
        · exact hx3
      have hk3 : k % 4 = 3 := by
        rcases Nat.odd_mod_four_iff.mp hko with hk1 | hk3
        · exfalso
          rcases cast8_one_mod_four k hk1 with e | e <;> rw [e] at hk <;> revert hk <;> decide
        · exact hk3
      rw [jacobiSym.quadratic_reciprocity_three_mod_four hx3 hk3]
      push_cast
      ring)
  have hNval : (N : ZMod 8) = ((k + 1 - 2 * jacobiSym x k : ℤ) : ZMod 8) := by
    push_cast
    rw [← htab, ← h8]
    linear_combination (-(N : ZMod 8)) * hxx
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hNval
  obtain ⟨c, hc⟩ := hNval
  push_cast at hc
  refine ⟨-c, ?_⟩
  rw [hN]
  have : (N : ℚ) = ((k + 1 - 2 * jacobiSym x k + 8 * (-c) : ℤ) : ℚ) := by
    congr 1
    linarith
  rw [this]
  push_cast
  ring

lemma coprime_mod {h k : ℕ} (hhk : Nat.Coprime h k) : Nat.Coprime (h % k) k := by
  unfold Nat.Coprime
  rw [← Nat.gcd_rec k h, Nat.gcd_comm]
  exact hhk

/-- Theorem 3 in the form used by `Main`. -/
theorem mod_eight : ∀ k : ℕ, k % 2 = 1 → ∀ h : ℕ, Nat.Coprime h k →
    ∃ m : ℤ, 12 * k * dsum h k = k + 1 - 2 * (jacobiSym h k : ℚ) + 8 * m := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hko h hhk
  have hk0 : 0 < k := by omega
  by_cases hk1 : k = 1
  · subst hk1
    refine ⟨0, ?_⟩
    simp [dsum, saw, jacobiSym.one_right]
    norm_num
  -- reduce `h` modulo `k`
  have hx : h % k < k := Nat.mod_lt h hk0
  have hxk : Nat.Coprime (h % k) k := coprime_mod hhk
  have hJ : jacobiSym h k = jacobiSym (h % k : ℕ) k := by
    rw [jacobiSym.mod_left]
    push_cast
    rfl
  rw [dsum_mod, hJ]
  set x := h % k with hxdef
  have hx0 : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h0 | h0
    · exfalso
      rw [h0] at hxk
      have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hxk) (dvd_zero k)
      exact hk1 ((Nat.coprime_zero_left k).mp hxk)
    · exact h0
  -- the odd case
  have hodd : ∀ y : ℕ, 0 < y → y < k → y % 2 = 1 → Nat.Coprime y k →
      ∃ m : ℤ, 12 * k * dsum y k = k + 1 - 2 * (jacobiSym y k : ℚ) + 8 * m := by
    intro y hy0 hyk hyo hyc
    obtain ⟨m', hm'⟩ := ih y hyk hyo k (Nat.Coprime.symm hyc)
    exact mod_eight_odd_step hy0 hyo hko hyc m' hm'
  rcases Nat.mod_two_eq_zero_or_one x with hxe | hxo
  · -- `x` even: use `k - x`
    have hy0 : 0 < k - x := by omega
    have hyo : (k - x) % 2 = 1 := by omega
    have hyc : Nat.Coprime (k - x) k := (Nat.coprime_self_sub_left hx.le).mpr hxk
    obtain ⟨m', hm'⟩ := hodd (k - x) hy0 (by omega) hyo hyc
    have hsub := dsum_sub x k hx.le
    have hJx : jacobiSym x k = ZMod.χ₄ k * jacobiSym (k - x : ℕ) k := by
      rw [← jacobiSym.neg _ (Nat.odd_iff.mpr hko)]
      apply jacobiSym.mod_left'
      push_cast [Nat.cast_sub hx.le]
      rw [show -((k : ℤ) - x) = x + (-1) * k by ring, Int.add_mul_emod_self_right]
    have hJy := jacobiSym.eq_one_or_neg_one (a := ((k - x : ℕ) : ℤ)) (b := k)
      (by rw [Int.gcd_natCast_natCast]; exact hyc)
    have hchi : ZMod.χ₄ k = 1 ∨ ZMod.χ₄ k = -1 := by
      rcases Nat.odd_mod_four_iff.mp hko with h1 | h3
      · exact Or.inl (ZMod.χ₄_nat_one_mod_four h1)
      · exact Or.inr (ZMod.χ₄_nat_three_mod_four h3)
    have hmod4 : (ZMod.χ₄ k = 1 ∧ k % 4 = 1) ∨ (ZMod.χ₄ k = -1 ∧ k % 4 = 3) := by
      rcases Nat.odd_mod_four_iff.mp hko with h1 | h3
      · exact Or.inl ⟨ZMod.χ₄_nat_one_mod_four h1, h1⟩
      · exact Or.inr ⟨ZMod.χ₄_nat_three_mod_four h3, h3⟩
    have hval : 12 * k * dsum x k = -(k + 1 - 2 * (jacobiSym (k - x : ℕ) k : ℚ) + 8 * m') := by
      have : dsum x k = - dsum (k - x) k := by rw [hsub]; ring
      rw [this, ← hm']; ring
    rw [hval, hJx]
    obtain ⟨c, hc⟩ : ∃ c, k = 4 * c + k % 4 := ⟨k / 4, by omega⟩
    rcases hmod4 with ⟨hχ, h4⟩ | ⟨hχ, h4⟩ <;> rcases hJy with hj | hj <;> rw [hχ, hj]
    · refine ⟨-c - m', ?_⟩
      have : (k : ℚ) = 4 * c + 1 := by rw [h4] at hc; exact_mod_cast hc
      push_cast; rw [this]; ring
    · refine ⟨-c - 1 - m', ?_⟩
      have : (k : ℚ) = 4 * c + 1 := by rw [h4] at hc; exact_mod_cast hc
      push_cast; rw [this]; ring
    · refine ⟨-c - 1 - m', ?_⟩
      have : (k : ℚ) = 4 * c + 3 := by rw [h4] at hc; exact_mod_cast hc
      push_cast; rw [this]; ring
    · refine ⟨-c - 1 - m', ?_⟩
      have : (k : ℚ) = 4 * c + 3 := by rw [h4] at hc; exact_mod_cast hc
      push_cast; rw [this]; ring
  · exact hodd x hx0 hx hxo hxk

end TuringTask
