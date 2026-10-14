import Mathlib
import TuringTask.ModEight

/-!
# Integrality and the two criteria (theorems 2, 4 and 5)

* `integral`: `2 gcd(3, k) k s(h, k)` is an integer. With `d = gcd(h, k)`, `s(h, k) = s(h', k')`
  for the coprime pair `(h', k') = (h/d, k/d)`, and
  `12 k' s(h', k') = 2 h' (k' - 1)(2 k' - 1) - 12 S₂ - 3 k' (k' - 1)`, where `k'(k' - 1)` is even
  and
  `(k' - 1)(2 k' - 1)` is divisible by `3` when `3 ∤ k'`.
* `dsum_eq_zero_iff`: `12 h k s = h² + 1 + k M` gives `k ∣ h² + 1` when `s = 0`. Conversely
  `h² ≡ -1` makes `k - h` an inverse of `h`, so `s(h, k) = s(k - h, k) = -s(h, k)`.
* `dsum_eq_iff`: if `s(a, k) = s(b, k)`, the same identity for `a` and `b` gives
  `k ∣ (a - b)(a b - 1)`; for a prime `k` this is the claim. The converse uses `dsum_mod` and
  `dsum_inv`.
-/

namespace TuringTask

open Finset

lemma dsum_zero_right (h : ℕ) : dsum h 0 = 0 := by simp [dsum]

/-- Theorem 2 in the form used by `Main`. -/
theorem integral (h k : ℕ) : ∃ m : ℤ, ((2 * Nat.gcd 3 k * k : ℕ) : ℚ) * dsum h k = m := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; exact ⟨0, by simp [dsum_zero_right]⟩
  set d := Nat.gcd h k with hd
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_right h hk
  obtain ⟨h', hh'⟩ : d ∣ h := Nat.gcd_dvd_left h k
  obtain ⟨k', hk'⟩ : d ∣ k := Nat.gcd_dvd_right h k
  have hk'0 : 0 < k' := by
    rcases Nat.eq_zero_or_pos k' with h0 | h0
    · rw [h0, mul_zero] at hk'; omega
    · exact h0
  have hcop : Nat.Coprime h' k' := by
    have := Nat.coprime_div_gcd_div_gcd (m := h) (n := k) hd0
    rw [← hd] at this
    rwa [hh', hk', Nat.mul_div_cancel_left _ hd0, Nat.mul_div_cancel_left _ hd0] at this
  have hscale : dsum h k = dsum h' k' := by
    rw [hh', hk', dsum_scale d h' k' hd0]
  have h12 := twelve_k_dsum hcop hk'0
  obtain ⟨t, ht⟩ := Nat.even_mul_pred_self k'
  have ht' : (k' : ℚ) * (k' - 1) = 2 * t := by
    have : ((k' * (k' - 1) : ℕ) : ℚ) = ((t + t : ℕ) : ℚ) := by rw [ht]
    push_cast [Nat.cast_sub (show 1 ≤ k' by omega)] at this
    linarith
  have hk'q : (k' : ℚ) ≠ 0 := by exact_mod_cast hk'0.ne'
  rw [hscale]
  by_cases h3 : 3 ∣ k
  · have hg : Nat.gcd 3 k = 3 := Nat.gcd_eq_left h3
    rw [hg]
    refine ⟨d * (h' * ((k' : ℤ) - 1) * (2 * k' - 1) - 6 * (dS2 h' k' : ℤ) - 3 * t), ?_⟩
    rw [hk']
    push_cast
    have : (6 * ((d : ℚ) * k')) * dsum h' k' = (d : ℚ) * (12 * k' * dsum h' k') / 2 := by ring
    rw [this, h12]
    linear_combination (-3 / 2 * (d : ℚ)) * ht'
  · have hg : Nat.gcd 3 k = 1 := by
      rw [← Nat.coprime_iff_gcd_eq_one]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
    have h3' : ¬ 3 ∣ k' := fun h' => h3 (by rw [hk']; exact Dvd.dvd.mul_left h' d)
    obtain ⟨u, hu⟩ : ∃ u : ℕ, ((k' : ℚ) - 1) * (2 * k' - 1) = 3 * u := by
      rcases (by omega : k' % 3 = 1 ∨ k' % 3 = 2) with e | e
      · obtain ⟨j, hj⟩ : ∃ j, k' = 3 * j + 1 := ⟨k' / 3, by omega⟩
        exact ⟨j * (6 * j + 1), by rw [hj]; push_cast; ring⟩
      · obtain ⟨j, hj⟩ : ∃ j, k' = 3 * j + 2 := ⟨k' / 3, by omega⟩
        exact ⟨(3 * j + 1) * (2 * j + 1), by rw [hj]; push_cast; ring⟩
    rw [hg]
    refine ⟨d * (h' * (u : ℤ) - t - 2 * (dS2 h' k' : ℤ)), ?_⟩
    rw [hk']
    push_cast
    have : (2 * ((d : ℚ) * k')) * dsum h' k' = (d : ℚ) * (12 * k' * dsum h' k') / 6 := by ring
    rw [this, h12]
    linear_combination (d : ℚ) / 6 * (2 * h' * hu) - (d : ℚ) / 2 * ht'

/-- Theorem 4 in the form used by `Main`. -/
theorem dsum_eq_zero_iff (h k : ℕ) (hk : 0 < k) (hhk : Nat.Coprime h k) :
    dsum h k = 0 ↔ (h ^ 2 + 1) % k = 0 := by
  constructor
  · intro h0
    have e := h_twelve_k_dsum hhk hk
    rw [h0, mul_zero, mul_zero] at e
    have hint : ((h ^ 2 + 1 : ℕ) : ℤ) = k * (-((h ^ 2 + 1) * (2 * k - 3) -
        6 * (dQ h k : ℤ) - 3 * h * (k - 1))) := by
      have : (((h ^ 2 + 1 : ℕ) : ℤ) : ℚ) = ((k * (-((h ^ 2 + 1) * (2 * k - 3) -
          6 * (dQ h k : ℤ) - 3 * h * (k - 1))) : ℤ) : ℚ) := by
        push_cast
        linear_combination -e
      exact_mod_cast this
    have hdvd : (k : ℤ) ∣ ((h ^ 2 + 1 : ℕ) : ℤ) := ⟨_, hint⟩
    exact Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mp hdvd)
  · intro hdiv
    by_cases hk1 : k = 1
    · subst hk1; simp [dsum, saw]
    have hk2 : 2 ≤ k := by omega
    have hlt : h % k < k := Nat.mod_lt h hk
    -- `k - h mod k` is an inverse of `h`
    have hinv : h * (k - h % k) % k = 1 % k := by
      have e1 : h * (k - h % k) + h * (h % k) = h * k := by
        rw [← mul_add, Nat.sub_add_cancel hlt.le]
      have e2 : h * (k - h % k) + h * h ≡ 1 + h * h [MOD k] := by
        calc h * (k - h % k) + h * h ≡ h * (k - h % k) + h * (h % k) [MOD k] :=
              Nat.ModEq.add_left _ (Nat.ModEq.mul_left h (Nat.mod_modEq h k).symm)
          _ = h * k := e1
          _ ≡ 0 [MOD k] := by rw [Nat.ModEq, Nat.mul_mod_left, Nat.zero_mod]
          _ ≡ 1 + h * h [MOD k] := by
              rw [Nat.ModEq, Nat.zero_mod, show 1 + h * h = h ^ 2 + 1 by ring, hdiv]
      exact Nat.ModEq.add_right_cancel' _ e2
    have h1 := dsum_inv h (k - h % k) k hinv
    have h2 := dsum_sub (h % k) k hlt.le
    rw [← dsum_mod] at h2
    rw [h1] at h2
    linarith

lemma dsum_mul_eq (a b k : ℕ) (hk : 0 < k) (ha : Nat.Coprime a k) (hb : Nat.Coprime b k)
    (hab : dsum a k = dsum b k) : (k : ℤ) ∣ ((a : ℤ) - b) * (a * b - 1) := by
  have ea := h_twelve_k_dsum ha hk
  have eb := h_twelve_k_dsum hb hk
  rw [hab] at ea
  refine ⟨a * ((b ^ 2 + 1) * (2 * k - 3) - 6 * (dQ b k : ℤ) - 3 * b * (k - 1)) -
    b * ((a ^ 2 + 1) * (2 * k - 3) - 6 * (dQ a k : ℤ) - 3 * a * (k - 1)), ?_⟩
  have : ((((a : ℤ) - b) * (a * b - 1) : ℤ) : ℚ) = ((k * (a * ((b ^ 2 + 1) * (2 * k - 3) -
      6 * (dQ b k : ℤ) - 3 * b * (k - 1)) - b * ((a ^ 2 + 1) * (2 * k - 3) -
      6 * (dQ a k : ℤ) - 3 * a * (k - 1))) : ℤ) : ℚ) := by
    push_cast
    linear_combination (a : ℚ) * eb - (b : ℚ) * ea
  exact_mod_cast this

/-- Theorem 5 in the form used by `Main`. -/
theorem dsum_eq_iff (a b k : ℕ) (hk : k.Prime) (ha : Nat.Coprime a k) (hb : Nat.Coprime b k) :
    dsum a k = dsum b k ↔ (a % k = b % k ∨ a * b % k = 1) := by
  have hk0 := hk.pos
  have hk1 : 1 % k = 1 := Nat.mod_eq_of_lt hk.one_lt
  constructor
  · intro hab
    rcases Int.Prime.dvd_mul' hk (dsum_mul_eq a b k hk0 ha hb hab) with h1 | h1
    · left
      have : (a : ℤ) % k = (b : ℤ) % k :=
        Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd h1)
      exact_mod_cast this
    · right
      have : ((a * b : ℕ) : ℤ) % k = ((1 : ℕ) : ℤ) % k := by
        push_cast
        exact (Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd h1))
      have : a * b % k = 1 % k := by exact_mod_cast this
      rwa [hk1] at this
  · rintro (h1 | h1)
    · rw [dsum_mod a k, dsum_mod b k, h1]
    · exact (dsum_inv a b k (by rw [h1, hk1])).symm

end TuringTask
