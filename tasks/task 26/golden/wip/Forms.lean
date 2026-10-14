import Mathlib

/-!
# Binary quadratic forms and Lagrange reduction

* `FormRep a b c m`: the form `a x^2 + b x y + c y^2` takes the value `m` at some integers `x, y`.
* `rep_swap`, `rep_shift`: the moves `(a, b, c) ↦ (c, -b, a)` and
  `(a, b, c) ↦ (a, b + 2 k a, a k^2 + b k + c)` keep the discriminant and the represented values.
* `reduce`: a positive definite form represents the same values as a form with
  `|b| ≤ a ≤ c`, by descent on `a`. Such a form has `3 a^2 ≤ 4 a c - b^2` (`reduced_bound`).
* `lagrange`: if `p ∣ t^2 + n`, the form `(p, 2 t, (t^2 + n) / p)` of discriminant `-4 n`
  represents `p`.
-/

namespace TuringTask

/-- The form `a x^2 + b x y + c y^2` represents `m`. -/
def FormRep (a b c m : ℤ) : Prop := ∃ x y : ℤ, a * x ^ 2 + b * x * y + c * y ^ 2 = m

lemma rep_swap {a b c m : ℤ} (h : FormRep a b c m) : FormRep c (-b) a m := by
  obtain ⟨x, y, h⟩ := h
  exact ⟨-y, x, by linear_combination h⟩

lemma rep_shift {a b c m : ℤ} (k : ℤ) (h : FormRep a b c m) :
    FormRep a (b + 2 * k * a) (a * k ^ 2 + b * k + c) m := by
  obtain ⟨x, y, h⟩ := h
  exact ⟨x - k * y, y, by linear_combination h⟩

lemma rep_neg {a b c m : ℤ} (h : FormRep a (-b) c m) : FormRep a b c m := by
  obtain ⟨x, y, h⟩ := h
  exact ⟨x, -y, by linear_combination h⟩

/-- Lagrange reduction: every positive definite form of discriminant `D` represents the same
values as a form with `|b| ≤ a ≤ c`. -/
theorem reduce (D : ℤ) (hD : D < 0) :
    ∀ (N : ℕ) (a b c m : ℤ), a.toNat = N → 0 < a → b ^ 2 - 4 * a * c = D → FormRep a b c m →
      ∃ a' b' c', |b'| ≤ a' ∧ a' ≤ c' ∧ b' ^ 2 - 4 * a' * c' = D ∧ FormRep a' b' c' m := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro a b c m hN ha hd hr
    set k : ℤ := -((b + a) / (2 * a)) with hk
    set b' : ℤ := b + 2 * k * a with hb'
    set c' : ℤ := a * k ^ 2 + b * k + c with hc'
    have hr' := rep_shift k hr
    have hd' : b' ^ 2 - 4 * a * c' = D := by rw [hb', hc', ← hd]; ring
    have hbb : b' = (b + a) % (2 * a) - a := by
      have := Int.emod_add_mul_ediv (b + a) (2 * a)
      rw [hb', hk]; linarith
    have hm1 : 0 ≤ (b + a) % (2 * a) := Int.emod_nonneg _ (by omega)
    have hm2 : (b + a) % (2 * a) < 2 * a := Int.emod_lt_of_pos _ (by omega)
    have habs : |b'| ≤ a := abs_le.mpr ⟨by omega, by omega⟩
    have hc0 : 0 < c' := by
      have : 0 < 4 * a * c' := by nlinarith
      nlinarith
    rcases le_or_gt a c' with hac | hac
    · exact ⟨a, b', c', habs, hac, hd', hr'⟩
    · have hs := rep_swap hr'
      refine ih c'.toNat (by omega) c' (-b') a m rfl hc0 (by rw [← hd']; ring) hs

lemma reduced_bound {a b c : ℤ} (h1 : |b| ≤ a) (h2 : a ≤ c) : 3 * a ^ 2 ≤ 4 * a * c - b ^ 2 := by
  have hb : b ^ 2 ≤ a ^ 2 := by
    have := abs_le.mp h1
    nlinarith
  have ha : 0 ≤ a := le_trans (abs_nonneg b) h1
  nlinarith

lemma lagrange {p : ℕ} (n t : ℤ) (h : (p : ℤ) ∣ t ^ 2 + n) :
    ∃ c, (2 * t) ^ 2 - 4 * (p : ℤ) * c = -4 * n ∧ FormRep p (2 * t) c p := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, by linear_combination 4 * hc, 1, 0, by ring⟩

end TuringTask
