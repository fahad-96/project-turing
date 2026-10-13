import Mathlib
import TuringTask.Criterion

/-!
# Thue's lemma and the forms `x^2 + 2 y^2`, `x^2 - 2 y^2`

* `thue`: for `t` in `ZMod p` there are integers `x, y`, not both `0`, with `x^2 < p`,
  `y^2 < p` and `x = t y` in `ZMod p`. The `(m + 1)^2 > p` pairs `0 ≤ u, v ≤ m = ⌊√p⌋` cannot
  have distinct values `u - t v` (pigeonhole).
* `rep_plus_two`: if `-2` is a square modulo an odd prime `p`, then `p = c^2 + 2 d^2`, because
  `x^2 + 2 y^2` is `p` or `2 p`.
* `rep_minus_two`: if `2` is a square modulo `p`, then `e^2 = p + 2 f^2`, because
  `x^2 - 2 y^2 = -p` and `(x + 2 y)^2 - 2 (x + y)^2 = 2 y^2 - x^2`.
-/

namespace TuringTask

lemma sqrt_sq_lt {p : ℕ} (hp : p.Prime) : Nat.sqrt p ^ 2 < p := by
  have h1 := Nat.sqrt_le' p
  rcases h1.lt_or_eq with h | h
  · exact h
  · exfalso
    rw [← h, sq] at hp
    rcases Nat.prime_mul_iff.mp hp with ⟨h2, h3⟩ | ⟨h2, h3⟩
    · rw [h3] at h2; exact Nat.not_prime_one h2
    · rw [h3] at h2; exact Nat.not_prime_one h2

lemma thue {p : ℕ} (hp : p.Prime) (t : ZMod p) :
    ∃ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) ∧ x ^ 2 < p ∧ y ^ 2 < p ∧ (x : ZMod p) = t * y := by
  haveI := Fact.mk hp
  set m := Nat.sqrt p
  have hm : m ^ 2 < p := sqrt_sq_lt hp
  have hm1 : p < (m + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt' p
    simpa [sq] using this
  set s : Finset (ℕ × ℕ) := Finset.range (m + 1) ×ˢ Finset.range (m + 1)
  have hcard : (Finset.univ : Finset (ZMod p)).card < s.card := by
    rw [Finset.card_univ, ZMod.card, Finset.card_product, Finset.card_range, ← sq]
    exact hm1
  obtain ⟨⟨u, v⟩, hu, ⟨u', v'⟩, hu', hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (f := fun w : ℕ × ℕ => ((w.1 : ZMod p) - t * w.2)) (fun _ _ => Finset.mem_univ _)
  simp only [s, Finset.mem_product, Finset.mem_range] at hu hu'
  refine ⟨(u : ℤ) - u', (v : ℤ) - v', ?_, ?_, ?_, ?_⟩
  · by_contra h
    push Not at h
    apply hne
    simp only [Prod.mk.injEq]
    omega
  · have h1 : ((u : ℤ) - u') ^ 2 ≤ (m : ℤ) ^ 2 := by
      exact sq_le_sq' (by omega) (by omega)
    have : ((m : ℤ)) ^ 2 < p := by exact_mod_cast hm
    linarith
  · have h1 : ((v : ℤ) - v') ^ 2 ≤ (m : ℤ) ^ 2 := by
      exact sq_le_sq' (by omega) (by omega)
    have : ((m : ℤ)) ^ 2 < p := by exact_mod_cast hm
    linarith
  · simp only at heq
    push_cast
    linear_combination heq

lemma int_dvd_of_zmod {p : ℕ} {z : ℤ} (h : (z : ZMod p) = 0) : (p : ℤ) ∣ z :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp h

lemma rep_plus_two {p : ℕ} (hp : p.Prime) (h : IsSquare (-2 : ZMod p)) :
    ∃ c d : ℕ, p = c ^ 2 + 2 * d ^ 2 := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨x, y, hxy, hx, hy, hxt⟩ := thue hp t
  have hdiv : (p : ℤ) ∣ x ^ 2 + 2 * y ^ 2 := by
    apply int_dvd_of_zmod
    push_cast
    rw [hxt]
    linear_combination (-(y : ZMod p) ^ 2) * ht
  obtain ⟨k, hk⟩ := hdiv
  have hpos : 0 < x ^ 2 + 2 * y ^ 2 := by
    rcases hxy with h | h <;> positivity
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hk1 : 0 < k := by nlinarith
  have hk3 : k < 3 := by nlinarith
  interval_cases k
  · exact ⟨x.natAbs, y.natAbs, by
      have : ((x.natAbs ^ 2 + 2 * y.natAbs ^ 2 : ℕ) : ℤ) = p := by
        push_cast; rw [sq_abs, sq_abs]; linarith
      exact_mod_cast this.symm⟩
  · have hxe : Even x := by
      have : Even (x ^ 2) := ⟨p - y ^ 2, by linarith⟩
      exact (Int.even_pow.mp this).1
    obtain ⟨x', rfl⟩ := hxe
    exact ⟨y.natAbs, x'.natAbs, by
      have : ((y.natAbs ^ 2 + 2 * x'.natAbs ^ 2 : ℕ) : ℤ) = p := by
        push_cast; rw [sq_abs, sq_abs]; linarith
      exact_mod_cast this.symm⟩

lemma sq_eq_two_mul_sq {x y : ℤ} (h : x ^ 2 = 2 * y ^ 2) : y = 0 := by
  by_contra hy
  have key : ∀ n : ℕ, ∀ x y : ℤ, x.natAbs = n → x ^ 2 = 2 * y ^ 2 → y ≠ 0 → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x y hn h hy
      have h2 : (2 : ℤ) ∣ x := Int.prime_two.dvd_of_dvd_pow ⟨y ^ 2, h⟩
      obtain ⟨x', rfl⟩ := h2
      have h3 : y ^ 2 = 2 * x' ^ 2 := by linarith
      have hx0 : x' ≠ 0 := by
        rintro rfl
        simp at h3
        exact hy h3
      have : y.natAbs < n := by
        have hy2 : (2 : ℤ) ∣ y := Int.prime_two.dvd_of_dvd_pow ⟨x' ^ 2, h3⟩
        obtain ⟨y', rfl⟩ := hy2
        have : x' ^ 2 = 2 * y' ^ 2 := by linarith
        rw [← hn]
        have hy' : y' ≠ 0 := by rintro rfl; simp at hy
        have h5 : x'.natAbs ^ 2 = 2 * y'.natAbs ^ 2 := by
          have := congrArg Int.natAbs this
          simpa [Int.natAbs_mul, Int.natAbs_pow] using this
        have h6 : 0 < y'.natAbs := Int.natAbs_pos.mpr hy'
        have h7 : y'.natAbs < x'.natAbs := by
          by_contra hc
          push Not at hc
          have := Nat.mul_le_mul hc hc
          nlinarith
        simp only [Int.natAbs_mul]
        norm_num
        omega
      exact ih _ this y x' rfl h3 hx0
  exact key _ x y rfl h hy

lemma rep_minus_two {p : ℕ} (hp : p.Prime) (h : IsSquare (2 : ZMod p)) :
    ∃ e f : ℕ, e ^ 2 = p + 2 * f ^ 2 := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨x, y, hxy, hx, hy, hxt⟩ := thue hp t
  have hdiv : (p : ℤ) ∣ x ^ 2 - 2 * y ^ 2 := by
    apply int_dvd_of_zmod
    push_cast
    rw [hxt]
    linear_combination (-(y : ZMod p) ^ 2) * ht
  obtain ⟨k, hk⟩ := hdiv
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hk1 : -2 < k := by nlinarith
  have hk3 : k < 1 := by nlinarith
  interval_cases k
  · refine ⟨(x + 2 * y).natAbs, (x + y).natAbs, ?_⟩
    have : (((x + 2 * y).natAbs ^ 2 : ℕ) : ℤ) = ((p + 2 * (x + y).natAbs ^ 2 : ℕ) : ℤ) := by
      push_cast; rw [sq_abs, sq_abs]; linarith
    exact_mod_cast this
  · exfalso
    have hz : y = 0 := sq_eq_two_mul_sq (x := x) (y := y) (by linarith)
    subst hz
    have : x = 0 := by nlinarith
    rcases hxy with h | h <;> simp_all

end TuringTask
