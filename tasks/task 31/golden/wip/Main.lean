import Mathlib
import TuringTask.Flat

/-!
# The five results on binary and ternary cyclotomic coefficients

The inverses `u, v` and the inverse `c` of `r` modulo `pq` are produced here. When two of the
primes `p, q, r` coincide, `Φ_{pqr}` is `Φ_m(X^x)` for a flat `Φ_m` and some `x ≥ 2`, so its
coefficients lie in `{-1, 0, 1}` and no two consecutive ones are both nonzero.
-/

namespace TuringTask

open Polynomial Finset

lemma exists_inv {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∃ u, u < q ∧ u * p % q = 1 := by
  haveI : Fact (1 < q) := ⟨hq.one_lt⟩
  refine ⟨((p : ZMod q)⁻¹).val, ZMod.val_lt _, ?_⟩
  rw [← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_zmod_val, mul_comm,
    ZMod.coe_mul_inv_eq_one p ((Nat.coprime_primes hp hq).2 hpq), ZMod.val_one]

lemma exists_inv_r {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hrp : r ≠ p)
    (hrq : r ≠ q) : ∃ c : ℕ, (c : ZMod (p * q)) * r = 1 := by
  haveI : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  have hcop : Nat.Coprime r (p * q) :=
    Nat.Coprime.mul_right ((Nat.coprime_primes hr hp).2 hrp) ((Nat.coprime_primes hr hq).2 hrq)
  exact ⟨((r : ZMod (p * q))⁻¹).val, by
    rw [ZMod.natCast_zmod_val, mul_comm ((r : ZMod (p * q))⁻¹), ZMod.coe_mul_inv_eq_one r hcop]⟩

lemma flat_prime {p : ℕ} (hp : p.Prime) (k : ℕ) : |(cyclotomic p ℤ).coeff k| ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [cyclotomic_prime, finsetSum_coeff]
  simp only [coeff_X_pow]
  rw [sum_ite_eq]
  split_ifs <;> simp

lemma flat_binary {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (k : ℕ) :
    |(cyclotomic (p * q) ℤ).coeff k| ≤ 1 := by
  obtain ⟨u, huq, hu⟩ := exists_inv hp hq hpq
  obtain ⟨v, hvp, hv⟩ := exists_inv hq hp (Ne.symm hpq)
  rcases coeff_binary_cases hp hq hu hv huq hvp k with h | h | h <;> rw [h] <;> norm_num

lemma flat_expand {f : ℤ[X]} (hf : ∀ k, |f.coeff k| ≤ 1) {x : ℕ} (hx : 2 ≤ x) :
    (∀ k, |(expand ℤ x f).coeff k| ≤ 1) ∧
      ∀ k, |(expand ℤ x f).coeff (k + 1) - (expand ℤ x f).coeff k| ≤ 1 := by
  have hx0 : 0 < x := by omega
  refine ⟨fun k => ?_, fun k => ?_⟩
  · rw [coeff_expand hx0]
    split_ifs
    · exact hf _
    · simp
  · rw [coeff_expand hx0, coeff_expand hx0]
    split_ifs with h1 h2
    · have := (Nat.dvd_add_right h2).1 h1
      exact absurd (Nat.le_of_dvd one_pos this) (by omega)
    · simpa using hf _
    · simpa using hf _
    · simp

lemma degenerate {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h : p = q ∨ p = r ∨ q = r) :
    (∀ k, |(cyclotomic (p * q * r) ℤ).coeff k| ≤ 1) ∧
      ∀ k, |(cyclotomic (p * q * r) ℤ).coeff (k + 1) - (cyclotomic (p * q * r) ℤ).coeff k| ≤ 1 := by
  suffices ∃ f : ℤ[X], ∃ x, 2 ≤ x ∧ (∀ k, |f.coeff k| ≤ 1) ∧
      cyclotomic (p * q * r) ℤ = expand ℤ x f by
    obtain ⟨f, x, hx, hf, he⟩ := this
    rw [he]
    exact flat_expand hf hx
  by_cases hpq : p = q
  · subst hpq
    by_cases hpr : p = r
    · subst hpr
      refine ⟨cyclotomic (p * p) ℤ, p, hp.two_le, ?_, ?_⟩
      · rw [← cyclotomic_expand_eq_cyclotomic hp (dvd_refl p)]
        exact (flat_expand (flat_prime hp) hp.two_le).1
      · rw [cyclotomic_expand_eq_cyclotomic hp (dvd_mul_right p p)]
    · refine ⟨cyclotomic (p * r) ℤ, p, hp.two_le, flat_binary hp hr hpr, ?_⟩
      rw [cyclotomic_expand_eq_cyclotomic hp (dvd_mul_right p r)]
      congr 1; ring
  · rcases h with h | h | h
    · exact absurd h hpq
    · subst h
      refine ⟨cyclotomic (p * q) ℤ, p, hp.two_le, flat_binary hp hq hpq, ?_⟩
      rw [cyclotomic_expand_eq_cyclotomic hp (dvd_mul_right p q)]
    · subst h
      refine ⟨cyclotomic (p * q) ℤ, q, hq.two_le, flat_binary hp hq hpq, ?_⟩
      rw [cyclotomic_expand_eq_cyclotomic hq (dvd_mul_left q p)]

/-- Theorem 1: the partial sums of the coefficients of `Φ_{pq}` lie in `{0, 1}`. -/
theorem partial_sums_mem (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (k : ℕ) :
    (∑ i ∈ range (k + 1), (cyclotomic (p * q) ℤ).coeff i) ∈ ({0, 1} : Finset ℤ) := by
  obtain ⟨u, huq, hu⟩ := exists_inv hp hq hpq
  obtain ⟨v, hvp, hv⟩ := exists_inv hq hp (Ne.symm hpq)
  exact sum_range_coeff_mem hp hq hu hv huq hvp k

/-- Theorem 2: exactly `u v` coefficients of `Φ_{pq}` equal `1`. -/
theorem card_ones (p q u v : ℕ) (hp : p.Prime) (hq : q.Prime) (hu : u * p % q = 1)
    (hv : v * q % p = 1) (huq : u < q) (hvp : v < p) :
    ((range (p * q)).filter (fun k => (cyclotomic (p * q) ℤ).coeff k = 1)).card = u * v :=
  card_coeff_eq_one hp hq hu hv huq hvp

/-- Theorem 3: Bang's bound `|a_{pqr}(k)| ≤ p - 1`. -/
theorem bang_bound (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (k : ℕ) :
    |(cyclotomic (p * q * r) ℤ).coeff k| ≤ (p : ℤ) - 1 := by
  by_cases h : p = q ∨ p = r ∨ q = r
  · have := (degenerate hp hq hr h).1 k
    have := hp.two_le
    have : (2 : ℤ) ≤ p := by exact_mod_cast this
    linarith
  · push Not at h
    obtain ⟨hpq, hpr, hqr⟩ := h
    obtain ⟨u, huq, hu⟩ := exists_inv hp hq hpq
    obtain ⟨v, hvp, hv⟩ := exists_inv hq hp (Ne.symm hpq)
    obtain ⟨c, hc⟩ := exists_inv_r hp hq hr (Ne.symm hpr) (Ne.symm hqr)
    exact bang hp hq hu hv huq hvp hr (Ne.symm hpr) (Ne.symm hqr) hc k

lemma mem_of_abs_le {a : ℤ} (h : |a| ≤ 1) : a ∈ ({-1, 0, 1} : Finset ℤ) := by
  rw [abs_le] at h
  have : a = -1 ∨ a = 0 ∨ a = 1 := by omega
  rcases this with rfl | rfl | rfl <;> simp

/-- Theorem 4: `Φ_{pqr}` is flat when `r ≡ ±1 (mod pq)`. -/
theorem flat_of_mod (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hr' : r % (p * q) = 1 ∨ r % (p * q) + 1 = p * q) (k : ℕ) :
    (cyclotomic (p * q * r) ℤ).coeff k ∈ ({-1, 0, 1} : Finset ℤ) := by
  apply mem_of_abs_le
  by_cases hpq : p = q
  · exact (degenerate hp hq hr (Or.inl hpq)).1 k
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hrp : r ≠ p := by
    rintro rfl
    rw [Nat.mod_eq_of_lt (show r < r * q by nlinarith)] at hr'
    rcases hr' with h | h <;> nlinarith
  have hrq : r ≠ q := by
    rintro rfl
    rw [Nat.mod_eq_of_lt (show r < p * r by nlinarith)] at hr'
    rcases hr' with h | h <;> nlinarith
  obtain ⟨u, huq, hu⟩ := exists_inv hp hq hpq
  obtain ⟨v, hvp, hv⟩ := exists_inv hq hp (Ne.symm hpq)
  rcases hr' with h | h
  · exact flat_one hp hq hu hv hr hrp hrq h k
  · exact flat_neg hp hq hu hv huq hvp hr hrp hrq h k

/-- Theorem 5: consecutive coefficients of `Φ_{pqr}` differ by at most `1`. -/
theorem jump_le_one (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (k : ℕ) :
    |(cyclotomic (p * q * r) ℤ).coeff (k + 1) - (cyclotomic (p * q * r) ℤ).coeff k| ≤ 1 := by
  by_cases h : p = q ∨ p = r ∨ q = r
  · exact (degenerate hp hq hr h).2 k
  · push Not at h
    obtain ⟨hpq, hpr, hqr⟩ := h
    obtain ⟨u, huq, hu⟩ := exists_inv hp hq hpq
    obtain ⟨v, hvp, hv⟩ := exists_inv hq hp (Ne.symm hpq)
    obtain ⟨c, hc⟩ := exists_inv_r hp hq hr (Ne.symm hpr) (Ne.symm hqr)
    exact jump hp hq hu hv huq hvp hr (Ne.symm hpr) (Ne.symm hqr) hc k

end TuringTask
