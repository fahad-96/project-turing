import Mathlib
import TuringTask.Sums

/-!
# Sums with the Legendre symbol

For an odd prime `p` the sum over squares is rewritten as a sum over `ZMod p` weighted by the
number of square roots, which is `1 + (y | p)`. This gives

* `∑_{k<p} (k | p) cx (a k / p) = (a | p) ρ(p)` for every integer `a` (`sum_legendre_cx`),
* `∑_{k<p} cx (a k² / p) = (a | p) ρ(p)` for `a` prime to `p` (`sum_sq_twist_cx`),

and, with the quadratic reciprocity law of Mathlib, the product formula for two distinct odd
primes (`sum_sq_mul_cx`).
-/

namespace TuringTask

open Finset

/-- The value `ρ(n)`: `√n` if `n ≡ 1 (mod 4)` and `i √n` otherwise. -/
noncomputable def rtv (n : ℕ) : ℂ :=
  if n % 4 = 1 then ((Real.sqrt (n : ℝ) : ℝ) : ℂ)
  else Complex.I * ((Real.sqrt (n : ℝ) : ℝ) : ℂ)

section Prime

variable (p : ℕ) [Fact p.Prime]

/-- The additive character `x ↦ exp (2 π i x / p)` of `ZMod p`. -/
noncomputable def psi (x : ZMod p) : ℂ := cx ((x.val : ℝ) / (p : ℝ))

lemma psi_intCast (c : ℤ) : psi p (c : ZMod p) = cx ((c : ℝ) / (p : ℝ)) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have h1 : (((c : ZMod p).val : ℕ) : ℤ) = c % (p : ℤ) := ZMod.val_intCast c
  have h2 : c = (((c : ZMod p).val : ℕ) : ℤ) + (p : ℤ) * (c / (p : ℤ)) := by
    rw [h1, Int.emod_def]
    ring
  have h3 : (c : ℝ) = (((c : ZMod p).val : ℕ) : ℝ) + (p : ℝ) * ((c / (p : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast h2
  have h4 : (c : ℝ) / (p : ℝ)
      = (((c : ZMod p).val : ℕ) : ℝ) / (p : ℝ) + ((c / (p : ℤ) : ℤ) : ℝ) := by
    rw [div_add' _ _ _ hp0, div_left_inj' hp0]
    linarith
  unfold psi
  rw [h4, cx_add, cx_int, mul_one]

lemma psi_zero : psi p 0 = 1 := by
  unfold psi
  simp [cx_zero]

/-- A sum over `range p` of a function of the residue class is a sum over `ZMod p`. -/
lemma sum_range_zmod (f : ZMod p → ℂ) :
    ∑ k ∈ range p, f (k : ZMod p) = ∑ x : ZMod p, f x := by
  refine Finset.sum_bij (fun k _ => (k : ZMod p)) (fun _ _ => mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro a ha b hb hab
    have ha' := mem_range.mp ha
    have hb' := mem_range.mp hb
    have h := (ZMod.natCast_eq_natCast_iff' a b p).mp hab
    rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at h
  · intro x _
    exact ⟨x.val, mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩

lemma sum_psi_zero : ∑ y : ZMod p, psi p y = 0 := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  rw [← sum_range_zmod p (psi p)]
  have h1 : ∀ k ∈ range p, psi p (k : ZMod p) = cx (1 / (p : ℝ)) ^ k := by
    intro k _
    have h2 := psi_intCast p (k : ℤ)
    simp only [Int.cast_natCast] at h2
    rw [h2, cx_pow]
    congr 1
    ring
  rw [sum_congr rfl h1]
  apply geom_sum_eq_zero'
  · exact cx_one_div_pow_self p (by omega)
  · have h3 := cx_one_div_pow_ne_one p 1 one_pos hp1
    rwa [pow_one] at h3

lemma sum_mul_left (a : ZMod p) (ha : a ≠ 0) (F : ZMod p → ℂ) :
    ∑ y : ZMod p, F (a * y) = ∑ y : ZMod p, F y :=
  Equiv.sum_comp (Equiv.mulLeft₀ a ha) F

/-- Summing over the squares is summing with the weight `1 + (y | p)`. -/
lemma sum_sq_fiber (hp : p ≠ 2) (h : ZMod p → ℂ) :
    ∑ x : ZMod p, h (x ^ 2)
      = ∑ y : ZMod p, (((quadraticChar (ZMod p) y : ℤ) : ℂ) + 1) * h y := by
  rw [← Finset.sum_fiberwise' univ (fun x : ZMod p => x ^ 2) h]
  apply sum_congr rfl
  intro y _
  rw [sum_const, nsmul_eq_mul]
  congr 1
  have hc := quadraticChar_card_sqrts ((ZMod.ringChar_zmod_n p).substr hp) y
  rw [Set.toFinset_setOf] at hc
  have hc2 : (((univ.filter (fun x : ZMod p => x ^ 2 = y)).card : ℤ) : ℂ)
      = ((quadraticChar (ZMod p) y + 1 : ℤ) : ℂ) := by
    rw [← hc]
  push_cast at hc2
  convert hc2

/-- The Gauss sum of the quadratic character equals the sum over squares. -/
lemma sum_char_psi (hp : p % 2 = 1) :
    ∑ y : ZMod p, ((quadraticChar (ZMod p) y : ℤ) : ℂ) * psi p y = rtv p := by
  have hp2 : p ≠ 2 := by omega
  have h1 := sum_sq_fiber p hp2 (psi p)
  have h2 : ∑ x : ZMod p, psi p (x ^ 2) = rtv p := by
    rw [← sum_range_zmod p (fun x => psi p (x ^ 2))]
    have h3 : ∀ k ∈ range p, psi p ((k : ZMod p) ^ 2) = cx ((k : ℝ) ^ 2 / (p : ℝ)) := by
      intro k _
      have h4 := psi_intCast p ((k : ℤ) ^ 2)
      push_cast at h4
      exact h4
    rw [sum_congr rfl h3]
    exact sum_sq_cx p hp
  rw [h2] at h1
  have h5 : ∑ y : ZMod p, (((quadraticChar (ZMod p) y : ℤ) : ℂ) + 1) * psi p y
      = ∑ y : ZMod p, ((quadraticChar (ZMod p) y : ℤ) : ℂ) * psi p y
        + ∑ y : ZMod p, psi p y := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro y _
    ring
  rw [h5, sum_psi_zero, add_zero] at h1
  exact h1.symm

lemma quadraticChar_sq_cast (a : ZMod p) (ha : a ≠ 0) :
    ((quadraticChar (ZMod p) a : ℤ) : ℂ) * ((quadraticChar (ZMod p) a : ℤ) : ℂ) = 1 := by
  have h := quadraticChar_sq_one ha
  have h2 : (((quadraticChar (ZMod p) a) ^ 2 : ℤ) : ℂ) = 1 := by
    rw [h]
    simp
  push_cast at h2
  linear_combination h2

/-- The twisted Gauss sum of the quadratic character. -/
lemma sum_char_twist (hp : p % 2 = 1) (a : ZMod p) (ha : a ≠ 0) :
    ∑ y : ZMod p, ((quadraticChar (ZMod p) y : ℤ) : ℂ) * psi p (a * y)
      = ((quadraticChar (ZMod p) a : ℤ) : ℂ) * rtv p := by
  have h1 := sum_mul_left p a ha
    (fun y => ((quadraticChar (ZMod p) y : ℤ) : ℂ) * psi p y)
  simp only [map_mul, Int.cast_mul] at h1
  rw [sum_char_psi p hp] at h1
  have h2 : ((quadraticChar (ZMod p) a : ℤ) : ℂ)
      * ∑ y : ZMod p, ((quadraticChar (ZMod p) y : ℤ) : ℂ) * psi p (a * y) = rtv p := by
    rw [← h1, mul_sum]
    apply sum_congr rfl
    intro y _
    ring
  have h3 := quadraticChar_sq_cast p a ha
  linear_combination ((quadraticChar (ZMod p) a : ℤ) : ℂ) * h2
    - (∑ y : ZMod p, ((quadraticChar (ZMod p) y : ℤ) : ℂ) * psi p (a * y)) * h3

theorem sum_legendre_cx (hp : p % 2 = 1) (a : ℤ) :
    ∑ k ∈ range p, ((legendreSym p (k : ℤ) : ℤ) : ℂ) * cx ((a : ℝ) * (k : ℝ) / (p : ℝ))
      = ((legendreSym p a : ℤ) : ℂ) * rtv p := by
  have hterm : ∀ k ∈ range p,
      ((legendreSym p (k : ℤ) : ℤ) : ℂ) * cx ((a : ℝ) * (k : ℝ) / (p : ℝ))
        = ((quadraticChar (ZMod p) (k : ZMod p) : ℤ) : ℂ)
          * psi p ((a : ZMod p) * (k : ZMod p)) := by
    intro k _
    have h1 := psi_intCast p (a * (k : ℤ))
    push_cast at h1
    rw [h1]
    simp only [legendreSym, Int.cast_natCast]
  rw [sum_congr rfl hterm,
    sum_range_zmod p (fun x : ZMod p => ((quadraticChar (ZMod p) x : ℤ) : ℂ)
      * psi p ((a : ZMod p) * x))]
  by_cases ha : (a : ZMod p) = 0
  · have hl : legendreSym p a = 0 := (legendreSym.eq_zero_iff p a).mpr ha
    have hF : ringChar (ZMod p) ≠ 2 := (ZMod.ringChar_zmod_n p).substr (by omega)
    rw [hl, ha]
    simp only [zero_mul, psi_zero, mul_one, Int.cast_zero]
    rw [← Int.cast_sum, quadraticChar_sum_zero hF, Int.cast_zero]
  · have h := sum_char_twist p hp (a : ZMod p) ha
    rw [h]
    simp only [legendreSym]

theorem sum_sq_twist_cx (hp : p % 2 = 1) (a : ℤ) (ha : (a : ZMod p) ≠ 0) :
    ∑ k ∈ range p, cx ((a : ℝ) * (k : ℝ) ^ 2 / (p : ℝ))
      = ((legendreSym p a : ℤ) : ℂ) * rtv p := by
  have hp2 : p ≠ 2 := by omega
  have hterm : ∀ k ∈ range p, cx ((a : ℝ) * (k : ℝ) ^ 2 / (p : ℝ))
      = psi p ((a : ZMod p) * (k : ZMod p) ^ 2) := by
    intro k _
    have h1 := psi_intCast p (a * (k : ℤ) ^ 2)
    push_cast at h1
    rw [h1]
  rw [sum_congr rfl hterm,
    sum_range_zmod p (fun x : ZMod p => psi p ((a : ZMod p) * x ^ 2)),
    sum_sq_fiber p hp2 (fun y => psi p ((a : ZMod p) * y))]
  have h5 : ∑ y : ZMod p, (((quadraticChar (ZMod p) y : ℤ) : ℂ) + 1) * psi p ((a : ZMod p) * y)
      = ∑ y : ZMod p, ((quadraticChar (ZMod p) y : ℤ) : ℂ) * psi p ((a : ZMod p) * y)
        + ∑ y : ZMod p, psi p ((a : ZMod p) * y) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro y _
    ring
  rw [h5, sum_char_twist p hp (a : ZMod p) ha, sum_mul_left p (a : ZMod p) ha (psi p),
    sum_psi_zero, add_zero]
  simp only [legendreSym]

end Prime

/-! ### Two distinct odd primes -/

lemma rtv_mul (p q : ℕ) (hp : p % 2 = 1) (hq : q % 2 = 1) :
    ((-1 : ℂ) ^ (p / 2 * (q / 2))) * (rtv p * rtv q) = rtv (p * q) := by
  have hs : ((Real.sqrt ((p * q : ℕ) : ℝ) : ℝ) : ℂ)
      = ((Real.sqrt (p : ℝ) : ℝ) : ℂ) * ((Real.sqrt (q : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (Nat.cast_nonneg p)]
    push_cast
    rfl
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by omega
  rcases hp4 with hp4 | hp4 <;> rcases hq4 with hq4 | hq4
  · have he : Even (p / 2 * (q / 2)) := Even.mul_right ⟨p / 4, by omega⟩ _
    have hpq : (p * q) % 4 = 1 := by rw [Nat.mul_mod, hp4, hq4]
    rw [he.neg_one_pow, rtv, rtv, rtv, if_pos hp4, if_pos hq4, if_pos hpq, hs]
    ring
  · have he : Even (p / 2 * (q / 2)) := Even.mul_right ⟨p / 4, by omega⟩ _
    have hpq : ¬ (p * q) % 4 = 1 := by rw [Nat.mul_mod, hp4, hq4]; decide
    have hq' : ¬ q % 4 = 1 := by omega
    rw [he.neg_one_pow, rtv, rtv, rtv, if_pos hp4, if_neg hq', if_neg hpq, hs]
    ring
  · have he : Even (p / 2 * (q / 2)) := Even.mul_left ⟨q / 4, by omega⟩ _
    have hpq : ¬ (p * q) % 4 = 1 := by rw [Nat.mul_mod, hp4, hq4]; decide
    have hp' : ¬ p % 4 = 1 := by omega
    rw [he.neg_one_pow, rtv, rtv, rtv, if_neg hp', if_pos hq4, if_neg hpq, hs]
    ring
  · have ho : Odd (p / 2 * (q / 2)) := Odd.mul ⟨p / 4, by omega⟩ ⟨q / 4, by omega⟩
    have hpq : (p * q) % 4 = 1 := by rw [Nat.mul_mod, hp4, hq4]
    have hp' : ¬ p % 4 = 1 := by omega
    have hq' : ¬ q % 4 = 1 := by omega
    rw [ho.neg_one_pow, rtv, rtv, rtv, if_neg hp', if_neg hq', if_pos hpq, hs]
    linear_combination
      (-(((Real.sqrt (p : ℝ) : ℝ) : ℂ) * ((Real.sqrt (q : ℝ) : ℝ) : ℂ))) * hI

theorem sum_sq_mul_cx (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hp : p % 2 = 1)
    (hq : q % 2 = 1) (hpq : p ≠ q) :
    (∑ j ∈ range p, cx ((q : ℝ) * (j : ℝ) ^ 2 / (p : ℝ)))
      * (∑ k ∈ range q, cx ((p : ℝ) * (k : ℝ) ^ 2 / (q : ℝ))) = rtv (p * q) := by
  have hpp : p.Prime := Fact.out
  have hqp : q.Prime := Fact.out
  have hq0 : (((q : ℕ) : ℤ) : ZMod p) ≠ 0 := by
    rw [Int.cast_natCast]
    intro h0
    have h1 : p ∣ q := (ZMod.natCast_eq_zero_iff q p).mp h0
    exact hpq ((Nat.prime_dvd_prime_iff_eq hpp hqp).mp h1)
  have hp0 : (((p : ℕ) : ℤ) : ZMod q) ≠ 0 := by
    rw [Int.cast_natCast]
    intro h0
    have h1 : q ∣ p := (ZMod.natCast_eq_zero_iff p q).mp h0
    exact hpq ((Nat.prime_dvd_prime_iff_eq hqp hpp).mp h1).symm
  have h1 := sum_sq_twist_cx p hp (q : ℤ) hq0
  have h2 := sum_sq_twist_cx q hq (p : ℤ) hp0
  simp only [Int.cast_natCast] at h1 h2
  have hr : ((legendreSym q (p : ℤ) : ℤ) : ℂ) * ((legendreSym p (q : ℤ) : ℤ) : ℂ)
      = (-1 : ℂ) ^ (p / 2 * (q / 2)) := by
    have h3 := legendreSym.quadratic_reciprocity (p := p) (q := q) (by omega) (by omega) hpq
    exact_mod_cast h3
  rw [h1, h2, ← rtv_mul p q hp hq, ← hr]
  ring

end TuringTask
