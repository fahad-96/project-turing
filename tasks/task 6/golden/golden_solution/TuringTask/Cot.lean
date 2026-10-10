import Mathlib
import TuringTask.Char

/-!
# The cotangent sum

For `0 < k < p` the number `x = cx (k/p)` is a `p`-th root of unity different from `1`, and

  `cot (π k / p) = i (x + 1) / (x - 1) = i (1 + (2/p) ∑_{j<p} j x^j)`.

Summing against the Legendre symbol and using `TuringTask.sum_legendre_cx` for every `j` gives
the cotangent identity for primes `p ≡ 3 (mod 4)`.
-/

namespace TuringTask

open Finset

lemma sub_one_mul_sum_mul_pow (n : ℕ) (x : ℂ) :
    (x - 1) * ∑ j ∈ range n, (j : ℂ) * x ^ j
      = (n : ℂ) * x ^ n - x * ∑ j ∈ range n, x ^ j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- If `x^n = 1` and `x ≠ 1` then `(x - 1) ∑_{j<n} j x^j = n`. -/
lemma sub_one_mul_sum (n : ℕ) (x : ℂ) (hx : x ^ n = 1) (hx1 : x ≠ 1) :
    (x - 1) * ∑ j ∈ range n, (j : ℂ) * x ^ j = (n : ℂ) := by
  rw [sub_one_mul_sum_mul_pow, hx, geom_sum_eq_zero' n x hx hx1]
  ring

/-- `cot (π y) (e^(2πiy) - 1) = i (e^(2πiy) + 1)`. -/
lemma cot_mul (y : ℝ) (hs : Real.sin (Real.pi * y) ≠ 0) :
    ((Real.cot (Real.pi * y) : ℝ) : ℂ) * (cx y - 1) = Complex.I * (cx y + 1) := by
  have hcx : cx y = (((Real.cos (Real.pi * y) : ℝ) : ℂ)
      + ((Real.sin (Real.pi * y) : ℝ) : ℂ) * Complex.I) ^ 2 := by
    unfold cx
    rw [Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hcs : ((Real.cos (Real.pi * y) : ℝ) : ℂ) ^ 2
      + ((Real.sin (Real.pi * y) : ℝ) : ℂ) ^ 2 = 1 := by
    have h := Real.cos_sq_add_sin_sq (Real.pi * y)
    exact_mod_cast h
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hs' : ((Real.sin (Real.pi * y) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  rw [Real.cot_eq_cos_div_sin, Complex.ofReal_div, hcx, div_mul_eq_mul_div, div_eq_iff hs']
  linear_combination
    (((Real.cos (Real.pi * y) : ℝ) : ℂ) + ((Real.sin (Real.pi * y) : ℝ) : ℂ) * Complex.I) * hcs
    - (((Real.sin (Real.pi * y) : ℝ) : ℂ) ^ 2
        * (((Real.cos (Real.pi * y) : ℝ) : ℂ)
          + ((Real.sin (Real.pi * y) : ℝ) : ℂ) * Complex.I)) * hI

/-- The finite Fourier expansion of the cotangent at `π k / p`. -/
lemma cot_formula (p k : ℕ) (hk : 0 < k) (hkp : k < p) :
    ((Real.cot (Real.pi * (k : ℝ) / (p : ℝ)) : ℝ) : ℂ)
      = Complex.I * (1 + 2 / (p : ℂ)
        * ∑ j ∈ range p, (j : ℂ) * cx ((j : ℝ) * (k : ℝ) / (p : ℝ))) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have harg : Real.pi * (k : ℝ) / (p : ℝ) = Real.pi * ((k : ℝ) / (p : ℝ)) := by ring
  have hx0 : 0 < (k : ℝ) / (p : ℝ) := div_pos hk0 hp0
  have hx1 : (k : ℝ) / (p : ℝ) < 1 := by
    rw [div_lt_one hp0]
    exact_mod_cast hkp
  have hsin := (sin_pi_mul_pos _ hx0 hx1).ne'
  have hcot := cot_mul ((k : ℝ) / (p : ℝ)) hsin
  have hE1 : cx ((k : ℝ) / (p : ℝ)) ≠ 1 := by
    have h := cx_one_div_pow_ne_one p k hk hkp
    rw [cx_pow] at h
    have e : (k : ℝ) * (1 / (p : ℝ)) = (k : ℝ) / (p : ℝ) := by ring
    rwa [e] at h
  have hEp : cx ((k : ℝ) / (p : ℝ)) ^ p = 1 := by
    have e : (p : ℝ) * ((k : ℝ) / (p : ℝ)) = (k : ℝ) := by
      field_simp
    rw [cx_pow, e, cx_nat]
  have hD := sub_one_mul_sum p (cx ((k : ℝ) / (p : ℝ))) hEp hE1
  have hpow : ∀ j ∈ range p, (j : ℂ) * cx ((j : ℝ) * (k : ℝ) / (p : ℝ))
      = (j : ℂ) * cx ((k : ℝ) / (p : ℝ)) ^ j := by
    intro j _
    rw [cx_pow]
    congr 2
    ring
  have h2 : (2 : ℂ) / (p : ℂ) * (p : ℂ) = 2 := by
    field_simp
  have hne : cx ((k : ℝ) / (p : ℝ)) - 1 ≠ 0 := sub_ne_zero.mpr hE1
  rw [sum_congr rfl hpow, harg]
  apply mul_right_cancel₀ hne
  rw [hcot]
  linear_combination (-(Complex.I * (2 / (p : ℂ)))) * hD - Complex.I * h2

theorem sum_cot_real (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    Real.sqrt (p : ℝ) * ∑ k ∈ range p,
        ((legendreSym p (k : ℤ) : ℤ) : ℝ) * Real.cot (Real.pi * (k : ℝ) / (p : ℝ))
      = -2 * ∑ k ∈ range p, (k : ℝ) * ((legendreSym p (k : ℤ) : ℤ) : ℝ) := by
  have hp2 : p % 2 = 1 := by omega
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hk : ∀ k ∈ range p,
      ((legendreSym p (k : ℤ) : ℤ) : ℂ) * ((Real.cot (Real.pi * (k : ℝ) / (p : ℝ)) : ℝ) : ℂ)
        = ((legendreSym p (k : ℤ) : ℤ) : ℂ) * (Complex.I * (1 + 2 / (p : ℂ)
          * ∑ j ∈ range p, (j : ℂ) * cx ((j : ℝ) * (k : ℝ) / (p : ℝ)))) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      simp [legendreSym.at_zero]
    · rw [cot_formula p k hpos (mem_range.mp hk)]
  have hsum0 : ∑ k ∈ range p, ((legendreSym p (k : ℤ) : ℤ) : ℂ) = 0 := by
    have h := sum_legendre_cx p hp2 0
    simpa [cx_zero, legendreSym.at_zero] using h
  have hLj : ∀ j ∈ range p,
      ∑ k ∈ range p, ((legendreSym p (k : ℤ) : ℤ) : ℂ) * cx ((j : ℝ) * (k : ℝ) / (p : ℝ))
        = ((legendreSym p (j : ℤ) : ℤ) : ℂ)
          * (Complex.I * ((Real.sqrt (p : ℝ) : ℝ) : ℂ)) := by
    intro j _
    have h := sum_legendre_cx p hp2 (j : ℤ)
    rw [rtv, if_neg (by omega)] at h
    simp only [Int.cast_natCast] at h
    exact h
  have hT : ∑ k ∈ range p, ((legendreSym p (k : ℤ) : ℤ) : ℂ)
        * ∑ j ∈ range p, (j : ℂ) * cx ((j : ℝ) * (k : ℝ) / (p : ℝ))
      = (Complex.I * ((Real.sqrt (p : ℝ) : ℝ) : ℂ))
        * ∑ j ∈ range p, (j : ℂ) * ((legendreSym p (j : ℤ) : ℤ) : ℂ) := by
    calc ∑ k ∈ range p, ((legendreSym p (k : ℤ) : ℤ) : ℂ)
          * ∑ j ∈ range p, (j : ℂ) * cx ((j : ℝ) * (k : ℝ) / (p : ℝ))
        = ∑ k ∈ range p, ∑ j ∈ range p, (j : ℂ)
          * (((legendreSym p (k : ℤ) : ℤ) : ℂ) * cx ((j : ℝ) * (k : ℝ) / (p : ℝ))) := by
          apply sum_congr rfl
          intro k _
          rw [mul_sum]
          apply sum_congr rfl
          intro j _
          ring
      _ = ∑ j ∈ range p, ∑ k ∈ range p, (j : ℂ)
          * (((legendreSym p (k : ℤ) : ℤ) : ℂ) * cx ((j : ℝ) * (k : ℝ) / (p : ℝ))) :=
          sum_comm
      _ = ∑ j ∈ range p, (j : ℂ) * (((legendreSym p (j : ℤ) : ℤ) : ℂ)
          * (Complex.I * ((Real.sqrt (p : ℝ) : ℝ) : ℂ))) := by
          apply sum_congr rfl
          intro j hj
          rw [← mul_sum, hLj j hj]
      _ = (Complex.I * ((Real.sqrt (p : ℝ) : ℝ) : ℂ))
          * ∑ j ∈ range p, (j : ℂ) * ((legendreSym p (j : ℤ) : ℤ) : ℂ) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro j _
          ring
  have hA : ∑ k ∈ range p, ((legendreSym p (k : ℤ) : ℤ) : ℂ) * (Complex.I * (1 + 2 / (p : ℂ)
        * ∑ j ∈ range p, (j : ℂ) * cx ((j : ℝ) * (k : ℝ) / (p : ℝ))))
      = Complex.I * ∑ k ∈ range p, ((legendreSym p (k : ℤ) : ℤ) : ℂ)
        + (2 * Complex.I / (p : ℂ)) * ∑ k ∈ range p, ((legendreSym p (k : ℤ) : ℤ) : ℂ)
          * ∑ j ∈ range p, (j : ℂ) * cx ((j : ℝ) * (k : ℝ) / (p : ℝ)) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    ring
  have hRR : ((Real.sqrt (p : ℝ) : ℝ) : ℂ) * ((Real.sqrt (p : ℝ) : ℝ) : ℂ) = (p : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg p), Complex.ofReal_natCast]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h3 : (2 : ℂ) / (p : ℂ) * (p : ℂ) = 2 := by
    field_simp
  have hmain : ((Real.sqrt (p : ℝ) : ℝ) : ℂ) * ∑ k ∈ range p,
        ((legendreSym p (k : ℤ) : ℤ) : ℂ)
          * ((Real.cot (Real.pi * (k : ℝ) / (p : ℝ)) : ℝ) : ℂ)
      = -2 * ∑ k ∈ range p, (k : ℂ) * ((legendreSym p (k : ℤ) : ℤ) : ℂ) := by
    rw [sum_congr rfl hk, hA, hsum0, hT]
    linear_combination
      ((2 : ℂ) / (p : ℂ) * ((Real.sqrt (p : ℝ) : ℝ) : ℂ) * ((Real.sqrt (p : ℝ) : ℝ) : ℂ)
        * ∑ j ∈ range p, (j : ℂ) * ((legendreSym p (j : ℤ) : ℤ) : ℂ)) * hI
      + ((2 : ℂ) / (p : ℂ) * (-1)
        * ∑ j ∈ range p, (j : ℂ) * ((legendreSym p (j : ℤ) : ℤ) : ℂ)) * hRR
      - (∑ j ∈ range p, (j : ℂ) * ((legendreSym p (j : ℤ) : ℤ) : ℂ)) * h3
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_neg, Complex.ofReal_ofNat,
    Complex.ofReal_intCast, Complex.ofReal_natCast]
  exact hmain

end TuringTask
