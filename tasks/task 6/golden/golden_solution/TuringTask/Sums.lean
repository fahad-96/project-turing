import Mathlib
import TuringTask.Root

/-!
# The two exponential sums over an odd modulus

`cx x = exp (2 π i x)`. For odd `n = 2m+1` this file proves

* `∑_{k<n} cx (k(k+1)/(2n)) = cx ((n-1)/(8n)) √n`  (`sum_tri_cx`),
* `∑_{k<n} cx (k²/n) = √n` or `i √n` according to `n mod 4`  (`sum_sq_cx`).

Both follow from the product formula of `TuringTask.sum_pow_tri`: the product is a unit
complex number times a product of real sines whose signs are known, and the absolute value of
the sum is `√n` by `TuringTask.conj_sum_mul`.
-/

namespace TuringTask

open Finset

/-- `cx x = exp (2 π i x)`. -/
noncomputable def cx (x : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ))

/-! ### Basic properties of `cx` -/

lemma cx_add (x y : ℝ) : cx (x + y) = cx x * cx y := by
  unfold cx
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma cx_zero : cx 0 = 1 := by
  simp [cx]

lemma cx_int (k : ℤ) : cx (k : ℝ) = 1 := by
  unfold cx
  have h : 2 * (Real.pi : ℂ) * Complex.I * (((k : ℤ) : ℝ) : ℂ)
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

lemma cx_nat (k : ℕ) : cx (k : ℝ) = 1 := by
  have h := cx_int (k : ℤ)
  rwa [Int.cast_natCast] at h

lemma cx_pow (x : ℝ) (k : ℕ) : cx x ^ k = cx ((k : ℝ) * x) := by
  unfold cx
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma cx_add_nat (x : ℝ) (k : ℕ) : cx (x + (k : ℝ)) = cx x := by
  rw [cx_add, cx_nat, mul_one]

lemma cx_neg_mul (x : ℝ) : cx (-x) * cx x = 1 := by
  rw [← cx_add, neg_add_cancel, cx_zero]

lemma norm_cx (x : ℝ) : ‖cx x‖ = 1 := by
  unfold cx
  have h : 2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)
      = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma conj_cx (x : ℝ) : (starRingEnd ℂ) (cx x) = cx (-x) := by
  have h1 : cx x * (starRingEnd ℂ) (cx x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_cx]
    simp
  have h2 := cx_neg_mul x
  calc (starRingEnd ℂ) (cx x) = (cx (-x) * cx x) * (starRingEnd ℂ) (cx x) := by
        rw [h2, one_mul]
    _ = cx (-x) * (cx x * (starRingEnd ℂ) (cx x)) := by ring
    _ = cx (-x) := by rw [h1, mul_one]

lemma cx_quarter : cx (1 / 4) = Complex.I := by
  unfold cx
  have h : 2 * (Real.pi : ℂ) * Complex.I * ((1 / 4 : ℝ) : ℂ)
      = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  simp

lemma cx_eq_one (x : ℝ) (h : cx x = 1) : ∃ k : ℤ, x = (k : ℝ) := by
  unfold cx at h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  have h3 : (x : ℂ) = (k : ℂ) := by
    apply mul_left_cancel₀ h2
    rw [hk]
    ring
  exact_mod_cast h3

lemma cx_frac_pow_self (n : ℕ) (hn : 0 < n) (c : ℤ) : cx ((c : ℝ) / (n : ℝ)) ^ n = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h : (n : ℝ) * ((c : ℝ) / (n : ℝ)) = (c : ℝ) := by
    field_simp
  rw [cx_pow, h, cx_int]

lemma cx_frac_pow_ne_one (n : ℕ) (c : ℤ) (hc : Nat.Coprime c.natAbs n) (i : ℕ) (hi : 0 < i)
    (hin : i < n) : cx ((c : ℝ) / (n : ℝ)) ^ i ≠ 1 := by
  intro h
  rw [cx_pow] at h
  obtain ⟨k, hk⟩ := cx_eq_one _ h
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 : (i : ℝ) * (c : ℝ) = (k : ℝ) * (n : ℝ) := by
    rw [← hk]
    field_simp
  have h2 : (i : ℤ) * c = k * (n : ℤ) := by exact_mod_cast h1
  have h3 : i * c.natAbs = k.natAbs * n := by
    have h4 := congrArg Int.natAbs h2
    rwa [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast] at h4
  have h5 : n ∣ i * c.natAbs := ⟨k.natAbs, by rw [h3, mul_comm]⟩
  have h6 : n ∣ i := hc.symm.dvd_of_dvd_mul_right h5
  have h7 := Nat.le_of_dvd hi h6
  omega

lemma cx_one_div_pow_self (n : ℕ) (hn : 0 < n) : cx (1 / (n : ℝ)) ^ n = 1 := by
  have h := cx_frac_pow_self n hn 1
  rwa [Int.cast_one] at h

lemma cx_one_div_pow_ne_one (n i : ℕ) (hi : 0 < i) (hin : i < n) :
    cx (1 / (n : ℝ)) ^ i ≠ 1 := by
  have h := cx_frac_pow_ne_one n 1 (by simp) i hi hin
  rwa [Int.cast_one] at h

lemma prod_cx {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∏ j ∈ s, cx (f j) = cx (∑ j ∈ s, f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cx_zero]
  | insert a s ha ih => rw [prod_insert ha, sum_insert ha, ih, cx_add]

/-! ### From the product of `TuringTask.sum_pow_tri` to sines -/

/-- `1 - e^(-2πix) = e^(-πix) · 2i sin(πx)`. -/
lemma one_sub_cx_neg (x : ℝ) :
    1 - cx (-x) = cx (-(x / 2)) * (2 * Complex.I * ((Real.sin (Real.pi * x) : ℝ) : ℂ)) := by
  have hs := Complex.two_sin ((Real.pi * x : ℝ) : ℂ)
  have hab : Complex.exp (-((Real.pi * x : ℝ) : ℂ) * Complex.I)
      * Complex.exp (((Real.pi * x : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero]
  have h1 : cx (-(x / 2)) = Complex.exp (-((Real.pi * x : ℝ) : ℂ) * Complex.I) := by
    unfold cx
    congr 1
    push_cast
    ring
  have h2 : cx (-x) = Complex.exp (-((Real.pi * x : ℝ) : ℂ) * Complex.I)
      * Complex.exp (-((Real.pi * x : ℝ) : ℂ) * Complex.I) := by
    unfold cx
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [h1, h2, Complex.ofReal_sin]
  linear_combination
    (-(Complex.exp (-((Real.pi * x : ℝ) : ℂ) * Complex.I) * Complex.I)) * hs
    + (-(Complex.exp (-((Real.pi * x : ℝ) : ℂ) * Complex.I)
        * (Complex.exp (-((Real.pi * x : ℝ) : ℂ) * Complex.I)
          - Complex.exp (((Real.pi * x : ℝ) : ℂ) * Complex.I)))) * hI
    - hab

lemma sum_odd_mul (m : ℕ) (y : ℝ) :
    ∑ j ∈ range m, -((2 * (j : ℝ) + 1) * y / 2) = -((m : ℝ) ^ 2 * y / 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- A product of factors `1 - e^(-2πi(2j+1)y)` as a unit times a product of real sines. -/
lemma prod_one_sub (m : ℕ) (y : ℝ) :
    ∏ j ∈ range m, (1 - cx (-((2 * (j : ℝ) + 1) * y)))
      = cx ((m : ℝ) / 4 - (m : ℝ) ^ 2 * y / 2)
        * ((∏ j ∈ range m, 2 * Real.sin (Real.pi * ((2 * (j : ℝ) + 1) * y)) : ℝ) : ℂ) := by
  have hfac : ∀ j ∈ range m, 1 - cx (-((2 * (j : ℝ) + 1) * y))
      = (cx (-((2 * (j : ℝ) + 1) * y / 2)) * Complex.I)
        * ((2 * Real.sin (Real.pi * ((2 * (j : ℝ) + 1) * y)) : ℝ) : ℂ) := by
    intro j _
    rw [one_sub_cx_neg]
    push_cast
    ring
  have e1 : ∏ j ∈ range m, cx (-((2 * (j : ℝ) + 1) * y / 2)) = cx (-((m : ℝ) ^ 2 * y / 2)) := by
    rw [prod_cx, sum_odd_mul]
  have e2 : ∏ _j ∈ range m, Complex.I = cx ((m : ℝ) / 4) := by
    rw [prod_const, card_range, ← cx_quarter, cx_pow]
    congr 1
    ring
  have e3 : ∏ j ∈ range m, ((2 * Real.sin (Real.pi * ((2 * (j : ℝ) + 1) * y)) : ℝ) : ℂ)
      = ((∏ j ∈ range m, 2 * Real.sin (Real.pi * ((2 * (j : ℝ) + 1) * y)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
  rw [prod_congr rfl hfac, prod_mul_distrib, prod_mul_distrib, e1, e2, e3, ← cx_add]
  congr 2
  ring

/-- The product formula at the root of unity `cx (c/n)`, `n = 2m+1`, `c` prime to `n`. -/
lemma root_sum (m n : ℕ) (hn : n = 2 * m + 1) (c : ℤ) (hc : Nat.Coprime c.natAbs n) :
    ∑ k ∈ range n, cx ((c : ℝ) / (n : ℝ)) ^ tri k
      = cx ((m : ℝ) / 4 - (m : ℝ) ^ 2 * ((c : ℝ) / (n : ℝ)) / 2)
        * ((∏ j ∈ range m,
            2 * Real.sin (Real.pi * ((2 * (j : ℝ) + 1) * ((c : ℝ) / (n : ℝ)))) : ℝ) : ℂ) := by
  have hnpos : 0 < n := by omega
  have hz : cx (((-c : ℤ) : ℝ) / (n : ℝ)) ^ (2 * m + 1) = 1 := by
    rw [← hn]
    exact cx_frac_pow_self n hnpos (-c)
  have hz' : ∀ i, 0 < i → i ≤ 2 * m → cx (((-c : ℤ) : ℝ) / (n : ℝ)) ^ i ≠ 1 := by
    intro i hi him
    exact cx_frac_pow_ne_one n (-c) (by rwa [Int.natAbs_neg]) i hi (by omega)
  have hw : cx ((c : ℝ) / (n : ℝ)) * cx (((-c : ℤ) : ℝ) / (n : ℝ)) = 1 := by
    have e : ((-c : ℤ) : ℝ) / (n : ℝ) = -((c : ℝ) / (n : ℝ)) := by
      push_cast
      ring
    rw [e, mul_comm, cx_neg_mul]
  have h := sum_pow_tri m (cx (((-c : ℤ) : ℝ) / (n : ℝ))) (cx ((c : ℝ) / (n : ℝ))) hz hz' hw
  rw [← hn] at h
  rw [h, ← prod_one_sub]
  apply prod_congr rfl
  intro j _
  rw [cx_pow]
  congr 2
  push_cast
  ring

/-! ### The absolute value of the sums -/

lemma norm_of_mul_conj (S : ℂ) (n : ℕ) (h : S * (starRingEnd ℂ) S = (n : ℂ)) :
    ‖S‖ = Real.sqrt (n : ℝ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  have h2 : ‖S‖ ^ 2 = (n : ℝ) := by exact_mod_cast h
  rw [← h2, Real.sqrt_sq (norm_nonneg S)]

lemma norm_sum_pow (n r : ℕ) (c : ℕ → ℕ) (hn : 0 < n)
    (hc : ∀ l d, c (l + d) = c l + c d + r * d * l) (hcn : n ∣ c n)
    (hr : Nat.Coprime r n) (hc0 : c 0 = 0) :
    ‖∑ k ∈ range n, cx (1 / (n : ℝ)) ^ c k‖ = Real.sqrt (n : ℝ) := by
  have hw : cx (1 / (n : ℝ)) ^ n = 1 := cx_one_div_pow_self n hn
  have hw' : ∀ i, 0 < i → i < n → cx (1 / (n : ℝ)) ^ i ≠ 1 :=
    fun i hi hin => cx_one_div_pow_ne_one n i hi hin
  have hu : cx (-(1 / (n : ℝ))) * cx (1 / (n : ℝ)) = 1 := cx_neg_mul _
  have h := conj_sum_mul n r c (cx (1 / (n : ℝ))) (cx (-(1 / (n : ℝ)))) hn hw hw' hu hc hcn hr hc0
  have hconj : (starRingEnd ℂ) (∑ k ∈ range n, cx (1 / (n : ℝ)) ^ c k)
      = ∑ l ∈ range n, cx (-(1 / (n : ℝ))) ^ c l := by
    rw [map_sum]
    apply sum_congr rfl
    intro l _
    rw [map_pow, conj_cx]
  apply norm_of_mul_conj
  rw [hconj]
  exact h

lemma eq_sqrt_of_norm (S u : ℂ) (P : ℝ) (n : ℕ) (hS : S = u * (P : ℂ)) (hu : ‖u‖ = 1)
    (hP : 0 ≤ P) (hnorm : ‖S‖ = Real.sqrt (n : ℝ)) :
    S = u * ((Real.sqrt (n : ℝ) : ℝ) : ℂ) := by
  have h1 : ‖S‖ = P := by
    rw [hS, norm_mul, hu, one_mul, Complex.norm_real, Real.norm_of_nonneg hP]
  rw [hS, ← hnorm, h1]

/-! ### Signs of sines -/

lemma sin_pi_mul_pos (x : ℝ) (h0 : 0 < x) (h1 : x < 1) : 0 < Real.sin (Real.pi * x) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact mul_pos Real.pi_pos h0
  · nlinarith [Real.pi_pos]

lemma sin_pi_mul_neg (x : ℝ) (h1 : 1 < x) (h2 : x < 2) : Real.sin (Real.pi * x) < 0 := by
  have h := Real.sin_neg_of_neg_of_neg_pi_lt (x := Real.pi * x - 2 * Real.pi)
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  rwa [Real.sin_sub_two_pi] at h

lemma prod_neg_eq (t : ℕ) (b : ℕ → ℝ) :
    ∏ j ∈ range t, b j = (-1) ^ t * ∏ j ∈ range t, (-b j) := by
  have h : ∀ j ∈ range t, b j = (-1) * (-b j) := by
    intro j _
    ring
  rw [prod_congr rfl h, prod_mul_distrib, prod_const, card_range]

/-- If the first `t₀` factors are positive and the next `t` factors are negative, the product
is `(-1)^t` times a positive number. -/
lemma sign_split (a : ℕ → ℝ) (t₀ t : ℕ) (hpos : ∀ j, j < t₀ → 0 < a j)
    (hneg : ∀ j, j < t → a (t₀ + j) < 0) :
    ∃ P : ℝ, 0 < P ∧ ∏ j ∈ range (t₀ + t), a j = (-1) ^ t * P := by
  refine ⟨(∏ j ∈ range t₀, a j) * ∏ j ∈ range t, (-a (t₀ + j)), ?_, ?_⟩
  · apply mul_pos
    · exact prod_pos (fun j hj => hpos j (mem_range.mp hj))
    · exact prod_pos (fun j hj => neg_pos.mpr (hneg j (mem_range.mp hj)))
  · rw [prod_range_add, prod_neg_eq t (fun j => a (t₀ + j))]
    ring

/-! ### The triangular sum -/

lemma two_mul_tri_real (k : ℕ) : (tri k : ℝ) = (k : ℝ) * ((k : ℝ) + 1) / 2 := by
  have h := two_mul_tri k
  have h2 : (2 : ℝ) * (tri k : ℝ) = (k : ℝ) * ((k : ℝ) + 1) := by exact_mod_cast h
  linarith

lemma tri_add (l d : ℕ) : tri (l + d) = tri l + tri d + 1 * d * l := by
  have h1 := two_mul_tri (l + d)
  have h2 := two_mul_tri l
  have h3 := two_mul_tri d
  have h4 : 2 * tri (l + d) = 2 * (tri l + tri d + 1 * d * l) := by
    have e : 2 * (tri l + tri d + 1 * d * l) = 2 * tri l + 2 * tri d + 2 * d * l := by ring
    rw [h1, e, h2, h3]
    ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h4

theorem sum_tri_cx (m n : ℕ) (hn : n = 2 * m + 1) :
    ∑ k ∈ range n, cx ((k : ℝ) * ((k : ℝ) + 1) / (2 * (n : ℝ)))
      = cx (((n : ℝ) - 1) / (8 * (n : ℝ))) * ((Real.sqrt (n : ℝ) : ℝ) : ℂ) := by
  have hnpos : 0 < n := by omega
  have hN : (n : ℝ) = 2 * (m : ℝ) + 1 := by
    rw [hn]
    push_cast
    ring
  have hN0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hterm : ∀ k ∈ range n, cx ((k : ℝ) * ((k : ℝ) + 1) / (2 * (n : ℝ)))
      = cx (1 / (n : ℝ)) ^ tri k := by
    intro k _
    rw [cx_pow, two_mul_tri_real]
    congr 1
    ring
  have hroot := root_sum m n hn 1 (by simp)
  rw [Int.cast_one] at hroot
  have hpos : 0 < ∏ j ∈ range m,
      2 * Real.sin (Real.pi * ((2 * (j : ℝ) + 1) * (1 / (n : ℝ)))) := by
    apply prod_pos
    intro j hj
    have hj' := mem_range.mp hj
    have hjn : (2 * (j : ℝ) + 1) < (n : ℝ) := by
      rw [hN]
      have : (j : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hj'
      linarith
    have hx0 : 0 < (2 * (j : ℝ) + 1) * (1 / (n : ℝ)) := by positivity
    have hx1 : (2 * (j : ℝ) + 1) * (1 / (n : ℝ)) < 1 := by
      rw [mul_one_div, div_lt_one hN0]
      exact hjn
    have := sin_pi_mul_pos _ hx0 hx1
    linarith
  have hnorm : ‖∑ k ∈ range n, cx (1 / (n : ℝ)) ^ tri k‖ = Real.sqrt (n : ℝ) := by
    apply norm_sum_pow n 1 tri hnpos tri_add
    · refine ⟨m + 1, ?_⟩
      have h := two_mul_tri n
      have h4 : 2 * tri n = 2 * (n * (m + 1)) := by
        rw [h, hn]
        ring
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h4
    · exact Nat.coprime_one_left n
    · rfl
  have hfinal := eq_sqrt_of_norm _ _ _ n hroot (norm_cx _) hpos.le hnorm
  rw [sum_congr rfl hterm, hfinal]
  congr 2
  rw [hN]
  field_simp
  ring

/-! ### The sum over squares -/

lemma sq_add' (l d : ℕ) : (l + d) ^ 2 = l ^ 2 + d ^ 2 + 2 * d * l := by ring

/-- The sum over squares as `i^m` times a product of real sines. -/
lemma sum_sq_core (m n : ℕ) (hn : n = 2 * m + 1) :
    ∑ k ∈ range n, cx (1 / (n : ℝ)) ^ (k ^ 2)
      = Complex.I ^ m * ((∏ j ∈ range m,
          2 * Real.sin (Real.pi * ((2 * (j : ℝ) + 1) * (2 / (n : ℝ)))) : ℝ) : ℂ) := by
  have hnpos : 0 < n := by omega
  have hN : (n : ℝ) = 2 * (m : ℝ) + 1 := by
    rw [hn]
    push_cast
    ring
  have hN0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hnpos.ne'
  have hw : cx (1 / (n : ℝ)) ^ n = 1 := cx_one_div_pow_self n hnpos
  have hper : ∀ k, cx (1 / (n : ℝ)) ^ ((k + n) ^ 2) = cx (1 / (n : ℝ)) ^ (k ^ 2) := by
    intro k
    rw [show (k + n) ^ 2 = k ^ 2 + n * (2 * k + n) by ring, pow_add, pow_mul, hw, one_pow,
      mul_one]
  have hshift : ∑ d ∈ range n, cx (1 / (n : ℝ)) ^ ((m + 1 + d) ^ 2)
      = ∑ k ∈ range n, cx (1 / (n : ℝ)) ^ (k ^ 2) :=
    sum_range_shift n (fun k => cx (1 / (n : ℝ)) ^ (k ^ 2)) hper (m + 1)
  have hd : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  have hterm : ∀ d ∈ range n, cx (1 / (n : ℝ)) ^ ((m + 1 + d) ^ 2)
      = cx (((m : ℝ) + 1) ^ 2 / (n : ℝ)) * cx (((2 : ℤ) : ℝ) / (n : ℝ)) ^ tri d := by
    intro d _
    rw [cx_pow, cx_pow, ← cx_add, two_mul_tri_real]
    have e : ((((m + 1 + d) ^ 2 : ℕ) : ℝ)) * (1 / (n : ℝ))
        = (((m : ℝ) + 1) ^ 2 / (n : ℝ)
          + (d : ℝ) * ((d : ℝ) + 1) / 2 * (((2 : ℤ) : ℝ) / (n : ℝ))) + (d : ℝ) := by
      push_cast
      rw [hN]
      field_simp
      ring
    rw [e, cx_add_nat]
  have hroot := root_sum m n hn 2
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega))
  have h2 : (((2 : ℤ) : ℝ)) = 2 := by norm_num
  rw [← hshift, sum_congr rfl hterm, ← mul_sum, hroot, ← mul_assoc, ← cx_add, h2]
  have e : ((m : ℝ) + 1) ^ 2 / (n : ℝ) + ((m : ℝ) / 4 - (m : ℝ) ^ 2 * (2 / (n : ℝ)) / 2)
      = (m : ℝ) * (1 / 4) + ((1 : ℕ) : ℝ) := by
    rw [hN]
    push_cast
    field_simp
    ring
  rw [e, cx_add_nat, ← cx_pow, cx_quarter]

lemma norm_sum_sq (m n : ℕ) (hn : n = 2 * m + 1) :
    ‖∑ k ∈ range n, cx (1 / (n : ℝ)) ^ (k ^ 2)‖ = Real.sqrt (n : ℝ) := by
  apply norm_sum_pow n 2 (fun k => k ^ 2) (by omega) sq_add'
  · exact ⟨n, sq n⟩
  · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
  · simp

lemma cx_sq_term (n k : ℕ) : cx ((k : ℝ) ^ 2 / (n : ℝ)) = cx (1 / (n : ℝ)) ^ (k ^ 2) := by
  rw [cx_pow]
  congr 1
  push_cast
  ring

/-- The factors of the sine product for the sum over squares. -/
noncomputable def sinFac (n : ℕ) (j : ℕ) : ℝ :=
  2 * Real.sin (Real.pi * ((2 * (j : ℝ) + 1) * (2 / (n : ℝ))))

lemma sinFac_pos (n j : ℕ) (hn : 0 < n) (h : 2 * (2 * j + 1) < n) : 0 < sinFac n j := by
  have hN0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h' : (2 * (2 * (j : ℝ) + 1)) < (n : ℝ) := by exact_mod_cast h
  have hx0 : 0 < (2 * (j : ℝ) + 1) * (2 / (n : ℝ)) := by positivity
  have hx1 : (2 * (j : ℝ) + 1) * (2 / (n : ℝ)) < 1 := by
    rw [mul_div_assoc', div_lt_one hN0]
    linarith
  have := sin_pi_mul_pos _ hx0 hx1
  unfold sinFac
  linarith

lemma sinFac_neg (n j : ℕ) (hn : 0 < n) (h1 : n < 2 * (2 * j + 1)) (h2 : 2 * (2 * j + 1) < 2 * n) :
    sinFac n j < 0 := by
  have hN0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1' : (n : ℝ) < (2 * (2 * (j : ℝ) + 1)) := by exact_mod_cast h1
  have h2' : (2 * (2 * (j : ℝ) + 1)) < 2 * (n : ℝ) := by exact_mod_cast h2
  have hx1 : 1 < (2 * (j : ℝ) + 1) * (2 / (n : ℝ)) := by
    rw [mul_div_assoc', one_lt_div hN0]
    linarith
  have hx2 : (2 * (j : ℝ) + 1) * (2 / (n : ℝ)) < 2 := by
    rw [mul_div_assoc', div_lt_iff₀ hN0]
    linarith
  have := sin_pi_mul_neg _ hx1 hx2
  unfold sinFac
  linarith

theorem sum_sq_cx (n : ℕ) (hn : n % 2 = 1) :
    ∑ k ∈ range n, cx ((k : ℝ) ^ 2 / (n : ℝ))
      = if n % 4 = 1 then ((Real.sqrt (n : ℝ) : ℝ) : ℂ)
        else Complex.I * ((Real.sqrt (n : ℝ) : ℝ) : ℂ) := by
  have hnpos : 0 < n := by omega
  rw [sum_congr rfl (fun k _ => cx_sq_term n k)]
  by_cases h4 : n % 4 = 1
  · rw [if_pos h4]
    obtain ⟨t, ht⟩ : ∃ t, n = 4 * t + 1 := ⟨n / 4, by omega⟩
    have hn' : n = 2 * (t + t) + 1 := by omega
    have hcore : ∑ k ∈ range n, cx (1 / (n : ℝ)) ^ (k ^ 2)
        = Complex.I ^ (t + t) * ((∏ j ∈ range (t + t), sinFac n j : ℝ) : ℂ) :=
      sum_sq_core (t + t) n hn'
    have hnorm := norm_sum_sq (t + t) n hn'
    obtain ⟨P, hP, hQ⟩ := sign_split (sinFac n) t t
      (fun j hj => sinFac_pos n j hnpos (by omega))
      (fun j hj => sinFac_neg n (t + j) hnpos (by omega) (by omega))
    have hI : Complex.I ^ (t + t) * ((-1 : ℂ)) ^ t = 1 := by
      rw [← two_mul, pow_mul, Complex.I_sq, ← mul_pow]
      simp
    have hS : ∑ k ∈ range n, cx (1 / (n : ℝ)) ^ (k ^ 2) = 1 * (P : ℂ) := by
      rw [hcore, hQ]
      push_cast
      linear_combination (P : ℂ) * hI
    have hfinal := eq_sqrt_of_norm _ _ _ n hS (by simp) hP.le hnorm
    rw [hfinal, one_mul]
  · rw [if_neg h4]
    obtain ⟨t, ht⟩ : ∃ t, n = 4 * t + 3 := ⟨n / 4, by omega⟩
    have hn' : n = 2 * (t + 1 + t) + 1 := by omega
    have hcore : ∑ k ∈ range n, cx (1 / (n : ℝ)) ^ (k ^ 2)
        = Complex.I ^ (t + 1 + t) * ((∏ j ∈ range (t + 1 + t), sinFac n j : ℝ) : ℂ) :=
      sum_sq_core (t + 1 + t) n hn'
    have hnorm := norm_sum_sq (t + 1 + t) n hn'
    obtain ⟨P, hP, hQ⟩ := sign_split (sinFac n) (t + 1) t
      (fun j hj => sinFac_pos n j hnpos (by omega))
      (fun j hj => sinFac_neg n (t + 1 + j) hnpos (by omega) (by omega))
    have hI : Complex.I ^ (t + 1 + t) * ((-1 : ℂ)) ^ t = Complex.I := by
      rw [show t + 1 + t = 2 * t + 1 by ring, pow_succ, pow_mul, Complex.I_sq, mul_right_comm,
        ← mul_pow]
      simp
    have hS : ∑ k ∈ range n, cx (1 / (n : ℝ)) ^ (k ^ 2) = Complex.I * (P : ℂ) := by
      rw [hcore, hQ]
      push_cast
      linear_combination (P : ℂ) * hI
    have hfinal := eq_sqrt_of_norm _ _ _ n hS (by simp) hP.le hnorm
    rw [hfinal]

end TuringTask
