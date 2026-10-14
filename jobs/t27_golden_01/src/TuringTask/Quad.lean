import Mathlib

/-!
# Positive definite quadratic rings `ℤ[ω]`, `ω^2 = a + b ω`

We work in Mathlib's `QuadraticAlgebra ℤ a b` with `-2 ≤ a` and `b^2 + 4 a ≤ -3`, so the norm
`N(x + y ω) = x^2 + b x y - a y^2` is positive definite.

* `norm_mk`, `four_norm`, `nm_nonneg`, `eq_zero_of_norm_eq_zero`, `mul_left_cancel'`: the
  norm and cancellation.
* `in_box`: a solution of `N(x + y ω) = n ≥ 1` has `|x|, |y| ≤ n`.
* `cnt a b n`: the number of pairs `(x, y)` in the box `[-n, n]^2` with `N(x + y ω) = n`.
* `cnt_dvd`: for `c` with `N(c) = k` and `k ∣ n`, the solutions divisible by `c` are the
  products `c w` with `N(w) = n / k`, so there are `cnt a b (n / k)` of them.
* The second part of the file treats divisor sums of a completely multiplicative function.
-/

namespace TuringTask

variable {a b : ℤ}

local notation "Nm" => QuadraticAlgebra.norm

lemma norm_mk (x y : ℤ) :
    Nm (⟨x, y⟩ : QuadraticAlgebra ℤ a b) = x ^ 2 + b * x * y - a * y ^ 2 := by
  rw [QuadraticAlgebra.norm_def]; ring

lemma four_norm (z : QuadraticAlgebra ℤ a b) :
    4 * Nm z = (2 * z.re + b * z.im) ^ 2 - (b ^ 2 + 4 * a) * z.im ^ 2 := by
  rw [QuadraticAlgebra.norm_def]; ring

lemma four_a_norm (z : QuadraticAlgebra ℤ a b) :
    -4 * a * Nm z = (2 * a * z.im - b * z.re) ^ 2 - (b ^ 2 + 4 * a) * z.re ^ 2 := by
  rw [QuadraticAlgebra.norm_def]; ring

lemma nm_nonneg (hD : b ^ 2 + 4 * a < 0) (z : QuadraticAlgebra ℤ a b) : 0 ≤ Nm z := by
  have := four_norm z
  nlinarith [sq_nonneg (2 * z.re + b * z.im), sq_nonneg z.im]

lemma eq_zero_of_norm_eq_zero (hD : b ^ 2 + 4 * a < 0) {z : QuadraticAlgebra ℤ a b}
    (h : Nm z = 0) : z = 0 := by
  have h4 := four_norm z
  rw [h] at h4
  have him : z.im = 0 := by
    nlinarith [sq_nonneg (2 * z.re + b * z.im), sq_nonneg z.im]
  rw [him] at h4
  have hre : z.re = 0 := by nlinarith [sq_nonneg z.re]
  ext
  · exact hre
  · exact him

lemma mul_left_cancel' (hD : b ^ 2 + 4 * a < 0) {c w₁ w₂ : QuadraticAlgebra ℤ a b} (hc : c ≠ 0)
    (h : c * w₁ = c * w₂) : w₁ = w₂ := by
  have h0 : c * (w₁ - w₂) = 0 := by rw [mul_sub, h, sub_self]
  have hn := congrArg QuadraticAlgebra.norm h0
  rw [map_mul, QuadraticAlgebra.norm_zero] at hn
  rcases mul_eq_zero.mp hn with h1 | h1
  · exact absurd (eq_zero_of_norm_eq_zero hD h1) hc
  · exact sub_eq_zero.mp (eq_zero_of_norm_eq_zero hD h1)

lemma in_box (ha : -2 ≤ a) (hD : b ^ 2 + 4 * a ≤ -3) {x y : ℤ} {n : ℕ}
    (h : x ^ 2 + b * x * y - a * y ^ 2 = n) (hn : 1 ≤ n) :
    -(n : ℤ) ≤ x ∧ x ≤ n ∧ -(n : ℤ) ≤ y ∧ y ≤ n := by
  have h1 := four_norm (⟨x, y⟩ : QuadraticAlgebra ℤ a b)
  have h2 := four_a_norm (⟨x, y⟩ : QuadraticAlgebra ℤ a b)
  rw [norm_mk, h] at h1 h2
  simp only at h1 h2
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hy : 3 * y ^ 2 ≤ 4 * n := by nlinarith [sq_nonneg (2 * x + b * y)]
  have hx : 3 * x ^ 2 ≤ 8 * n := by nlinarith [sq_nonneg (2 * a * y - b * x), sq_nonneg x]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases le_or_gt (-1) x with h' | h'
    · linarith
    · nlinarith
  · rcases le_or_gt x 1 with h' | h'
    · linarith
    · nlinarith
  · rcases le_or_gt (-1) y with h' | h'
    · linarith
    · nlinarith
  · rcases le_or_gt y 1 with h' | h'
    · linarith
    · nlinarith

/-- The box `[-n, n]^2` of the prompt. -/
noncomputable def box (n : ℕ) : Finset (ℤ × ℤ) :=
  Finset.product (Finset.Icc (-(n : ℤ)) n) (Finset.Icc (-(n : ℤ)) n)

/-- The number of pairs in the box with `N(x + y ω) = n`. -/
noncomputable def cnt (a b : ℤ) (n : ℕ) : ℕ :=
  ((box n).filter (fun v : ℤ × ℤ => v.1 ^ 2 + b * v.1 * v.2 - a * v.2 ^ 2 = n)).card

lemma mem_box {n : ℕ} {v : ℤ × ℤ} : v ∈ box n ↔
    (-(n : ℤ) ≤ v.1 ∧ v.1 ≤ n) ∧ (-(n : ℤ) ≤ v.2 ∧ v.2 ≤ n) := by
  simp [box, Finset.mem_product]

open scoped Classical in
/-- Solutions divisible by `c` with `N(c) = k` correspond to the solutions for `n / k`. -/
lemma cnt_dvd (ha : -2 ≤ a) (hD : b ^ 2 + 4 * a ≤ -3) (c : QuadraticAlgebra ℤ a b) {k n : ℕ}
    (hk : Nm c = k) (hk1 : 1 ≤ k) (hkn : k ∣ n) (hn : 1 ≤ n) :
    ((box n).filter (fun v : ℤ × ℤ => v.1 ^ 2 + b * v.1 * v.2 - a * v.2 ^ 2 = n ∧
      c ∣ (⟨v.1, v.2⟩ : QuadraticAlgebra ℤ a b))).card = cnt a b (n / k) := by
  have hD' : b ^ 2 + 4 * a < 0 := by omega
  have hc0 : c ≠ 0 := by
    intro h; rw [h, QuadraticAlgebra.norm_zero] at hk; omega
  obtain ⟨m, rfl⟩ := hkn
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; omega
    · exact h
  rw [Nat.mul_div_cancel_left _ (by omega)]
  symm
  apply Finset.card_bij (fun w _ => ((c * ⟨w.1, w.2⟩).re, (c * ⟨w.1, w.2⟩).im))
  · intro w hw
    rw [Finset.mem_filter] at hw ⊢
    have hN : Nm (c * ⟨w.1, w.2⟩ : QuadraticAlgebra ℤ a b) = (k * m : ℕ) := by
      rw [map_mul, hk, norm_mk, hw.2]; push_cast; ring
    have hN' : (c * ⟨w.1, w.2⟩).re ^ 2 + b * (c * ⟨w.1, w.2⟩).re * (c * ⟨w.1, w.2⟩).im -
        a * (c * ⟨w.1, w.2⟩).im ^ 2 = ((k * m : ℕ) : ℤ) := by
      rw [← hN, QuadraticAlgebra.norm_def]; ring
    obtain ⟨b1, b2, b3, b4⟩ := in_box ha hD hN' (by nlinarith)
    refine ⟨mem_box.mpr ⟨⟨b1, b2⟩, b3, b4⟩, hN', ⟨⟨w.1, w.2⟩, rfl⟩⟩
  · intro w₁ _ w₂ _ h
    simp only [Prod.mk.injEq] at h
    have : c * ⟨w₁.1, w₁.2⟩ = c * ⟨w₂.1, w₂.2⟩ := QuadraticAlgebra.ext h.1 h.2
    have := mul_left_cancel' hD' hc0 this
    exact Prod.ext (congrArg QuadraticAlgebra.re this) (congrArg QuadraticAlgebra.im this)
  · intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨-, hvn, w, hw⟩ := hv
    have hN : Nm (⟨v.1, v.2⟩ : QuadraticAlgebra ℤ a b) = ((k * m : ℕ) : ℤ) := by
      rw [norm_mk, hvn]
    rw [hw, map_mul, hk] at hN
    have hwm : Nm w = m := by
      push_cast at hN
      have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
      exact mul_left_cancel₀ hk0 hN
    have hwm' : w.re ^ 2 + b * w.re * w.im - a * w.im ^ 2 = (m : ℤ) := by
      rw [← hwm, QuadraticAlgebra.norm_def]; ring
    obtain ⟨b1, b2, b3, b4⟩ := in_box ha hD hwm' hm1
    refine ⟨(w.re, w.im), Finset.mem_filter.mpr ⟨mem_box.mpr ⟨⟨b1, b2⟩, b3, b4⟩, hwm'⟩, ?_⟩
    simp only
    rw [show (⟨w.re, w.im⟩ : QuadraticAlgebra ℤ a b) = w from rfl, ← hw]

end TuringTask

/-!
# Divisor sums of a completely multiplicative function

For `χ : ℕ → ℤ` with `χ (m n) = χ m χ n` let `S n = ∑_{d ∣ n} χ d`. For a prime `p ∣ n`, split
the divisors by `p ∣ d`: `S n = T n + χ p S (n / p)`, where `T n` sums over the divisors prime to
`p` and `T n = T (n / p)` (`divSum_split`, `T_div`). This gives
* `χ p = 1`: `S n = 2 S (n / p) - S (n / p^2)` (the last term only when `p^2 ∣ n`),
* `χ p = 0`: `S n = S (n / p)`,
* `χ p = -1`: `S n = S (n / p^2)` when `p^2 ∣ n`, and `S n = 0` otherwise.
-/

namespace TuringTask

/-- `∑_{d ∣ n} χ d`. -/
def divSum (χ : ℕ → ℤ) (n : ℕ) : ℤ := ∑ d ∈ n.divisors, χ d

/-- The part of `divSum` over divisors prime to `p`. -/
def divSumT (χ : ℕ → ℤ) (p n : ℕ) : ℤ := ∑ d ∈ n.divisors.filter (fun d => ¬ p ∣ d), χ d

variable {χ : ℕ → ℤ}

lemma divisors_filter_dvd {p n : ℕ} (hp : 0 < p) (hpn : p ∣ n) (hn : n ≠ 0) :
    n.divisors.filter (fun d => p ∣ d) =
      (n / p).divisors.map ⟨fun e => p * e, fun _ _ h => Nat.eq_of_mul_eq_mul_left hp h⟩ := by
  obtain ⟨m, rfl⟩ := hpn
  have hm : m ≠ 0 := by rintro rfl; simp at hn
  rw [Nat.mul_div_cancel_left _ hp]
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_map]
  constructor
  · rintro ⟨⟨hd, -⟩, ⟨e, rfl⟩⟩
    exact ⟨e, ⟨(Nat.mul_dvd_mul_iff_left hp).mp hd, hm⟩, rfl⟩
  · rintro ⟨e, ⟨he, -⟩, rfl⟩
    exact ⟨⟨Nat.mul_dvd_mul_left p he, hn⟩, dvd_mul_right p e⟩

lemma divSum_split (hmul : ∀ m n, m ≠ 0 → n ≠ 0 → χ (m * n) = χ m * χ n) {p n : ℕ}
    (hp : p.Prime) (hpn : p ∣ n) (hn : n ≠ 0) :
    divSum χ n = divSumT χ p n + χ p * divSum χ (n / p) := by
  unfold divSum divSumT
  rw [← Finset.sum_filter_add_sum_filter_not n.divisors (fun d => p ∣ d), add_comm,
    divisors_filter_dvd hp.pos hpn hn, Finset.sum_map, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun e he =>
    hmul p e hp.ne_zero (Nat.ne_of_gt (Nat.pos_of_mem_divisors he))

lemma divSumT_div {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hn : n ≠ 0) :
    divSumT χ p n = divSumT χ p (n / p) := by
  unfold divSumT
  congr 1
  obtain ⟨m, rfl⟩ := hpn
  have hm : m ≠ 0 := by rintro rfl; simp at hn
  rw [Nat.mul_div_cancel_left _ hp.pos]
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, -⟩, hpd⟩
    have hc : Nat.Coprime d p := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd))
    exact ⟨⟨hc.dvd_of_dvd_mul_left hd, hm⟩, hpd⟩
  · rintro ⟨⟨hd, -⟩, hpd⟩
    exact ⟨⟨Dvd.dvd.mul_left hd p, hn⟩, hpd⟩

lemma divSum_eq_T {p n : ℕ} (hpn : ¬ p ∣ n) : divSum χ n = divSumT χ p n := by
  unfold divSum divSumT
  congr 1
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨hd, hn⟩
    exact ⟨⟨hd, hn⟩, fun h => hpn (h.trans hd)⟩
  · rintro ⟨h, -⟩
    exact h

/-- The three recursions for a prime `p ∣ n`. -/
lemma divSum_rec (hmul : ∀ m n, m ≠ 0 → n ≠ 0 → χ (m * n) = χ m * χ n) {p n : ℕ}
    (hp : p.Prime) (hpn : p ∣ n) (hn : n ≠ 0) :
    (χ p = 1 → divSum χ n = 2 * divSum χ (n / p) - if p ^ 2 ∣ n then divSum χ (n / p ^ 2) else 0) ∧
    (χ p = 0 → divSum χ n = divSum χ (n / p)) ∧
    (χ p = -1 → divSum χ n = if p ^ 2 ∣ n then divSum χ (n / p ^ 2) else 0) := by
  have h1 := divSum_split hmul hp hpn hn
  have hT := divSumT_div (χ := χ) hp hpn hn
  have hnp : n / p ≠ 0 := Nat.div_ne_zero_iff_of_dvd hpn |>.mpr ⟨hn, hp.ne_zero⟩
  have hS : divSum χ (n / p) =
      divSumT χ p (n / p) + if p ^ 2 ∣ n then χ p * divSum χ (n / p ^ 2) else 0 := by
    by_cases h2 : p ^ 2 ∣ n
    · have hd : p ∣ n / p := by
        obtain ⟨k, hk⟩ := h2
        exact ⟨k, by rw [hk, sq, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]⟩
      rw [if_pos h2, divSum_split hmul hp hd hnp, Nat.div_div_eq_div_mul, ← sq]
    · have hd : ¬ p ∣ n / p := by
        rintro ⟨k, hk⟩
        apply h2
        exact ⟨k, by rw [sq, mul_assoc, ← hk, Nat.mul_div_cancel' hpn]⟩
      rw [if_neg h2, add_zero]
      exact divSum_eq_T hd
  refine ⟨fun hc => ?_, fun hc => ?_, fun hc => ?_⟩
  · rw [hc] at h1 hS
    split_ifs at hS ⊢ <;> linarith
  · rw [hc] at h1 hS
    split_ifs at hS <;> linarith
  · rw [hc] at h1 hS
    split_ifs at hS ⊢ <;> linarith

end TuringTask
