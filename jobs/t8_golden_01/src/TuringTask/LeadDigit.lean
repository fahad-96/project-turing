import Mathlib
import TuringTask.Counting

/-!
# Leading decimal digits through fractional parts of logarithms

* `logb_ten_two_irrational`: `log_10 2` is irrational (`2^q = 10^p` is impossible for `q >= 1`).
* `div_pow_log_eq_iff`: for `m >= 1` and `1 <= d <= 9`, the leading digit
  `m / 10 ^ Nat.log 10 m` equals `d` iff `log_10 d <= fract (log_10 m) < log_10 (d + 1)`.
-/

open Finset Filter

namespace TuringTask

lemma logb_ten_two_irrational : Irrational (Real.logb 10 2) := by
  rintro ⟨q, hq⟩
  have hpos : (0 : ℝ) < Real.logb 10 2 := Real.logb_pos (by norm_num) (by norm_num)
  have hq0 : 0 < q := by
    have : (0 : ℝ) < q := hq ▸ hpos
    exact_mod_cast this
  have hnum : 0 < q.num := Rat.num_pos.mpr hq0
  set p : ℕ := q.num.toNat with hp
  have hpnum : (p : ℤ) = q.num := Int.toNat_of_nonneg hnum.le
  have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hqr : (q : ℝ) = p / q.den := by
    rw [Rat.cast_def]
    congr 1
    exact_mod_cast hpnum.symm
  have hl2 : (0 : ℝ) < Real.log 10 := Real.log_pos (by norm_num)
  have hlog : (p : ℝ) * Real.log 10 = q.den * Real.log 2 := by
    rw [hqr, Real.logb] at hq
    field_simp at hq
    linarith
  have hpow : (10 : ℝ) ^ p = 2 ^ q.den := by
    rw [← Real.log_pow, ← Real.log_pow] at hlog
    have := congrArg Real.exp hlog
    rwa [Real.exp_log (by positivity), Real.exp_log (by positivity)] at this
  have hnat : (10 : ℕ) ^ p = 2 ^ q.den := by exact_mod_cast hpow
  rcases Nat.eq_zero_or_pos p with h0 | h0
  · rw [h0, pow_zero] at hnat
    have : 1 < 2 ^ q.den := Nat.one_lt_two_pow q.den_pos.ne'
    omega
  · have h5 : 5 ∣ 2 ^ q.den := by
      rw [← hnat]
      exact Dvd.dvd.pow (by norm_num) h0.ne'
    have := (Nat.Prime.dvd_of_dvd_pow (by norm_num) h5)
    omega

lemma logb_cast_mul_pow (d k : ℕ) (hd : d ≠ 0) :
    Real.logb 10 ((d : ℝ) * 10 ^ k) = Real.logb 10 d + k := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  rw [Real.logb_mul hd' (by positivity), Real.logb_pow, Real.logb_self_eq_one (by norm_num),
    mul_one]

/-- Leading decimal digit and the fractional part of the logarithm. -/
lemma div_pow_log_eq_iff (m d : ℕ) (hm : 1 ≤ m) (hd1 : 1 ≤ d) :
    m / 10 ^ Nat.log 10 m = d ↔
      Real.logb 10 d ≤ Int.fract (Real.logb 10 m) ∧
        Int.fract (Real.logb 10 m) < Real.logb 10 ((d : ℝ) + 1) := by
  set k := Nat.log 10 m with hk
  have h1 : 10 ^ k ≤ m := Nat.pow_log_le_self 10 (by omega)
  have h2 : m < 10 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hfl : Int.fract (Real.logb 10 m) = Real.logb 10 m - k := by
    rw [Int.fract, sub_right_inj]
    have : ⌊Real.logb 10 (m : ℝ)⌋ = (k : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor
      · have e := logb_cast_mul_pow 1 k one_ne_zero
        rw [Nat.cast_one, one_mul, Real.logb_one, zero_add] at e
        push_cast
        rw [← e]
        exact (Real.logb_le_logb (by norm_num) (by positivity) hm').mpr (by exact_mod_cast h1)
      · have e := logb_cast_mul_pow 1 (k + 1) one_ne_zero
        rw [Nat.cast_one, one_mul, Real.logb_one, zero_add] at e
        push_cast at e ⊢
        rw [← e]
        exact (Real.logb_lt_logb_iff (by norm_num) hm' (by positivity)).mpr
          (by exact_mod_cast h2)
    rw [this]
    rfl
  rw [hfl]
  have hlow : Real.logb 10 d ≤ Real.logb 10 m - k ↔ d * 10 ^ k ≤ m := by
    rw [le_sub_iff_add_le, ← logb_cast_mul_pow d k (by omega),
      Real.logb_le_logb (by norm_num) (by positivity) hm']
    exact_mod_cast Iff.rfl
  have hup : Real.logb 10 m - k < Real.logb 10 ((d : ℝ) + 1) ↔ m < (d + 1) * 10 ^ k := by
    have e := logb_cast_mul_pow (d + 1) k (by omega)
    push_cast at e
    rw [sub_lt_iff_lt_add, ← e, Real.logb_lt_logb_iff (by norm_num) hm' (by positivity)]
    exact_mod_cast Iff.rfl
  rw [hlow, hup]
  have hpos : 0 < 10 ^ k := by positivity
  constructor
  · intro h
    rw [← h]
    exact ⟨Nat.div_mul_le_self m _, by
      have := Nat.lt_div_mul_add (a := m) hpos
      rw [add_mul, one_mul]
      exact this⟩
  · rintro ⟨hl, hu⟩
    have a1 : d ≤ m / 10 ^ k := (Nat.le_div_iff_mul_le hpos).mpr hl
    have a2 : m / 10 ^ k < d + 1 := (Nat.div_lt_iff_lt_mul hpos).mpr hu
    omega

end TuringTask
