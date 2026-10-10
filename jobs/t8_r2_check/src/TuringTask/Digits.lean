import Mathlib
import TuringTask.Bridge

/-!
# Leading decimal digits of powers of two

We show `Real.logb 10 2` is irrational and characterise the leading decimal digit of `2 ^ E`
in terms of the fractional part of `E * Real.logb 10 2`.
-/

open Finset Filter Complex Polynomial MeasureTheory AddCircle Real

namespace TuringTask

noncomputable section

set_option maxHeartbeats 1000000

def Lg : ℝ := Real.logb 10 2

lemma Lg_pos : 0 < Lg := Real.logb_pos (by norm_num) (by norm_num)

lemma Lg_irrational : Irrational Lg := by
  rw [Lg, irrational_iff_ne_rational]
  intro a b hb hc
  have hq : Real.logb 10 2 = ((a/b : ℚ) : ℝ) := by rw [hc]; push_cast; ring
  revert hq
  generalize ((a/b : ℚ)) = q
  intro h
  have h2 : (0:ℝ) < 2 := by norm_num
  have hqe : (10:ℝ) ^ (q:ℝ) = 2 := by
    rw [← h, Real.rpow_logb (by norm_num) (by norm_num) h2]
  have hqpos : 0 < q := by
    by_contra hcc
    rw [not_lt] at hcc
    have : (10:ℝ) ^ (q:ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by exact_mod_cast hcc)
    rw [hqe] at this; norm_num at this
  set p := q.num.toNat with hp
  set r := q.den with hr
  have hrpos : 0 < r := q.pos
  have hqab : (q:ℝ) = (p:ℝ)/(r:ℝ) := by
    rw [hp, hr, Rat.cast_def]
    congr 1
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (le_of_lt (Rat.num_pos.2 hqpos))]
  have hkey : (10:ℝ)^(p:ℕ) = (2:ℝ)^(r:ℕ) := by
    have hb0 : (r:ℝ) ≠ 0 := by positivity
    have hcg := congrArg (fun z : ℝ => z ^ (r:ℝ)) hqe
    rw [← Real.rpow_natCast (10:ℝ) p, ← Real.rpow_natCast (2:ℝ) r]
    rw [← hcg, ← Real.rpow_mul (by norm_num), hqab]
    congr 1
    field_simp
  have hnat : (10:ℕ)^p = 2^r := by exact_mod_cast hkey
  have hppos : 0 < p := by
    rw [hp]
    have := Rat.num_pos.2 hqpos
    omega
  have h5 : (5:ℕ) ∣ 10^p := dvd_pow (by norm_num) (by omega)
  rw [hnat] at h5
  have := Nat.Prime.dvd_of_dvd_pow (p := 5) (by norm_num) h5
  norm_num at this

lemma two_pow_eq_rpow (E : ℕ) : ((2:ℝ)^E) = (10:ℝ) ^ ((E:ℝ) * Lg) := by
  rw [Lg, mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) (by norm_num), Real.rpow_natCast]

lemma natlog_two_pow (E : ℕ) : Nat.log 10 (2^E) = ⌊(E:ℝ) * Lg⌋.toNat := by
  set t : ℝ := (E:ℝ) * Lg with ht
  have ht0 : 0 ≤ t := by rw [ht]; exact mul_nonneg (Nat.cast_nonneg E) Lg_pos.le
  set k : ℤ := ⌊t⌋ with hk
  have hk0 : 0 ≤ k := Int.floor_nonneg.2 ht0
  have hcast : ((k.toNat : ℕ) : ℝ) = ((k : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => ((z:ℤ):ℝ)) (Int.toNat_of_nonneg hk0)
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · have h1 : ((10:ℝ))^(k.toNat) ≤ (2:ℝ)^E := by
      rw [two_pow_eq_rpow E, ← ht,
        show ((10:ℝ))^(k.toNat) = (10:ℝ)^((k.toNat : ℝ)) by rw [Real.rpow_natCast]]
      refine (Real.rpow_le_rpow_left_iff (by norm_num)).2 ?_
      rw [hcast, hk]; exact Int.floor_le t
    exact_mod_cast h1
  · have h1 : (2:ℝ)^E < ((10:ℝ))^(k.toNat + 1) := by
      rw [two_pow_eq_rpow E, ← ht,
        show ((10:ℝ))^(k.toNat+1) = (10:ℝ)^(((k.toNat+1 : ℕ)) : ℝ) by rw [Real.rpow_natCast]]
      refine (Real.rpow_lt_rpow_left_iff (by norm_num)).2 ?_
      push_cast
      rw [hcast, hk]; exact Int.lt_floor_add_one t
    exact_mod_cast h1

lemma digit_lower (d : ℕ) (hd : 1 ≤ d) (t : ℝ) :
    ((d:ℝ) * (10:ℝ)^(⌊t⌋ : ℤ) ≤ (10:ℝ)^t) ↔ Real.logb 10 d ≤ Int.fract t := by
  set s : ℝ := Real.logb 10 d with hs
  have hdR : ((d:ℝ)) = (10:ℝ) ^ s :=
    (Real.rpow_logb (by norm_num) (by norm_num) (by exact_mod_cast hd)).symm
  rw [hdR, ← Real.rpow_intCast (10:ℝ) ⌊t⌋, ← Real.rpow_add (by norm_num),
    Real.rpow_le_rpow_left_iff (by norm_num), Int.fract]
  constructor <;> intro h <;> linarith

lemma digit_upper (d : ℕ) (t : ℝ) :
    ((10:ℝ)^t < ((d:ℝ)+1) * (10:ℝ)^(⌊t⌋ : ℤ)) ↔ Int.fract t < Real.logb 10 ((d:ℝ)+1) := by
  set s : ℝ := Real.logb 10 ((d:ℝ)+1) with hs
  have hdR : ((d:ℝ)+1) = (10:ℝ) ^ s :=
    (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
  rw [hdR, ← Real.rpow_intCast (10:ℝ) ⌊t⌋, ← Real.rpow_add (by norm_num),
    Real.rpow_lt_rpow_left_iff (by norm_num), Int.fract]
  constructor <;> intro h <;> linarith

lemma nat_div_eq_iff (m q c : ℕ) (hq : 0 < q) : (m / q = c ↔ (c * q ≤ m ∧ m < (c+1)*q)) := by
  constructor
  · rintro rfl
    refine ⟨Nat.div_mul_le_self m q, ?_⟩
    rw [add_mul, one_mul]
    have ha : q * (m / q) + m % q = m := Nat.div_add_mod m q
    have hb := Nat.mod_lt m hq
    have hc : m / q * q = q * (m/q) := Nat.mul_comm _ _
    omega
  · rintro ⟨h1, h2⟩
    exact Nat.div_eq_of_lt_le h1 h2

lemma digit_iff (d E : ℕ) (hd : 1 ≤ d) :
    (2^E / 10^(Nat.log 10 (2^E)) = d) ↔
      (Real.logb 10 d ≤ Int.fract ((E:ℝ)*Lg) ∧
        Int.fract ((E:ℝ)*Lg) < Real.logb 10 ((d:ℝ)+1)) := by
  set t : ℝ := (E:ℝ)*Lg with ht
  have ht0 : 0 ≤ t := by rw [ht]; exact mul_nonneg (Nat.cast_nonneg E) Lg_pos.le
  set k : ℕ := Nat.log 10 (2^E) with hk
  have hkflr : (k:ℤ) = ⌊t⌋ := by
    rw [hk, natlog_two_pow E, ← ht]
    exact Int.toNat_of_nonneg (Int.floor_nonneg.2 ht0)
  have hkpos : (0:ℕ) < 10^k := by positivity
  have htwo : ((2:ℝ)^E) = (10:ℝ)^t := by rw [ht]; exact two_pow_eq_rpow E
  rw [nat_div_eq_iff (2^E) (10^k) d hkpos]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · rw [← digit_lower d hd t]
      have h3 : ((d:ℝ)) * (10:ℝ)^(k:ℕ) ≤ (2:ℝ)^E := by exact_mod_cast h1
      rw [htwo] at h3
      rwa [← hkflr, zpow_natCast]
    · rw [← digit_upper d t]
      have h3 : ((2:ℝ))^E < ((d:ℝ)+1) * (10:ℝ)^(k:ℕ) := by exact_mod_cast h2
      rw [htwo] at h3
      rwa [← hkflr, zpow_natCast]
  · rintro ⟨h1, h2⟩
    rw [← digit_lower d hd t] at h1
    rw [← digit_upper d t] at h2
    rw [← hkflr, zpow_natCast] at h1 h2
    rw [← htwo] at h1 h2
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩


end

end TuringTask
