import Mathlib
import TuringTask.Regular

/-!
# The unit group of `ZMod n` (theorem 3)

* `split_of_not_cyclic`: if `n` is not `0, 1, 2, 4, p^k, 2 p^k` (`p` an odd prime, `k ≥ 1`),
  then `n = 2^(e + 3)` or `n = a b` with `a, b ≥ 3` coprime.
* `exists_sqrt_one`: in both cases `ZMod n` has a square root `x` of `1` with `x ≠ ±1`
  (`x = 1 + 2^(e + 2)`, or `x = 1 (mod a)`, `x = -1 (mod b)` by the Chinese remainder theorem).
* `sign_units_iff`: if `(ZMod n)ˣ` is cyclic, `sign_mulLeft_eq_neg_one_iff` and
  `isSquare_iff_pow_half` give the answer; otherwise `x` and `-1` are two different elements of
  order `2`, and every sign is `1` (`sign_mulLeft_of_two_involutions`).
-/

namespace TuringTask

open Equiv

/-- The moduli of theorem 3. -/
lemma list_iff (n : ℕ) (h0 : n ≠ 0) (h1 : n ≠ 1) (h2 : n ≠ 2) :
    IsCyclic (ZMod n)ˣ ↔ (n = 4 ∨ ∃ p k : ℕ, p.Prime ∧ p % 2 = 1 ∧ 0 < k ∧
      (n = p ^ k ∨ n = 2 * p ^ k)) := by
  rw [ZMod.isCyclic_units_iff]
  simp only [h0, h1, h2, false_or]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨p, k, hp, hpo, hk, h⟩
    exact ⟨p, k, hp, Nat.odd_iff.mp hpo, hk, h⟩
  · rintro ⟨p, k, hp, hpo, hk, h⟩
    exact ⟨p, k, hp, Nat.odd_iff.mpr hpo, hk, h⟩

lemma split_of_not_cyclic {n : ℕ} (h0 : n ≠ 0) (h1 : n ≠ 1) (h2 : n ≠ 2)
    (hn : ¬ IsCyclic (ZMod n)ˣ) :
    (∃ e, n = 2 ^ (e + 3)) ∨ ∃ a b, 3 ≤ a ∧ 3 ≤ b ∧ Nat.Coprime a b ∧ n = a * b := by
  rw [list_iff n h0 h1 h2] at hn
  push Not at hn
  obtain ⟨h4, hpk⟩ := hn
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd h0
  have hm0 : m ≠ 0 := by rintro rfl; exact (Nat.not_odd_iff_even.mpr ⟨0, rfl⟩) hm
  by_cases hm1 : m = 1
  · subst hm1
    left
    refine ⟨e - 3, ?_⟩
    rw [mul_one]
    congr 1
    rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ 3 ≤ e) with he | he | he | he
    · subst he; simp at h1
    · subst he; simp at h2
    · subst he; simp at h4
    · omega
  · right
    obtain ⟨p, hp, hpm⟩ : ∃ p, p.Prime ∧ p ∣ m := ⟨m.minFac, Nat.minFac_prime hm1, Nat.minFac_dvd m⟩
    have hpodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · exfalso
        rw [h] at hpm
        exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hpm)
      · exact h
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    obtain ⟨k, r, hr, hmr⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 p hp.ne_one
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · exfalso
        rw [hk, pow_zero, one_mul] at hmr
        exact hr (hmr ▸ hpm)
      · exact hk
    have hpk3 : 3 ≤ p ^ k := le_trans hp3 (Nat.le_self_pow hk.ne' p)
    have hcop2 : Nat.Coprime 2 p := Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hpodd)
    by_cases hr1 : r = 1
    · subst hr1
      rw [mul_one] at hmr
      subst hmr
      have he : 2 ≤ e := by
        rcases (by omega : e = 0 ∨ e = 1 ∨ 2 ≤ e) with he | he | he
        · subst he; exact absurd (by ring) ((hpk p k hp hpodd hk).1)
        · subst he; exact absurd (by ring) ((hpk p k hp hpodd hk).2)
        · exact he
      refine ⟨2 ^ e, p ^ k, ?_, hpk3, Nat.Coprime.pow e k hcop2, rfl⟩
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    · have hrm : r ∣ m := ⟨p ^ k, by rw [hmr]; ring⟩
      have hrodd : Odd r := Odd.of_dvd_nat hm hrm
      have hr0 : r ≠ 0 := by rintro rfl; exact (Nat.not_odd_iff_even.mpr ⟨0, rfl⟩) hrodd
      have hr3 : 3 ≤ r := by
        obtain ⟨t, ht⟩ := hrodd
        omega
      refine ⟨2 ^ e * p ^ k, r, le_trans hpk3 (Nat.le_mul_of_pos_left _ (by positivity)), hr3,
        Nat.Coprime.mul_left (Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hrodd))
          (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hr)), ?_⟩
      rw [hmr]; ring

lemma natCast_ne_zero_of_lt {N m : ℕ} (h0 : 0 < m) (hm : m < N) : ((m : ℕ) : ZMod N) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd h0 h
  omega

lemma exists_sqrt_one {n : ℕ} (h0 : n ≠ 0) (h1 : n ≠ 1) (h2 : n ≠ 2)
    (hn : ¬ IsCyclic (ZMod n)ˣ) :
    ∃ x : ZMod n, x * x = 1 ∧ x ≠ 1 ∧ x ≠ -1 ∧ (1 : ZMod n) ≠ -1 := by
  rcases split_of_not_cyclic h0 h1 h2 hn with ⟨e, rfl⟩ | ⟨a, b, ha, hb, hab, rfl⟩
  · have hlt : 2 ^ (e + 2) < 2 ^ (e + 3) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h4 : 4 ≤ 2 ^ (e + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h32 : 2 ^ (e + 3) = 2 * 2 ^ (e + 2) := by ring
    have hlt2 : 2 + 2 ^ (e + 2) < 2 ^ (e + 3) := by omega
    have hN : (2 : ZMod (2 ^ (e + 3))) ^ (e + 3) = 0 := by
      have := ZMod.natCast_self (2 ^ (e + 3))
      push_cast at this; exact this
    have hA : (2 : ZMod (2 ^ (e + 3))) ^ (e + 2) ≠ 0 := by
      have := natCast_ne_zero_of_lt (N := 2 ^ (e + 3)) (by positivity) hlt
      push_cast at this; exact this
    have hB : (2 : ZMod (2 ^ (e + 3))) + 2 ^ (e + 2) ≠ 0 := by
      have := natCast_ne_zero_of_lt (N := 2 ^ (e + 3)) (by positivity) hlt2
      push_cast at this; exact this
    have hC : (2 : ZMod (2 ^ (e + 3))) ≠ 0 := by
      have := natCast_ne_zero_of_lt (N := 2 ^ (e + 3)) (m := 2) (by norm_num) (by omega)
      push_cast at this; exact this
    refine ⟨1 + 2 ^ (e + 2), ?_, ?_, ?_, ?_⟩
    · linear_combination (1 + (2 : ZMod (2 ^ (e + 3))) ^ (e + 1)) * hN
    · intro h
      exact hA (by linear_combination h)
    · intro h
      exact hB (by linear_combination h)
    · intro h
      exact hC (by linear_combination h)
  · haveI : Fact (2 < a) := ⟨by omega⟩
    haveI : Fact (2 < b) := ⟨by omega⟩
    set cr := ZMod.chineseRemainder hab
    have hna : (-1 : ZMod a) ≠ 1 := ZMod.neg_one_ne_one
    have hnb : (-1 : ZMod b) ≠ 1 := ZMod.neg_one_ne_one
    refine ⟨cr.symm (1, -1), ?_, ?_, ?_, ?_⟩
    · apply cr.injective
      simp
    · intro h
      have := congrArg cr h
      simp only [RingEquiv.apply_symm_apply, map_one, Prod.mk_eq_one] at this
      exact hnb this.2
    · intro h
      have := congrArg cr h
      simp only [RingEquiv.apply_symm_apply, map_neg, map_one, Prod.ext_iff, Prod.fst_neg,
        Prod.fst_one] at this
      exact hna this.1.symm
    · intro h
      have := congrArg cr h
      simp only [map_neg, map_one, Prod.ext_iff, Prod.fst_neg, Prod.fst_one] at this
      exact hna this.1.symm

/-- Theorem 3 in the form used by `Main`. -/
theorem sign_units_iff (n : ℕ) [NeZero n] (u : (ZMod n)ˣ) :
    Perm.sign (Equiv.mulLeft u) = -1 ↔
      (n = 4 ∨ ∃ p k : ℕ, p.Prime ∧ p % 2 = 1 ∧ 0 < k ∧ (n = p ^ k ∨ n = 2 * p ^ k)) ∧
        ¬ IsSquare u := by
  have h0 : n ≠ 0 := NeZero.ne n
  by_cases h12 : n = 1 ∨ n = 2
  · have hcard : Fintype.card (ZMod n)ˣ = 1 := by
      rw [ZMod.card_units_eq_totient]
      rcases h12 with rfl | rfl <;> rfl
    rw [sign_mulLeft_eq_neg_one_iff, hcard]
    refine iff_of_false (fun h => (Nat.not_even_one) h.1) ?_
    rintro ⟨h | ⟨p, k, hp, hpo, hk, h | h⟩, -⟩
    · omega
    · have : 3 ≤ p ^ k := le_trans (by have := hp.two_le; omega) (Nat.le_self_pow hk.ne' p)
      omega
    · have : 3 ≤ p ^ k := le_trans (by have := hp.two_le; omega) (Nat.le_self_pow hk.ne' p)
      omega
  · push Not at h12
    rw [← list_iff n h0 h12.1 h12.2]
    by_cases hc : IsCyclic (ZMod n)ˣ
    · have hev : Even (Fintype.card (ZMod n)ˣ) := by
        rw [ZMod.card_units_eq_totient]
        exact Nat.totient_even (by omega)
      have hev' : Even n.totient := by rwa [ZMod.card_units_eq_totient] at hev
      rw [sign_mulLeft_eq_neg_one_iff, isSquare_iff_pow_half hev]
      simp [hc, hev']
    · obtain ⟨x, hxx, hx1, hxn, h1n⟩ := exists_sqrt_one h0 h12.1 h12.2 hc
      let xu : (ZMod n)ˣ := ⟨x, x, hxx, hxx⟩
      have hs := sign_mulLeft_of_two_involutions (x := xu) (y := -1)
        (fun h => hx1 (by have := Units.ext_iff.mp h; rwa [Units.val_one] at this))
        (fun h => h1n (by
          have := Units.ext_iff.mp h
          rw [Units.val_neg, Units.val_one] at this
          exact this.symm))
        (fun h => hxn (by
          have := Units.ext_iff.mp h
          rwa [Units.val_neg, Units.val_one] at this))
        (Units.ext (by rw [sq, Units.val_mul, Units.val_one]; exact hxx)) (by simp) u
      rw [hs]
      exact iff_of_false (by decide) (fun h => hc h.1)

end TuringTask
