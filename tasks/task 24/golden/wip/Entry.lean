import Mathlib
import TuringTask.Pisano

/-!
# The entry point: `z(n) = 2 n` and `z(n) = n`

* `entry_bound`: for `n = 2 ^ a m` with `m` odd, `invZ` gives a zero `2 ^ s t` modulo `m`; with
  the zero `3 * 2 ^ (a - 1)` modulo `2 ^ a` this gives a zero at most `2 n`, and equal to `2 n`
  only for `n = 6 * 5 ^ j`. When `3 ∣ t` the factor `3` is not needed.
* `entry_eq_two_mul`: the converse from the zeros modulo `2`, `3` and `5 ^ j`.
* `entry_eq_self`: if `n` divides all its zeros, then `n = 2 ^ a 3 ^ b 5 ^ c` with `a ≤ 2` and
  `b ≤ 1`, and the zeros modulo `2`, `3`, `4` leave `n = 5 ^ c` and `n = 12 * 5 ^ c`.
-/

namespace TuringTask

/-- A zero at most `2 n`, equal to `2 n` only for `n = 6 * 5 ^ j`. -/
theorem entry_bound {n : ℕ} (hn : 0 < n) :
    ∃ k, 0 < k ∧ k ≤ 2 * n ∧ Zer n k ∧ (k = 2 * n → ∃ j, n = 6 * 5 ^ j) := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have hm0 : 0 < m := hm.pos
  obtain ⟨s, t, ht, hZ, hb, htm, he, -⟩ := invZ_odd m hm
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
  have h2s : 0 < 2 ^ s := by positivity
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine ⟨2 ^ s * t, by positivity, by simp; omega, by simpa using hZ, ?_⟩
    intro h; simp at h; omega
  have hA := pow_two_le ha
  set A := 2 ^ (a - 1) with hAdef
  have hA1 : 1 ≤ A := Nat.one_le_two_pow
  rcases le_or_gt s (a - 1) with hs | hs
  · refine ⟨3 * A * t, by positivity, ?_, ?_, ?_⟩
    · rw [hA]; nlinarith
    · rw [zer_mul_iff hcop]
      refine ⟨zer_two_of ⟨t, by ring⟩, zer_of_dvd hZ ⟨3 * 2 ^ (a - 1 - s), ?_⟩⟩
      rw [hAdef, show a - 1 = s + (a - 1 - s) by omega, pow_add]
      simp only [Nat.add_sub_cancel_left]; ring
    · intro h; rw [hA] at h; nlinarith
  · by_cases h3 : 3 ∣ t
    · obtain ⟨t', rfl⟩ := h3
      refine ⟨2 ^ s * (3 * t'), by positivity, ?_, ?_, ?_⟩
      · rw [hA]; nlinarith
      · rw [zer_mul_iff hcop]
        refine ⟨zer_two_of ⟨2 ^ (s - (a - 1)) * t', ?_⟩, hZ⟩
        rw [show s = (a - 1) + (s - (a - 1)) by omega, pow_add]
        simp only [Nat.add_sub_cancel_left]; ring
      · intro h; rw [hA] at h; nlinarith
    · refine ⟨3 * (2 ^ s * t), by positivity, ?_, ?_, ?_⟩
      · rw [hA]; nlinarith
      · rw [zer_mul_iff hcop]
        refine ⟨zer_two_of ⟨2 ^ (s - (a - 1)) * t, ?_⟩, zer_of_dvd hZ ⟨3, by ring⟩⟩
        rw [show s = (a - 1) + (s - (a - 1)) by omega, pow_add]
        simp only [Nat.add_sub_cancel_left]; ring
      · intro h
        have hle : 2 ^ a ≤ 2 := by
          rw [hA] at h ⊢; nlinarith
        have ha1 : a = 1 := by
          rcases Nat.lt_or_ge a 2 with h1 | h1
          · omega
          · have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h1; omega
        subst ha1
        obtain ⟨e, c, -, rfl, he1⟩ := he (by simp at h; omega)
        rw [he1 h3]
        exact ⟨c, by ring⟩

lemma prompt_zer (n k : ℕ) : 0 < Nat.fib k % n ↔ ¬ Zer n k := by
  rw [Nat.pos_iff_ne_zero, Zer, Nat.dvd_iff_mod_eq_zero]

theorem entry_eq_two_mul {n : ℕ} (hn : 0 < n) :
    (Zer n (2 * n) ∧ ∀ k, 0 < k → k < 2 * n → ¬ Zer n k) ↔ ∃ j, n = 6 * 5 ^ j := by
  constructor
  · rintro ⟨-, hmin⟩
    obtain ⟨k, hk, hk2, hZ, heq⟩ := entry_bound hn
    rcases lt_or_eq_of_le hk2 with h | h
    · exact absurd hZ (hmin k hk h)
    · exact heq h
  · rintro ⟨j, rfl⟩
    have hcop : Nat.Coprime (2 * 3) (5 ^ j) := Nat.Coprime.pow_right _ (by norm_num)
    have hcop' : Nat.Coprime 2 3 := by norm_num
    refine ⟨?_, fun k hk hlt hZ => ?_⟩
    · rw [show 6 * 5 ^ j = 2 * 3 * 5 ^ j by ring, zer_mul_iff hcop, zer_mul_iff hcop']
      exact ⟨⟨zer_of_dvd zer_2 ⟨4 * 5 ^ j, by ring⟩, zer_of_dvd zer_3 ⟨3 * 5 ^ j, by ring⟩⟩,
        zer_five_of ⟨12, by ring⟩⟩
    · rw [show 6 * 5 ^ j = 2 * 3 * 5 ^ j by ring, zer_mul_iff hcop, zer_mul_iff hcop'] at hZ
      have h3 := zer_2_dvd hZ.1.1
      have h4 := zer_3_dvd hZ.1.2
      have h5 := five_pow_dvd_of_zer j k hZ.2
      have h12 : 12 ∣ k := by
        have := Nat.lcm_dvd h3 h4
        rwa [show Nat.lcm 3 4 = 12 by norm_num] at this
      have := Nat.le_of_dvd hk (Nat.Coprime.mul_dvd_of_dvd_of_dvd
        (Nat.Coprime.pow_right _ (by norm_num)) h12 h5)
      omega

theorem entry_eq_self {n : ℕ} (hn : 0 < n) :
    (Zer n n ∧ ∀ k, 0 < k → k < n → ¬ Zer n k) ↔
      ((∃ j, n = 5 ^ j) ∨ ∃ j, n = 12 * 5 ^ j) := by
  constructor
  · rintro ⟨hZ, hmin⟩
    have hdiv : ∀ K, Zer n K → n ∣ K := fun K hK => zer_dvd_of_min hn hZ hmin hK
    obtain ⟨a, b, c, rfl⟩ := eq_two_three_five hn (primes_le_five_of_zer hn hdiv)
    have ha : a ≤ 2 := by
      by_contra h
      push Not at h
      refine not_dvd_v2 (a := a) (b := b) (c := c) (by omega) (hdiv _ (zer_parts ?_ ?_ ?_))
      · exact zer_two_of ⟨3 ^ b * 5 ^ c, by ring⟩
      · rcases Nat.eq_zero_or_pos b with rfl | hb
        · refine zer_three_of ⟨2 ^ (a - 3) * 3 * 5 ^ c, ?_⟩
          rw [show a - 1 = 2 + (a - 3) by omega, pow_add]; ring
        · refine zer_three_of ⟨2 ^ (a - 3) * 3 ^ 2 * 5 ^ c, ?_⟩
          rw [show a - 1 = 2 + (a - 3) by omega, show b + 1 = (b - 1) + 2 by omega, pow_add,
            pow_add]; ring
      · exact zer_five_of ⟨2 ^ (a - 1) * 3 ^ (b + 1), by ring⟩
    have hb : b ≤ 1 := by
      by_contra h
      push Not at h
      refine not_dvd_v3 (a := a) (b := b) (c := c) (e := a + 2) (by omega)
        (hdiv _ (zer_parts ?_ ?_ ?_))
      · rcases Nat.eq_zero_or_pos a with rfl | ha'
        · refine zer_two_of ⟨2 ^ 2 * 3 ^ (b - 2) * 5 ^ c, ?_⟩
          rw [show b - 1 = (b - 2) + 1 by omega, pow_succ]; ring
        · refine zer_two_of ⟨2 ^ 3 * 3 ^ (b - 2) * 5 ^ c, ?_⟩
          rw [show a + 2 = (a - 1) + 3 by omega, show b - 1 = (b - 2) + 1 by omega, pow_add,
            pow_succ]; ring
      · exact zer_three_of ⟨2 ^ a * 5 ^ c, by rw [pow_add]; ring⟩
      · exact zer_five_of ⟨3 ^ (b - 1) * 2 ^ (a + 2), by ring⟩
    obtain ⟨h2, h3, -⟩ := zer_parts_of hZ
    interval_cases a <;> interval_cases b
    · left; exact ⟨c, by ring⟩
    · exfalso
      have h8 : 4 ∣ 3 * 5 ^ c := by simpa using zer_3_dvd (h3.of_dvd (by norm_num))
      have := dvd_of_dvd_mul_five_pow (d := 4) (by norm_num) h8
      omega
    · exfalso
      have h8 : 3 ∣ 2 * 5 ^ c := by simpa using zer_2_dvd (h2.of_dvd (by norm_num))
      have := dvd_of_dvd_mul_five_pow (d := 3) (by norm_num) h8
      omega
    · exfalso
      have h8 : 4 ∣ 2 * 3 * 5 ^ c := by simpa using zer_3_dvd (h3.of_dvd (by norm_num))
      have := dvd_of_dvd_mul_five_pow (d := 4) (by norm_num) h8
      omega
    · exfalso
      have h8 : 6 ∣ 4 * 5 ^ c := by simpa using zer_4_dvd (h2.of_dvd (by norm_num))
      have := dvd_of_dvd_mul_five_pow (d := 6) (by norm_num) h8
      omega
    · right; exact ⟨c, by ring⟩
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · refine ⟨zer_five_pow j, fun k hk hlt hZ => ?_⟩
      have := Nat.le_of_dvd hk (five_pow_dvd_of_zer j k hZ)
      omega
    · have hcop : Nat.Coprime (4 * 3) (5 ^ j) := Nat.Coprime.pow_right _ (by norm_num)
      have hcop' : Nat.Coprime 4 3 := by norm_num
      refine ⟨?_, fun k hk hlt hZ => ?_⟩
      · rw [show 12 * 5 ^ j = 4 * 3 * 5 ^ j by ring, zer_mul_iff hcop, zer_mul_iff hcop']
        exact ⟨⟨zer_of_dvd zer_4 ⟨2 * 5 ^ j, by ring⟩, zer_of_dvd zer_3 ⟨3 * 5 ^ j, by ring⟩⟩,
          zer_five_of ⟨12, by ring⟩⟩
      · rw [show 12 * 5 ^ j = 4 * 3 * 5 ^ j by ring, zer_mul_iff hcop, zer_mul_iff hcop']
          at hZ
        have h6 := zer_4_dvd hZ.1.1
        have h4 := zer_3_dvd hZ.1.2
        have h12 : 12 ∣ k := by
          have := Nat.lcm_dvd h6 h4
          rwa [show Nat.lcm 6 4 = 12 by norm_num] at this
        have h5 := five_pow_dvd_of_zer j k hZ.2
        have := Nat.le_of_dvd hk (Nat.Coprime.mul_dvd_of_dvd_of_dvd
          (Nat.Coprime.pow_right _ (by norm_num)) h12 h5)
        omega

end TuringTask
