import Mathlib
import TuringTask.Large

/-!
# The period: `π(n) ≤ 6 n`, `π(n) = 6 n` and `π(n) = n`

* `per_parts`, `zer_parts`: a period (zero) modulo `2 ^ a 3 ^ b 5 ^ c` from the three parts.
* `pisano_bound`: for `n = 2 ^ a m` with `m` odd, `invP` gives a period `2 ^ s t` modulo `m`,
  and `3 * 2 ^ max (a - 1) s * t` is a period modulo `n`; it is at most `6 n`, with equality only
  for `n = 2 * 5 ^ j`, `j ≥ 1`.
* `pisano_eq_six_mul`: the converse uses `3 ∣ k` (period modulo `2`) and `4 * 5 ^ j ∣ k`.
* `pisano_eq_self`: if `n` divides all its periods, then `n = 2 ^ a 3 ^ b 5 ^ c` (`Large.lean`),
  explicit periods give `a ≤ 3` and `b ≤ 1`, and the periods modulo `2`, `3`, `4`, `5`, `8`
  leave `n = 1` and `n = 24 * 5 ^ c`.
-/

namespace TuringTask

lemma cop_235 (a b c : ℕ) : Nat.Coprime (2 ^ a * 3 ^ b) (5 ^ c) ∧ Nat.Coprime (2 ^ a) (3 ^ b) :=
  ⟨Nat.Coprime.mul_left (Nat.Coprime.pow _ _ (by norm_num)) (Nat.Coprime.pow _ _ (by norm_num)),
    Nat.Coprime.pow _ _ (by norm_num)⟩

lemma per_parts {a b c K : ℕ} (h2 : Per (2 ^ a) K) (h3 : Per (3 ^ b) K) (h5 : Per (5 ^ c) K) :
    Per (2 ^ a * 3 ^ b * 5 ^ c) K := by
  rw [per_mul_iff (cop_235 a b c).1, per_mul_iff (cop_235 a b c).2]
  exact ⟨⟨h2, h3⟩, h5⟩

lemma per_parts_of {a b c K : ℕ} (h : Per (2 ^ a * 3 ^ b * 5 ^ c) K) :
    Per (2 ^ a) K ∧ Per (3 ^ b) K ∧ Per (5 ^ c) K := by
  rw [per_mul_iff (cop_235 a b c).1, per_mul_iff (cop_235 a b c).2] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

lemma zer_parts {a b c K : ℕ} (h2 : Zer (2 ^ a) K) (h3 : Zer (3 ^ b) K) (h5 : Zer (5 ^ c) K) :
    Zer (2 ^ a * 3 ^ b * 5 ^ c) K := by
  rw [zer_mul_iff (cop_235 a b c).1, zer_mul_iff (cop_235 a b c).2]
  exact ⟨⟨h2, h3⟩, h5⟩

lemma zer_parts_of {a b c K : ℕ} (h : Zer (2 ^ a * 3 ^ b * 5 ^ c) K) :
    Zer (2 ^ a) K ∧ Zer (3 ^ b) K ∧ Zer (5 ^ c) K := by
  rw [zer_mul_iff (cop_235 a b c).1, zer_mul_iff (cop_235 a b c).2] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

lemma per_two_of {a K : ℕ} (h : 3 * 2 ^ (a - 1) ∣ K) : Per (2 ^ a) K := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simpa using per_one K
  · exact per_of_dvd (per_two_pow ha) h

lemma per_three_of {b K : ℕ} (h : 8 * 3 ^ (b - 1) ∣ K) : Per (3 ^ b) K := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simpa using per_one K
  · exact per_of_dvd (per_three_pow hb) h

lemma per_five_of {c K : ℕ} (h : 4 * 5 ^ c ∣ K) : Per (5 ^ c) K :=
  per_of_dvd (per_five_pow c) h

lemma zer_two_of {a K : ℕ} (h : 3 * 2 ^ (a - 1) ∣ K) : Zer (2 ^ a) K := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [Zer]
  · exact zer_of_dvd (per_two_pow ha).zer h

lemma zer_three_of {b K : ℕ} (h : 4 * 3 ^ (b - 1) ∣ K) : Zer (3 ^ b) K := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [Zer]
  · exact zer_of_dvd (zer_three_pow hb) h

lemma zer_five_of {c K : ℕ} (h : 5 ^ c ∣ K) : Zer (5 ^ c) K :=
  zer_of_dvd (zer_five_pow c) h

/-- `d` coprime to `5 ^ c` and dividing `x * 5 ^ c` divides `x`. -/
lemma dvd_of_dvd_mul_five_pow {d x c : ℕ} (hd : Nat.Coprime d 5) (h : d ∣ x * 5 ^ c) : d ∣ x :=
  (Nat.Coprime.pow_right c hd).dvd_of_dvd_mul_right h

lemma pow_two_le {a : ℕ} (ha : 1 ≤ a) : 2 ^ a = 2 * 2 ^ (a - 1) := by
  rw [← pow_succ', Nat.sub_add_cancel ha]

/-- A period at most `6 n`, equal to `6 n` only for `n = 2 * 5 ^ j`. -/
theorem pisano_bound {n : ℕ} (hn : 0 < n) :
    ∃ k, 0 < k ∧ k ≤ 6 * n ∧ Per n k ∧ (k = 6 * n → ∃ j, 0 < j ∧ n = 2 * 5 ^ j) := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have hm0 : 0 < m := hm.pos
  obtain ⟨s, t, ht, hP, hb, htm, he, -⟩ := invP_odd m hm
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
  have h2s : 0 < 2 ^ s := by positivity
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine ⟨2 ^ s * t, by positivity, by simp; omega, by simpa using hP, ?_⟩
    intro h; simp at h; omega
  have hA := pow_two_le ha
  set A := 2 ^ (a - 1) with hAdef
  have hA1 : 1 ≤ A := Nat.one_le_two_pow
  rcases le_or_gt s (a - 1) with hs | hs
  · refine ⟨3 * A * t, by positivity, ?_, ?_, ?_⟩
    · rw [hA]; nlinarith
    · rw [per_mul_iff hcop]
      refine ⟨per_two_of ⟨t, by ring⟩, per_of_dvd hP ⟨3 * 2 ^ (a - 1 - s), ?_⟩⟩
      rw [hAdef, show a - 1 = s + (a - 1 - s) by omega, pow_add]
      simp only [Nat.add_sub_cancel_left]; ring
    · intro h; rw [hA] at h; nlinarith
  · refine ⟨3 * (2 ^ s * t), by positivity, ?_, ?_, ?_⟩
    · rw [hA]; nlinarith
    · rw [per_mul_iff hcop]
      refine ⟨per_two_of ⟨2 ^ (s - (a - 1)) * t, ?_⟩, per_of_dvd hP ⟨3, by ring⟩⟩
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
      obtain ⟨c, hc, rfl⟩ := he (by simp at h; omega)
      exact ⟨c, hc, by ring⟩

lemma prompt_per (n k : ℕ) :
    (Nat.fib k % n = 0 ∧ Nat.fib (k + 1) % n = 1 % n) ↔ Per n k := by
  simp [Per, Nat.ModEq]

theorem pisano_le {n : ℕ} (hn : 0 < n) :
    ∃ k, 0 < k ∧ k ≤ 6 * n ∧ Nat.fib k % n = 0 ∧ Nat.fib (k + 1) % n = 1 % n := by
  obtain ⟨k, hk, hk6, hP, -⟩ := pisano_bound hn
  exact ⟨k, hk, hk6, (prompt_per n k).mpr hP⟩

theorem pisano_eq_six_mul {n : ℕ} (hn : 0 < n) :
    (Per n (6 * n) ∧ ∀ k, 0 < k → k < 6 * n → ¬ Per n k) ↔ ∃ j, 0 < j ∧ n = 2 * 5 ^ j := by
  constructor
  · rintro ⟨-, hmin⟩
    obtain ⟨k, hk, hk6, hP, heq⟩ := pisano_bound hn
    rcases lt_or_eq_of_le hk6 with h | h
    · exact absurd hP (hmin k hk h)
    · exact heq h
  · rintro ⟨j, hj, rfl⟩
    have hcop : Nat.Coprime 2 (5 ^ j) := Nat.Coprime.pow_right _ (by norm_num)
    refine ⟨?_, fun k hk hlt hP => ?_⟩
    · rw [per_mul_iff hcop]
      exact ⟨per_of_dvd per_2 ⟨4 * 5 ^ j, by ring⟩, per_five_of ⟨3, by ring⟩⟩
    · rw [per_mul_iff hcop] at hP
      have h3 := per_2_dvd hP.1
      have h4 := per_five_pow_dvd hj hP.2
      have h12 : 3 * (4 * 5 ^ j) ∣ k :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd
          (Nat.Coprime.mul_right (by norm_num) (Nat.Coprime.pow_right _ (by norm_num))) h3 h4
      have := Nat.le_of_dvd hk h12
      omega

lemma not_dvd_v2 {a b c : ℕ} (ha : 1 ≤ a) :
    ¬ 2 ^ a * 3 ^ b * 5 ^ c ∣ 2 ^ (a - 1) * (3 ^ (b + 1) * 5 ^ c) := by
  intro h
  have h1 : 2 ^ (a - 1) * 2 ∣ 2 ^ (a - 1) * (3 ^ (b + 1) * 5 ^ c) := by
    rw [← pow_succ, Nat.sub_add_cancel ha]
    exact dvd_trans (Dvd.intro (3 ^ b * 5 ^ c) (by ring)) h
  have h2 := (Nat.mul_dvd_mul_iff_left (by positivity)).mp h1
  have : Nat.Coprime 2 (3 ^ (b + 1) * 5 ^ c) :=
    Nat.Coprime.mul_right (Nat.Coprime.pow_right _ (by norm_num))
      (Nat.Coprime.pow_right _ (by norm_num))
  exact absurd (Nat.eq_one_of_dvd_coprimes this (dvd_refl 2) h2) (by norm_num)

lemma not_dvd_v3 {a b c e : ℕ} (hb : 1 ≤ b) :
    ¬ 2 ^ a * 3 ^ b * 5 ^ c ∣ 3 ^ (b - 1) * (2 ^ e * 5 ^ c) := by
  intro h
  have h1 : 3 ^ (b - 1) * 3 ∣ 3 ^ (b - 1) * (2 ^ e * 5 ^ c) := by
    rw [← pow_succ, Nat.sub_add_cancel hb]
    exact dvd_trans (Dvd.intro (2 ^ a * 5 ^ c) (by ring)) h
  have h2 := (Nat.mul_dvd_mul_iff_left (by positivity)).mp h1
  have : Nat.Coprime 3 (2 ^ e * 5 ^ c) :=
    Nat.Coprime.mul_right (Nat.Coprime.pow_right _ (by norm_num))
      (Nat.Coprime.pow_right _ (by norm_num))
  exact absurd (Nat.eq_one_of_dvd_coprimes this (dvd_refl 3) h2) (by norm_num)

theorem pisano_eq_self {n : ℕ} (hn : 0 < n) :
    (Per n n ∧ ∀ k, 0 < k → k < n → ¬ Per n k) ↔ (n = 1 ∨ ∃ j, n = 24 * 5 ^ j) := by
  constructor
  · rintro ⟨hP, hmin⟩
    have hdiv : ∀ K, Per n K → n ∣ K := fun K hK => per_dvd_of_min hn hP hmin hK
    obtain ⟨a, b, c, rfl⟩ := eq_two_three_five hn (primes_le_five_of_per hn hdiv)
    have ha : a ≤ 3 := by
      by_contra h
      push Not at h
      refine not_dvd_v2 (a := a) (b := b) (c := c) (by omega) (hdiv _ (per_parts ?_ ?_ ?_))
      · exact per_two_of ⟨3 ^ b * 5 ^ c, by ring⟩
      · rcases Nat.eq_zero_or_pos b with rfl | hb
        · refine per_three_of ⟨2 ^ (a - 4) * 3 * 5 ^ c, ?_⟩
          rw [show a - 1 = 3 + (a - 4) by omega, pow_add]; ring
        · refine per_three_of ⟨2 ^ (a - 4) * 3 ^ 2 * 5 ^ c, ?_⟩
          rw [show a - 1 = 3 + (a - 4) by omega, show b + 1 = (b - 1) + 2 by omega, pow_add,
            pow_add]; ring
      · refine per_five_of ⟨2 ^ (a - 3) * 3 ^ (b + 1), ?_⟩
        rw [show a - 1 = 2 + (a - 3) by omega, pow_add]; ring
    have hb : b ≤ 1 := by
      by_contra h
      push Not at h
      refine not_dvd_v3 (a := a) (b := b) (c := c) (e := a + 3) (by omega)
        (hdiv _ (per_parts ?_ ?_ ?_))
      · rcases Nat.eq_zero_or_pos a with rfl | ha'
        · refine per_two_of ⟨2 ^ 3 * 3 ^ (b - 2) * 5 ^ c, ?_⟩
          rw [show b - 1 = (b - 2) + 1 by omega, pow_succ]; ring
        · refine per_two_of ⟨2 ^ 4 * 3 ^ (b - 2) * 5 ^ c, ?_⟩
          rw [show a + 3 = (a - 1) + 4 by omega, show b - 1 = (b - 2) + 1 by omega, pow_add,
            pow_succ]; ring
      · exact per_three_of ⟨2 ^ a * 5 ^ c, by rw [pow_add]; ring⟩
      · exact per_five_of ⟨2 ^ (a + 1) * 3 ^ (b - 1), by rw [pow_add]; ring⟩
    obtain ⟨h2, h3, h5⟩ := per_parts_of hP
    have h5' : c = 0 ∨ 4 * 5 ^ c ∣ 2 ^ a * 3 ^ b * 5 ^ c := by
      rcases Nat.eq_zero_or_pos c with rfl | hc
      · left; rfl
      · right; exact per_five_pow_dvd hc h5
    interval_cases a <;> interval_cases b
    · rcases h5' with rfl | h
      · left; rfl
      · exfalso
        have h' : 4 * 5 ^ c ∣ 1 * 5 ^ c := by simpa using h
        have := Nat.dvd_of_mul_dvd_mul_right (by positivity) h'
        omega
    · exfalso
      have h8 : 8 ∣ 3 * 5 ^ c := by simpa using per_3_dvd (h3.of_dvd (by norm_num))
      have := dvd_of_dvd_mul_five_pow (d := 8) (by norm_num) h8
      omega
    · exfalso
      have h8 : 3 ∣ 2 * 5 ^ c := by simpa using per_2_dvd (h2.of_dvd (by norm_num))
      have := dvd_of_dvd_mul_five_pow (d := 3) (by norm_num) h8
      omega
    · exfalso
      have h8 : 8 ∣ 2 * 3 * 5 ^ c := by simpa using per_3_dvd (h3.of_dvd (by norm_num))
      have := dvd_of_dvd_mul_five_pow (d := 8) (by norm_num) h8
      omega
    · exfalso
      have h8 : 6 ∣ 4 * 5 ^ c := by simpa using per_4_dvd (h2.of_dvd (by norm_num))
      have := dvd_of_dvd_mul_five_pow (d := 6) (by norm_num) h8
      omega
    · exfalso
      have h8 : 8 ∣ 4 * 3 * 5 ^ c := by simpa using per_3_dvd (h3.of_dvd (by norm_num))
      have := dvd_of_dvd_mul_five_pow (d := 8) (by norm_num) h8
      omega
    · exfalso
      have h8 : 12 ∣ 8 * 5 ^ c := by simpa using per_8_dvd (h2.of_dvd (by norm_num))
      have := dvd_of_dvd_mul_five_pow (d := 12) (by norm_num) h8
      omega
    · right; exact ⟨c, by ring⟩
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨per_one 1, fun k hk hlt => by omega⟩
    · have hcop : Nat.Coprime (8 * 3) (5 ^ j) := Nat.Coprime.pow_right _ (by norm_num)
      have hcop' : Nat.Coprime 8 3 := by norm_num
      refine ⟨?_, fun k hk hlt hP => ?_⟩
      · rw [show 24 * 5 ^ j = 8 * 3 * 5 ^ j by ring, per_mul_iff hcop, per_mul_iff hcop']
        exact ⟨⟨per_of_dvd per_8 ⟨2 * 5 ^ j, by ring⟩, per_of_dvd per_3 ⟨3 * 5 ^ j, by ring⟩⟩,
          per_five_of ⟨6, by ring⟩⟩
      · rw [show 24 * 5 ^ j = 8 * 3 * 5 ^ j by ring, per_mul_iff hcop, per_mul_iff hcop']
          at hP
        have h12 := per_8_dvd hP.1.1
        have h8 := per_3_dvd hP.1.2
        have h24 : 24 ∣ k := by
          have := Nat.lcm_dvd h12 h8
          rwa [show Nat.lcm 12 8 = 24 by norm_num] at this
        have h5 : 5 ^ j ∣ k := by
          rcases Nat.eq_zero_or_pos j with rfl | hj
          · simp
          · exact dvd_trans (dvd_mul_left _ _) (per_five_pow_dvd hj hP.2)
        have := Nat.le_of_dvd hk (Nat.Coprime.mul_dvd_of_dvd_of_dvd
          (Nat.Coprime.pow_right _ (by norm_num)) h24 h5)
        omega

end TuringTask
