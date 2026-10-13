import Mathlib
import TuringTask.Bounds

/-!
# The largest prime factor

* `small_periods`: if every prime factor of `m` is below a prime `p ≥ 7`, then `m` has a period
  and a zero that are not divisible by `p`.
* `primes_le_five_of_per`, `primes_le_five_of_zer`: if `n` divides every period (every zero) of
  `n`, then the prime factors of `n` are at most `5`. Otherwise let `p ≥ 7` be the largest prime
  factor and `n = p ^ e m`; the period `p ^ (e - 1) M K` (with `M` from `big_pow` and `K` from
  `small_periods`) is not divisible by `p ^ e`.
* `eq_two_three_five`: such an `n` is `2 ^ a 3 ^ b 5 ^ c`.
-/

namespace TuringTask

lemma not_dvd_small {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q < p)
    {n M : ℕ} (hM : ¬ p ∣ M) : ¬ p ∣ q ^ (n - 1) * M := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
  · have := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h1)
    omega
  · exact hM h1

lemma not_dvd_of_lt {p x : ℕ} (h0 : 0 < x) (h : x < p) : ¬ p ∣ x :=
  fun hd => absurd (Nat.le_of_dvd h0 hd) (by omega)

lemma not_dvd_two_pow {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (k : ℕ) : ¬ p ∣ 2 ^ k := fun h =>
  not_dvd_of_lt (by norm_num) (by omega) (hp.dvd_of_dvd_pow h)

/-- Periods and zeros prime to `p` for moduli with prime factors below `p`. -/
lemma small_periods {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) :
    ∀ m : ℕ, 0 < m → (∀ q, q.Prime → q ∣ m → q < p) →
      (∃ K, 0 < K ∧ Per m K ∧ ¬ p ∣ K) ∧ (∃ K, 0 < K ∧ Zer m K ∧ ¬ p ∣ K) := by
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow q n hq hn =>
    intro _ hlt
    have hqp : q < p := hlt q hq (dvd_pow_self q hn.ne')
    have hq1 : 0 < q ^ (n - 1) := pow_pos hq.pos _
    have hp2 : ¬ p ∣ 2 := not_dvd_of_lt (by norm_num) (by omega)
    rcases prime_cases hq with rfl | rfl | rfl | hq7
    · refine ⟨⟨3 * 2 ^ (n - 1), by positivity, per_two_pow hn, ?_⟩,
        ⟨3 * 2 ^ (n - 1), by positivity, (per_two_pow hn).zer, ?_⟩⟩ <;>
      · rw [mul_comm]; exact not_dvd_small hp Nat.prime_two hqp
          (not_dvd_of_lt (by norm_num) (by omega))
    · refine ⟨⟨8 * 3 ^ (n - 1), by positivity, per_three_pow hn, ?_⟩,
        ⟨4 * 3 ^ (n - 1), by positivity, zer_three_pow hn, ?_⟩⟩
      · rw [mul_comm]; exact not_dvd_small hp Nat.prime_three hqp
          (by rw [show (8 : ℕ) = 2 ^ 3 from rfl]; exact not_dvd_two_pow hp h7 3)
      · rw [mul_comm]; exact not_dvd_small hp Nat.prime_three hqp
          (by rw [show (4 : ℕ) = 2 ^ 2 from rfl]; exact not_dvd_two_pow hp h7 2)
    · refine ⟨⟨4 * 5 ^ n, by positivity, per_five_pow n, ?_⟩,
        ⟨5 ^ n, by positivity, zer_five_pow n, ?_⟩⟩
      · intro h
        rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
        · exact not_dvd_two_pow hp h7 2 h1
        · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp (hp.dvd_of_dvd_pow h1)
          omega
      · intro h1
        have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp (hp.dvd_of_dvd_pow h1)
        omega
    · have hqodd : Odd q := hq.eq_two_or_odd'.resolve_left (by omega)
      have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left (by omega)
      have hq1' : ¬ p ∣ q + 1 := by
        intro hd
        have hle := Nat.le_of_dvd (by omega) hd
        have heq : q + 1 = p := by omega
        rw [← heq] at hpodd
        obtain ⟨r, hr⟩ := hqodd
        obtain ⟨r', hr'⟩ := hpodd
        omega
      have hqm : ¬ p ∣ q - 1 := not_dvd_of_lt (by omega) (by omega)
      rcases big_pow hq hq7 hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨⟨_, Nat.mul_pos hq1 (by omega), h1, not_dvd_small hp hq hqp hqm⟩,
          ⟨_, Nat.mul_pos hq1 (by omega), h2, not_dvd_small hp hq hqp hqm⟩⟩
      · refine ⟨⟨_, Nat.mul_pos hq1 (by omega), h1, not_dvd_small hp hq hqp ?_⟩,
          ⟨_, Nat.mul_pos hq1 (by omega), h2, not_dvd_small hp hq hqp hq1'⟩⟩
        intro h
        rcases (Nat.Prime.dvd_mul hp).mp h with h3 | h3
        · exact hp2 h3
        · exact hq1' h3
  | zero => intro h; omega
  | one =>
    intro _ _
    exact ⟨⟨1, by norm_num, per_one 1, hp.not_dvd_one⟩,
      ⟨1, by norm_num, by simp [Zer], hp.not_dvd_one⟩⟩
  | coprime a b ha hb hab iha ihb =>
    intro _ hlt
    have hla : ∀ q, q.Prime → q ∣ a → q < p :=
      fun q hq hd => hlt q hq (Dvd.dvd.mul_right hd b)
    have hlb : ∀ q, q.Prime → q ∣ b → q < p :=
      fun q hq hd => hlt q hq (Dvd.dvd.mul_left hd a)
    obtain ⟨⟨K1, hK1, hP1, hn1⟩, ⟨Z1, hZ1, hz1, hm1⟩⟩ := iha (by omega) hla
    obtain ⟨⟨K2, hK2, hP2, hn2⟩, ⟨Z2, hZ2, hz2, hm2⟩⟩ := ihb (by omega) hlb
    refine ⟨⟨K1 * K2, Nat.mul_pos hK1 hK2, ?_, ?_⟩, ⟨Z1 * Z2, Nat.mul_pos hZ1 hZ2, ?_, ?_⟩⟩
    · rw [per_mul_iff hab]
      exact ⟨per_mul hP1 K2, by rw [mul_comm]; exact per_mul hP2 K1⟩
    · intro h
      rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
      exacts [hn1 h1, hn2 h1]
    · rw [zer_mul_iff hab]
      exact ⟨zer_mul hz1 Z2, by rw [mul_comm]; exact zer_mul hz2 Z1⟩
    · intro h
      rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
      exacts [hm1 h1, hm2 h1]

/-- If some prime factor of `n` exceeds `5`, the largest one is at least `7`. -/
lemma exists_largest {n : ℕ} (hn : 0 < n) (h : ¬ ∀ q, q.Prime → q ∣ n → q ≤ 5) :
    ∃ p, p.Prime ∧ 7 ≤ p ∧ p ∣ n ∧ ∀ q, q.Prime → q ∣ n → q ≤ p := by
  push Not at h
  obtain ⟨q, hq, hqn, hq5⟩ := h
  have hne : n.primeFactors.Nonempty := ⟨q, Nat.mem_primeFactors.mpr ⟨hq, hqn, hn.ne'⟩⟩
  set p := n.primeFactors.max' hne with hp
  have hpm : p ∈ n.primeFactors := Finset.max'_mem _ _
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpm
  have hle : ∀ r, r.Prime → r ∣ n → r ≤ p := fun r hr hd =>
    Finset.le_max' _ r (Nat.mem_primeFactors.mpr ⟨hr, hd, hn.ne'⟩)
  have hqp := hle q hq hqn
  refine ⟨p, hpp, ?_, Nat.dvd_of_mem_primeFactors hpm, hle⟩
  rcases prime_cases hpp with h | h | h | h <;> omega

/-- The key step: a prime `p ≥ 7` dividing `n` gives a period (zero) not divisible by `n`. -/
lemma large_prime_step {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (h7 : 7 ≤ p) (hpn : p ∣ n)
    (hmax : ∀ q, q.Prime → q ∣ n → q ≤ p) :
    (∃ K, Per n K ∧ ¬ n ∣ K) ∧ (∃ K, Zer n K ∧ ¬ n ∣ K) := by
  obtain ⟨e, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.one_lt.ne'
  have he : 1 ≤ e := by
    by_contra h0
    push Not at h0
    have : e = 0 := by omega
    subst this
    simp at hpn
    exact hpm hpn
  have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hlt : ∀ q, q.Prime → q ∣ m → q < p := by
    intro q hq hd
    have hle := hmax q hq (Dvd.dvd.mul_left hd _)
    rcases lt_or_eq_of_le hle with h | rfl
    · exact h
    · exact absurd hd hpm
  obtain ⟨⟨K, -, hK, hKp⟩, ⟨Z, -, hZ, hZp⟩⟩ := small_periods hp h7 m hm hlt
  have hcop : Nat.Coprime (p ^ e) m :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)
  have hpe : 0 < p ^ (e - 1) := pow_pos hp.pos _
  have hsplit : p ^ e = p ^ (e - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel he]
  have hp2 : ¬ p ∣ 2 := not_dvd_of_lt (by norm_num) (by omega)
  have hp1 : ¬ p ∣ p + 1 := by
    intro h
    have := (Nat.dvd_add_right (dvd_refl p)).mp h
    exact hp.not_dvd_one this
  have hpm1 : ¬ p ∣ p - 1 := not_dvd_of_lt (by omega) (by omega)
  -- a period `p ^ (e - 1) * M * X` with `p ∤ M X` is not divisible by `p ^ e m`
  have hfin : ∀ M X : ℕ, ¬ p ∣ M → ¬ p ∣ X → ¬ p ^ e * m ∣ p ^ (e - 1) * M * X := by
    intro M X hM hX hd
    have h1 : p ^ (e - 1) * p ∣ p ^ (e - 1) * (M * X) := by
      rw [← hsplit, ← mul_assoc]; exact dvd_trans (dvd_mul_right _ _) hd
    have h2 := (Nat.mul_dvd_mul_iff_left hpe).mp h1
    rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
    exacts [hM h3, hX h3]
  rcases big_pow hp h7 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨⟨p ^ (e - 1) * (p - 1) * K, ?_, hfin _ _ hpm1 hKp⟩,
      ⟨p ^ (e - 1) * (p - 1) * Z, ?_, hfin _ _ hpm1 hZp⟩⟩
    · rw [per_mul_iff hcop]
      exact ⟨per_mul h1 K, per_of_dvd hK (dvd_mul_left _ _)⟩
    · rw [zer_mul_iff hcop]
      exact ⟨zer_mul h2 Z, zer_of_dvd hZ (dvd_mul_left _ _)⟩
  · have hM : ¬ p ∣ 2 * (p + 1) := by
      intro h
      rcases (Nat.Prime.dvd_mul hp).mp h with h3 | h3
      exacts [hp2 h3, hp1 h3]
    refine ⟨⟨p ^ (e - 1) * (2 * (p + 1)) * K, ?_, hfin _ _ hM hKp⟩,
      ⟨p ^ (e - 1) * (p + 1) * Z, ?_, hfin _ _ hp1 hZp⟩⟩
    · rw [per_mul_iff hcop]
      exact ⟨per_mul h1 K, per_of_dvd hK (dvd_mul_left _ _)⟩
    · rw [zer_mul_iff hcop]
      exact ⟨zer_mul h2 Z, zer_of_dvd hZ (dvd_mul_left _ _)⟩

lemma primes_le_five_of_per {n : ℕ} (hn : 0 < n) (h : ∀ K, Per n K → n ∣ K) :
    ∀ q, q.Prime → q ∣ n → q ≤ 5 := by
  by_contra hc
  obtain ⟨p, hp, h7, hpn, hmax⟩ := exists_largest hn hc
  obtain ⟨⟨K, hK, hnK⟩, -⟩ := large_prime_step hn hp h7 hpn hmax
  exact hnK (h K hK)

lemma primes_le_five_of_zer {n : ℕ} (hn : 0 < n) (h : ∀ K, Zer n K → n ∣ K) :
    ∀ q, q.Prime → q ∣ n → q ≤ 5 := by
  by_contra hc
  obtain ⟨p, hp, h7, hpn, hmax⟩ := exists_largest hn hc
  obtain ⟨-, ⟨K, hK, hnK⟩⟩ := large_prime_step hn hp h7 hpn hmax
  exact hnK (h K hK)

/-- A positive `n` with prime factors at most `5` is `2 ^ a 3 ^ b 5 ^ c`. -/
lemma eq_two_three_five {n : ℕ} (hn : 0 < n) (h : ∀ q, q.Prime → q ∣ n → q ≤ 5) :
    ∃ a b c : ℕ, n = 2 ^ a * 3 ^ b * 5 ^ c := by
  obtain ⟨a, m1, h1, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 2 (by norm_num)
  have hm1 : m1 ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨b, m2, h2, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm1 3 (by norm_num)
  have hm2 : m2 ≠ 0 := by rintro rfl; simp at hm1
  obtain ⟨c, m3, h3, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm2 5 (by norm_num)
  refine ⟨a, b, c, ?_⟩
  by_cases hm3 : m3 = 1
  · subst hm3; ring
  exfalso
  obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm3
  have hqn : q ∣ 2 ^ a * (3 ^ b * (5 ^ c * m3)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_left hqm _) _) _
  have hq5 := h q hq hqn
  rcases prime_cases hq with rfl | rfl | rfl | h7
  · exact h1 (Dvd.dvd.mul_left (Dvd.dvd.mul_left hqm _) _)
  · exact h2 (Dvd.dvd.mul_left hqm _)
  · exact h3 hqm
  · omega

end TuringTask
