import Mathlib
import TuringTask.PellDescent

/-!
# Indices with small prime factors, and helpers for the explicit units

* `index_form`: a positive `k` whose prime factors are at most `13` is
  `2 ^ a 3 ^ b 5 ^ c 7 ^ d 11 ^ e 13 ^ f`.
* `dvd_of_bounds`: bounds on these exponents (from `¬ p ^ (n + 1) ∣ k`) give `k ∣ L`.
* `primes_210`, `primes_65`, `primes_30030`: the prime factors of `210`, `65` and `30030`.
* `rank210`, `rank65`, `rank30030`: the rank hypothesis of `smooth_index` from one index per
  prime.
* `squarefree_dvd`: a squarefree number whose prime factors divide `P` divides `P`.
* `hmin_of_sqrt`: the minimality hypothesis of `pell_descent` from `Nat.sqrt` checks.
-/

namespace TuringTask

lemma prime_le_13 {p : ℕ} (hp : p.Prime) (h : p ≤ 13) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 := by
  interval_cases p <;> first | omega | (exfalso; norm_num at hp)

/-- A positive integer with prime factors at most `13`. -/
lemma index_form {k : ℕ} (hk : 0 < k) (h : ∀ p, p.Prime → p ∣ k → p ≤ 13) :
    ∃ a b c d e f : ℕ, k = 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e * 13 ^ f := by
  obtain ⟨a, m1, h1, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk.ne' 2 (by norm_num)
  have hm1 : m1 ≠ 0 := by rintro rfl; simp at hk
  obtain ⟨b, m2, h2, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm1 3 (by norm_num)
  have hm2 : m2 ≠ 0 := by rintro rfl; simp at hm1
  obtain ⟨c, m3, h3, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm2 5 (by norm_num)
  have hm3 : m3 ≠ 0 := by rintro rfl; simp at hm2
  obtain ⟨d, m4, h4, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm3 7 (by norm_num)
  have hm4 : m4 ≠ 0 := by rintro rfl; simp at hm3
  obtain ⟨e, m5, h5, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm4 11 (by norm_num)
  have hm5 : m5 ≠ 0 := by rintro rfl; simp at hm4
  obtain ⟨f, m6, h6, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm5 13 (by norm_num)
  refine ⟨a, b, c, d, e, f, ?_⟩
  by_cases hm6 : m6 = 1
  · subst hm6; ring
  exfalso
  obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm6
  have hqk : q ∣ 2 ^ a * (3 ^ b * (5 ^ c * (7 ^ d * (11 ^ e * (13 ^ f * m6))))) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_left
      (Dvd.dvd.mul_left (Dvd.dvd.mul_left hqm _) _) _) _) _) _
  rcases prime_le_13 hq (h q hq hqk) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1 (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_left
      (Dvd.dvd.mul_left hqm _) _) _) _) _)
  · exact h2 (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_left
      (Dvd.dvd.mul_left hqm _) _) _) _)
  · exact h3 (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_left hqm _) _) _)
  · exact h4 (Dvd.dvd.mul_left (Dvd.dvd.mul_left hqm _) _)
  · exact h5 (Dvd.dvd.mul_left hqm _)
  · exact h6 hqm

lemma exp_le_of_not_dvd {p e n k : ℕ} (he : p ^ e ∣ k) (h : ¬ p ^ (n + 1) ∣ k) : e ≤ n := by
  by_contra hc
  push Not at hc
  exact h (dvd_trans (pow_dvd_pow p hc) he)

/-- Exponent bounds give `k ∣ L`. -/
lemma dvd_of_bounds {k A B C E F G : ℕ} (hk : 0 < k) (h : ∀ p, p.Prime → p ∣ k → p ≤ 13)
    (h2 : ¬ 2 ^ (A + 1) ∣ k) (h3 : ¬ 3 ^ (B + 1) ∣ k) (h5 : ¬ 5 ^ (C + 1) ∣ k)
    (h7 : ¬ 7 ^ (E + 1) ∣ k) (h11 : ¬ 11 ^ (F + 1) ∣ k) (h13 : ¬ 13 ^ (G + 1) ∣ k) :
    k ∣ 2 ^ A * 3 ^ B * 5 ^ C * 7 ^ E * 11 ^ F * 13 ^ G := by
  obtain ⟨a, b, c, d, e, f, rfl⟩ := index_form hk h
  have ha := exp_le_of_not_dvd (e := a) (Dvd.intro (3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e * 13 ^ f)
    (by ring)) h2
  have hb := exp_le_of_not_dvd (e := b) (Dvd.intro (2 ^ a * 5 ^ c * 7 ^ d * 11 ^ e * 13 ^ f)
    (by ring)) h3
  have hc := exp_le_of_not_dvd (e := c) (Dvd.intro (2 ^ a * 3 ^ b * 7 ^ d * 11 ^ e * 13 ^ f)
    (by ring)) h5
  have hd := exp_le_of_not_dvd (e := d) (Dvd.intro (2 ^ a * 3 ^ b * 5 ^ c * 11 ^ e * 13 ^ f)
    (by ring)) h7
  have he := exp_le_of_not_dvd (e := e) (Dvd.intro (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 13 ^ f)
    (by ring)) h11
  have hf := exp_le_of_not_dvd (e := f) (Dvd.intro (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e)
    (by ring)) h13
  exact mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul
    (pow_dvd_pow 2 ha) (pow_dvd_pow 3 hb)) (pow_dvd_pow 5 hc)) (pow_dvd_pow 7 hd))
    (pow_dvd_pow 11 he)) (pow_dvd_pow 13 hf)

lemma not_dvd_of_gt {k p R : ℕ} (hp : p.Prime) (h : ∀ q, q.Prime → q ∣ k → q ≤ R)
    (h7 : R < p) : ¬ p ^ (0 + 1) ∣ k := by
  rw [zero_add, pow_one]
  intro hd
  have := h p hp hd
  omega

lemma primes_210 {q : ℕ} (hq : q.Prime) (h : q ∣ 210) : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 := by
  have := Nat.le_of_dvd (by norm_num) h
  interval_cases q <;> first | omega | (exfalso; norm_num at hq)

lemma primes_65 {q : ℕ} (hq : q.Prime) (h : q ∣ 65) : q = 5 ∨ q = 13 := by
  have := Nat.le_of_dvd (by norm_num) h
  interval_cases q <;> first | omega | (exfalso; norm_num at hq)

lemma primes_30030 {q : ℕ} (hq : q.Prime) (h : q ∣ 30030) :
    q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 := by
  have h' : q ∣ 2 * 3 * 5 * 7 * 11 * 13 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hq).mp h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hq).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hq).mp h2 with h3 | h3
      · rcases (Nat.Prime.dvd_mul hq).mp h3 with h4 | h4
        · rcases (Nat.Prime.dvd_mul hq).mp h4 with h5 | h5
          · left; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h5
          · right; left; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h5
        · right; right; left; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp h4
      · right; right; right; left
        exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h3
    · right; right; right; right; left
      exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h2
  · right; right; right; right; right
    exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h1

variable {D a b : ℕ}

lemma rank210 {R r2 r3 r5 r7 : ℕ} (h2 : 0 < r2 ∧ r2 ≤ R ∧ 2 ∣ pY D a b r2)
    (h3 : 0 < r3 ∧ r3 ≤ R ∧ 3 ∣ pY D a b r3) (h5 : 0 < r5 ∧ r5 ≤ R ∧ 5 ∣ pY D a b r5)
    (h7 : 0 < r7 ∧ r7 ≤ R ∧ 7 ∣ pY D a b r7) :
    ∀ q, q.Prime → q ∣ 210 → ∃ r, 0 < r ∧ r ≤ R ∧ q ∣ pY D a b r := by
  intro q hq hd
  rcases primes_210 hq hd with rfl | rfl | rfl | rfl
  exacts [⟨r2, h2⟩, ⟨r3, h3⟩, ⟨r5, h5⟩, ⟨r7, h7⟩]

lemma rank65 {R r5 r13 : ℕ} (h5 : 0 < r5 ∧ r5 ≤ R ∧ 5 ∣ pY D a b r5)
    (h13 : 0 < r13 ∧ r13 ≤ R ∧ 13 ∣ pY D a b r13) :
    ∀ q, q.Prime → q ∣ 65 → ∃ r, 0 < r ∧ r ≤ R ∧ q ∣ pY D a b r := by
  intro q hq hd
  rcases primes_65 hq hd with rfl | rfl
  exacts [⟨r5, h5⟩, ⟨r13, h13⟩]

lemma rank30030 {R r2 r3 r5 r7 r11 r13 : ℕ} (h2 : 0 < r2 ∧ r2 ≤ R ∧ 2 ∣ pY D a b r2)
    (h3 : 0 < r3 ∧ r3 ≤ R ∧ 3 ∣ pY D a b r3) (h5 : 0 < r5 ∧ r5 ≤ R ∧ 5 ∣ pY D a b r5)
    (h7 : 0 < r7 ∧ r7 ≤ R ∧ 7 ∣ pY D a b r7) (h11 : 0 < r11 ∧ r11 ≤ R ∧ 11 ∣ pY D a b r11)
    (h13 : 0 < r13 ∧ r13 ≤ R ∧ 13 ∣ pY D a b r13) :
    ∀ q, q.Prime → q ∣ 30030 → ∃ r, 0 < r ∧ r ≤ R ∧ q ∣ pY D a b r := by
  intro q hq hd
  rcases primes_30030 hq hd with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨r2, h2⟩, ⟨r3, h3⟩, ⟨r5, h5⟩, ⟨r7, h7⟩, ⟨r11, h11⟩, ⟨r13, h13⟩]

lemma bR_of_le {R : ℕ} (hb : 0 < b) (h : b ≤ R) : ∀ p, p.Prime → p ∣ b → p ≤ R :=
  fun _ _ hd => (Nat.le_of_dvd hb hd).trans h

lemma bR_210 {R : ℕ} (hb : b ∣ 210 ^ 2) (h : 7 ≤ R) : ∀ p, p.Prime → p ∣ b → p ≤ R := by
  intro p hp hd
  rcases primes_210 hp (hp.dvd_of_dvd_pow (dvd_trans hd hb)) with rfl | rfl | rfl | rfl <;> omega

/-- A squarefree number whose prime factors divide `P` divides `P`. -/
lemma squarefree_dvd {P n : ℕ} (hn : Squarefree n) (hs : Smooth P n) : n ∣ P := by
  rw [← Nat.prod_primeFactors_of_squarefree hn]
  refine Finset.prod_primes_dvd P (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) ?_
  intro p hp
  exact hs p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)

lemma le_13_of_le {k R : ℕ} (h : ∀ q, q.Prime → q ∣ k → q ≤ R) (hR : R ≤ 13) :
    ∀ q, q.Prime → q ∣ k → q ≤ 13 :=
  fun q hq hd => (h q hq hd).trans hR

lemma not_two_dvd_of_norm {D a b k : ℕ} (hσ : (a : ℤ) ^ 2 - D * b ^ 2 = -1)
    (h : (pX D a b k : ℤ) ^ 2 - D * (pY D a b k : ℤ) ^ 2 = -1) : ¬ 2 ^ (0 + 1) ∣ k := by
  rw [norm_pow hσ] at h
  rw [zero_add, pow_one, ← even_iff_two_dvd, Nat.not_even_iff_odd]
  exact (neg_one_pow_eq_neg_one_iff_odd (by norm_num)).mp h

/-- The minimality hypothesis of `pell_descent` from `Nat.sqrt` evaluations. -/
lemma hmin_of_sqrt {σ : ℤ} (hσ1 : σ = 1 ∨ σ = -1)
    (h : ∀ y : ℕ, 0 < y → y < b → Nat.sqrt (D * y ^ 2 + 1) ^ 2 ≠ D * y ^ 2 + 1 ∧
      (σ = -1 → Nat.sqrt (D * y ^ 2 - 1) ^ 2 ≠ D * y ^ 2 - 1)) :
    ∀ x y : ℕ, 0 < y → y < b → (x : ℤ) ^ 2 - D * y ^ 2 ≠ 1 ∧ (x : ℤ) ^ 2 - D * y ^ 2 ≠ σ := by
  intro x y hy hyb
  have h1 : (x : ℤ) ^ 2 - D * y ^ 2 ≠ 1 := by
    intro he
    have : x ^ 2 = D * y ^ 2 + 1 := by zify; linarith
    exact (h y hy hyb).1 (sqrt_sq_of_sq this)
  refine ⟨h1, ?_⟩
  rcases hσ1 with rfl | rfl
  · exact h1
  · intro he
    have : x ^ 2 = D * y ^ 2 - 1 := by
      have hle : 1 ≤ D * y ^ 2 := by
        by_contra hc
        push Not at hc
        have h0 : D * y ^ 2 = 0 := by omega
        have : (x : ℤ) ^ 2 = -1 := by
          have h0' : (D : ℤ) * y ^ 2 = 0 := by exact_mod_cast h0
          linarith
        nlinarith [sq_nonneg (x : ℤ)]
      zify [hle]
      linarith
    exact (h y hy hyb).2 rfl (sqrt_sq_of_sq this)

end TuringTask
