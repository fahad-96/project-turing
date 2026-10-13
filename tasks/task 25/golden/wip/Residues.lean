import Mathlib
import TuringTask.Lucas

/-!
# Residues of Fibonacci and Lucas numbers, and the obstruction modulo `L(k)`

* `fib_mod_eq_of_period`: if `F(P) = 0` and `F(P + 1) = 1` modulo `M`, then `F(n) mod M`
  depends only on `n mod P` (used with `(M, P) = (2, 3), (3, 8), (4, 6), (8, 12)`).
* Residues of `L(n) = F(n - 1) + F(n + 1)` modulo 3, 4 and 8.
* `exists_prime_dvd_mod_four`: a number `= 3 (mod 4)` has a prime factor `= 3 (mod 4)`;
  hence `x^2 + c^2` is never divisible by such a number coprime to `c`.
* `exists_split_three`: `N = 2 k t` with `k` even, `3` not dividing `k`, `t` a power of `3`.
-/

namespace TuringTask

/-- Periodicity of `F(n) mod M` with period `P`. -/
lemma fib_mod_eq_of_period (M P : ℕ) (hP : 0 < P) (h0 : Nat.fib P % M = 0)
    (h1 : Nat.fib (P + 1) % M = 1 % M) (j : ℕ) : Nat.fib j % M = Nat.fib (j % P) % M := by
  obtain ⟨Q, rfl⟩ : ∃ Q, P = Q + 1 := ⟨P - 1, by omega⟩
  have hQ : Nat.fib Q ≡ 1 [MOD M] := by
    have e : Nat.fib (Q + 2) = Nat.fib Q + Nat.fib (Q + 1) := Nat.fib_add_two
    rw [show Q + 1 + 1 = Q + 2 by ring, e, Nat.add_mod, h0, add_zero, Nat.mod_mod] at h1
    exact h1
  have hstep : ∀ m, Nat.fib (m + (Q + 1)) % M = Nat.fib m % M := by
    intro m
    rw [show m + (Q + 1) = m + Q + 1 by ring, Nat.fib_add]
    have h : Nat.fib m * Nat.fib Q + Nat.fib (m + 1) * Nat.fib (Q + 1)
        ≡ Nat.fib m * 1 + Nat.fib (m + 1) * 0 [MOD M] :=
      Nat.ModEq.add (Nat.ModEq.mul_left _ hQ) (Nat.ModEq.mul_left _ h0)
    rw [mul_one, mul_zero, add_zero] at h
    exact h
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j < Q + 1
    · rw [Nat.mod_eq_of_lt hj]
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + (Q + 1) := ⟨j - (Q + 1), by omega⟩
      rw [hstep, Nat.add_mod_right, ih i (by omega)]

/-- The Lucas number `L(n) = F(n - 1) + F(n + 1)` of the prompt (natural index). -/
def lucNat (n : ℕ) : ℕ := Nat.fib (n - 1) + Nat.fib (n + 1)

lemma lucNat_mod (M P : ℕ) (hP : 0 < P) (h0 : Nat.fib P % M = 0)
    (h1 : Nat.fib (P + 1) % M = 1 % M) (n : ℕ) :
    lucNat n % M = (Nat.fib ((n - 1) % P) % M + Nat.fib ((n + 1) % P) % M) % M := by
  rw [lucNat, Nat.add_mod, fib_mod_eq_of_period M P hP h0 h1 (n - 1),
    fib_mod_eq_of_period M P hP h0 h1 (n + 1)]

lemma lucNat_mod_four_of_even (k : ℕ) (hk : k % 2 = 0) (h3 : k % 3 ≠ 0) :
    lucNat k % 4 = 3 := by
  rw [lucNat_mod 4 6 (by norm_num) (by decide) (by decide)]
  rcases (by omega : k % 6 = 2 ∨ k % 6 = 4) with h | h
  · rw [show (k - 1) % 6 = 1 by omega, show (k + 1) % 6 = 3 by omega]
    decide
  · rw [show (k - 1) % 6 = 3 by omega, show (k + 1) % 6 = 5 by omega]
    decide

lemma lucNat_mod_four_even (n : ℕ) (hn : 1 ≤ n) (he : n % 2 = 0) :
    lucNat n % 4 = 2 ∨ lucNat n % 4 = 3 := by
  rw [lucNat_mod 4 6 (by norm_num) (by decide) (by decide)]
  rcases (by omega : n % 6 = 0 ∨ n % 6 = 2 ∨ n % 6 = 4) with h | h | h
  · rw [show (n - 1) % 6 = 5 by omega, show (n + 1) % 6 = 1 by omega]
    decide
  · rw [show (n - 1) % 6 = 1 by omega, show (n + 1) % 6 = 3 by omega]
    decide
  · rw [show (n - 1) % 6 = 3 by omega, show (n + 1) % 6 = 5 by omega]
    decide

lemma lucNat_mod_three_ne_zero (k : ℕ) (hk : k % 4 = 0) : lucNat k % 3 ≠ 0 := by
  rw [lucNat_mod 3 8 (by norm_num) (by decide) (by decide)]
  rcases (by omega : k % 8 = 0 ∨ k % 8 = 4) with h | h
  · rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      decide
    · rw [show (k - 1) % 8 = 7 by omega, show (k + 1) % 8 = 1 by omega]
      decide
  · rw [show (k - 1) % 8 = 3 by omega, show (k + 1) % 8 = 5 by omega]
    decide

lemma lucNat_mod_eight_odd (n : ℕ) (ho : n % 2 = 1) :
    lucNat n % 8 ≠ 0 ∧ lucNat n % 8 ≠ 2 := by
  rw [lucNat_mod 8 12 (by norm_num) (by decide) (by decide)]
  have h : n % 12 = 1 ∨ n % 12 = 3 ∨ n % 12 = 5 ∨ n % 12 = 7 ∨ n % 12 = 9 ∨ n % 12 = 11 := by
    omega
  rcases h with h | h | h | h | h | h
  · rw [show (n - 1) % 12 = 0 by omega, show (n + 1) % 12 = 2 by omega]
    decide
  · rw [show (n - 1) % 12 = 2 by omega, show (n + 1) % 12 = 4 by omega]
    decide
  · rw [show (n - 1) % 12 = 4 by omega, show (n + 1) % 12 = 6 by omega]
    decide
  · rw [show (n - 1) % 12 = 6 by omega, show (n + 1) % 12 = 8 by omega]
    decide
  · rw [show (n - 1) % 12 = 8 by omega, show (n + 1) % 12 = 10 by omega]
    decide
  · rw [show (n - 1) % 12 = 10 by omega, show (n + 1) % 12 = 0 by omega]
    decide

lemma fib_mod_two (n : ℕ) : Nat.fib n % 2 = if n % 3 = 0 then 0 else 1 := by
  rw [fib_mod_eq_of_period 2 3 (by norm_num) (by decide) (by decide)]
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h <;> rw [h] <;> decide

/-- `L(n) = 2 F(n - 1) + F(n)` for `n >= 1`. -/
lemma lucNat_eq (n : ℕ) (hn : 1 ≤ n) : lucNat n = 2 * Nat.fib (n - 1) + Nat.fib n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_add_cancel hn).symm⟩
  rw [lucNat, show m + 1 - 1 = m by omega, show m + 1 + 1 = m + 2 by ring, Nat.fib_add_two]
  ring

lemma lucNat_mod_two (n : ℕ) (hn : 1 ≤ n) : lucNat n % 2 = Nat.fib n % 2 := by
  rw [lucNat_eq n hn]
  omega

/-- `F(2 m) = F(m) L(m)` for `m >= 1`. -/
lemma fib_two_mul_eq (m : ℕ) (hm : 1 ≤ m) : Nat.fib (2 * m) = Nat.fib m * lucNat m := by
  rw [Nat.fib_two_mul, lucNat_eq m hm]
  congr 1
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [show j + 1 - 1 = j by omega, show j + 1 + 1 = j + 2 by ring, Nat.fib_add_two]
  omega

/-- `gcd(F(m), L(m))` divides `2`. -/
lemma gcd_fib_lucNat_dvd_two (m : ℕ) (hm : 1 ≤ m) : Nat.gcd (Nat.fib m) (lucNat m) ∣ 2 := by
  set g := Nat.gcd (Nat.fib m) (lucNat m)
  have h1 : g ∣ Nat.fib m := Nat.gcd_dvd_left _ _
  have h2 : g ∣ 2 * Nat.fib (m - 1) := by
    have hL : g ∣ lucNat m := Nat.gcd_dvd_right _ _
    rw [lucNat_eq m hm] at hL
    exact (Nat.dvd_add_left h1).mp hL
  have hcop : Nat.Coprime (Nat.fib (m - 1)) (Nat.fib m) := by
    have := Nat.fib_coprime_fib_succ (m - 1)
    rwa [show m - 1 + 1 = m by omega] at this
  have : Nat.Coprime g (Nat.fib (m - 1)) :=
    Nat.Coprime.coprime_dvd_left h1 hcop.symm
  exact this.dvd_of_dvd_mul_right h2

/-- A natural number `= 3 (mod 4)` has a prime factor `= 3 (mod 4)`. -/
lemma exists_prime_dvd_mod_four (M : ℕ) (hM : M % 4 = 3) :
    ∃ p, p.Prime ∧ p ∣ M ∧ p % 4 = 3 := by
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    have hM1 : M ≠ 1 := by omega
    have hp := Nat.minFac_prime hM1
    have hdvd := Nat.minFac_dvd M
    by_cases h3 : M.minFac % 4 = 3
    · exact ⟨_, hp, hdvd, h3⟩
    · have hodd : M.minFac % 2 = 1 := by
        rcases hp.eq_two_or_odd with h2 | h2
        · rw [h2] at hdvd
          omega
        · exact h2
      have h1 : M.minFac % 4 = 1 := by omega
      obtain ⟨q, hq⟩ := hdvd
      have hq4 : q % 4 = 3 := by
        have := congrArg (· % 4) hq
        simp only [Nat.mul_mod, h1, one_mul, Nat.mod_mod] at this
        omega
      have hqlt : q < M := by
        have h2 := hp.two_le
        have hq0 : 0 < q := by omega
        nlinarith
      obtain ⟨r, hr, hrq, hr4⟩ := ih q hqlt hq4
      exact ⟨r, hr, hq ▸ Dvd.dvd.mul_left hrq _, hr4⟩

/-- If `M = 3 (mod 4)` and `c` is coprime to `M`, then `M` does not divide `x^2 + c^2`. -/
lemma not_dvd_sq_add_sq (M : ℕ) (hM : M % 4 = 3) (x c : ℤ) (hc : IsCoprime c (M : ℤ))
    (h : (M : ℤ) ∣ x ^ 2 + c ^ 2) : False := by
  obtain ⟨p, hp, hpM, hp4⟩ := exists_prime_dvd_mod_four M hM
  haveI := Fact.mk hp
  have hpM' : (p : ℤ) ∣ M := Int.natCast_dvd_natCast.mpr hpM
  have hzero : ((x ^ 2 + c ^ 2 : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (hpM'.trans h)
  have hcne : ((c : ℤ) : ZMod p) ≠ 0 := by
    intro hc0
    have hpc : (p : ℤ) ∣ c := (ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp hc0
    have hu := hc.isUnit_of_dvd' hpc hpM'
    rw [Int.isUnit_iff] at hu
    have := hp.two_le
    omega
  push_cast at hzero
  have hsq : IsSquare (-1 : ZMod p) := by
    refine ⟨(x : ZMod p) * ((c : ℤ) : ZMod p)⁻¹, ?_⟩
    field_simp
    linear_combination -hzero
  exact (ZMod.exists_sq_eq_neg_one_iff.mp hsq) hp4

/-- `N = 2 k t` with `k` even and prime to `3`, and `t` an odd power of `3`. -/
lemma exists_split_three (N : ℕ) (hN : 0 < N) (h4 : 4 ∣ N) :
    ∃ k t : ℕ, N = 2 * k * t ∧ k % 2 = 0 ∧ k % 3 ≠ 0 ∧ Odd t ∧ (8 ∣ N → k % 4 = 0) := by
  obtain ⟨M, rfl⟩ : 2 ∣ N := (by norm_num : (2 : ℕ) ∣ 4).trans h4
  have hM0 : M ≠ 0 := by omega
  obtain ⟨e, k, hk3, hMk⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM0 3 (by norm_num)
  have hcop2 : Nat.Coprime 2 (3 ^ e) := Nat.Coprime.pow_right _ (by norm_num)
  have hcop4 : Nat.Coprime 4 (3 ^ e) := Nat.Coprime.pow_right _ (by norm_num)
  refine ⟨k, 3 ^ e, by rw [hMk]; ring, ?_, by omega, Odd.pow (by decide), ?_⟩
  · have h2M : 2 ∣ M := by omega
    rw [hMk] at h2M
    have := hcop2.dvd_of_dvd_mul_left h2M
    omega
  · intro h8
    have h4M : 4 ∣ M := by omega
    rw [hMk] at h4M
    have := hcop4.dvd_of_dvd_mul_left h4M
    omega

/-- The obstruction: for `k` even and prime to `3`, `L(k)` never divides `x^2 + c^2` when `c`
is coprime to `L(k)`. -/
lemma lucZ_not_dvd (k : ℕ) (hk : k % 2 = 0) (h3 : k % 3 ≠ 0) (x c : ℤ)
    (hc : IsCoprime c (lucNat k : ℤ)) (h : lucZ k ∣ x ^ 2 + c ^ 2) : False := by
  have hk1 : 1 ≤ k := by omega
  rw [lucZ_natCast k hk1] at h
  exact not_dvd_sq_add_sq _ (lucNat_mod_four_of_even k hk h3) x c hc h

lemma lucZ_not_dvd_sq_add_one (k : ℕ) (hk : k % 2 = 0) (h3 : k % 3 ≠ 0) (x : ℤ)
    (h : lucZ k ∣ x ^ 2 + 1) : False :=
  lucZ_not_dvd k hk h3 x 1 isCoprime_one_left (by simpa using h)

lemma lucZ_not_dvd_sq_add_four (k : ℕ) (hk : k % 2 = 0) (h3 : k % 3 ≠ 0) (x : ℤ)
    (h : lucZ k ∣ x ^ 2 + 4) : False := by
  have hodd : Nat.Coprime 2 (lucNat k) := by
    rw [Nat.coprime_two_left, Nat.odd_iff]
    have := lucNat_mod_four_of_even k hk h3
    omega
  exact lucZ_not_dvd k hk h3 x 2 (by exact_mod_cast Nat.isCoprime_iff_coprime.mpr hodd)
    (by norm_num; exact h)

lemma lucZ_not_dvd_sq_add_nine (k : ℕ) (hk : k % 4 = 0) (h3 : k % 3 ≠ 0) (x : ℤ)
    (h : lucZ k ∣ x ^ 2 + 9) : False := by
  have hcop : Nat.Coprime 3 (lucNat k) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    have := lucNat_mod_three_ne_zero k hk
    omega
  exact lucZ_not_dvd k (by omega) h3 x 3 (by exact_mod_cast Nat.isCoprime_iff_coprime.mpr hcop)
    (by norm_num; exact h)

end TuringTask
