import Mathlib
import TuringTask.Residues

/-!
# Squares and twice squares among Fibonacci and Lucas numbers (Cohn)

Odd indices: write `n = m + 2 k t` with a small base `m` in `{0, +-1, +-3, +-6}`, `k` even and
prime to `3`, `t` odd; then `F(n) = -F(m)` and `L(n) = -L(m)` modulo `L(k)`, and `L(k) = 3
(mod 4)` excludes `x^2 = -1, -4, -9` modulo `L(k)`.  Even indices: `F(2 m) = F(m) L(m)` with
`gcd(F(m), L(m)) | 2`, which reduces the Fibonacci statements to the Lucas statements.
-/

namespace TuringTask

lemma sq_mod_four (x : ℕ) : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  rw [Nat.pow_mod]
  rcases (by omega : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3) with h | h | h | h <;>
    rw [h] <;> decide

lemma two_mul_sq_mod_eight (x : ℕ) : 2 * x ^ 2 % 8 = 0 ∨ 2 * x ^ 2 % 8 = 2 := by
  rw [Nat.mul_mod, Nat.pow_mod]
  rcases (by omega : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨
    x % 8 = 6 ∨ x % 8 = 7) with h | h | h | h | h | h | h | h <;> rw [h] <;> decide

lemma lucZ_eq_lucNat (n : ℕ) (hn : 1 ≤ n) : lucZ n = (lucNat n : ℤ) :=
  lucZ_natCast n hn

lemma even_natCast_of_mod (k : ℕ) (hk : k % 2 = 0) : Even (k : ℤ) := by
  exact_mod_cast Nat.even_iff.mpr hk

/-- Shift of a Fibonacci number with natural index `n = m + 2 k t`. -/
lemma lucZ_dvd_fib_nat (n : ℕ) (m : ℤ) (k t : ℕ) (hk : k % 2 = 0) (ht : Odd t)
    (hn : (n : ℤ) = m + 2 * k * t) : lucZ k ∣ (Nat.fib n : ℤ) + Int.fib m := by
  have := lucZ_dvd_fib_shift (k : ℤ) (even_natCast_of_mod k hk) m t ht
  rwa [← hn, Int.fib_natCast] at this

/-- Shift of a Lucas number with natural index `n = m + 2 k t`. -/
lemma lucZ_dvd_lucNat (n : ℕ) (hn1 : 1 ≤ n) (m : ℤ) (k t : ℕ) (hk : k % 2 = 0) (ht : Odd t)
    (hn : (n : ℤ) = m + 2 * k * t) : lucZ k ∣ (lucNat n : ℤ) + lucZ m := by
  have := lucZ_dvd_lucZ_shift (k : ℤ) (even_natCast_of_mod k hk) m t ht
  rwa [← hn, lucZ_eq_lucNat n hn1] at this

/-- `L(k)` is odd for `k` even and prime to `3`, so a factor `2` can be cancelled. -/
lemma lucZ_dvd_of_dvd_two_mul (k : ℕ) (hk : k % 2 = 0) (h3 : k % 3 ≠ 0) (y : ℤ)
    (h : lucZ k ∣ 2 * y) : lucZ k ∣ y := by
  rw [lucZ_eq_lucNat k (by omega)] at h ⊢
  have hodd : Nat.Coprime (lucNat k) 2 := by
    rw [Nat.coprime_comm, Nat.coprime_two_left, Nat.odd_iff]
    have := lucNat_mod_four_of_even k hk h3
    omega
  have hcop : IsCoprime ((lucNat k : ℕ) : ℤ) ((2 : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hodd
  exact hcop.dvd_of_dvd_mul_left (by simpa [mul_comm] using h)

/-- A number `= 0 (mod 4)` above zero splits as `2 k t`. -/
lemma split_of_mod_four (N : ℕ) (hN : 0 < N) (h4 : N % 4 = 0) :
    ∃ k t : ℕ, N = 2 * k * t ∧ k % 2 = 0 ∧ k % 3 ≠ 0 ∧ Odd t ∧ (N % 8 = 0 → k % 4 = 0) := by
  obtain ⟨k, t, h1, h2, h3, h4, h5⟩ := exists_split_three N hN (Nat.dvd_of_mod_eq_zero h4)
  exact ⟨k, t, h1, h2, h3, h4, fun h8 => h5 (Nat.dvd_of_mod_eq_zero h8)⟩

/-- Cohn: `L(n) = x^2` with `n >= 1` forces `n = 1` or `n = 3`. -/
theorem lucNat_eq_sq_cases (n x : ℕ) (hn : 1 ≤ n) (h : lucNat n = x ^ 2) : n = 1 ∨ n = 3 := by
  rcases Nat.even_or_odd n with he | ho
  · have := lucNat_mod_four_even n hn (Nat.even_iff.mp he)
    have := sq_mod_four x
    omega
  have ho' := Nat.odd_iff.mp ho
  by_contra hne
  push Not at hne
  have hx : (lucNat n : ℤ) = (x : ℤ) ^ 2 := by exact_mod_cast h
  rcases (by omega : n % 4 = 1 ∨ n % 4 = 3) with h4 | h4
  · obtain ⟨k, t, hN, hk, hk3, ht, -⟩ := split_of_mod_four (n - 1) (by omega) (by omega)
    have hn' : n = 2 * k * t + 1 := by rw [← hN]; omega
    have hd := lucZ_dvd_lucNat n hn 1 k t hk ht (by rw [hn']; push_cast; ring)
    rw [hx, show lucZ 1 = 1 by decide] at hd
    exact lucZ_not_dvd_sq_add_one k hk hk3 x hd
  · obtain ⟨k, t, hN, hk, hk3, ht, -⟩ := split_of_mod_four (n - 3) (by omega) (by omega)
    have hn' : n = 2 * k * t + 3 := by rw [← hN]; omega
    have hd := lucZ_dvd_lucNat n hn 3 k t hk ht (by rw [hn']; push_cast; ring)
    rw [hx, show lucZ 3 = 4 by decide] at hd
    exact lucZ_not_dvd_sq_add_four k hk hk3 x hd

/-- Cohn: `L(n) = 2 x^2` with `n >= 1` forces `n = 6`. -/
theorem lucNat_eq_two_mul_sq_cases (n x : ℕ) (hn : 1 ≤ n) (h : lucNat n = 2 * x ^ 2) :
    n = 6 := by
  rcases Nat.even_or_odd n with he | ho
  swap
  · have := lucNat_mod_eight_odd n (Nat.odd_iff.mp ho)
    have := two_mul_sq_mod_eight x
    omega
  have he' := Nat.even_iff.mp he
  by_contra hne
  have hx : (lucNat n : ℤ) = 2 * (x : ℤ) ^ 2 := by exact_mod_cast h
  rcases (by omega : n % 4 = 0 ∨ n % 8 = 6 ∨ n % 8 = 2) with h4 | h4 | h4
  · obtain ⟨k, t, hN, hk, hk3, ht, -⟩ := split_of_mod_four n (by omega) h4
    have hd := lucZ_dvd_lucNat n hn 0 k t hk ht (by rw [hN]; push_cast; ring)
    rw [hx, show lucZ 0 = 2 by decide, show 2 * (x : ℤ) ^ 2 + 2 = 2 * ((x : ℤ) ^ 2 + 1) by ring]
      at hd
    exact lucZ_not_dvd_sq_add_one k hk hk3 x (lucZ_dvd_of_dvd_two_mul k hk hk3 _ hd)
  · obtain ⟨k, t, hN, hk, hk3, ht, h8⟩ := split_of_mod_four (n - 6) (by omega) (by omega)
    have hn' : n = 2 * k * t + 6 := by rw [← hN]; omega
    have hd := lucZ_dvd_lucNat n hn 6 k t hk ht (by rw [hn']; push_cast; ring)
    rw [hx, show lucZ 6 = 18 by decide,
      show 2 * (x : ℤ) ^ 2 + 18 = 2 * ((x : ℤ) ^ 2 + 9) by ring] at hd
    exact lucZ_not_dvd_sq_add_nine k (h8 (by omega)) hk3 x
      (lucZ_dvd_of_dvd_two_mul k hk hk3 _ hd)
  · obtain ⟨k, t, hN, hk, hk3, ht, h8⟩ := split_of_mod_four (n + 6) (by omega) (by omega)
    have hn' : (n : ℤ) = -6 + 2 * k * t := by
      have : ((n + 6 : ℕ) : ℤ) = ((2 * k * t : ℕ) : ℤ) := by rw [hN]
      push_cast at this
      linarith
    have hd := lucZ_dvd_lucNat n hn (-6) k t hk ht hn'
    rw [hx, show lucZ (-6) = 18 by decide,
      show 2 * (x : ℤ) ^ 2 + 18 = 2 * ((x : ℤ) ^ 2 + 9) by ring] at hd
    exact lucZ_not_dvd_sq_add_nine k (h8 (by omega)) hk3 x
      (lucZ_dvd_of_dvd_two_mul k hk hk3 _ hd)

/-- Odd Fibonacci indices: for a base `m` in `{1, -1, 3, -3}` with `n = m (mod 4)` and `n != m`,
some `L(k)` with `k` even and prime to `3` divides `F(n) + F(m)`. -/
lemma fib_odd_index_dvd (n : ℕ) (hn : n % 2 = 1) (m : ℤ) (hm : m = 1 ∨ m = -1 ∨ m = 3 ∨ m = -3)
    (hnm : (n : ℤ) ≠ m) (hmod : ((n : ℤ) - m) % 4 = 0) :
    ∃ k : ℕ, k % 2 = 0 ∧ k % 3 ≠ 0 ∧ lucZ k ∣ (Nat.fib n : ℤ) + Int.fib m := by
  have hpos : 0 < (n : ℤ) - m ∨ (n : ℤ) - m < 0 := by omega
  rcases hpos with hpos | hneg
  · obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = (n : ℤ) - m := ⟨((n : ℤ) - m).toNat, by omega⟩
    obtain ⟨k, t, hNk, hk, hk3, ht, -⟩ := split_of_mod_four N (by omega) (by omega)
    refine ⟨k, hk, hk3, lucZ_dvd_fib_nat n m k t hk ht ?_⟩
    have : ((N : ℕ) : ℤ) = ((2 * k * t : ℕ) : ℤ) := by rw [hNk]
    push_cast at this
    linarith
  · exfalso
    rcases hm with rfl | rfl | rfl | rfl <;> omega

lemma sq_of_coprime_mul {a b c : ℕ} (hab : Nat.Coprime a b) (h : a * b = c ^ 2) :
    ∃ d, b = d ^ 2 :=
  exists_eq_pow_of_mul_eq_pow (by rw [Nat.isUnit_iff]; exact hab.symm) (by rw [mul_comm]; exact h)

/-- For `3 | m`, `m >= 1`: `F(m) = 2 a` and `L(m) = 2 b` with `a`, `b` coprime. -/
lemma fib_lucNat_halves (m : ℕ) (hm : 1 ≤ m) (h3 : m % 3 = 0) :
    ∃ a b : ℕ, Nat.fib m = 2 * a ∧ lucNat m = 2 * b ∧ Nat.Coprime a b := by
  have hF : Nat.fib m % 2 = 0 := by rw [fib_mod_two, if_pos h3]
  have hL : lucNat m % 2 = 0 := by rw [lucNat_mod_two m hm, hF]
  obtain ⟨a, ha⟩ : 2 ∣ Nat.fib m := Nat.dvd_of_mod_eq_zero hF
  obtain ⟨b, hb⟩ : 2 ∣ lucNat m := Nat.dvd_of_mod_eq_zero hL
  refine ⟨a, b, ha, hb, ?_⟩
  have hg := gcd_fib_lucNat_dvd_two m hm
  rw [ha, hb, Nat.gcd_mul_left] at hg
  have : Nat.gcd a b ∣ 1 :=
    (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp (by rwa [mul_one])
  exact Nat.Coprime.symm (Nat.coprime_comm.mp (Nat.dvd_one.mp this))

/-- For `3` not dividing `m`, `m >= 1`: `F(m)` and `L(m)` are odd and coprime. -/
lemma fib_lucNat_odd_coprime (m : ℕ) (hm : 1 ≤ m) (h3 : m % 3 ≠ 0) :
    Nat.fib m % 2 = 1 ∧ lucNat m % 2 = 1 ∧ Nat.Coprime (Nat.fib m) (lucNat m) := by
  have hF : Nat.fib m % 2 = 1 := by rw [fib_mod_two, if_neg h3]
  have hL : lucNat m % 2 = 1 := by rw [lucNat_mod_two m hm, hF]
  refine ⟨hF, hL, ?_⟩
  have hg := gcd_fib_lucNat_dvd_two m hm
  have hodd : ¬ 2 ∣ Nat.gcd (Nat.fib m) (lucNat m) := by
    intro h2
    have := h2.trans (Nat.gcd_dvd_left _ _)
    omega
  rcases (Nat.dvd_prime Nat.prime_two).mp hg with h | h
  · exact h
  · omega

/-- Cohn: `F(n) = x^2` forces `n` in `{0, 1, 2, 12}`. -/
theorem fib_eq_sq_cases (n x : ℕ) (h : Nat.fib n = x ^ 2) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 12 := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by have := Nat.even_iff.mp he; omega⟩
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · left
      omega
    rw [fib_two_mul_eq m hm0] at h
    by_cases h3 : m % 3 = 0
    · obtain ⟨a, b, ha, hb, hab⟩ := fib_lucNat_halves m hm0 h3
      rw [ha, hb] at h
      have hx : Even x := (Nat.even_pow.mp ⟨2 * a * b, by rw [← h]; ring⟩).1
      obtain ⟨y, rfl⟩ := hx
      have hy : a * b = y ^ 2 := by nlinarith
      obtain ⟨s, hs⟩ := sq_of_coprime_mul hab hy
      have := lucNat_eq_two_mul_sq_cases m s hm0 (by rw [hb, hs])
      omega
    · obtain ⟨-, -, hcop⟩ := fib_lucNat_odd_coprime m hm0 h3
      obtain ⟨s, hs⟩ := sq_of_coprime_mul hcop h
      have := lucNat_eq_sq_cases m s hm0 hs
      omega
  · have ho' := Nat.odd_iff.mp ho
    by_contra hne
    have hx : (Nat.fib n : ℤ) = (x : ℤ) ^ 2 := by exact_mod_cast h
    rcases (by omega : n % 4 = 1 ∨ n % 4 = 3) with h4 | h4
    · obtain ⟨k, hk, hk3, hd⟩ := fib_odd_index_dvd n ho' 1 (by simp) (by omega) (by omega)
      rw [hx, Int.fib_one] at hd
      exact lucZ_not_dvd_sq_add_one k hk hk3 x hd
    · obtain ⟨k, hk, hk3, hd⟩ := fib_odd_index_dvd n ho' (-1) (by simp) (by omega) (by omega)
      rw [hx, Int.fib_neg_one] at hd
      exact lucZ_not_dvd_sq_add_one k hk hk3 x hd

/-- Cohn: `F(n) = 2 x^2` forces `n` in `{0, 3, 6}`. -/
theorem fib_eq_two_mul_sq_cases (n x : ℕ) (h : Nat.fib n = 2 * x ^ 2) :
    n = 0 ∨ n = 3 ∨ n = 6 := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by have := Nat.even_iff.mp he; omega⟩
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · left
      omega
    rw [fib_two_mul_eq m hm0] at h
    by_cases h3 : m % 3 = 0
    · obtain ⟨a, b, ha, hb, hab⟩ := fib_lucNat_halves m hm0 h3
      rw [ha, hb] at h
      have hx2 : x ^ 2 = a * b + a * b := by nlinarith
      have hx : Even x := (Nat.even_pow.mp ⟨a * b, hx2⟩).1
      obtain ⟨y, rfl⟩ := hx
      have hy : a * b = 2 * y ^ 2 := by nlinarith
      rcases Nat.even_or_odd b with hbe | hbo
      · obtain ⟨b', rfl⟩ := hbe
        have hy' : a * b' = y ^ 2 := by nlinarith
        have hab' : Nat.Coprime a b' := Nat.Coprime.coprime_dvd_right ⟨2, by ring⟩ hab
        obtain ⟨s, hs⟩ := sq_of_coprime_mul hab' hy'
        have := lucNat_eq_sq_cases m (2 * s) hm0 (by rw [hb, hs]; ring)
        omega
      · have hae : Even a := by
          by_contra hao
          rw [Nat.not_even_iff_odd] at hao
          have : Odd (a * b) := hao.mul hbo
          rw [hy] at this
          exact (Nat.not_even_iff_odd.mpr this) ⟨y ^ 2, by ring⟩
        obtain ⟨a', rfl⟩ := hae
        have hy' : a' * b = y ^ 2 := by nlinarith
        have hab' : Nat.Coprime a' b := Nat.Coprime.coprime_dvd_left ⟨2, by ring⟩ hab
        obtain ⟨s, hs⟩ := sq_of_coprime_mul hab' hy'
        have hm6 := lucNat_eq_two_mul_sq_cases m s hm0 (by rw [hb, hs])
        subst hm6
        have h12 : Nat.fib 6 * lucNat 6 = 144 := by decide
        rw [ha, hb] at h12
        have : y ^ 2 = 18 := by nlinarith
        have hy4 : y ≤ 4 := by nlinarith
        interval_cases y <;> omega
    · obtain ⟨hF, hL, -⟩ := fib_lucNat_odd_coprime m hm0 h3
      have : (Nat.fib m * lucNat m) % 2 = 1 := by
        rw [Nat.mul_mod, hF, hL]
      omega
  · have ho' := Nat.odd_iff.mp ho
    by_contra hne
    have hx : (Nat.fib n : ℤ) = 2 * (x : ℤ) ^ 2 := by exact_mod_cast h
    rcases (by omega : n % 4 = 3 ∨ n % 4 = 1) with h4 | h4
    · obtain ⟨k, hk, hk3, hd⟩ := fib_odd_index_dvd n ho' 3 (by simp) (by omega) (by omega)
      rw [hx, show Int.fib 3 = 2 by decide,
        show 2 * (x : ℤ) ^ 2 + 2 = 2 * ((x : ℤ) ^ 2 + 1) by ring] at hd
      exact lucZ_not_dvd_sq_add_one k hk hk3 x (lucZ_dvd_of_dvd_two_mul k hk hk3 _ hd)
    · obtain ⟨k, hk, hk3, hd⟩ := fib_odd_index_dvd n ho' (-3) (by simp) (by omega) (by omega)
      rw [hx, show Int.fib (-3) = 2 by decide,
        show 2 * (x : ℤ) ^ 2 + 2 = 2 * ((x : ℤ) ^ 2 + 1) by ring] at hd
      exact lucZ_not_dvd_sq_add_one k hk hk3 x (lucZ_dvd_of_dvd_two_mul k hk hk3 _ hd)

end TuringTask
