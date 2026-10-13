import Mathlib
import TuringTask.Factor

/-!
# `F(n) + 1 = x^2`, `F(n) = x^2 + 1` and `F(n) = 2 x^2 + 1`

* `lnat_three_sq`: `L(n) = 3 y^2` only for `n = 2`. Here `3 ∣ L(n)` gives `n = 2 (mod 4)`, and
  `n = 2 + 2 k t` or `n = -2 + 2 k t` with `4 ∣ k` gives `L(k) ∣ L(n) + 3 = 3 (y^2 + 1)` with
  `3` prime to `L(k)`, which `Residues.lean` excludes.
* `fib_two_mod_four`: `F(n) = 2 x^2 + 1` with `n = 2 (mod 4)` only for `n = 2`, from
  `L(k) ∣ F(n) + F(2) = 2 (x^2 + 1)`.
* Theorems 1 to 3 by `n mod 4`: `fib_factor` writes `F(n) + 1` and `F(n) - 1` as `F(a) L(b)`
  with `gcd(F(a), L(b))` equal to `1` or `3`, and Cohn's results fix one factor.
-/

namespace TuringTask

lemma lucZ_dvd_of_dvd_three_mul (k : ℕ) (hk : k % 4 = 0) (hk3 : k % 3 ≠ 0) (y : ℤ)
    (h : lucZ k ∣ 3 * y) : lucZ k ∣ y := by
  have hk0 : 1 ≤ k := by omega
  rw [lucZ_eq_lucNat k hk0] at h ⊢
  have hcop : Nat.Coprime (lucNat k) 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    have := lucNat_mod_three_ne_zero k hk
    omega
  have hc : IsCoprime ((lucNat k : ℕ) : ℤ) ((3 : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  exact hc.dvd_of_dvd_mul_left (by simpa [mul_comm] using h)

/-- `L(n) = 3 y^2` only for `n = 2`. -/
lemma lnat_three_sq {n y : ℕ} (h : lnat n = 3 * y ^ 2) : n = 2 := by
  have h4 := three_dvd_lnat ⟨y ^ 2, h⟩
  have hn1 : 1 ≤ n := by omega
  by_contra hne
  have hx : (lucNat n : ℤ) = 3 * (y : ℤ) ^ 2 := by
    rw [← lnat_eq_lucNat hn1]; exact_mod_cast h
  rcases (by omega : n % 8 = 2 ∨ n % 8 = 6) with h8 | h8
  · obtain ⟨k, t, hN, hk, hk3, ht, hk4⟩ := split_of_mod_four (n - 2) (by omega) (by omega)
    have hn' : n = 2 * k * t + 2 := by rw [← hN]; omega
    have hd := lucZ_dvd_lucNat n hn1 2 k t hk ht (by rw [hn']; push_cast; ring)
    rw [hx, show lucZ 2 = 3 by decide, show 3 * (y : ℤ) ^ 2 + 3 = 3 * ((y : ℤ) ^ 2 + 1) by ring]
      at hd
    exact lucZ_not_dvd_sq_add_one k hk hk3 y
      (lucZ_dvd_of_dvd_three_mul k (hk4 (by omega)) hk3 _ hd)
  · obtain ⟨k, t, hN, hk, hk3, ht, hk4⟩ := split_of_mod_four (n + 2) (by omega) (by omega)
    have hn' : (n : ℤ) = -2 + 2 * k * t := by
      have : ((n + 2 : ℕ) : ℤ) = ((2 * k * t : ℕ) : ℤ) := by rw [hN]
      push_cast at this
      linarith
    have hd := lucZ_dvd_lucNat n hn1 (-2) k t hk ht hn'
    rw [hx, show lucZ (-2) = 3 by decide,
      show 3 * (y : ℤ) ^ 2 + 3 = 3 * ((y : ℤ) ^ 2 + 1) by ring] at hd
    exact lucZ_not_dvd_sq_add_one k hk hk3 y
      (lucZ_dvd_of_dvd_three_mul k (hk4 (by omega)) hk3 _ hd)

/-- `F(n) = 2 x^2 + 1` with `n = 2 (mod 4)` forces `n = 2`. -/
lemma fib_two_mod_four {n x : ℕ} (h4 : n % 4 = 2) (h : Nat.fib n = 2 * x ^ 2 + 1) : n = 2 := by
  by_contra hne
  obtain ⟨k, t, hN, hk, hk3, ht, -⟩ := split_of_mod_four (n - 2) (by omega) (by omega)
  have hd := lucZ_dvd_fib_nat n 2 k t hk ht
    (by rw [show n = 2 * k * t + 2 by omega]; push_cast; ring)
  have hx : (Nat.fib n : ℤ) = 2 * (x : ℤ) ^ 2 + 1 := by exact_mod_cast h
  rw [hx, show Int.fib 2 = 1 by decide,
    show 2 * (x : ℤ) ^ 2 + 1 + 1 = 2 * ((x : ℤ) ^ 2 + 1) by ring] at hd
  exact lucZ_not_dvd_sq_add_one k hk hk3 x (lucZ_dvd_of_dvd_two_mul k hk hk3 _ hd)

/-- `n = 4 k + r` with `r < 4`. -/
lemma four_cases (n : ℕ) : ∃ k, n = 4 * k ∨ n = 4 * k + 1 ∨ n = 4 * k + 2 ∨ n = 4 * k + 3 :=
  ⟨n / 4, by omega⟩

lemma gcd_one_or_three {a b : ℕ} (h : Nat.gcd a b ∣ 3) : Nat.gcd a b = 1 ∨ Nat.gcd a b = 3 :=
  (Nat.dvd_prime Nat.prime_three).mp h

/-- Theorem 1: `F(n) + 1 = x^2` forces `n` in `{0, 4, 6}`. -/
theorem fib_add_one_sq {n x : ℕ} (h : Nat.fib n + 1 = x ^ 2) : n = 0 ∨ n = 4 ∨ n = 6 := by
  obtain ⟨k, rfl | rfl | rfl | rfl⟩ := four_cases n
  · rcases k with _ | k
    · left; rfl
    obtain ⟨-, -, P3, -⟩ := fib_factor k
    rw [show 4 * (k + 1) = 4 * k + 4 by ring, P3] at h
    have hg := gcd_fib_lnat_two (2 * k + 1)
    rw [show 2 * k + 1 + 2 = 2 * k + 3 by ring] at hg
    rcases gcd_one_or_three hg with hg | hg
    · obtain ⟨d, hd⟩ := sq_left hg h
      have := fib_eq_sq_cases _ d hd
      omega
    · have := three_dvd_lnat (hg ▸ Nat.gcd_dvd_right _ _)
      omega
  · obtain ⟨P1, -⟩ := fib_factor k
    rw [P1] at h
    obtain ⟨d, hd⟩ := sq_of_coprime_mul (cop_fib_succ_lnat (2 * k)) h
    have := lnat_sq hd
    omega
  · obtain ⟨-, -, -, P4, -⟩ := fib_factor k
    rw [P4] at h
    have hg := gcd_fib_two_lnat (2 * k)
    rcases gcd_one_or_three hg with hg | hg
    · obtain ⟨d, hd⟩ := sq_of_coprime_mul hg h
      have := lnat_sq hd
      omega
    · obtain ⟨v, hv⟩ := gcd_three_sq hg h
      have := lnat_three_sq hv
      omega
  · obtain ⟨-, P2, -⟩ := fib_factor k
    rw [P2] at h
    have hc := cop_fib_lnat_succ (2 * k + 1)
    rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring] at hc
    obtain ⟨d, hd⟩ := sq_of_coprime_mul hc h
    have := lnat_sq hd
    omega

/-- Theorem 2: `F(n) = x^2 + 1` forces `n` in `{1, 2, 3, 5}`. -/
theorem fib_sq_add_one {n x : ℕ} (h : Nat.fib n = x ^ 2 + 1) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 5 := by
  obtain ⟨k, rfl | rfl | rfl | rfl⟩ := four_cases n
  · rcases k with _ | k
    · simp at h
    obtain ⟨-, -, -, -, -, -, M3, -⟩ := fib_factor k
    rw [show 4 * (k + 1) = 4 * k + 4 by ring, M3] at h
    have h' : Nat.fib (2 * k + 3) * lnat (2 * k + 1) = x ^ 2 := by omega
    have hg := gcd_fib_two_lnat (2 * k + 1)
    rw [show 2 * k + 1 + 2 = 2 * k + 3 by ring] at hg
    rcases gcd_one_or_three hg with hg | hg
    · obtain ⟨d, hd⟩ := sq_left hg h'
      have := fib_eq_sq_cases _ d hd
      omega
    · have := three_dvd_lnat (hg ▸ Nat.gcd_dvd_right _ _)
      omega
  · obtain ⟨-, -, -, -, M1, -⟩ := fib_factor k
    rw [M1] at h
    have h' : Nat.fib (2 * k) * lnat (2 * k + 1) = x ^ 2 := by omega
    obtain ⟨d, hd⟩ := sq_of_coprime_mul (cop_fib_lnat_succ (2 * k)) h'
    have := lnat_sq hd
    omega
  · obtain ⟨-, -, -, -, -, -, -, M4⟩ := fib_factor k
    rw [M4] at h
    have h' : Nat.fib (2 * k) * lnat (2 * k + 2) = x ^ 2 := by omega
    have hg := gcd_fib_lnat_two (2 * k)
    rcases gcd_one_or_three hg with hg | hg
    · obtain ⟨d, hd⟩ := sq_of_coprime_mul hg h'
      have := lnat_sq hd
      omega
    · obtain ⟨v, hv⟩ := gcd_three_sq hg h'
      have := lnat_three_sq hv
      omega
  · obtain ⟨-, -, -, -, -, M2, -⟩ := fib_factor k
    rw [M2] at h
    have h' : Nat.fib (2 * k + 2) * lnat (2 * k + 1) = x ^ 2 := by omega
    have hc := cop_fib_succ_lnat (2 * k + 1)
    rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring] at hc
    obtain ⟨d, hd⟩ := sq_of_coprime_mul hc h'
    obtain ⟨e, he⟩ := sq_left hc h'
    have h1 := lnat_sq hd
    have h2 := fib_eq_sq_cases _ e he
    omega

/-- A coprime product `A * L = 2 x^2` with `L` odd-indexed: `L` is a square and `A = 2 a`. -/
lemma split_two {A m x : ℕ} (hc : Nat.Coprime A (lnat (2 * m + 1)))
    (h : A * lnat (2 * m + 1) = 2 * x ^ 2) :
    (∃ A', A = 2 * A') ∧ (m = 0 ∨ m = 1) := by
  rcases prime_split Nat.prime_two h with ⟨A', hA, hA'⟩ | ⟨B', hB, hB'⟩
  · have hc' : Nat.Coprime A' (lnat (2 * m + 1)) :=
      Nat.Coprime.coprime_dvd_left ⟨2, by rw [hA]; ring⟩ hc
    obtain ⟨d, hd⟩ := sq_of_coprime_mul hc' hA'
    have := lnat_sq hd
    exact ⟨⟨A', hA⟩, by omega⟩
  · have hc' : Nat.Coprime A B' := Nat.Coprime.coprime_dvd_right ⟨2, by rw [hB]; ring⟩ hc
    obtain ⟨d, hd⟩ := sq_of_coprime_mul hc' hB'
    have := lnat_two_sq (x := d) (by rw [hB, hd])
    omega

/-- Theorem 3: `F(n) = 2 x^2 + 1` forces `n` in `{1, 2, 4}`. -/
theorem fib_two_sq_add_one {n x : ℕ} (h : Nat.fib n = 2 * x ^ 2 + 1) : n = 1 ∨ n = 2 ∨ n = 4 := by
  obtain ⟨f2, f4, f5⟩ : Nat.fib 2 = 1 ∧ Nat.fib 4 = 3 ∧ Nat.fib 5 = 5 := by decide
  obtain ⟨k, rfl | rfl | rfl | rfl⟩ := four_cases n
  · rcases k with _ | k
    · simp at h
    obtain ⟨-, -, -, -, -, -, M3, -⟩ := fib_factor k
    rw [show 4 * (k + 1) = 4 * k + 4 by ring, M3] at h
    have h' : Nat.fib (2 * k + 3) * lnat (2 * k + 1) = 2 * x ^ 2 := by omega
    have hg := gcd_fib_two_lnat (2 * k + 1)
    rw [show 2 * k + 1 + 2 = 2 * k + 3 by ring] at hg
    rcases gcd_one_or_three hg with hg | hg
    · obtain ⟨⟨A', hA⟩, hk⟩ := split_two hg h'
      rcases hk with rfl | rfl
      · right; right; rfl
      · rw [show 2 * 1 + 3 = 5 by rfl, f5] at hA
        omega
    · have := three_dvd_lnat (hg ▸ Nat.gcd_dvd_right _ _)
      omega
  · obtain ⟨-, -, -, -, M1, -⟩ := fib_factor k
    rw [M1] at h
    have h' : Nat.fib (2 * k) * lnat (2 * k + 1) = 2 * x ^ 2 := by omega
    obtain ⟨⟨A', hA⟩, hk⟩ := split_two (cop_fib_lnat_succ (2 * k)) h'
    rcases hk with rfl | rfl
    · left; rfl
    · rw [show 2 * 1 = 2 by rfl, f2] at hA
      omega
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · right; left; rfl
    · have := fib_two_mod_four (by omega) h
      omega
  · obtain ⟨-, -, -, -, -, M2, -⟩ := fib_factor k
    rw [M2] at h
    have h' : Nat.fib (2 * k + 2) * lnat (2 * k + 1) = 2 * x ^ 2 := by omega
    have hc := cop_fib_succ_lnat (2 * k + 1)
    rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring] at hc
    obtain ⟨⟨A', hA⟩, hk⟩ := split_two hc h'
    rcases hk with rfl | rfl
    · rw [show 2 * 0 + 2 = 2 by rfl, f2] at hA
      omega
    · rw [show 2 * 1 + 2 = 4 by rfl, f4] at hA
      omega

end TuringTask
