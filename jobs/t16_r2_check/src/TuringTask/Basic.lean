import Mathlib
import TuringTask.Lemmas

namespace TuringTask

theorem lucas_eq_sq (n x : Nat) (hn : 1 ≤ n) (h : Nat.fib (n - 1) + Nat.fib (n + 1) = x ^ 2) :
    n = 1 ∨ n = 3 := by
  rw [fib_pred_add_fib_succ n hn] at h
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h1, h3⟩ := hcon
  rcases Nat.even_or_odd n with hev | hodd
  · have hm := luc_even_mod_four n (Nat.even_iff.mp hev)
    have hx : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
      have hc4 : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
      rcases hc4 with hc | hc | hc | hc <;> rw [Nat.pow_mod, hc] <;> norm_num
    omega
  · have hodd' : n % 2 = 1 := Nat.odd_iff.mp hodd
    rcases (by omega : n % 4 = 1 ∨ n % 4 = 3) with hc | hc
    · obtain ⟨j, t, hj, ht, hdt⟩ := split_two_adic (d := n - 1) (by omega) (by omega)
      have hn' : n = 1 + 2 * 2 ^ j * t := by omega
      have hN4 : luc (2 ^ j) % 4 = 3 := luc_two_pow_mod_four j hj
      have hmod : ((luc n : ℤ)) ≡ ((x : ℤ)) ^ 2 [ZMOD (luc (2 ^ j) : ℤ)] := by
        have he : (luc n : ℤ) = ((x : ℤ)) ^ 2 := by exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) h
        rw [he]
      have hk := luc_toolA_jacobi hj ht hn' hmod
      rw [luc_one] at hk
      norm_num at hk
      rw [jacobi_neg_one_of_mod_four hN4] at hk
      norm_num at hk
    · have hn3 : 3 < n := by omega
      obtain ⟨j, t, hj, ht, hdt⟩ := split_two_adic (d := n - 3) (by omega) (by omega)
      have hn' : n = 3 + 2 * 2 ^ j * t := by omega
      have hN4 : luc (2 ^ j) % 4 = 3 := luc_two_pow_mod_four j hj
      have hmod : ((luc n : ℤ)) ≡ ((x : ℤ)) ^ 2 [ZMOD (luc (2 ^ j) : ℤ)] := by
        have he : (luc n : ℤ) = ((x : ℤ)) ^ 2 := by exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) h
        rw [he]
      have hk := luc_toolA_jacobi hj ht hn' hmod
      have hl3 : (luc 3 : ℤ) = 4 := by norm_num [luc]
      rw [hl3] at hk
      have hcop2 : Int.gcd 2 (luc (2 ^ j)) = 1 := int_gcd_two_of_odd (by omega)
      have hfac : (-(4 : ℤ)) = (-1) * 2 ^ 2 := by norm_num
      rw [hfac, jacobiSym.mul_left, jacobiSym.sq_one' hcop2,
        jacobi_neg_one_of_mod_four hN4] at hk
      norm_num at hk

theorem lucas_eq_two_mul_sq (n x : Nat) (hn : 1 ≤ n)
    (h : Nat.fib (n - 1) + Nat.fib (n + 1) = 2 * x ^ 2) :
    n = 6 := by
  rw [fib_pred_add_fib_succ n hn] at h
  -- base reductions: `n % 6 = 0` and `n % 16 ∈ {0, 6, 10}`
  have hb6 : n % 6 = 0 := luc_two_sq_mod6 h
  have hb16 := luc_two_sq_mod16 h
  have heven : n % 2 = 0 := by omega
  have hb16' : n % 16 = 0 ∨ n % 16 = 6 ∨ n % 16 = 10 := by omega
  -- hence `n % 48 ∈ {0, 6, 42}`
  have h48 : n % 48 = 0 ∨ n % 48 = 6 ∨ n % 48 = 42 := by omega
  by_contra hne
  have hN3 : ∀ j, 3 ≤ j → luc (2 ^ j) % 3 = 1 ∨ luc (2 ^ j) % 3 = 2 :=
    fun j hj => luc_two_pow_mod_three j (by omega)
  rcases h48 with hc | hc | hc
  · -- `48 ∣ n`, use Tool A with `c = 0`
    obtain ⟨j, t, hj, ht, hdt⟩ := split_two_adic16 (d := n) (by omega) (by omega)
    refine luc_two_sq_killA hj ht (c := 0) (by omega) h ?_
    rw [luc_zero]
    have : (-((2 : ℕ) : ℤ)) = -2 := by norm_num
    rw [this]
    exact jacobi_neg_two (luc_two_pow_mod_eight j (by omega))
  · -- `n ≡ 6 [MOD 48]`, use Tool A with `c = 6`
    have hn6 : 6 < n := by omega
    obtain ⟨j, t, hj, ht, hdt⟩ := split_two_adic16 (d := n - 6) (by omega) (by omega)
    refine luc_two_sq_killA hj ht (c := 6) (by omega) h ?_
    have hl6 : (luc 6 : ℤ) = 18 := by norm_num [luc]
    rw [hl6]
    have : (-(18 : ℤ)) = -18 := by norm_num
    rw [this]
    exact jacobi_neg_eighteen (luc_two_pow_mod_eight j (by omega)) (hN3 j hj)
  · -- `n ≡ 42 [MOD 48]`, use Tool B with `c = 6`
    obtain ⟨j, t, hj, ht, hdt⟩ := split_two_adic16 (d := n + 6) (by omega) (by omega)
    have hcj : 6 + 1 < 2 * 2 ^ j := by
      have : (8 : ℕ) ≤ 2 ^ j := by
        calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
      omega
    refine luc_two_sq_killB hj ht hcj (by omega) h ?_
    have hl6 : (luc 6 : ℤ) = 18 := by norm_num [luc]
    rw [hl6]
    have hsgn : ((-1 : ℤ)) ^ (6 + 1) * 18 = -18 := by norm_num
    rw [hsgn]
    exact jacobi_neg_eighteen (luc_two_pow_mod_eight j (by omega)) (hN3 j hj)

theorem fib_eq_sq (n x : Nat) (h : Nat.fib n = x ^ 2) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 12 := by
  rcases Nat.even_or_odd n with hev | hodd
  · -- `n = 2 * m`
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by
      obtain ⟨c, hc⟩ := hev; omega⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · left; rfl
    rw [fib_two_mul_nat] at h
    by_cases h3 : m % 3 = 0
    · -- `gcd = 2`: `fib m = 2a`, `luc m = 2b`, `4ab = x^2`, so `a`, `b` are squares,
      -- giving `luc m = 2 * q ^ 2`; theorem 4 forces `m = 6`.
      obtain ⟨a, b, ha, hb, hab⟩ := split_gcd_two h3
      rw [ha, hb] at h
      have h4 : 4 * (a * b) = x ^ 2 := by ring_nf; ring_nf at h; omega
      have hx2 : 2 ∣ x := by
        have : (2 : ℕ) ∣ x ^ 2 := ⟨2 * (a * b), by omega⟩
        exact (Nat.Prime.dvd_of_dvd_pow Nat.prime_two this)
      obtain ⟨c, rfl⟩ := hx2
      have hc : a * b = c ^ 2 := by ring_nf at h4 ⊢; omega
      obtain ⟨q, hq⟩ := nat_sq_of_coprime (c := c) hab.symm (by rw [mul_comm]; exact hc)
      have hL : Nat.fib (m - 1) + Nat.fib (m + 1) = 2 * q ^ 2 := by
        rw [fib_pred_add_fib_succ m hm0, hb, hq]
      have := lucas_eq_two_mul_sq m q hm0 hL
      subst this
      right; right; right; rfl
    · -- `gcd = 1`: both factors are squares; theorem 2 forces `m ∈ {1, 3}`.
      have hcop : Nat.Coprime (Nat.fib m) (luc m) := by
        have hg := gcd_fib_luc m
        rw [if_neg h3] at hg
        exact hg
      obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := split_coprime_sq hcop h
      have hL : Nat.fib (m - 1) + Nat.fib (m + 1) = q ^ 2 := by
        rw [fib_pred_add_fib_succ m hm0, hq]
      rcases lucas_eq_sq m q hm0 hL with rfl | rfl
      · right; right; left; rfl
      · -- `m = 3`: then `fib 6 = 8` is not a square
        exfalso
        norm_num at hp
        -- `2 = p ^ 2` is impossible
        rcases Nat.lt_or_ge p 2 with hlt | hge
        · interval_cases p <;> omega
        · have : 2 * 2 ≤ p * p := Nat.mul_le_mul hge hge
          have hp2 : p ^ 2 = p * p := by ring
          omega
  · -- `n` odd
    have := fib_sq_odd (Nat.odd_iff.mp hodd) h
    right; left; exact this

theorem fib_eq_two_mul_sq (n x : Nat) (h : Nat.fib n = 2 * x ^ 2) :
    n = 0 ∨ n = 3 ∨ n = 6 := by
  rcases Nat.even_or_odd n with hev | hodd
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by obtain ⟨c, hc⟩ := hev; omega⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · left; rfl
    rw [fib_two_mul_nat] at h
    -- `luc m` must be even, hence `3 ∣ m`
    have h3 : m % 3 = 0 := by
      by_contra hc
      -- `3 ∤ m` gives `fib m` odd, and `luc m` odd, so the product is odd
      have hfo : Nat.fib m % 2 = 1 := by
        have := (fib_even_iff m); omega
      have hlo : luc m % 2 = 1 := by
        have := (luc_even_iff m); omega
      have hprod : (Nat.fib m * luc m) % 2 = 1 := by rw [Nat.mul_mod, hfo, hlo]
      omega
    obtain ⟨a, b, ha, hb, hab⟩ := split_gcd_two h3
    rw [ha, hb] at h
    -- `4ab = 2x^2`, so `2ab = x^2`, forcing `x` even
    have h2 : 2 * (a * b) = x ^ 2 := by ring_nf at h ⊢; omega
    have hx2 : 2 ∣ x := by
      have hdvd : (2 : ℕ) ∣ x ^ 2 := ⟨a * b, h2.symm⟩
      exact Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
    obtain ⟨c, rfl⟩ := hx2
    have hc2 : a * b = 2 * c ^ 2 := by ring_nf at h2 ⊢; omega
    -- `a` and `b` are coprime with product `2 c^2`
    rcases Nat.even_or_odd a with hae | hao
    · -- `a` even: `a = 2 a'`, `b` odd, so `b` is a square and `a'` is a square
      obtain ⟨a', rfl⟩ : ∃ a', a = 2 * a' := ⟨a / 2, by obtain ⟨u, hu⟩ := hae; omega⟩
      have hab' : a' * b = c ^ 2 := by ring_nf at hc2 ⊢; omega
      obtain ⟨p, hp⟩ := nat_sq_of_coprime (c := c) (by
        have := Nat.Coprime.coprime_dvd_left (show a' ∣ 2 * a' from ⟨2, by ring⟩) hab
        exact this) hab'
      -- then `fib m = 2 * (2 a') = (2p)^2` is a perfect square
      have hsq : Nat.fib m = (2 * p) ^ 2 := by rw [ha, hp]; ring
      rcases fib_eq_sq m (2 * p) hsq with hm | hm | hm | hm
      · omega
      · omega
      · omega
      · -- `m = 12`: then `luc 12 = 322 = 2 * b` so `b = 161`, which must be a square
        exfalso
        subst hm
        have hb161 : b = 161 := by rw [luc_twelve] at hb; omega
        have hcopb : Nat.Coprime b a' :=
          (Nat.Coprime.coprime_dvd_left (show a' ∣ 2 * a' from ⟨2, by ring⟩) hab).symm
        obtain ⟨q, hq⟩ := nat_sq_of_coprime (c := c) hcopb (by rw [mul_comm]; exact hab')
        exact not_sq_161 q (by omega)
    · -- `a` odd: then `b` is even, `b = 2 b'`, and `luc m = 4 b' = (2q)^2`
      have hbe : b % 2 = 0 := by
        rcases Nat.even_or_odd b with hbe | hbo
        · obtain ⟨u, hu⟩ := hbe; omega
        · exfalso
          have h1 : a % 2 = 1 := Nat.odd_iff.mp hao
          have h2' : b % 2 = 1 := Nat.odd_iff.mp hbo
          have : (a * b) % 2 = 1 := by
            rw [Nat.mul_mod, h1, h2']
          omega
      obtain ⟨b', rfl⟩ : ∃ b', b = 2 * b' := ⟨b / 2, by omega⟩
      have hab' : a * b' = c ^ 2 := by ring_nf at hc2 ⊢; omega
      obtain ⟨q, hq⟩ := nat_sq_of_coprime (c := c) (by
        have := Nat.Coprime.coprime_dvd_right (show b' ∣ 2 * b' from ⟨2, by ring⟩) hab
        exact this.symm) (by rw [mul_comm]; exact hab')
      -- `luc m = 2 * (2 b') = (2q)^2`
      have hL : Nat.fib (m - 1) + Nat.fib (m + 1) = (2 * q) ^ 2 := by
        rw [fib_pred_add_fib_succ m hm0, hb, hq]; ring
      rcases lucas_eq_sq m (2 * q) hm0 hL with hm | hm
      · omega
      · subst hm; right; right; rfl
  · right; left; exact fib_two_sq_odd (Nat.odd_iff.mp hodd) h

theorem fib_eq_two_pow (n k : Nat) (h : Nat.fib n = 2 ^ k) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `fib n = 1`
    rw [pow_zero] at h
    rcases fib_eq_one h with rfl | rfl
    · left; rfl
    · right; left; rfl
  -- `k ≥ 1`, so `fib n` is even, hence `3 ∣ n`; in particular `n ≠ 0`
  have hfe : Nat.fib n % 2 = 0 := by
    have hdvd : (2 : ℕ) ∣ Nat.fib n := by
      rw [h, show (2 : ℕ) = 2 ^ 1 by norm_num]
      exact pow_dvd_pow 2 hk
    omega
  have h3 : n % 3 = 0 := (fib_even_iff n).mp hfe
  have hn0 : n ≠ 0 := by
    intro hc; subst hc
    rw [Nat.fib_zero] at h
    have : 0 < 2 ^ k := Nat.two_pow_pos k
    omega
  -- `n` is even or odd
  rcases Nat.even_or_odd n with hev | hodd
  · -- `n = 2 * m`; then `fib m * luc m = 2 ^ k`, so `luc m` is a power of two
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by obtain ⟨c, hc⟩ := hev; omega⟩
    rw [fib_two_mul_nat] at h
    have hldvd : luc m ∣ 2 ^ k := ⟨Nat.fib m, by rw [← h]; ring⟩
    obtain ⟨s, _, hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hldvd
    rcases luc_eq_two_pow hs with rfl | rfl | rfl
    · -- `m = 0` gives `n = 0`, excluded
      exact absurd rfl hn0
    · -- `m = 1`, `n = 2`
      right; left; rfl
    · -- `m = 3`, `n = 6`
      right; right; right; rfl
  · -- `n` odd and `3 ∣ n`.  Then `n ≥ 3`, and `fib n = 2 ^ k` with `k ≥ 1`.
    -- `4 ∤ fib n` because `6 ∤ n` (as `n` is odd), so `k = 1` and `fib n = 2`, i.e. `n = 3`.
    have hodd' : n % 2 = 1 := Nat.odd_iff.mp hodd
    have h4 : Nat.fib n % 4 = 2 := by
      have hper := fib_mod_eq (M := 4) (p := 6) (by norm_num) (by decide) (by decide) n
      have hr : n % 6 = 3 := by omega
      rw [hper, hr]
      norm_num
    have hk1 : k = 1 := by
      by_contra hc
      have hk2 : 2 ≤ k := by omega
      have : (4 : ℕ) ∣ Nat.fib n := by
        rw [h, show (4 : ℕ) = 2 ^ 2 by norm_num]
        exact pow_dvd_pow 2 hk2
      omega
    subst hk1
    norm_num at h
    -- `fib n = 2` forces `n = 3`
    right; right; left
    by_contra hne
    rcases Nat.lt_or_ge n 4 with hn | hn
    · interval_cases n <;> simp_all
    · have : Nat.fib 4 ≤ Nat.fib n := Nat.fib_mono hn
      have h4' : Nat.fib 4 = 3 := by norm_num
      omega

end TuringTask
