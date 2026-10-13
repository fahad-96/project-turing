import Mathlib
import TuringTask.Equations

/-!
# Lucas numbers `lnat n = 2 F(n + 1) - F(n)`, factorizations and coprimality

* `lnat_add`: `F(n) + lnat n = 2 F(n + 1)`, the form of the prompt; `lnat n = lucNat n` for
  `n >= 1`, so Cohn's results of `Equations.lean` apply (`lnat_sq`, `lnat_two_sq`).
* `quad`: with `x = F(2k)`, `y = F(2k+1)` the numbers `F(2k + i)` and `F(4k + i)` are
  polynomials in `x, y`, and Cassini gives `y^2 - x y - x^2 = 1` (`cassini`). Every
  factorization below is this relation times a constant, for example
  `F(4k + 1) + 1 = F(2k + 1) L(2k)` and `L(4k + 1) - 1 = 5 F(2k + 1) F(2k)`.
* Coprimality: `F(m)` and `L(m + 1)`, `F(m + 1)` and `L(m)`, `L(m)` and `L(m + 1)` are coprime;
  `gcd(F(m), L(m + 2))` and `gcd(F(m + 2), L(m))` divide `3`, and `3 ∣ L(m)` forces
  `m = 2 (mod 4)`.
* Splitting: a product `A B = p M` of coprime numbers, and squares with a prime factor.
-/

namespace TuringTask

/-- The Lucas number `L(n) = 2 F(n + 1) - F(n)`. -/
def lnat (n : ℕ) : ℕ := 2 * Nat.fib (n + 1) - Nat.fib n

lemma fib_le_two_mul (n : ℕ) : Nat.fib n ≤ 2 * Nat.fib (n + 1) := by
  have := Nat.fib_le_fib_succ (n := n)
  omega

lemma lnat_add (n : ℕ) : Nat.fib n + lnat n = 2 * Nat.fib (n + 1) := by
  have := fib_le_two_mul n
  unfold lnat
  omega

lemma lnat_cast (n : ℕ) : (lnat n : ℤ) = 2 * Nat.fib (n + 1) - Nat.fib n := by
  have := lnat_add n
  have h : ((Nat.fib n + lnat n : ℕ) : ℤ) = ((2 * Nat.fib (n + 1) : ℕ) : ℤ) := by rw [this]
  push_cast at h
  linarith

lemma lnat_eq_lucNat {n : ℕ} (hn : 1 ≤ n) : lnat n = lucNat n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := lnat_add (m + 1)
  have h2 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
  unfold lucNat
  rw [show m + 1 - 1 = m by omega, show m + 1 + 1 = m + 2 by ring]
  rw [show m + 1 + 1 = m + 2 by ring] at h1
  omega

lemma lnat_succ_succ (m : ℕ) : lnat (m + 2) = lnat (m + 1) + lnat m := by
  have h1 := lnat_add m
  have h2 := lnat_add (m + 1)
  have h3 := lnat_add (m + 2)
  have e1 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
  have e2 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  rw [show m + 1 + 1 = m + 2 by ring] at h2
  rw [show m + 2 + 1 = m + 3 by ring] at h3
  omega

lemma lnat_pos (n : ℕ) : 1 ≤ lnat n := by
  have := lnat_add n
  have h1 := Nat.fib_le_fib_succ (n := n)
  have h2 : 0 < Nat.fib (n + 1) := Nat.fib_pos.mpr (by omega)
  omega

lemma lnat_ge_two {n : ℕ} (hn : n ≠ 1) : 2 ≤ lnat n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    · decide
    · omega
  · have := lnat_add n
    have h1 := Nat.fib_le_fib_succ (n := n)
    have h2 : 2 ≤ Nat.fib (n + 1) :=
      le_trans (by decide : 2 ≤ Nat.fib 3) (Nat.fib_mono (show 3 ≤ n + 1 by omega))
    omega

lemma lnat_sq {n x : ℕ} (h : lnat n = x ^ 2) : n = 1 ∨ n = 3 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h2 : x ^ 2 = 2 := by rw [← h]; decide
    have : x ≤ 1 := by nlinarith
    interval_cases x <;> omega
  · rw [lnat_eq_lucNat hn] at h
    exact lucNat_eq_sq_cases n x hn h

lemma lnat_two_sq {n x : ℕ} (h : lnat n = 2 * x ^ 2) : n = 0 ∨ n = 6 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · left; rfl
  · rw [lnat_eq_lucNat hn] at h
    exact Or.inr (lucNat_eq_two_mul_sq_cases n x hn h)

/-! ### Cassini and the factorizations -/

lemma cassini (j : ℕ) :
    (Nat.fib (j + 1) : ℤ) ^ 2 - Nat.fib (j + 1) * Nat.fib j - (Nat.fib j : ℤ) ^ 2 = (-1) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : (Nat.fib (j + 2) : ℤ) = Nat.fib j + Nat.fib (j + 1) := by
      exact_mod_cast Nat.fib_add_two
    rw [show j + 1 + 1 = j + 2 by ring, e, pow_succ]
    linear_combination -ih

/-- The numbers `F(2k + i)` and `F(4k + i)` in terms of `x = F(2k)` and `y = F(2k + 1)`. -/
lemma quad (k : ℕ) :
    let x : ℤ := Nat.fib (2 * k)
    let y : ℤ := Nat.fib (2 * k + 1)
    y ^ 2 - x * y - x ^ 2 = 1 ∧
    (Nat.fib (2 * k + 2) : ℤ) = x + y ∧ (Nat.fib (2 * k + 3) : ℤ) = x + 2 * y ∧
    (Nat.fib (2 * k + 4) : ℤ) = 2 * x + 3 * y ∧ (Nat.fib (4 * k) : ℤ) = 2 * x * y - x ^ 2 ∧
    (Nat.fib (4 * k + 1) : ℤ) = x ^ 2 + y ^ 2 ∧ (Nat.fib (4 * k + 2) : ℤ) = 2 * x * y + y ^ 2 ∧
    (Nat.fib (4 * k + 3) : ℤ) = x ^ 2 + 2 * x * y + 2 * y ^ 2 ∧
    (Nat.fib (4 * k + 4) : ℤ) = x ^ 2 + 4 * x * y + 3 * y ^ 2 := by
  intro x y
  have hc := cassini (2 * k)
  rw [pow_mul] at hc
  norm_num at hc
  have f2 : (Nat.fib (2 * k + 2) : ℤ) = x + y := by
    have : Nat.fib (2 * k + 2) = Nat.fib (2 * k) + Nat.fib (2 * k + 1) := Nat.fib_add_two
    rw [this]; push_cast; ring
  have f3 : (Nat.fib (2 * k + 3) : ℤ) = x + 2 * y := by
    have : Nat.fib (2 * k + 3) = Nat.fib (2 * k + 1) + Nat.fib (2 * k + 2) := Nat.fib_add_two
    rw [this]; push_cast; rw [f2]; ring
  have f4 : (Nat.fib (2 * k + 4) : ℤ) = 2 * x + 3 * y := by
    have : Nat.fib (2 * k + 4) = Nat.fib (2 * k + 2) + Nat.fib (2 * k + 3) := Nat.fib_add_two
    rw [this]; push_cast; rw [f2, f3]; ring
  have g1 : (Nat.fib (4 * k + 1) : ℤ) = x ^ 2 + y ^ 2 := by
    have := Nat.fib_add (2 * k) (2 * k)
    rw [show 2 * k + 2 * k + 1 = 4 * k + 1 by ring] at this
    rw [this]; push_cast; ring
  have g2 : (Nat.fib (4 * k + 2) : ℤ) = 2 * x * y + y ^ 2 := by
    have := Nat.fib_add (2 * k) (2 * k + 1)
    rw [show 2 * k + (2 * k + 1) + 1 = 4 * k + 2 by ring, show 2 * k + 1 + 1 = 2 * k + 2 by ring]
      at this
    rw [this]; push_cast; rw [f2]; ring
  have g0 : (Nat.fib (4 * k) : ℤ) = 2 * x * y - x ^ 2 := by
    have : Nat.fib (4 * k + 2) = Nat.fib (4 * k) + Nat.fib (4 * k + 1) := Nat.fib_add_two
    have h : (Nat.fib (4 * k + 2) : ℤ) = Nat.fib (4 * k) + Nat.fib (4 * k + 1) := by
      exact_mod_cast this
    linear_combination h.symm + g2 - g1
  have g3 : (Nat.fib (4 * k + 3) : ℤ) = x ^ 2 + 2 * x * y + 2 * y ^ 2 := by
    have : Nat.fib (4 * k + 3) = Nat.fib (4 * k + 1) + Nat.fib (4 * k + 2) := Nat.fib_add_two
    rw [this]; push_cast; rw [g1, g2]; ring
  have g4 : (Nat.fib (4 * k + 4) : ℤ) = x ^ 2 + 4 * x * y + 3 * y ^ 2 := by
    have : Nat.fib (4 * k + 4) = Nat.fib (4 * k + 2) + Nat.fib (4 * k + 3) := Nat.fib_add_two
    rw [this]; push_cast; rw [g2, g3]; ring
  refine ⟨by linear_combination hc, f2, f3, f4, g0, g1, g2, g3, g4⟩

/-- The eight factorizations of `F(n) + 1` and `F(n) - 1` (with `F(n) - 1` written as a sum). -/
lemma fib_factor (k : ℕ) :
    Nat.fib (4 * k + 1) + 1 = Nat.fib (2 * k + 1) * lnat (2 * k) ∧
    Nat.fib (4 * k + 3) + 1 = Nat.fib (2 * k + 1) * lnat (2 * k + 2) ∧
    Nat.fib (4 * k + 4) + 1 = Nat.fib (2 * k + 1) * lnat (2 * k + 3) ∧
    Nat.fib (4 * k + 2) + 1 = Nat.fib (2 * k + 2) * lnat (2 * k) ∧
    Nat.fib (4 * k + 1) = Nat.fib (2 * k) * lnat (2 * k + 1) + 1 ∧
    Nat.fib (4 * k + 3) = Nat.fib (2 * k + 2) * lnat (2 * k + 1) + 1 ∧
    Nat.fib (4 * k + 4) = Nat.fib (2 * k + 3) * lnat (2 * k + 1) + 1 ∧
    Nat.fib (4 * k + 2) = Nat.fib (2 * k) * lnat (2 * k + 2) + 1 := by
  obtain ⟨hc, f2, f3, f4, -, g1, g2, g3, g4⟩ := quad k
  have l0 := lnat_cast (2 * k)
  have l1 := lnat_cast (2 * k + 1)
  have l2 := lnat_cast (2 * k + 2)
  have l3 := lnat_cast (2 * k + 3)
  rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring] at l1
  rw [show 2 * k + 2 + 1 = 2 * k + 3 by ring] at l2
  rw [show 2 * k + 3 + 1 = 2 * k + 4 by ring] at l3
  rw [f2] at l1 l2; rw [f3] at l2 l3; rw [f4] at l3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> zify <;>
    simp only [g1, g2, g3, g4, f2, f3, l0, l1, l2, l3]
  · linear_combination -hc
  · linear_combination -hc
  · linear_combination -hc
  · linear_combination -hc
  · linear_combination hc
  · linear_combination hc
  · linear_combination hc
  · linear_combination hc

/-- The factorizations of `L(n) - 1` and `L(n) + 1` for odd `n`, and `L(2a)` for even `n`. -/
lemma lucas_factor (k : ℕ) :
    lnat (4 * k + 1) = 5 * Nat.fib (2 * k + 1) * Nat.fib (2 * k) + 1 ∧
    lnat (4 * k + 3) = lnat (2 * k + 2) * lnat (2 * k + 1) + 1 ∧
    lnat (4 * k + 1) + 1 = lnat (2 * k + 1) * lnat (2 * k) ∧
    lnat (4 * k + 3) + 1 = 5 * Nat.fib (2 * k + 2) * Nat.fib (2 * k + 1) ∧
    lnat (4 * k) + 2 = lnat (2 * k) ^ 2 ∧
    lnat (4 * k + 2) = lnat (2 * k + 1) ^ 2 + 2 := by
  obtain ⟨hc, f2, f3, -, g0, g1, g2, g3, g4⟩ := quad k
  have l0 := lnat_cast (2 * k)
  have l1 := lnat_cast (2 * k + 1)
  have l2 := lnat_cast (2 * k + 2)
  have m0 := lnat_cast (4 * k)
  have m1 := lnat_cast (4 * k + 1)
  have m2 := lnat_cast (4 * k + 2)
  have m3 := lnat_cast (4 * k + 3)
  rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring] at l1
  rw [show 2 * k + 2 + 1 = 2 * k + 3 by ring] at l2
  rw [show 4 * k + 1 + 1 = 4 * k + 2 by ring] at m1
  rw [show 4 * k + 2 + 1 = 4 * k + 3 by ring] at m2
  rw [show 4 * k + 3 + 1 = 4 * k + 4 by ring] at m3
  rw [f2] at l1 l2; rw [f3] at l2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> zify <;>
    simp only [g0, g1, g2, g3, g4, f2, l0, l1, l2, m0, m1, m2, m3]
  · linear_combination hc
  · linear_combination hc
  · linear_combination -hc
  · linear_combination -hc
  · linear_combination -2 * hc
  · linear_combination 2 * hc

/-! ### Coprimality -/

lemma coprime_of_dvd' {a b c : ℕ} (hc : Nat.Coprime c a) (h : ∀ g, g ∣ a → g ∣ b → g ∣ c) :
    Nat.Coprime a b := by
  have h1 := h _ (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)
  exact Nat.eq_one_of_dvd_one (by
    have := Nat.dvd_gcd h1 (Nat.gcd_dvd_left a b)
    rwa [hc] at this)

lemma cop_fib_lnat_succ (m : ℕ) : Nat.Coprime (Nat.fib m) (lnat (m + 1)) := by
  have h := lnat_add (m + 1)
  have e : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
  rw [show m + 1 + 1 = m + 2 by ring] at h
  have : lnat (m + 1) = Nat.fib (m + 1) + Nat.fib m * 2 := by omega
  rw [this, Nat.coprime_add_mul_left_right]
  exact Nat.fib_coprime_fib_succ m

lemma cop_fib_succ_lnat (m : ℕ) : Nat.Coprime (Nat.fib (m + 1)) (lnat m) := by
  refine coprime_of_dvd' (Nat.fib_coprime_fib_succ m) fun g h1 h2 => ?_
  have h := lnat_add m
  have : g ∣ Nat.fib m + lnat m := by rw [h]; exact Dvd.dvd.mul_left h1 2
  exact (Nat.dvd_add_left h2).mp this

lemma cop_lnat_succ (m : ℕ) : Nat.Coprime (lnat m) (lnat (m + 1)) := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [show m + 1 + 1 = m + 2 by ring, lnat_succ_succ, Nat.coprime_self_add_right]
    exact ih.symm

lemma gcd_fib_lnat_two (m : ℕ) : Nat.gcd (Nat.fib m) (lnat (m + 2)) ∣ 3 := by
  set g := Nat.gcd (Nat.fib m) (lnat (m + 2))
  have h1 : g ∣ Nat.fib m := Nat.gcd_dvd_left _ _
  have h2 : g ∣ lnat (m + 2) := Nat.gcd_dvd_right _ _
  have h := lnat_add (m + 2)
  have e1 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
  have e2 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  rw [show m + 2 + 1 = m + 3 by ring] at h
  have hl : lnat (m + 2) = 3 * Nat.fib (m + 1) + Nat.fib m := by omega
  rw [hl] at h2
  have h3 : g ∣ 3 * Nat.fib (m + 1) := (Nat.dvd_add_left h1).mp h2
  have hcop : Nat.Coprime g (Nat.fib (m + 1)) :=
    Nat.Coprime.coprime_dvd_left h1 (Nat.fib_coprime_fib_succ m)
  exact hcop.dvd_of_dvd_mul_right h3

lemma gcd_fib_two_lnat (m : ℕ) : Nat.gcd (Nat.fib (m + 2)) (lnat m) ∣ 3 := by
  set g := Nat.gcd (Nat.fib (m + 2)) (lnat m)
  have h1 : g ∣ Nat.fib (m + 2) := Nat.gcd_dvd_left _ _
  have h2 : g ∣ lnat m := Nat.gcd_dvd_right _ _
  have h := lnat_add m
  have e1 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
  have h3 : g ∣ 3 * Nat.fib (m + 1) := by
    have : lnat m + Nat.fib (m + 2) = 3 * Nat.fib (m + 1) := by omega
    rw [← this]; exact dvd_add h2 h1
  have hcop : Nat.Coprime g (Nat.fib (m + 1)) := by
    have := Nat.fib_coprime_fib_succ (m + 1)
    exact Nat.Coprime.coprime_dvd_left h1 this.symm
  exact hcop.dvd_of_dvd_mul_right h3

lemma three_dvd_lnat {m : ℕ} (h : 3 ∣ lnat m) : m % 4 = 2 := by
  have h0 := fib_mod_eq_of_period 3 8 (by norm_num) (by decide) (by decide) m
  have h1 := fib_mod_eq_of_period 3 8 (by norm_num) (by decide) (by decide) (m + 1)
  have hl := lnat_add m
  have hr : (m + 1) % 8 = (m % 8 + 1) % 8 := by omega
  rw [hr] at h1
  have key : (Nat.fib m + lnat m) % 3 = (2 * Nat.fib (m + 1)) % 3 := by rw [hl]
  have hm : m % 8 < 8 := Nat.mod_lt _ (by norm_num)
  obtain ⟨c, hc⟩ := h
  rw [hc] at key
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ : Nat.fib 0 = 0 ∧ Nat.fib 1 = 1 ∧ Nat.fib 2 = 1 ∧
      Nat.fib 3 = 2 ∧ Nat.fib 4 = 3 ∧ Nat.fib 5 = 5 ∧ Nat.fib 6 = 8 ∧ Nat.fib 7 = 13 := by decide
  generalize hr8 : m % 8 = r at h0 h1 hm
  interval_cases r <;> simp only [f0, f1, f2, f3, f4, f5, f6, f7, Nat.reduceAdd, Nat.reduceMod]
    at h0 h1 <;> omega

/-! ### Splitting products -/

lemma prime_split {p A B M : ℕ} (hp : p.Prime) (h : A * B = p * M) :
    (∃ A', A = p * A' ∧ A' * B = M) ∨ (∃ B', B = p * B' ∧ A * B' = M) := by
  have hd : p ∣ A * B := ⟨M, h⟩
  rcases (Nat.Prime.dvd_mul hp).mp hd with ⟨A', rfl⟩ | ⟨B', rfl⟩
  · left
    refine ⟨A', rfl, ?_⟩
    have : p * (A' * B) = p * M := by rw [← h]; ring
    exact Nat.eq_of_mul_eq_mul_left hp.pos this
  · right
    refine ⟨B', rfl, ?_⟩
    have : p * (A * B') = p * M := by rw [← h]; ring
    exact Nat.eq_of_mul_eq_mul_left hp.pos this

lemma sq_left {a b c : ℕ} (hab : Nat.Coprime a b) (h : a * b = c ^ 2) : ∃ d, a = d ^ 2 :=
  sq_of_coprime_mul hab.symm (by rw [mul_comm]; exact h)

lemma sq_prime {p x M : ℕ} (hp : p.Prime) (h : x ^ 2 = p * M) : ∃ z, M = p * z ^ 2 := by
  have : p ∣ x := hp.dvd_of_dvd_pow ⟨M, h⟩
  obtain ⟨z, rfl⟩ := this
  refine ⟨z, ?_⟩
  have : p * (p * z ^ 2) = p * M := by rw [← h]; ring
  exact (Nat.eq_of_mul_eq_mul_left hp.pos this).symm

lemma gcd_three_sq {A B x : ℕ} (hg : Nat.gcd A B = 3) (h : A * B = x ^ 2) :
    ∃ v, B = 3 * v ^ 2 := by
  obtain ⟨A', hA⟩ : 3 ∣ A := hg ▸ Nat.gcd_dvd_left A B
  obtain ⟨B', hB⟩ : 3 ∣ B := hg ▸ Nat.gcd_dvd_right A B
  have hcop : Nat.Coprime A' B' := by
    have := Nat.coprime_div_gcd_div_gcd (m := A) (n := B) (by rw [hg]; norm_num)
    rwa [hg, hA, hB, Nat.mul_div_cancel_left _ (by norm_num),
      Nat.mul_div_cancel_left _ (by norm_num)] at this
  obtain ⟨z, hz⟩ := sq_prime Nat.prime_three (M := 3 * (A' * B')) (x := x)
    (by rw [← h, hA, hB]; ring)
  have : A' * B' = z ^ 2 := by omega
  obtain ⟨v, hv⟩ := sq_of_coprime_mul hcop this
  exact ⟨v, by rw [hB, hv]⟩

end TuringTask
