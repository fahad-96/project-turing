import Mathlib
import TuringTask.FibEq

/-!
# `L(n) = x^2 + 1` and `L(n) + 1 = 2 x^2`

* Even `n`: `L(4k) = L(2k)^2 - 2` and `L(4k + 2) = L(2k + 1)^2 + 2` reduce both equations to
  `X^2 = x^2 + 3`, `x^2 = X^2 + 1`, `X^2 + 3 = 2 x^2` (impossible modulo `8`) and the Pell
  equation `X^2 = 2 x^2 + 1`. For the last one `X + 1` or `X - 1` is a square
  (`pell_split`), and `L(m) + 1 = z^2` with `m` even only for `m = 2`.
* Odd `n`: `L(4k + 1) - 1 = 5 F(2k + 1) F(2k)`, `L(4k + 3) - 1 = L(2k + 2) L(2k + 1)`,
  `L(4k + 1) + 1 = L(2k + 1) L(2k)` and `L(4k + 3) + 1 = 5 F(2k + 2) F(2k + 1)`, with coprime
  factors. One factor is a square or twice a square, Cohn's results leave a few indices, and
  `n = 5, 7, 23, 25` fail by the size of `x`.
-/

namespace TuringTask

lemma sq_succ {Y z : ℕ} (h : Y ^ 2 = z ^ 2 + 1) : Y = 1 ∧ z = 0 := by
  have hzY : z < Y := by
    by_contra hc
    push Not at hc
    nlinarith [Nat.pow_le_pow_left hc 2]
  have hz : z = 0 := by nlinarith
  subst hz
  exact ⟨by simpa using h, rfl⟩

lemma sq_add_three {Y z : ℕ} (h : Y ^ 2 = z ^ 2 + 3) : Y = 2 ∧ z = 1 := by
  have hzY : z < Y := by
    by_contra hc
    push Not at hc
    nlinarith [Nat.pow_le_pow_left hc 2]
  have hz : z ≤ 1 := by nlinarith
  have hY : Y ≤ 2 := by nlinarith
  interval_cases z <;> interval_cases Y <;> simp_all

lemma no_sq_add_three {X x : ℕ} (h : X ^ 2 + 3 = 2 * x ^ 2) : False := by
  have key : ∀ a b : ZMod 8, a ^ 2 + 3 ≠ 2 * b ^ 2 := by decide
  have := congrArg (Nat.cast : ℕ → ZMod 8) h
  push_cast at this
  exact key _ _ this

lemma not_sq_between {x a N : ℕ} (h : x ^ 2 = N) (h1 : a ^ 2 < N) (h2 : N < (a + 1) ^ 2) :
    False := by
  rcases le_or_gt x a with hx | hx
  · nlinarith [Nat.pow_le_pow_left hx 2]
  · nlinarith [Nat.pow_le_pow_left (show a + 1 ≤ x by omega) 2]

lemma lnat_ge_three {m : ℕ} (hm : 2 ≤ m) : 3 ≤ lnat m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  have h1 := lnat_add (j + 2)
  have e1 : Nat.fib (j + 3) = Nat.fib (j + 1) + Nat.fib (j + 2) := Nat.fib_add_two
  have e2 : Nat.fib (j + 2) = Nat.fib j + Nat.fib (j + 1) := Nat.fib_add_two
  have p1 : 0 < Nat.fib (j + 1) := Nat.fib_pos.mpr (by omega)
  have p2 : 0 < Nat.fib (j + 2) := Nat.fib_pos.mpr (by omega)
  rw [show j + 2 + 1 = j + 3 by ring] at h1
  omega

lemma lnat_eq_one {m : ℕ} (h : lnat m = 1) : m = 1 := by
  by_contra hm
  have := lnat_ge_two hm
  omega

lemma lnat_eq_two {m : ℕ} (h : lnat m = 2) : m = 0 := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · rfl
    · exact absurd h (by decide)
  · have := lnat_ge_three hm
    omega

/-- Theorem 4: `L(n) = x^2 + 1` forces `n = 0` or `n = 1`. -/
theorem lnat_sq_add_one {n x : ℕ} (h : lnat n = x ^ 2 + 1) : n = 0 ∨ n = 1 := by
  obtain ⟨k, rfl | rfl | rfl | rfl⟩ := four_cases n
  · obtain ⟨-, -, -, -, E0, -⟩ := lucas_factor k
    have e : lnat (2 * k) ^ 2 = x ^ 2 + 3 := by omega
    have := lnat_eq_two (sq_add_three e).1
    omega
  · obtain ⟨LM1, -⟩ := lucas_factor k
    rw [LM1] at h
    obtain ⟨z, hz⟩ := sq_prime Nat.prime_five (x := x)
      (M := Nat.fib (2 * k + 1) * Nat.fib (2 * k)) (by rw [← mul_assoc]; omega)
    have hc : Nat.Coprime (Nat.fib (2 * k + 1)) (Nat.fib (2 * k)) :=
      (Nat.fib_coprime_fib_succ (2 * k)).symm
    rcases prime_split Nat.prime_five hz with ⟨A', hA, hA'⟩ | ⟨B', hB, hB'⟩
    · have hc' : Nat.Coprime A' (Nat.fib (2 * k)) :=
        Nat.Coprime.coprime_dvd_left ⟨5, by rw [hA]; ring⟩ hc
      obtain ⟨d, hd⟩ := sq_of_coprime_mul hc' hA'
      have hk := fib_eq_sq_cases _ d hd
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 6) with rfl | rfl | rfl
      · right; rfl
      · exfalso
        have h5 : lnat 5 = 11 := by decide
        rw [← LM1, show 4 * 1 + 1 = 5 from rfl, h5] at h
        exact not_sq_between (x := x) (a := 3) (N := 10) (by omega) (by norm_num) (by norm_num)
      · exfalso
        have h25 : lnat 25 = 167761 := by decide
        rw [← LM1, show 4 * 6 + 1 = 25 from rfl, h25] at h
        exact not_sq_between (x := x) (a := 409) (N := 167760) (by omega) (by norm_num)
          (by norm_num)
    · have hc' : Nat.Coprime (Nat.fib (2 * k + 1)) B' :=
        Nat.Coprime.coprime_dvd_right ⟨5, by rw [hB]; ring⟩ hc
      obtain ⟨d, hd⟩ := sq_left hc' hB'
      have := fib_eq_sq_cases _ d hd
      omega
  · obtain ⟨-, -, -, -, -, E2⟩ := lucas_factor k
    have e : x ^ 2 = lnat (2 * k + 1) ^ 2 + 1 := by omega
    have := (sq_succ e).2
    have := lnat_pos (2 * k + 1)
    omega
  · obtain ⟨-, LM3, -⟩ := lucas_factor k
    rw [LM3] at h
    have h' : lnat (2 * k + 2) * lnat (2 * k + 1) = x ^ 2 := by omega
    have hc := (cop_lnat_succ (2 * k + 1)).symm
    rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring] at hc
    obtain ⟨d, hd⟩ := sq_left hc h'
    have := lnat_sq hd
    omega

/-- `X^2 = 2 x^2 + 1` makes `X + 1` or `X - 1` a square. -/
lemma pell_split {X x : ℕ} (h : X ^ 2 = 2 * x ^ 2 + 1) :
    (∃ z, X + 1 = z ^ 2) ∨ (∃ z, X = z ^ 2 + 1) := by
  have hX : Odd X := by
    have : Odd (X ^ 2) := ⟨x ^ 2, by rw [h]⟩
    exact (Nat.odd_pow_iff two_ne_zero).mp this
  obtain ⟨p, rfl⟩ := hX
  have hx2 : x ^ 2 = 2 * (p * (p + 1)) := by nlinarith
  have hxe : Even x := (Nat.even_pow.mp ⟨p * (p + 1), by rw [hx2]; ring⟩).1
  obtain ⟨w, rfl⟩ := hxe
  have hw : p * (p + 1) = 2 * w ^ 2 := by nlinarith
  have hc : Nat.Coprime p (p + 1) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  rcases prime_split Nat.prime_two hw with ⟨A', hA, hA'⟩ | ⟨B', hB, hB'⟩
  · have hc' : Nat.Coprime A' (p + 1) := Nat.Coprime.coprime_dvd_left ⟨2, by rw [hA]; ring⟩ hc
    obtain ⟨a, ha⟩ := sq_left hc' hA'
    right
    exact ⟨2 * a, by rw [hA, ha]; ring⟩
  · have hc' : Nat.Coprime p B' := Nat.Coprime.coprime_dvd_right ⟨2, by rw [hB]; ring⟩ hc
    obtain ⟨b, hb⟩ := sq_of_coprime_mul hc' hB'
    left
    exact ⟨2 * b, by rw [show 2 * p + 1 + 1 = 2 * (p + 1) by ring, hB, hb]; ring⟩

/-- `L(m) + 1 = z^2` with `m` even forces `m = 2`. -/
lemma lnat_even_add_one_sq {m z : ℕ} (hm : m % 2 = 0) (h : lnat m + 1 = z ^ 2) : m = 2 := by
  obtain ⟨j, rfl | rfl | rfl | rfl⟩ := four_cases m
  · obtain ⟨-, -, -, -, E0, -⟩ := lucas_factor j
    have e : lnat (2 * j) ^ 2 = z ^ 2 + 1 := by omega
    have := lnat_eq_one (sq_succ e).1
    omega
  · omega
  · obtain ⟨-, -, -, -, -, E2⟩ := lucas_factor j
    have e : z ^ 2 = lnat (2 * j + 1) ^ 2 + 3 := by omega
    have := lnat_eq_one (sq_add_three e).2
    omega
  · omega

/-- Theorem 5: `L(n) + 1 = 2 x^2` forces `n` in `{1, 4, 11}`. -/
theorem lnat_add_one_two_sq {n x : ℕ} (h : lnat n + 1 = 2 * x ^ 2) :
    n = 1 ∨ n = 4 ∨ n = 11 := by
  obtain ⟨k, rfl | rfl | rfl | rfl⟩ := four_cases n
  · obtain ⟨-, -, -, -, E0, -⟩ := lucas_factor k
    have e : lnat (2 * k) ^ 2 = 2 * x ^ 2 + 1 := by omega
    rcases pell_split e with ⟨z, hz⟩ | ⟨z, hz⟩
    · have := lnat_even_add_one_sq (by omega) hz
      omega
    · have := lnat_sq_add_one hz
      have hk : k = 0 := by omega
      subst hk
      have h0 : lnat 0 = 2 := by decide
      rw [h0] at h
      omega
  · obtain ⟨-, -, LP1, -⟩ := lucas_factor k
    rw [LP1] at h
    have hc := (cop_lnat_succ (2 * k)).symm
    rcases prime_split Nat.prime_two h with ⟨A', hA, hA'⟩ | ⟨B', hB, hB'⟩
    · have hc' : Nat.Coprime A' (lnat (2 * k)) :=
        Nat.Coprime.coprime_dvd_left ⟨2, by rw [hA]; ring⟩ hc
      obtain ⟨a, ha⟩ := sq_left hc' hA'
      have := lnat_two_sq (x := a) (by rw [hA, ha])
      omega
    · have hc' : Nat.Coprime (lnat (2 * k + 1)) B' :=
        Nat.Coprime.coprime_dvd_right ⟨2, by rw [hB]; ring⟩ hc
      obtain ⟨a, ha⟩ := sq_left hc' hB'
      have hk := lnat_sq ha
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · left; rfl
      · exfalso
        have h5 : lnat 5 = 11 := by decide
        rw [← LP1, show 4 * 1 + 1 = 5 from rfl, h5] at h
        exact not_sq_between (x := x) (a := 2) (N := 6) (by omega) (by norm_num) (by norm_num)
  · obtain ⟨-, -, -, -, -, E2⟩ := lucas_factor k
    exact absurd (by omega : lnat (2 * k + 1) ^ 2 + 3 = 2 * x ^ 2) fun e => no_sq_add_three e
  · obtain ⟨-, -, -, LP3, -⟩ := lucas_factor k
    rw [LP3] at h
    have h5 : 5 ∣ x := by
      have : 5 ∣ 2 * x ^ 2 := ⟨_, by rw [← h, mul_assoc]⟩
      rcases (Nat.Prime.dvd_mul Nat.prime_five).mp this with h2 | h2
      · omega
      · exact Nat.prime_five.dvd_of_dvd_pow h2
    obtain ⟨y, rfl⟩ := h5
    have hP : Nat.fib (2 * k + 2) * Nat.fib (2 * k + 1) = 2 * (5 * y ^ 2) := by
      rw [mul_assoc] at h; nlinarith
    have hc : Nat.Coprime (Nat.fib (2 * k + 2)) (Nat.fib (2 * k + 1)) :=
      (Nat.fib_coprime_fib_succ (2 * k + 1)).symm
    have l3 : lnat 3 = 4 := by decide
    rcases prime_split Nat.prime_two hP with ⟨A', hA, hA'⟩ | ⟨B', hB, hB'⟩
    · have hc' : Nat.Coprime A' (Nat.fib (2 * k + 1)) :=
        Nat.Coprime.coprime_dvd_left ⟨2, by rw [hA]; ring⟩ hc
      rcases prime_split Nat.prime_five hA' with ⟨C, hC, hC'⟩ | ⟨D, hD, hD'⟩
      · have hc'' : Nat.Coprime C (Nat.fib (2 * k + 1)) :=
          Nat.Coprime.coprime_dvd_left ⟨5, by rw [hC]; ring⟩ hc'
        obtain ⟨d, hd⟩ := sq_of_coprime_mul hc'' hC'
        have := fib_eq_sq_cases _ d hd
        have hk : k = 0 := by omega
        subst hk
        rw [← LP3, show 4 * 0 + 3 = 3 from rfl, l3] at h
        omega
      · have hc'' : Nat.Coprime A' D :=
          Nat.Coprime.coprime_dvd_right ⟨5, by rw [hD]; ring⟩ hc'
        obtain ⟨d, hd⟩ := sq_left hc'' hD'
        have := fib_eq_two_mul_sq_cases _ d (by rw [hA, hd])
        right; right; omega
    · have hc' : Nat.Coprime (Nat.fib (2 * k + 2)) B' :=
        Nat.Coprime.coprime_dvd_right ⟨2, by rw [hB]; ring⟩ hc
      rcases prime_split Nat.prime_five hB' with ⟨C, hC, hC'⟩ | ⟨D, hD, hD'⟩
      · have hc'' : Nat.Coprime C B' := Nat.Coprime.coprime_dvd_left ⟨5, by rw [hC]; ring⟩ hc'
        obtain ⟨d, hd⟩ := sq_of_coprime_mul hc'' hC'
        have := fib_eq_two_mul_sq_cases _ d (by rw [hB, hd])
        have hk : k = 1 := by omega
        subst hk
        have l7 : lnat 7 = 29 := by decide
        rw [← LP3, show 4 * 1 + 3 = 7 from rfl, l7] at h
        exfalso
        exact not_sq_between (x := 5 * y) (a := 3) (N := 15) (by omega) (by norm_num)
          (by norm_num)
      · have hc'' : Nat.Coprime (Nat.fib (2 * k + 2)) D :=
          Nat.Coprime.coprime_dvd_right ⟨5, by rw [hD]; ring⟩ hc'
        obtain ⟨d, hd⟩ := sq_left hc'' hD'
        have := fib_eq_sq_cases _ d hd
        rcases (by omega : k = 0 ∨ k = 5) with rfl | rfl
        · rw [← LP3, show 4 * 0 + 3 = 3 from rfl, l3] at h
          omega
        · exfalso
          have l23 : lnat 23 = 64079 := by decide
          rw [← LP3, show 4 * 5 + 3 = 23 from rfl, l23] at h
          exact not_sq_between (x := 5 * y) (a := 178) (N := 32040) (by omega) (by norm_num)
            (by norm_num)

end TuringTask
