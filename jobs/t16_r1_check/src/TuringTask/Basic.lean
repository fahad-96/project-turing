import Mathlib

namespace TuringTask

/-!
### Helper Definitions and Lemmas on Fibonacci and Lucas numbers
-/

def lucas (n : ℕ) : ℕ := Nat.fib (n - 1) + Nat.fib (n + 1)
def lucasZ (n : ℤ) : ℤ := Int.fib (n - 1) + Int.fib (n + 1)

theorem no_sq_diff_two (A B : ℕ) (h : A ^ 2 = B ^ 2 + 2) : False := by
  apply_fun (fun n : ℕ => (n : ZMod 4)) at h
  push_cast at h
  have H : ∀ (a b : ZMod 4), a ^ 2 = b ^ 2 + 2 → False := by decide
  exact H A B h

theorem lucasZ_two_mul (n : ℤ) :
    lucasZ (2 * n) = lucasZ n ^ 2 - 2 * (-1) ^ n.natAbs := by
  have h2 : 2 * n - 1 = 2 * (n - 1) + 1 := by ring
  have h3 := Int.fib_two_mul_add_one n
  have h4 := Int.fib_two_mul_add_one (n - 1)
  have h5 := Int.fib_succ_mul_fib_pred_sub_fib_sq n
  have h6 : n - 1 + 1 = n := by ring
  rw [h6] at h4
  dsimp [lucasZ]
  rw [h2, h4, h3]
  rw [← h5]
  ring

theorem lucas_eq_lucasZ (n : ℕ) (hn : 1 ≤ n) :
    (lucas n : ℤ) = lucasZ n := by
  dsimp [lucas, lucasZ]
  have e1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have e2 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by omega
  rw [← e1, ← e2, Int.fib_natCast, Int.fib_natCast]

theorem not_lucas_even_sq (m x : ℕ) (hm : 1 ≤ m) (h : lucas (2 * m) = x ^ 2) : False := by
  have hL2m : (lucas (2 * m) : ℤ) = (x : ℤ) ^ 2 := by
    rw [h, Nat.cast_pow]
  have h1 : 1 ≤ 2 * m := by omega
  rw [lucas_eq_lucasZ (2 * m) h1] at hL2m
  have h2m : ((2 * m : ℕ) : ℤ) = 2 * (m : ℤ) := by push_cast; rfl
  rw [h2m] at hL2m
  rw [lucasZ_two_mul (m : ℤ)] at hL2m
  have hmZ : lucasZ (m : ℤ) = (lucas m : ℤ) := (lucas_eq_lucasZ m hm).symm
  rw [hmZ] at hL2m
  have hnatAbs : ((m : ℤ).natAbs) = m := Int.natAbs_natCast m
  rw [hnatAbs] at hL2m
  rcases Nat.mod_two_eq_zero_or_one m with hm_even | hm_odd
  · have hpow : (-1 : ℤ) ^ m = 1 := by
      rw [← Nat.even_iff, even_iff_two_dvd] at hm_even
      rcases hm_even with ⟨k, rfl⟩
      rw [pow_mul, neg_one_sq, one_pow]
    rw [hpow] at hL2m
    have h_nat : (lucas m) ^ 2 = x ^ 2 + 2 := by
      zify
      linarith
    exact no_sq_diff_two (lucas m) x h_nat
  · have hpow : (-1 : ℤ) ^ m = -1 := by
      have : m = 2 * (m / 2) + 1 := by omega
      rw [this, pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
    rw [hpow] at hL2m
    have h_nat : x ^ 2 = (lucas m) ^ 2 + 2 := by
      zify
      linarith
    exact no_sq_diff_two x (lucas m) h_nat

theorem no_sq_add_one_dvd_prime (p x : ℕ) [hp : Fact (Nat.Prime p)] (hp4 : p % 4 = 3)
    (h : p ∣ x ^ 2 + 1) : False := by
  have hsq : IsSquare (-1 : ZMod p) := by
    use (x : ZMod p)
    have : ((x ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
      rw [CharP.cast_eq_zero_iff (ZMod p) p]
      exact h
    push_cast at this
    have : (x : ZMod p) ^ 2 = -1 := eq_neg_of_add_eq_zero_left this
    rw [sq] at this
    exact this.symm
  have hiff := @ZMod.exists_sq_eq_neg_one_iff p hp
  rw [hiff] at hsq
  exact hsq hp4

theorem exists_prime_factor_mod_four_eq_three (M : ℕ) (hM : M % 4 = 3) :
    ∃ p, p.Prime ∧ p ∣ M ∧ p % 4 = 3 := by
  induction' M using Nat.strong_induction_on with M ih
  by_cases hp : M.Prime
  · exact ⟨M, hp, dvd_rfl, hM⟩
  · have hM1 : M ≠ 1 := by omega
    obtain ⟨p, hpp, q, rfl⟩ := Nat.exists_prime_and_dvd hM1
    have hp2 : p ≠ 2 := by
      rintro rfl
      omega
    have hp4_cases : p % 4 = 1 ∨ p % 4 = 3 := by
      have : p % 2 = 1 := (hpp.mod_two_eq_one_iff_ne_two).mpr hp2
      omega
    rcases hp4_cases with hp4_1 | hp4_3
    · have hq4 : q % 4 = 3 := by
        have h_mod := Nat.mul_mod p q 4
        rw [hp4_1, one_mul, Nat.mod_mod] at h_mod
        rw [← h_mod]
        exact hM
      have hq_pos : 0 < q := by
        rcases q with _ | q
        · simp at hM
        · omega
      have hq_lt : q < p * q := by
        calc q = 1 * q := (one_mul q).symm
        _ < p * q := Nat.mul_lt_mul_of_pos_right hpp.one_lt hq_pos
      obtain ⟨r, hrp, hrdvd, hr4⟩ := ih q hq_lt hq4
      exact ⟨r, hrp, dvd_trans hrdvd (dvd_mul_left q p), hr4⟩
    · exact ⟨p, hpp, dvd_mul_right p q, hp4_3⟩

theorem no_sq_add_one_dvd_mod_four_three (M x : ℕ) (hM : M % 4 = 3) (h : M ∣ x ^ 2 + 1) : False := by
  obtain ⟨p, hpp, hpdvd, hp4⟩ := exists_prime_factor_mod_four_eq_three M hM
  have hp_fact : Fact (Nat.Prime p) := ⟨hpp⟩
  have hpx : p ∣ x ^ 2 + 1 := dvd_trans hpdvd h
  exact no_sq_add_one_dvd_prime p x hp4 hpx

theorem no_sq_add_four_dvd_prime (p x : ℕ) [hp : Fact (Nat.Prime p)] (hp4 : p % 4 = 3)
    (h : p ∣ x ^ 2 + 4) : False := by
  have hp2 : (2 : ZMod p) ≠ 0 := by
    intro h2
    have hdvd : p ∣ 2 := by
      rw [← CharP.cast_eq_zero_iff (ZMod p) p]
      exact h2
    have : p ≤ 2 := Nat.le_of_dvd (by decide) hdvd
    omega
  have hsq : IsSquare (-1 : ZMod p) := by
    use (x : ZMod p) * (2 : ZMod p)⁻¹
    have h4 : ((x ^ 2 + 4 : ℕ) : ZMod p) = 0 := by
      rw [CharP.cast_eq_zero_iff (ZMod p) p]
      exact h
    push_cast at h4
    have hx2 : (x : ZMod p) ^ 2 = -4 := eq_neg_of_add_eq_zero_left h4
    have hinv : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hp2
    have hcalc : ((x : ZMod p) * (2 : ZMod p)⁻¹) ^ 2 = -1 := by
      calc ((x : ZMod p) * (2 : ZMod p)⁻¹) ^ 2 = (x : ZMod p) ^ 2 * ((2 : ZMod p)⁻¹) ^ 2 := by ring
      _ = -4 * ((2 : ZMod p)⁻¹) ^ 2 := by rw [hx2]
      _ = - (2 * (2 : ZMod p)⁻¹) ^ 2 := by ring
      _ = - (1 : ZMod p) ^ 2 := by rw [hinv]
      _ = -1 := by ring
    rw [sq] at hcalc
    exact hcalc.symm
  have hiff := @ZMod.exists_sq_eq_neg_one_iff p hp
  rw [hiff] at hsq
  exact hsq hp4

theorem no_sq_add_four_dvd_mod_four_three (M x : ℕ) (hM : M % 4 = 3) (h : M ∣ x ^ 2 + 4) : False := by
  obtain ⟨p, hpp, hpdvd, hp4⟩ := exists_prime_factor_mod_four_eq_three M hM
  have hp_fact : Fact (Nat.Prime p) := ⟨hpp⟩
  have hpx : p ∣ x ^ 2 + 4 := dvd_trans hpdvd h
  exact no_sq_add_four_dvd_prime p x hp4 hpx

theorem lucas_pow_two_mod_four (r : ℕ) (hr : 1 ≤ r) :
    lucas (2 ^ r) % 4 = 3 := by
  induction' r with r ih
  · omega
  · by_cases hr1 : r = 0
    · subst hr1
      decide
    · have hr_ge_1 : 1 ≤ r := by omega
      have ih_res := ih hr_ge_1
      have h2pow : 2 ^ (r + 1) = 2 * 2 ^ r := by ring
      rw [h2pow]
      have h1 : 1 ≤ 2 * 2 ^ r := by
        have : 0 < 2 ^ r := by positivity
        omega
      have h1' : 1 ≤ 2 ^ r := by
        have : 0 < 2 ^ r := by positivity
        omega
      have hL := lucasZ_two_mul (2 ^ r : ℤ)
      have hL1 : (lucas (2 * 2 ^ r) : ℤ) = lucasZ (2 * (2 ^ r : ℤ)) := by
        rw [lucas_eq_lucasZ (2 * 2 ^ r) h1]
        push_cast; rfl
      have hL2 : lucasZ (2 ^ r : ℤ) = (lucas (2 ^ r) : ℤ) := (lucas_eq_lucasZ (2 ^ r) h1').symm
      have heven : (-1 : ℤ) ^ ((2 ^ r : ℤ).natAbs) = 1 := by
        have : (2 ^ r : ℤ).natAbs = 2 ^ r := by simp
        rw [this]
        have he : 2 ^ r = 2 * 2 ^ (r - 1) := by
          have : r = (r - 1) + 1 := by omega
          conv_lhs => rw [this, pow_succ]
          ring
        rw [he, pow_mul, neg_one_sq, one_pow]
      rw [hL2, heven] at hL
      rw [← hL1] at hL
      have hmod : ((lucas (2 * 2 ^ r) : ℤ) : ZMod 4) = (((lucas (2 ^ r) : ℤ) ^ 2 - 2 * 1 : ℤ) : ZMod 4) := by
        rw [hL]
      push_cast at hmod
      have hr_mod : (lucas (2 ^ r) : ZMod 4) = 3 := by
        have : (lucas (2 ^ r) : ZMod 4) = ((lucas (2 ^ r) % 4 : ℕ) : ZMod 4) := by
          rw [ZMod.natCast_mod]
        rw [this, ih_res]
        rfl
      rw [hr_mod] at hmod
      have h3_sq : (3 : ZMod 4) ^ 2 - 2 = 3 := by decide
      rw [h3_sq] at hmod
      have hmod_nat : (lucas (2 * 2 ^ r) : ZMod 4) = ((lucas (2 * 2 ^ r) % 4 : ℕ) : ZMod 4) := by
        rw [ZMod.natCast_mod]
      rw [hmod_nat] at hmod
      have hlt : lucas (2 * 2 ^ r) % 4 < 4 := Nat.mod_lt _ (by decide)
      interval_cases (lucas (2 * 2 ^ r) % 4)
      · revert hmod; decide
      · revert hmod; decide
      · revert hmod; decide
      · rfl

theorem odd_ne_two_mul_sq {a x : ℕ} (ha : a % 2 = 1) (h : a = 2 * x ^ 2) : False := by
  have : a % 2 = (2 * x ^ 2) % 2 := by rw [h]
  omega

/-!
### Lemmas for fib_eq_two_pow
-/

theorem fib_zmod_two (n : ℕ) : (Nat.fib n : ZMod 2) = if n % 3 = 0 then 0 else 1 := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | n
  · rfl
  · rfl
  · have h2 : (Nat.fib (n + 2) : ZMod 2) = (Nat.fib n : ZMod 2) + (Nat.fib (n + 1) : ZMod 2) := by
      push_cast [Nat.fib_add_two]
      ring
    rw [h2, ih n (by omega), ih (n + 1) (by omega)]
    have hlt : n % 3 < 3 := Nat.mod_lt _ (by decide)
    interval_cases hn3 : (n % 3)
    · have h1 : (n + 1) % 3 = 1 := by omega
      have h2 : (n + 2) % 3 = 2 := by omega
      have : n + 1 + 1 = n + 2 := rfl
      rw [this, h1, h2]
      decide
    · have h1 : (n + 1) % 3 = 2 := by omega
      have h2 : (n + 2) % 3 = 0 := by omega
      have : n + 1 + 1 = n + 2 := rfl
      rw [this, h1, h2]
      decide
    · have h1 : (n + 1) % 3 = 0 := by omega
      have h2 : (n + 2) % 3 = 1 := by omega
      have : n + 1 + 1 = n + 2 := rfl
      rw [this, h1, h2]
      decide

theorem fib_odd_of_not_dvd_three (n : ℕ) (h : ¬ 3 ∣ n) : Nat.fib n % 2 = 1 := by
  have hz := fib_zmod_two n
  have hmod : n % 3 ≠ 0 := by
    intro h0
    exact h (Nat.dvd_of_mod_eq_zero h0)
  rw [if_neg hmod] at hz
  have : (Nat.fib n : ZMod 2) = ((Nat.fib n % 2 : ℕ) : ZMod 2) := by
    rw [ZMod.natCast_mod]
  rw [this] at hz
  have hlt : Nat.fib n % 2 < 2 := Nat.mod_lt _ (by decide)
  interval_cases (Nat.fib n % 2)
  · revert hz; decide
  · rfl

theorem odd_dvd_pow_two {d k : ℕ} (hodd : d % 2 = 1) (hdvd : d ∣ 2 ^ k) : d = 1 := by
  rcases eq_or_ne d 1 with rfl | hd1
  · rfl
  · obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd hd1
    have hp2 : p ∣ 2 := hpp.dvd_of_dvd_pow (dvd_trans hpdvd hdvd)
    have hp_eq : p = 2 := by
      have : p ≤ 2 := Nat.le_of_dvd (by decide) hp2
      have : 1 < p := hpp.one_lt
      omega
    subst hp_eq
    have : 2 ∣ d := hpdvd
    omega

theorem fib_ge_two_of_ge_three {d : ℕ} (hd : 3 ≤ d) : 2 ≤ Nat.fib d := by
  induction' d, hd using Nat.le_induction with d hd ih
  · decide
  · rcases d with _ | _ | d
    · omega
    · omega
    · rw [Nat.fib_add_two]
      have : 0 < Nat.fib d := by
        rw [Nat.fib_pos]
        omega
      omega

theorem not_dvd_and_ge_three_fib {n k d : ℕ} (hd_dvd : d ∣ n) (hd_ge : 3 ≤ d)
    (hd_not3 : ¬ 3 ∣ d) (h : Nat.fib n = 2 ^ k) : False := by
  have hfib_dvd : Nat.fib d ∣ Nat.fib n := Nat.fib_dvd d n hd_dvd
  rw [h] at hfib_dvd
  have hodd : Nat.fib d % 2 = 1 := fib_odd_of_not_dvd_three d hd_not3
  have heq1 : Nat.fib d = 1 := odd_dvd_pow_two hodd hfib_dvd
  have hge2 : 2 ≤ Nat.fib d := fib_ge_two_of_ge_three hd_ge
  omega

theorem not_nine_dvd_fib {n k : ℕ} (hdvd : 9 ∣ n) (h : Nat.fib n = 2 ^ k) : False := by
  have hfib_dvd : Nat.fib 9 ∣ Nat.fib n := Nat.fib_dvd 9 n hdvd
  rw [h] at hfib_dvd
  have h34 : Nat.fib 9 = 34 := by decide
  rw [h34] at hfib_dvd
  have h17 : 17 ∣ 34 := by decide
  have h17_dvd : 17 ∣ 2 ^ k := dvd_trans h17 hfib_dvd
  have h17_odd : 17 % 2 = 1 := by decide
  have : 17 = 1 := odd_dvd_pow_two h17_odd h17_dvd
  omega

theorem exists_bad_subfactor {m : ℕ} (hm : 1 < m) (hodd : m % 2 = 1) (hnot3 : ¬ 3 ∣ m) :
    ∃ p, p ∣ m ∧ 3 ≤ p ∧ ¬ 3 ∣ p := by
  have hne1 : m ≠ 1 := by omega
  obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd hne1
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : 2 ∣ m := hpdvd
    omega
  have hp3 : ¬ 3 ∣ p := by
    intro h3
    have := hpp.eq_one_or_self_of_dvd 3 h3
    rcases this with h1 | h2
    · contradiction
    · subst h2
      exact hnot3 hpdvd
  have hp_ge : 3 ≤ p := by
    have : 1 < p := hpp.one_lt
    omega
  exact ⟨p, hpdvd, hp_ge, hp3⟩

/-!
### The Five Required Theorems
-/

theorem fib_eq_sq (n x : Nat) (h : Nat.fib n = x ^ 2) :
    n = 0 \/ n = 1 \/ n = 2 \/ n = 12 := by
  rcases n with _ | _ | _ | n
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · sorry

theorem lucas_eq_sq (n x : Nat) (hn : 1 <= n) (h : Nat.fib (n - 1) + Nat.fib (n + 1) = x ^ 2) :
    n = 1 \/ n = 3 := by
  rcases Nat.mod_two_eq_zero_or_one n with h_even | h_odd
  · have h2 : 2 ∣ n := Nat.dvd_of_mod_eq_zero h_even
    rcases h2 with ⟨m, rfl⟩
    have hm : 1 ≤ m := by omega
    exfalso
    exact not_lucas_even_sq m x hm h
  · rcases n with _ | _ | _ | _ | n
    · omega
    · exact Or.inl rfl
    · omega
    · exact Or.inr rfl
    · sorry

theorem fib_eq_two_mul_sq (n x : Nat) (h : Nat.fib n = 2 * x ^ 2) :
    n = 0 \/ n = 3 \/ n = 6 := by
  rcases n with _ | _ | _ | _ | _ | _ | _ | n
  · exact Or.inl rfl
  · exfalso; exact odd_ne_two_mul_sq (by decide) h
  · exfalso; exact odd_ne_two_mul_sq (by decide) h
  · exact Or.inr (Or.inl rfl)
  · exfalso; exact odd_ne_two_mul_sq (by decide) h
  · exfalso; exact odd_ne_two_mul_sq (by decide) h
  · exact Or.inr (Or.inr rfl)
  · sorry

theorem lucas_eq_two_mul_sq (n x : Nat) (hn : 1 <= n)
    (h : Nat.fib (n - 1) + Nat.fib (n + 1) = 2 * x ^ 2) :
    n = 6 := by
  rcases n with _ | _ | _ | _ | _ | _ | _ | n
  · omega
  · exfalso; exact odd_ne_two_mul_sq (by decide) h
  · exfalso; exact odd_ne_two_mul_sq (by decide) h
  · exfalso
    have : (4 : ℕ) = 2 * x ^ 2 := h
    have : x ^ 2 = 2 := by omega
    have : x ≤ 1 ∨ 2 ≤ x := by omega
    rcases this with h1 | h2
    · interval_cases x <;> omega
    · nlinarith
  · exfalso; exact odd_ne_two_mul_sq (by decide) h
  · exfalso; exact odd_ne_two_mul_sq (by decide) h
  · rfl
  · sorry

theorem fib_eq_two_pow (n k : Nat) (h : Nat.fib n = 2 ^ k) :
    n = 1 \/ n = 2 \/ n = 3 \/ n = 6 := by
  rcases n with _ | _ | _ | _ | _ | _ | _ | n
  · have : Nat.fib 0 = 0 := rfl
    rw [this] at h
    have : 0 < 2 ^ k := by positivity
    omega
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exfalso
    exact not_dvd_and_ge_three_fib dvd_rfl (by decide) (by decide) h
  · exfalso
    exact not_dvd_and_ge_three_fib dvd_rfl (by decide) (by decide) h
  · exact Or.inr (Or.inr (Or.inr rfl))
  · have hm : 7 ≤ n + 7 := by omega
    rcases Nat.mod_two_eq_zero_or_one (n + 7) with hm_even | hm_odd
    · have h2m : 2 ∣ (n + 7) := Nat.dvd_of_mod_eq_zero hm_even
      rcases h2m with ⟨k_m, hk_m⟩
      by_cases hk_even : 2 ∣ k_m
      · exfalso
        have h4 : 4 ∣ (n + 7) := by
          rcases hk_even with ⟨j, rfl⟩
          rw [hk_m]
          exact ⟨j, by ring⟩
        exact not_dvd_and_ge_three_fib h4 (by decide) (by decide) h
      · have hk_odd : k_m % 2 = 1 := by
          have : k_m % 2 < 2 := Nat.mod_lt _ (by decide)
          have : k_m % 2 ≠ 0 := by
            intro h0
            exact hk_even (Nat.dvd_of_mod_eq_zero h0)
          omega
        by_cases hk3 : 3 ∣ k_m
        · rcases hk3 with ⟨j, rfl⟩
          by_cases hj3 : 3 ∣ j
          · exfalso
            have h9 : 9 ∣ (n + 7) := by
              rcases hj3 with ⟨l, rfl⟩
              rw [hk_m]
              exact ⟨2 * l, by ring⟩
            exact not_nine_dvd_fib h9 h
          · by_cases hj1 : j = 1
            · subst hj1
              omega
            · have hj_odd : j % 2 = 1 := by
                have : (3 * j) % 2 = 1 := hk_odd
                have : (3 * j) % 2 = ((3 % 2) * (j % 2)) % 2 := Nat.mul_mod 3 j 2
                omega
              have hj_gt1 : 1 < j := by omega
              obtain ⟨p, hpdvd, hp_ge, hp3⟩ := exists_bad_subfactor hj_gt1 hj_odd hj3
              exfalso
              have hp_m : p ∣ (n + 7) := by
                rw [hk_m]
                exact dvd_trans hpdvd ⟨6, by ring⟩
              exact not_dvd_and_ge_three_fib hp_m hp_ge hp3 h
        · by_cases hk1 : k_m = 1
          · subst hk1; omega
          · have hk_gt1 : 1 < k_m := by omega
            obtain ⟨p, hpdvd, hp_ge, hp3⟩ := exists_bad_subfactor hk_gt1 hk_odd hk3
            exfalso
            have hp_m : p ∣ (n + 7) := by
              rw [hk_m]
              exact dvd_trans hpdvd (dvd_mul_left k_m 2)
            exact not_dvd_and_ge_three_fib hp_m hp_ge hp3 h
    · by_cases hm3 : 3 ∣ (n + 7)
      · rcases hm3 with ⟨q, hq⟩
        by_cases hq3 : 3 ∣ q
        · exfalso
          have h9 : 9 ∣ (n + 7) := by
            rcases hq3 with ⟨l, rfl⟩
            rw [hq]
            exact ⟨l, by ring⟩
          exact not_nine_dvd_fib h9 h
        · by_cases hq1 : q = 1
          · subst hq1; omega
          · have hq_odd : q % 2 = 1 := by
              have : (n + 7) % 2 = 1 := hm_odd
              rw [hq] at this
              have : (3 * q) % 2 = ((3 % 2) * (q % 2)) % 2 := Nat.mul_mod 3 q 2
              omega
            have hq_gt1 : 1 < q := by omega
            obtain ⟨p, hpdvd, hp_ge, hp3⟩ := exists_bad_subfactor hq_gt1 hq_odd hq3
            exfalso
            have hp_m : p ∣ (n + 7) := by
              rw [hq]
              exact dvd_trans hpdvd (dvd_mul_left q 3)
            exact not_dvd_and_ge_three_fib hp_m hp_ge hp3 h
      · have hm_gt1 : 1 < n + 7 := by omega
        obtain ⟨p, hpdvd, hp_ge, hp3⟩ := exists_bad_subfactor hm_gt1 hm_odd hm3
        exfalso
        exact not_dvd_and_ge_three_fib hpdvd hp_ge hp3 h

end TuringTask
