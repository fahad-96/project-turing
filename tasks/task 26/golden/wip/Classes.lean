import Mathlib
import TuringTask.Values

/-!
# Primes `x^2 + n y^2` for `n = 5, 6, 13, 21`

For each `n` (with `M = 4 n`):
* `reduced_n`: the reduced forms of discriminant `-M` (from `3 a^2 ≤ M`).
* `vals_n_prin`, `vals_n_a_b`: `decide` over `x, y < 2 n` lists the values modulo `M` of each
  reduced form. The prime values of the principal form `x^2 + n y^2` lie in the stated classes,
  and no other reduced form takes a value in these classes.
* `fwd_n`: a prime `x^2 + n y^2` lies in the stated classes (or is `n` itself).
* `bwd_n`: for a prime in the stated classes, `-n` is a square modulo `p` (`sq_neg_of`), so the
  form `(p, 2 t, c)` of `lagrange` represents `p`. `reduce` gives a reduced form that represents
  `p`, and the value tables leave only the principal form.
-/

namespace TuringTask

lemma no_small {q n x y : ℕ} (hq : q < n) (h : q = x ^ 2 + n * y ^ 2)
    (hs : ∀ z, z ≤ q → z ^ 2 ≠ q) : False := by
  have hy : y = 0 := by
    by_contra hy
    have : 1 ≤ y ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hy)
    nlinarith
  subst hy
  exact hs x (by nlinarith) (by simpa using h.symm)

/-- The reduced forms of discriminant `-20`. -/
lemma reduced_5 {a b c : ℤ} (h1 : |b| ≤ a) (h2 : a ≤ c) (hd : b ^ 2 - 4 * a * c = -20) :
    (a = 1 ∧ b = 0 ∧ c = 5) ∨ (a = 2 ∧ b = 2 ∧ c = 3) ∨ (a = 2 ∧ b = -2 ∧ c = 3) := by
  have hb := reduced_bound h1 h2
  obtain ⟨hb1, hb2⟩ := abs_le.mp h1
  have ha : a ≤ 2 := by nlinarith
  have ha0 : 0 < a := by nlinarith
  interval_cases a <;> interval_cases b <;> (ring_nf at hd; omega)

lemma vals_5_prin : ∀ x, x < 2 * 5 → ∀ y, y < 2 * 5 →
    (fun r => r = 1 ∨ r = 9 ∨ r % 2 = 0 ∨ r % 5 = 0)
      ((1 * x ^ 2 + 2 * 0 * x * y + 5 * y ^ 2) % (4 * 5)) := by
  decide

lemma vals_5_2_1 : ∀ x, x < 2 * 5 → ∀ y, y < 2 * 5 →
    (fun r => r ≠ 1 ∧ r ≠ 9)
      ((2 * x ^ 2 + 2 * 1 * x * y + 3 * y ^ 2) % (4 * 5)) := by
  decide

/-- A prime `x^2 + 5 y^2` lies in the stated classes modulo `20`. -/
theorem fwd_5 {p x y : ℕ} (hp : p.Prime) (h : p = x ^ 2 + 5 * y ^ 2) :
    p = 5 ∨ (p % 20 = 1 ∨ p % 20 = 9) := by
  have hr : FormRep (1 : ℕ) (2 * (0 : ℕ)) (5 : ℕ) p := ⟨x, y, by rw [h]; push_cast; ring⟩
  obtain ⟨u, v, hu, hv, hm⟩ := rep_mod_nat rfl rfl rfl (by norm_num : 0 < 5) hr
  have hval := vals_5_prin u hu v hv
  simp only at hval
  generalize (1 * u ^ 2 + 2 * 0 * u * v + 5 * v ^ 2) % (4 * 5) = r at hm hval
  rcases hval with hr | hr | hr | hr
  · right; omega
  · right; omega
  · have hq := prime_eq_of_mod hp (by norm_num : Nat.Prime 2) (by omega)
    exact (no_small (q := 2) (n := 5) (by norm_num) (by subst hq; exact h) (by decide)).elim
  · have hq := prime_eq_of_mod hp (by norm_num : Nat.Prime 5) (by omega)
    left; exact hq

/-- A prime in the stated classes modulo `20` is `x^2 + 5 y^2`. -/
theorem bwd_5 {p : ℕ} (hp : p.Prime) (h : p % 20 = 1 ∨ p % 20 = 9) :
    ∃ x y : ℕ, p = x ^ 2 + 5 * y ^ 2 := by
  have hodd : p % 2 = 1 := by omega
  obtain ⟨t, ht⟩ := sq_neg_of hp 5 20 rfl hodd (by
    rcases h with h | h <;> rw [h] <;> norm_num)
  obtain ⟨c, hc, hr⟩ := lagrange (p := p) (5 : ℤ) t (by exact_mod_cast ht)
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  obtain ⟨a', b', c', h1, h2, hd, hr'⟩ :=
    reduce (-20) (by norm_num) _ p (2 * t) c p rfl hp0 (by linarith) hr
  rcases reduced_5 h1 h2 hd with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · obtain ⟨X, Y, hXY⟩ := hr'
    exact natAbs_rep (n := 5) (by exact_mod_cast hXY)
  · exfalso
    obtain ⟨u, v, hu, hv, hm⟩ := rep_mod_nat (a := 2) (b := 1) (c := 3) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num : 0 < 5) (hr')
    have hval := vals_5_2_1 u hu v hv
    simp only at hval
    generalize (2 * u ^ 2 + 2 * 1 * u * v + 3 * v ^ 2) % (4 * 5) = r at hm hval
    omega
  · exfalso
    obtain ⟨u, v, hu, hv, hm⟩ := rep_mod_nat (a := 2) (b := 1) (c := 3) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num : 0 < 5) (rep_neg hr')
    have hval := vals_5_2_1 u hu v hv
    simp only at hval
    generalize (2 * u ^ 2 + 2 * 1 * u * v + 3 * v ^ 2) % (4 * 5) = r at hm hval
    omega

/-- The reduced forms of discriminant `-24`. -/
lemma reduced_6 {a b c : ℤ} (h1 : |b| ≤ a) (h2 : a ≤ c) (hd : b ^ 2 - 4 * a * c = -24) :
    (a = 1 ∧ b = 0 ∧ c = 6) ∨ (a = 2 ∧ b = 0 ∧ c = 3) := by
  have hb := reduced_bound h1 h2
  obtain ⟨hb1, hb2⟩ := abs_le.mp h1
  have ha : a ≤ 2 := by nlinarith
  have ha0 : 0 < a := by nlinarith
  interval_cases a <;> interval_cases b <;> (ring_nf at hd; omega)

lemma vals_6_prin : ∀ x, x < 2 * 6 → ∀ y, y < 2 * 6 →
    (fun r => r = 1 ∨ r = 7 ∨ r % 2 = 0 ∨ r % 3 = 0)
      ((1 * x ^ 2 + 2 * 0 * x * y + 6 * y ^ 2) % (4 * 6)) := by
  decide

lemma vals_6_2_0 : ∀ x, x < 2 * 6 → ∀ y, y < 2 * 6 →
    (fun r => r ≠ 1 ∧ r ≠ 7)
      ((2 * x ^ 2 + 2 * 0 * x * y + 3 * y ^ 2) % (4 * 6)) := by
  decide

/-- A prime `x^2 + 6 y^2` lies in the stated classes modulo `24`. -/
theorem fwd_6 {p x y : ℕ} (hp : p.Prime) (h : p = x ^ 2 + 6 * y ^ 2) :
    p % 24 = 1 ∨ p % 24 = 7 := by
  have hr : FormRep (1 : ℕ) (2 * (0 : ℕ)) (6 : ℕ) p := ⟨x, y, by rw [h]; push_cast; ring⟩
  obtain ⟨u, v, hu, hv, hm⟩ := rep_mod_nat rfl rfl rfl (by norm_num : 0 < 6) hr
  have hval := vals_6_prin u hu v hv
  simp only at hval
  generalize (1 * u ^ 2 + 2 * 0 * u * v + 6 * v ^ 2) % (4 * 6) = r at hm hval
  rcases hval with hr | hr | hr | hr
  · omega
  · omega
  · have hq := prime_eq_of_mod hp (by norm_num : Nat.Prime 2) (by omega)
    exact (no_small (q := 2) (n := 6) (by norm_num) (by subst hq; exact h) (by decide)).elim
  · have hq := prime_eq_of_mod hp (by norm_num : Nat.Prime 3) (by omega)
    exact (no_small (q := 3) (n := 6) (by norm_num) (by subst hq; exact h) (by decide)).elim

/-- A prime in the stated classes modulo `24` is `x^2 + 6 y^2`. -/
theorem bwd_6 {p : ℕ} (hp : p.Prime) (h : p % 24 = 1 ∨ p % 24 = 7) :
    ∃ x y : ℕ, p = x ^ 2 + 6 * y ^ 2 := by
  have hodd : p % 2 = 1 := by omega
  obtain ⟨t, ht⟩ := sq_neg_of hp 6 24 rfl hodd (by
    rcases h with h | h <;> rw [h] <;> norm_num)
  obtain ⟨c, hc, hr⟩ := lagrange (p := p) (6 : ℤ) t (by exact_mod_cast ht)
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  obtain ⟨a', b', c', h1, h2, hd, hr'⟩ :=
    reduce (-24) (by norm_num) _ p (2 * t) c p rfl hp0 (by linarith) hr
  rcases reduced_6 h1 h2 hd with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · obtain ⟨X, Y, hXY⟩ := hr'
    exact natAbs_rep (n := 6) (by exact_mod_cast hXY)
  · exfalso
    obtain ⟨u, v, hu, hv, hm⟩ := rep_mod_nat (a := 2) (b := 0) (c := 3) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num : 0 < 6) (hr')
    have hval := vals_6_2_0 u hu v hv
    simp only at hval
    generalize (2 * u ^ 2 + 2 * 0 * u * v + 3 * v ^ 2) % (4 * 6) = r at hm hval
    omega

/-- The reduced forms of discriminant `-52`. -/
lemma reduced_13 {a b c : ℤ} (h1 : |b| ≤ a) (h2 : a ≤ c) (hd : b ^ 2 - 4 * a * c = -52) :
    (a = 1 ∧ b = 0 ∧ c = 13) ∨ (a = 2 ∧ b = 2 ∧ c = 7) ∨ (a = 2 ∧ b = -2 ∧ c = 7) := by
  have hb := reduced_bound h1 h2
  obtain ⟨hb1, hb2⟩ := abs_le.mp h1
  have ha : a ≤ 4 := by nlinarith
  have ha0 : 0 < a := by nlinarith
  interval_cases a <;> interval_cases b <;> (ring_nf at hd; omega)

lemma vals_13_prin : ∀ x, x < 2 * 13 → ∀ y, y < 2 * 13 →
    (fun r => r = 1 ∨ r = 9 ∨ r = 17 ∨ r = 25 ∨ r = 29 ∨ r = 49 ∨ r % 2 = 0 ∨ r % 13 = 0)
      ((1 * x ^ 2 + 2 * 0 * x * y + 13 * y ^ 2) % (4 * 13)) := by
  decide

lemma vals_13_2_1 : ∀ x, x < 2 * 13 → ∀ y, y < 2 * 13 →
    (fun r => r ≠ 1 ∧ r ≠ 9 ∧ r ≠ 17 ∧ r ≠ 25 ∧ r ≠ 29 ∧ r ≠ 49)
      ((2 * x ^ 2 + 2 * 1 * x * y + 7 * y ^ 2) % (4 * 13)) := by
  decide

/-- A prime `x^2 + 13 y^2` lies in the stated classes modulo `52`. -/
theorem fwd_13 {p x y : ℕ} (hp : p.Prime) (h : p = x ^ 2 + 13 * y ^ 2) :
    p = 13 ∨ (p % 52 = 1 ∨ p % 52 = 9 ∨ p % 52 = 17 ∨ p % 52 = 25 ∨ p % 52 = 29 ∨ p % 52 = 49) := by
  have hr : FormRep (1 : ℕ) (2 * (0 : ℕ)) (13 : ℕ) p := ⟨x, y, by rw [h]; push_cast; ring⟩
  obtain ⟨u, v, hu, hv, hm⟩ := rep_mod_nat rfl rfl rfl (by norm_num : 0 < 13) hr
  have hval := vals_13_prin u hu v hv
  simp only at hval
  generalize (1 * u ^ 2 + 2 * 0 * u * v + 13 * v ^ 2) % (4 * 13) = r at hm hval
  rcases hval with hr | hr | hr | hr | hr | hr | hr | hr
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · have hq := prime_eq_of_mod hp (by norm_num : Nat.Prime 2) (by omega)
    exact (no_small (q := 2) (n := 13) (by norm_num) (by subst hq; exact h) (by decide)).elim
  · have hq := prime_eq_of_mod hp (by norm_num : Nat.Prime 13) (by omega)
    left; exact hq

/-- A prime in the stated classes modulo `52` is `x^2 + 13 y^2`. -/
theorem bwd_13 {p : ℕ} (hp : p.Prime)
    (h : p % 52 = 1 ∨ p % 52 = 9 ∨ p % 52 = 17 ∨ p % 52 = 25 ∨ p % 52 = 29 ∨ p % 52 = 49) :
    ∃ x y : ℕ, p = x ^ 2 + 13 * y ^ 2 := by
  have hodd : p % 2 = 1 := by omega
  obtain ⟨t, ht⟩ := sq_neg_of hp 13 52 rfl hodd (by
    rcases h with h | h | h | h | h | h <;> rw [h] <;> norm_num)
  obtain ⟨c, hc, hr⟩ := lagrange (p := p) (13 : ℤ) t (by exact_mod_cast ht)
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  obtain ⟨a', b', c', h1, h2, hd, hr'⟩ :=
    reduce (-52) (by norm_num) _ p (2 * t) c p rfl hp0 (by linarith) hr
  rcases reduced_13 h1 h2 hd with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · obtain ⟨X, Y, hXY⟩ := hr'
    exact natAbs_rep (n := 13) (by exact_mod_cast hXY)
  · exfalso
    obtain ⟨u, v, hu, hv, hm⟩ := rep_mod_nat (a := 2) (b := 1) (c := 7) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num : 0 < 13) (hr')
    have hval := vals_13_2_1 u hu v hv
    simp only at hval
    generalize (2 * u ^ 2 + 2 * 1 * u * v + 7 * v ^ 2) % (4 * 13) = r at hm hval
    omega
  · exfalso
    obtain ⟨u, v, hu, hv, hm⟩ := rep_mod_nat (a := 2) (b := 1) (c := 7) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num : 0 < 13) (rep_neg hr')
    have hval := vals_13_2_1 u hu v hv
    simp only at hval
    generalize (2 * u ^ 2 + 2 * 1 * u * v + 7 * v ^ 2) % (4 * 13) = r at hm hval
    omega

/-- The reduced forms of discriminant `-84`. -/
lemma reduced_21 {a b c : ℤ} (h1 : |b| ≤ a) (h2 : a ≤ c) (hd : b ^ 2 - 4 * a * c = -84) :
    (a = 1 ∧ b = 0 ∧ c = 21) ∨ (a = 2 ∧ b = 2 ∧ c = 11) ∨ (a = 2 ∧ b = -2 ∧ c = 11) ∨ (a = 3 ∧
    b = 0 ∧ c = 7) ∨ (a = 5 ∧ b = 4 ∧ c = 5) ∨ (a = 5 ∧ b = -4 ∧ c = 5) := by
  have hb := reduced_bound h1 h2
  obtain ⟨hb1, hb2⟩ := abs_le.mp h1
  have ha : a ≤ 5 := by nlinarith
  have ha0 : 0 < a := by nlinarith
  interval_cases a <;> interval_cases b <;> (ring_nf at hd; omega)

lemma vals_21_prin : ∀ x, x < 2 * 21 → ∀ y, y < 2 * 21 →
    (fun r => r = 1 ∨ r = 25 ∨ r = 37 ∨ r % 2 = 0 ∨ r % 3 = 0 ∨ r % 7 = 0)
      ((1 * x ^ 2 + 2 * 0 * x * y + 21 * y ^ 2) % (4 * 21)) := by
  decide

lemma vals_21_2_1 : ∀ x, x < 2 * 21 → ∀ y, y < 2 * 21 →
    (fun r => r ≠ 1 ∧ r ≠ 25 ∧ r ≠ 37)
      ((2 * x ^ 2 + 2 * 1 * x * y + 11 * y ^ 2) % (4 * 21)) := by
  decide

lemma vals_21_3_0 : ∀ x, x < 2 * 21 → ∀ y, y < 2 * 21 →
    (fun r => r ≠ 1 ∧ r ≠ 25 ∧ r ≠ 37)
      ((3 * x ^ 2 + 2 * 0 * x * y + 7 * y ^ 2) % (4 * 21)) := by
  decide

lemma vals_21_5_2 : ∀ x, x < 2 * 21 → ∀ y, y < 2 * 21 →
    (fun r => r ≠ 1 ∧ r ≠ 25 ∧ r ≠ 37)
      ((5 * x ^ 2 + 2 * 2 * x * y + 5 * y ^ 2) % (4 * 21)) := by
  decide

/-- A prime `x^2 + 21 y^2` lies in the stated classes modulo `84`. -/
theorem fwd_21 {p x y : ℕ} (hp : p.Prime) (h : p = x ^ 2 + 21 * y ^ 2) :
    p % 84 = 1 ∨ p % 84 = 25 ∨ p % 84 = 37 := by
  have hr : FormRep (1 : ℕ) (2 * (0 : ℕ)) (21 : ℕ) p := ⟨x, y, by rw [h]; push_cast; ring⟩
  obtain ⟨u, v, hu, hv, hm⟩ := rep_mod_nat rfl rfl rfl (by norm_num : 0 < 21) hr
  have hval := vals_21_prin u hu v hv
  simp only at hval
  generalize (1 * u ^ 2 + 2 * 0 * u * v + 21 * v ^ 2) % (4 * 21) = r at hm hval
  rcases hval with hr | hr | hr | hr | hr | hr
  · omega
  · omega
  · omega
  · have hq := prime_eq_of_mod hp (by norm_num : Nat.Prime 2) (by omega)
    exact (no_small (q := 2) (n := 21) (by norm_num) (by subst hq; exact h) (by decide)).elim
  · have hq := prime_eq_of_mod hp (by norm_num : Nat.Prime 3) (by omega)
    exact (no_small (q := 3) (n := 21) (by norm_num) (by subst hq; exact h) (by decide)).elim
  · have hq := prime_eq_of_mod hp (by norm_num : Nat.Prime 7) (by omega)
    exact (no_small (q := 7) (n := 21) (by norm_num) (by subst hq; exact h) (by decide)).elim

/-- A prime in the stated classes modulo `84` is `x^2 + 21 y^2`. -/
theorem bwd_21 {p : ℕ} (hp : p.Prime) (h : p % 84 = 1 ∨ p % 84 = 25 ∨ p % 84 = 37) :
    ∃ x y : ℕ, p = x ^ 2 + 21 * y ^ 2 := by
  have hodd : p % 2 = 1 := by omega
  obtain ⟨t, ht⟩ := sq_neg_of hp 21 84 rfl hodd (by
    rcases h with h | h | h <;> rw [h] <;> norm_num)
  obtain ⟨c, hc, hr⟩ := lagrange (p := p) (21 : ℤ) t (by exact_mod_cast ht)
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  obtain ⟨a', b', c', h1, h2, hd, hr'⟩ :=
    reduce (-84) (by norm_num) _ p (2 * t) c p rfl hp0 (by linarith) hr
  rcases reduced_21 h1 h2 hd with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩
  · obtain ⟨X, Y, hXY⟩ := hr'
    exact natAbs_rep (n := 21) (by exact_mod_cast hXY)
  · exfalso
    obtain ⟨u, v, hu, hv, hm⟩ := rep_mod_nat (a := 2) (b := 1) (c := 11) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num : 0 < 21) (hr')
    have hval := vals_21_2_1 u hu v hv
    simp only at hval
    generalize (2 * u ^ 2 + 2 * 1 * u * v + 11 * v ^ 2) % (4 * 21) = r at hm hval
    omega
  · exfalso
    obtain ⟨u, v, hu, hv, hm⟩ := rep_mod_nat (a := 2) (b := 1) (c := 11) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num : 0 < 21) (rep_neg hr')
    have hval := vals_21_2_1 u hu v hv
    simp only at hval
    generalize (2 * u ^ 2 + 2 * 1 * u * v + 11 * v ^ 2) % (4 * 21) = r at hm hval
    omega
  · exfalso
    obtain ⟨u, v, hu, hv, hm⟩ := rep_mod_nat (a := 3) (b := 0) (c := 7) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num : 0 < 21) (hr')
    have hval := vals_21_3_0 u hu v hv
    simp only at hval
    generalize (3 * u ^ 2 + 2 * 0 * u * v + 7 * v ^ 2) % (4 * 21) = r at hm hval
    omega
  · exfalso
    obtain ⟨u, v, hu, hv, hm⟩ := rep_mod_nat (a := 5) (b := 2) (c := 5) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num : 0 < 21) (hr')
    have hval := vals_21_5_2 u hu v hv
    simp only at hval
    generalize (5 * u ^ 2 + 2 * 2 * u * v + 5 * v ^ 2) % (4 * 21) = r at hm hval
    omega
  · exfalso
    obtain ⟨u, v, hu, hv, hm⟩ := rep_mod_nat (a := 5) (b := 2) (c := 5) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num : 0 < 21) (rep_neg hr')
    have hval := vals_21_5_2 u hu v hv
    simp only at hval
    generalize (5 * u ^ 2 + 2 * 2 * u * v + 5 * v ^ 2) % (4 * 21) = r at hm hval
    omega

end TuringTask
