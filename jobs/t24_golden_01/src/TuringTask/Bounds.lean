import Mathlib
import TuringTask.FibRing

/-!
# Periods and zeros modulo prime powers, and bounds for odd moduli

* `per_two_pow`, `per_three_pow`, `zer_three_pow`, `big_pow`: periods and zeros modulo `2 ^ a`,
  `3 ^ b` and `p ^ e` for primes `p ≥ 7`, by lifting (`per_pow`, `zer_pow`) and `apparition`.
* `invP`: every odd `m` has a period `2 ^ s t` with `2 ^ s t ≤ 4 m` and `t ≤ m`; equality in
  the first bound forces `m = 5 ^ c` with `c ≥ 1`, and `t = m` forces `m = 5 ^ c`.
* `invZ`: every odd `m` has a zero `2 ^ s t` with `3 * 2 ^ s t ≤ 4 m` and `t ≤ m`; equality in
  the first bound forces `m = 3 ^ e 5 ^ c` with `e ≥ 1`, and `e = 1` when `3 ∤ t`.
Both are proved by induction over coprime prime powers (`Nat.recOnPosPrimePosCoprime`), with
`s = max s₁ s₂` and `t = t₁ t₂` for a product.
-/

namespace TuringTask

lemma per_two_pow {a : ℕ} (ha : 1 ≤ a) : Per (2 ^ a) (3 * 2 ^ (a - 1)) := by
  have := per_pow per_2 (a - 1)
  rwa [Nat.sub_add_cancel ha, mul_comm] at this

lemma per_three_pow {b : ℕ} (hb : 1 ≤ b) : Per (3 ^ b) (8 * 3 ^ (b - 1)) := by
  have := per_pow per_3 (b - 1)
  rwa [Nat.sub_add_cancel hb, mul_comm] at this

lemma zer_three_pow {b : ℕ} (hb : 1 ≤ b) : Zer (3 ^ b) (4 * 3 ^ (b - 1)) := by
  have := zer_pow zer_3 (b - 1)
  rwa [Nat.sub_add_cancel hb, mul_comm] at this

lemma prime_cases {p : ℕ} (hp : p.Prime) : p = 2 ∨ p = 3 ∨ p = 5 ∨ 7 ≤ p := by
  by_contra h
  push Not at h
  obtain ⟨h2, h3, h5, h7⟩ := h
  interval_cases p <;> first | omega | (norm_num at hp)

/-- Periods and zeros modulo `p ^ e` for a prime `p ≥ 7`. -/
lemma big_pow {p e : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (he : 1 ≤ e) :
    (Per (p ^ e) (p ^ (e - 1) * (p - 1)) ∧ Zer (p ^ e) (p ^ (e - 1) * (p - 1))) ∨
      (Per (p ^ e) (p ^ (e - 1) * (2 * (p + 1))) ∧ Zer (p ^ e) (p ^ (e - 1) * (p + 1))) := by
  rcases apparition hp h7 with h | ⟨h1, h2⟩
  · left
    have := per_pow h (e - 1)
    rw [Nat.sub_add_cancel he] at this
    exact ⟨this, this.zer⟩
  · right
    have a1 := per_pow h1 (e - 1)
    have a2 := zer_pow h2 (e - 1)
    rw [Nat.sub_add_cancel he] at a1 a2
    exact ⟨a1, a2⟩

lemma per_of_dvd {m k k' : ℕ} (h : Per m k) (hd : k ∣ k') : Per m k' := by
  obtain ⟨t, rfl⟩ := hd; exact per_mul h t

lemma zer_of_dvd {m k k' : ℕ} (h : Zer m k) (hd : k ∣ k') : Zer m k' := by
  obtain ⟨t, rfl⟩ := hd; exact zer_mul h t

/-- The invariant for periods modulo an odd `m`. -/
def InvP (m : ℕ) : Prop :=
  ∃ s t : ℕ, 0 < t ∧ Per m (2 ^ s * t) ∧ 2 ^ s * t ≤ 4 * m ∧ t ≤ m ∧
    (2 ^ s * t = 4 * m → ∃ c, 1 ≤ c ∧ m = 5 ^ c) ∧ (t = m → ∃ c, m = 5 ^ c)

/-- The invariant for zeros modulo an odd `m`. -/
def InvZ (m : ℕ) : Prop :=
  ∃ s t : ℕ, 0 < t ∧ Zer m (2 ^ s * t) ∧ 3 * (2 ^ s * t) ≤ 4 * m ∧ t ≤ m ∧
    (3 * (2 ^ s * t) = 4 * m → ∃ e c, 1 ≤ e ∧ m = 3 ^ e * 5 ^ c ∧ (¬ 3 ∣ t → e = 1)) ∧
    (t = m → ∃ c, m = 5 ^ c)

lemma pow_lt_pow_succ' {p n : ℕ} (hp : 2 ≤ p) : p ^ (n - 1) < p ^ n ∨ n = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · right; rfl
  · left; exact Nat.pow_lt_pow_right (by omega) (by omega)

lemma invP_prime_pow {p n : ℕ} (hp : p.Prime) (hn : 0 < n) (hodd : Odd (p ^ n)) :
    InvP (p ^ n) := by
  have hpn : p ^ n = p ^ (n - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hn]
  have hp1 : 0 < p ^ (n - 1) := pow_pos hp.pos _
  rcases prime_cases hp with rfl | rfl | rfl | h7
  · exfalso
    rw [Nat.odd_iff] at hodd
    have : 2 ∣ 2 ^ n := dvd_pow_self 2 hn.ne'
    omega
  · refine ⟨3, 3 ^ (n - 1), hp1, ?_, ?_, ?_, ?_, ?_⟩
    · have := per_three_pow hn; rwa [show (8 : ℕ) = 2 ^ 3 from rfl] at this
    · nlinarith [hpn]
    · nlinarith [hpn]
    · intro h; rw [hpn] at h; omega
    · intro h; rw [hpn] at h; omega
  · refine ⟨2, 5 ^ n, pow_pos (by norm_num) _, ?_, ?_, le_refl _, ?_, ?_⟩
    · exact per_five_pow n
    · omega
    · intro _; exact ⟨n, hn, rfl⟩
    · intro _; exact ⟨n, rfl⟩
  · rcases big_pow hp h7 hn with ⟨h1, -⟩ | ⟨h1, -⟩
    · refine ⟨0, p ^ (n - 1) * (p - 1), Nat.mul_pos hp1 (by omega), by simpa using h1, ?_, ?_,
        ?_, ?_⟩
      · simp only [pow_zero, one_mul]
        calc p ^ (n - 1) * (p - 1) ≤ p ^ (n - 1) * (4 * p) := Nat.mul_le_mul_left _ (by omega)
          _ = 4 * p ^ n := by rw [hpn]; ring
      · rw [hpn]; exact Nat.mul_le_mul_left _ (by omega)
      · intro h
        have : p ^ (n - 1) * (p - 1) = p ^ (n - 1) * (4 * p) := by
          simp only [pow_zero, one_mul] at h; rw [h, hpn]; ring
        have := Nat.eq_of_mul_eq_mul_left hp1 this
        omega
      · intro h; rw [hpn] at h
        have := Nat.eq_of_mul_eq_mul_left hp1 h
        omega
    · obtain ⟨r, hr⟩ : ∃ r, p + 1 = 2 * r := by
        rcases hp.eq_two_or_odd' with h | ⟨r, hr⟩
        · omega
        · exact ⟨r + 1, by omega⟩
      refine ⟨2, p ^ (n - 1) * r, Nat.mul_pos hp1 (by omega), ?_, ?_, ?_, ?_, ?_⟩
      · have : 2 ^ 2 * (p ^ (n - 1) * r) = p ^ (n - 1) * (2 * (p + 1)) := by rw [hr]; ring
        rw [this]; exact h1
      · calc 2 ^ 2 * (p ^ (n - 1) * r) = p ^ (n - 1) * (4 * r) := by ring
          _ ≤ p ^ (n - 1) * (4 * p) := Nat.mul_le_mul_left _ (by omega)
          _ = 4 * p ^ n := by rw [hpn]; ring
      · rw [hpn]; exact Nat.mul_le_mul_left _ (by omega)
      · intro h
        have : p ^ (n - 1) * (4 * r) = p ^ (n - 1) * (4 * p) := by
          calc p ^ (n - 1) * (4 * r) = 2 ^ 2 * (p ^ (n - 1) * r) := by ring
            _ = 4 * p ^ n := h
            _ = p ^ (n - 1) * (4 * p) := by rw [hpn]; ring
        have := Nat.eq_of_mul_eq_mul_left hp1 this
        omega
      · intro h; rw [hpn] at h
        have := Nat.eq_of_mul_eq_mul_left hp1 h
        omega

lemma invZ_prime_pow {p n : ℕ} (hp : p.Prime) (hn : 0 < n) (hodd : Odd (p ^ n)) :
    InvZ (p ^ n) := by
  have hpn : p ^ n = p ^ (n - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hn]
  have hp1 : 0 < p ^ (n - 1) := pow_pos hp.pos _
  rcases prime_cases hp with rfl | rfl | rfl | h7
  · exfalso
    rw [Nat.odd_iff] at hodd
    have : 2 ∣ 2 ^ n := dvd_pow_self 2 hn.ne'
    omega
  · refine ⟨2, 3 ^ (n - 1), hp1, ?_, ?_, ?_, ?_, ?_⟩
    · exact zer_three_pow hn
    · nlinarith [hpn]
    · nlinarith [hpn]
    · intro _
      refine ⟨n, 0, hn, by simp, fun h3 => ?_⟩
      by_contra hn1
      exact h3 (dvd_pow_self 3 (by omega))
    · intro h; rw [hpn] at h; omega
  · refine ⟨0, 5 ^ n, pow_pos (by norm_num) _, by simpa using zer_five_pow n, ?_, le_refl _,
      ?_, ?_⟩
    · simp only [pow_zero, one_mul]; omega
    · intro h; simp at h
    · intro _; exact ⟨n, rfl⟩
  · have hodd' : Odd p := hp.eq_two_or_odd'.resolve_left (by omega)
    have gen : ∀ r q : ℕ, 3 * (2 * r) ≤ 4 * p → 3 * (2 * r) ≠ 4 * p → r < p → 0 < r →
        Zer (p ^ n) (p ^ (n - 1) * (2 * r)) → InvZ (p ^ n) := by
      intro r _ hle hne hlt hr0 hz
      refine ⟨1, p ^ (n - 1) * r, Nat.mul_pos hp1 hr0, ?_, ?_, ?_, ?_, ?_⟩
      · rw [show 2 ^ 1 * (p ^ (n - 1) * r) = p ^ (n - 1) * (2 * r) by ring]; exact hz
      · calc 3 * (2 ^ 1 * (p ^ (n - 1) * r)) = p ^ (n - 1) * (3 * (2 * r)) := by ring
          _ ≤ p ^ (n - 1) * (4 * p) := Nat.mul_le_mul_left _ hle
          _ = 4 * p ^ n := by rw [hpn]; ring
      · rw [hpn]; exact Nat.mul_le_mul_left _ hlt.le
      · intro h
        exfalso
        apply hne
        apply Nat.eq_of_mul_eq_mul_left hp1
        calc p ^ (n - 1) * (3 * (2 * r)) = 3 * (2 ^ 1 * (p ^ (n - 1) * r)) := by ring
          _ = 4 * p ^ n := h
          _ = p ^ (n - 1) * (4 * p) := by rw [hpn]; ring
      · intro h; rw [hpn] at h
        have := Nat.eq_of_mul_eq_mul_left hp1 h
        omega
    rcases big_pow hp h7 hn with ⟨-, h1⟩ | ⟨-, h1⟩
    · obtain ⟨r, hr⟩ := hodd'
      exact gen r 0 (by omega) (by omega) (by omega) (by omega)
        (by rw [show 2 * r = p - 1 by omega]; exact h1)
    · obtain ⟨r, hr⟩ := hodd'
      exact gen (r + 1) 0 (by omega) (by omega) (by omega) (by omega)
        (by rw [show 2 * (r + 1) = p + 1 by omega]; exact h1)

lemma eq_of_le_of_mul_eq {X Y A B : ℕ} (hX : X ≤ A) (hY : Y ≤ B) (hA : 0 < A) (hB : 0 < B)
    (h : X * Y = A * B) : X = A ∧ Y = B := by
  have h1 : X * Y ≤ X * B := Nat.mul_le_mul_left _ hY
  have h2 : X * B ≤ A * B := Nat.mul_le_mul_right _ hX
  have hXB : X * B = A * B := le_antisymm h2 (h ▸ h1)
  have hXA : X = A := Nat.eq_of_mul_eq_mul_right hB hXB
  subst hXA
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hA h⟩

lemma invP_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (Ha : InvP a) (Hb : InvP b) : InvP (a * b) := by
  obtain ⟨s1, t1, ht1, hP1, hb1, ht1m, he1, hq1⟩ := Ha
  obtain ⟨s2, t2, ht2, hP2, hb2, ht2m, he2, hq2⟩ := Hb
  have key : ∀ (s1 t1 s2 t2 : ℕ) (a b : ℕ), 0 < a → 0 < b → s2 ≤ s1 →
      2 ^ s1 * t1 ≤ 4 * a → t2 ≤ b →
      (2 ^ s1 * t1 = 4 * a → ∃ c, 1 ≤ c ∧ a = 5 ^ c) → (t2 = b → ∃ c, b = 5 ^ c) →
      2 ^ s1 * (t1 * t2) ≤ 4 * (a * b) ∧
      (2 ^ s1 * (t1 * t2) = 4 * (a * b) → ∃ c, 1 ≤ c ∧ a * b = 5 ^ c) := by
    intro s1 t1 s2 t2 a b ha hb _ hb1 ht2m he1 hq2
    refine ⟨?_, fun h => ?_⟩
    · calc 2 ^ s1 * (t1 * t2) = (2 ^ s1 * t1) * t2 := by ring
        _ ≤ (4 * a) * b := Nat.mul_le_mul hb1 ht2m
        _ = 4 * (a * b) := by ring
    · have h' : (2 ^ s1 * t1) * t2 = (4 * a) * b := by rw [← mul_assoc] at h; linarith
      obtain ⟨e1, e2⟩ := eq_of_le_of_mul_eq hb1 ht2m (by omega) hb h'
      obtain ⟨c1, hc1, rfl⟩ := he1 e1
      obtain ⟨c2, rfl⟩ := hq2 e2
      exact ⟨c1 + c2, by omega, by ring⟩
  refine ⟨max s1 s2, t1 * t2, Nat.mul_pos ht1 ht2, ?_, ?_, Nat.mul_le_mul ht1m ht2m, ?_, ?_⟩
  · rw [per_mul_iff hab]
    constructor
    · refine per_of_dvd hP1 ⟨2 ^ (max s1 s2 - s1) * t2, ?_⟩
      rw [← Nat.sub_add_cancel (le_max_left s1 s2), pow_add]
      simp only [Nat.add_sub_cancel]; ring
    · refine per_of_dvd hP2 ⟨2 ^ (max s1 s2 - s2) * t1, ?_⟩
      rw [← Nat.sub_add_cancel (le_max_right s1 s2), pow_add]
      simp only [Nat.add_sub_cancel]; ring
  · rcases le_total s2 s1 with h | h
    · rw [max_eq_left h]; exact (key s1 t1 s2 t2 a b ha hb h hb1 ht2m he1 hq2).1
    · rw [max_eq_right h, mul_comm t1 t2, mul_comm a b]
      exact (key s2 t2 s1 t1 b a hb ha h hb2 ht1m he2 hq1).1
  · intro heq
    rcases le_total s2 s1 with h | h
    · rw [max_eq_left h] at heq; exact (key s1 t1 s2 t2 a b ha hb h hb1 ht2m he1 hq2).2 heq
    · rw [max_eq_right h, mul_comm t1 t2, mul_comm a b] at heq
      rw [mul_comm a b]
      exact (key s2 t2 s1 t1 b a hb ha h hb2 ht1m he2 hq1).2 heq
  · intro heq
    obtain ⟨e1, e2⟩ := eq_of_le_of_mul_eq ht1m ht2m ha hb heq
    obtain ⟨c1, rfl⟩ := hq1 e1
    obtain ⟨c2, rfl⟩ := hq2 e2
    exact ⟨c1 + c2, by ring⟩

lemma invZ_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (Ha : InvZ a) (Hb : InvZ b) : InvZ (a * b) := by
  obtain ⟨s1, t1, ht1, hP1, hb1, ht1m, he1, hq1⟩ := Ha
  obtain ⟨s2, t2, ht2, hP2, hb2, ht2m, he2, hq2⟩ := Hb
  have key : ∀ (s1 t1 s2 t2 : ℕ) (a b : ℕ), 0 < a → 0 < b → s2 ≤ s1 →
      3 * (2 ^ s1 * t1) ≤ 4 * a → t2 ≤ b →
      (3 * (2 ^ s1 * t1) = 4 * a → ∃ e c, 1 ≤ e ∧ a = 3 ^ e * 5 ^ c ∧ (¬ 3 ∣ t1 → e = 1)) →
      (t2 = b → ∃ c, b = 5 ^ c) →
      3 * (2 ^ s1 * (t1 * t2)) ≤ 4 * (a * b) ∧
      (3 * (2 ^ s1 * (t1 * t2)) = 4 * (a * b) →
        ∃ e c, 1 ≤ e ∧ a * b = 3 ^ e * 5 ^ c ∧ (¬ 3 ∣ t1 * t2 → e = 1)) := by
    intro s1 t1 s2 t2 a b ha hb _ hb1 ht2m he1 hq2
    refine ⟨?_, fun h => ?_⟩
    · calc 3 * (2 ^ s1 * (t1 * t2)) = (3 * (2 ^ s1 * t1)) * t2 := by ring
        _ ≤ (4 * a) * b := Nat.mul_le_mul hb1 ht2m
        _ = 4 * (a * b) := by ring
    · have h' : (3 * (2 ^ s1 * t1)) * t2 = (4 * a) * b := by
        calc (3 * (2 ^ s1 * t1)) * t2 = 3 * (2 ^ s1 * (t1 * t2)) := by ring
          _ = 4 * (a * b) := h
          _ = (4 * a) * b := by ring
      obtain ⟨e1, e2⟩ := eq_of_le_of_mul_eq hb1 ht2m (by omega) hb h'
      obtain ⟨e, c1, he, rfl, h3⟩ := he1 e1
      obtain ⟨c2, rfl⟩ := hq2 e2
      exact ⟨e, c1 + c2, he, by ring, fun h3' => h3 (fun hd => h3' (Dvd.dvd.mul_right hd _))⟩
  refine ⟨max s1 s2, t1 * t2, Nat.mul_pos ht1 ht2, ?_, ?_, Nat.mul_le_mul ht1m ht2m, ?_, ?_⟩
  · rw [zer_mul_iff hab]
    constructor
    · refine zer_of_dvd hP1 ⟨2 ^ (max s1 s2 - s1) * t2, ?_⟩
      rw [← Nat.sub_add_cancel (le_max_left s1 s2), pow_add]
      simp only [Nat.add_sub_cancel]; ring
    · refine zer_of_dvd hP2 ⟨2 ^ (max s1 s2 - s2) * t1, ?_⟩
      rw [← Nat.sub_add_cancel (le_max_right s1 s2), pow_add]
      simp only [Nat.add_sub_cancel]; ring
  · rcases le_total s2 s1 with h | h
    · rw [max_eq_left h]; exact (key s1 t1 s2 t2 a b ha hb h hb1 ht2m he1 hq2).1
    · rw [max_eq_right h, mul_comm t1 t2, mul_comm a b]
      exact (key s2 t2 s1 t1 b a hb ha h hb2 ht1m he2 hq1).1
  · intro heq
    rcases le_total s2 s1 with h | h
    · rw [max_eq_left h] at heq; exact (key s1 t1 s2 t2 a b ha hb h hb1 ht2m he1 hq2).2 heq
    · rw [max_eq_right h, mul_comm t1 t2, mul_comm a b] at heq
      rw [mul_comm a b, mul_comm t1 t2]
      exact (key s2 t2 s1 t1 b a hb ha h hb2 ht1m he2 hq1).2 heq
  · intro heq
    obtain ⟨e1, e2⟩ := eq_of_le_of_mul_eq ht1m ht2m ha hb heq
    obtain ⟨c1, rfl⟩ := hq1 e1
    obtain ⟨c2, rfl⟩ := hq2 e2
    exact ⟨c1 + c2, by ring⟩

theorem invP_odd : ∀ m : ℕ, Odd m → InvP m := by
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn => exact fun h => invP_prime_pow hp hn h
  | zero => intro h; simp at h
  | one =>
    intro _
    exact ⟨0, 1, by norm_num, per_one _, by norm_num, le_refl _, by norm_num,
      fun _ => ⟨0, rfl⟩⟩
  | coprime a b ha hb hab iha ihb =>
    intro h
    have hoa : Odd a := (Nat.odd_mul.mp h).1
    have hob : Odd b := (Nat.odd_mul.mp h).2
    exact invP_mul (by omega) (by omega) hab (iha hoa) (ihb hob)

theorem invZ_odd : ∀ m : ℕ, Odd m → InvZ m := by
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn => exact fun h => invZ_prime_pow hp hn h
  | zero => intro h; simp at h
  | one =>
    intro _
    exact ⟨0, 1, by norm_num, by simp [Zer], by norm_num, le_refl _, by norm_num,
      fun _ => ⟨0, rfl⟩⟩
  | coprime a b ha hb hab iha ihb =>
    intro h
    have hoa : Odd a := (Nat.odd_mul.mp h).1
    have hob : Odd b := (Nat.odd_mul.mp h).2
    exact invZ_mul (by omega) (by omega) hab (iha hoa) (ihb hob)

end TuringTask
