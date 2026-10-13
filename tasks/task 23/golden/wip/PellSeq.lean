import Mathlib

/-!
# Powers of a unit `a + b √D`

For natural numbers `D`, `a`, `b` put `pX k + pY k √D = (a + b √D) ^ k`, computed by the
recursion `pX (k + 1) = a pX k + D b pY k`, `pY (k + 1) = b pX k + a pY k`.
If `a ^ 2 - D b ^ 2 = σ` with `σ = ±1`:
* `norm_pow`: `pX k ^ 2 - D pY k ^ 2 = σ ^ k`;
* `pY_dvd_pY`: `pY j ∣ pY k` for `j ∣ k`, and `prime_dvd_pY_gcd`: a prime dividing `pY m` and
  `pY n` divides `pY (gcd m n)`;
* `pY_eq`: `pY k = b (k a ^ (k - 1) + b ^ 2 R)`;
* `smooth_index`: if all prime factors of `pY k` divide `P`, every prime `q ∣ P` divides some
  `pY r` with `r ≤ R`, and the prime factors of `b` are at most `R`, then the prime factors of
  `k` are at most `R`;
* `not_dvd_of_split`: an explicit factor of `pY j` prime to `P` excludes `j ∣ k`.
-/

namespace TuringTask

/-- `pellP D a b k = (X, Y)` with `X + Y √D = (a + b √D) ^ k`. -/
def pellP (D a b : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | k + 1 =>
    match pellP D a b k with
    | (x, y) => (a * x + D * b * y, b * x + a * y)

/-- The rational coordinate of `(a + b √D) ^ k`. -/
def pX (D a b k : ℕ) : ℕ := (pellP D a b k).1

/-- The `√D`-coordinate of `(a + b √D) ^ k`. -/
def pY (D a b k : ℕ) : ℕ := (pellP D a b k).2

/-- Every prime factor of `n` divides `P`. -/
def Smooth (P n : ℕ) : Prop := ∀ q : ℕ, q.Prime → q ∣ n → q ∣ P

variable {D a b : ℕ}

@[simp] lemma pX_zero : pX D a b 0 = 1 := rfl

@[simp] lemma pY_zero : pY D a b 0 = 0 := rfl

lemma pX_succ (k : ℕ) : pX D a b (k + 1) = a * pX D a b k + D * b * pY D a b k := by
  unfold pX pY
  rw [pellP]

lemma pY_succ (k : ℕ) : pY D a b (k + 1) = b * pX D a b k + a * pY D a b k := by
  unfold pX pY
  rw [pellP]

@[simp] lemma pX_one : pX D a b 1 = a := by rw [pX_succ]; simp

@[simp] lemma pY_one : pY D a b 1 = b := by rw [pY_succ]; simp

lemma norm_pow {σ : ℤ} (hσ : (a : ℤ) ^ 2 - D * b ^ 2 = σ) (k : ℕ) :
    (pX D a b k : ℤ) ^ 2 - D * (pY D a b k : ℤ) ^ 2 = σ ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pX_succ, pY_succ]
    push_cast
    linear_combination ((pX D a b k : ℤ) ^ 2 - D * (pY D a b k : ℤ) ^ 2) * hσ + σ * ih

lemma pX_add (m n : ℕ) :
    pX D a b (m + n) = pX D a b m * pX D a b n + D * pY D a b m * pY D a b n ∧
      pY D a b (m + n) = pX D a b m * pY D a b n + pY D a b m * pX D a b n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, pX_succ, pY_succ, pX_succ, pY_succ, ih.1, ih.2]
    constructor <;> ring

lemma pX_pos (ha : 1 ≤ a) (k : ℕ) : 1 ≤ pX D a b k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pX_succ]
    nlinarith [Nat.zero_le (D * b * pY D a b k)]

lemma pY_strictMono (ha : 1 ≤ a) (hb : 1 ≤ b) : StrictMono (pY D a b) := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  rw [pY_succ]
  nlinarith [pX_pos (D := D) (b := b) ha k]

lemma pY_pos (ha : 1 ≤ a) (hb : 1 ≤ b) {k : ℕ} (hk : 0 < k) : 0 < pY D a b k := by
  have := pY_strictMono (D := D) ha hb hk
  simpa using this

lemma pY_dvd_pY_mul (m t : ℕ) : pY D a b m ∣ pY D a b (m * t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [mul_add, mul_one, (pX_add _ _).2]
    exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_left ih _)

lemma pY_dvd_pY {j k : ℕ} (h : j ∣ k) : pY D a b j ∣ pY D a b k := by
  obtain ⟨t, rfl⟩ := h
  exact pY_dvd_pY_mul j t

lemma not_dvd_pX_of_dvd_pY {σ : ℤ} (hσ : (a : ℤ) ^ 2 - D * b ^ 2 = σ) (hσ1 : σ = 1 ∨ σ = -1)
    {q n : ℕ} (hq : q.Prime) (h1 : q ∣ pX D a b n) (h2 : q ∣ pY D a b n) : False := by
  have hn := norm_pow hσ n
  have hd : (q : ℤ) ∣ σ ^ n := by
    rw [← hn]
    exact dvd_sub (dvd_pow (Int.natCast_dvd_natCast.mpr h1) (by norm_num))
      (dvd_mul_of_dvd_right (dvd_pow (Int.natCast_dvd_natCast.mpr h2) (by norm_num)) _)
  have h1' : (q : ℤ) ∣ 1 := by
    rcases hσ1 with rfl | rfl
    · simpa using hd
    · rcases neg_one_pow_eq_or ℤ n with h | h <;> rw [h] at hd
      · exact hd
      · exact (dvd_neg).mp hd
  have := Int.eq_one_of_dvd_one (by positivity) h1'
  exact hq.one_lt.ne' (by exact_mod_cast this)

lemma prime_dvd_pY_sub {σ : ℤ} (hσ : (a : ℤ) ^ 2 - D * b ^ 2 = σ) (hσ1 : σ = 1 ∨ σ = -1)
    {q m n : ℕ} (hq : q.Prime) (hm : q ∣ pY D a b m) (hn : q ∣ pY D a b n) (hnm : n ≤ m) :
    q ∣ pY D a b (m - n) := by
  have hsum := (pX_add (D := D) (a := a) (b := b) (m - n) n).2
  rw [Nat.sub_add_cancel hnm] at hsum
  rw [hsum] at hm
  have h2 : q ∣ pY D a b (m - n) * pX D a b n :=
    (Nat.dvd_add_right (dvd_mul_of_dvd_right hn _)).mp hm
  rcases (Nat.Prime.dvd_mul hq).mp h2 with h | h
  · exact h
  · exact (not_dvd_pX_of_dvd_pY hσ hσ1 hq h hn).elim

lemma prime_dvd_pY_gcd {σ : ℤ} (hσ : (a : ℤ) ^ 2 - D * b ^ 2 = σ) (hσ1 : σ = 1 ∨ σ = -1)
    {q : ℕ} (hq : q.Prime) : ∀ m n : ℕ, q ∣ pY D a b m → q ∣ pY D a b n →
      q ∣ pY D a b (Nat.gcd m n) := by
  intro m n
  induction m, n using Nat.gcd.induction with
  | H0 n => intro _ hn; simpa using hn
  | H1 m n hm ih =>
    intro h1 h2
    rw [Nat.gcd_rec]
    refine ih ?_ h1
    have h3 : q ∣ pY D a b (m * (n / m)) := dvd_trans h1 (pY_dvd_pY_mul m (n / m))
    rw [Nat.mod_eq_sub_mul_div]
    exact prime_dvd_pY_sub hσ hσ1 hq h2 h3 (Nat.mul_div_le n m)

/-- `pX k ≡ a ^ k (mod b ^ 2)` and `pY k = b (k a ^ (k - 1) + b ^ 2 R)`. -/
lemma pY_eq (k : ℕ) : ∃ S R : ℕ, pX D a b k = a ^ k + b ^ 2 * S ∧
    pY D a b k = b * (k * a ^ (k - 1) + b ^ 2 * R) := by
  induction k with
  | zero => exact ⟨0, 0, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨S, R, hS, hR⟩ := ih
    refine ⟨a * S + D * (k * a ^ (k - 1) + b ^ 2 * R), S + a * R, ?_, ?_⟩
    · rw [pX_succ, hS, hR]; ring
    · rw [pY_succ, hS, hR]
      rcases k with _ | k
      · simp; ring
      · simp only [Nat.add_sub_cancel]; ring

lemma not_prime_dvd_a_b {σ : ℤ} (hσ : (a : ℤ) ^ 2 - D * b ^ 2 = σ) (hσ1 : σ = 1 ∨ σ = -1)
    {q : ℕ} (hq : q.Prime) (ha : q ∣ a) (hb : q ∣ b) : False := by
  have h := not_dvd_pX_of_dvd_pY hσ hσ1 (n := 1) hq
  simp only [pX_one, pY_one] at h
  exact h ha hb

/-- If `k` is prime to `b` and every prime factor of `pY k` divides `b`, then `k = 1`. -/
lemma eq_one_of_primes_dvd {σ : ℤ} (hσ : (a : ℤ) ^ 2 - D * b ^ 2 = σ) (hσ1 : σ = 1 ∨ σ = -1)
    (ha : 1 ≤ a) (hb : 1 ≤ b) {k : ℕ} (hcop : Nat.Coprime k b)
    (hall : ∀ q, q.Prime → q ∣ pY D a b k → q ∣ b) : k = 1 := by
  obtain ⟨S, R, -, hR⟩ := pY_eq (D := D) (a := a) (b := b) k
  by_cases hU : k * a ^ (k - 1) + b ^ 2 * R = 1
  · have h1 : pY D a b k = pY D a b 1 := by rw [hR, hU, pY_one, mul_one]
    exact (pY_strictMono (D := D) ha hb).injective h1
  · obtain ⟨q, hq, hqU⟩ := Nat.exists_prime_and_dvd hU
    have hqY : q ∣ pY D a b k := by rw [hR]; exact dvd_mul_of_dvd_right hqU _
    have hqb := hall q hq hqY
    have h2 : q ∣ k * a ^ (k - 1) :=
      (Nat.dvd_add_left (dvd_mul_of_dvd_left (dvd_pow hqb (by norm_num)) _)).mp hqU
    rcases (Nat.Prime.dvd_mul hq).mp h2 with h | h
    · exact (hq.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop h hqb)).elim
    · exact (not_prime_dvd_a_b hσ hσ1 hq (hq.dvd_of_dvd_pow h) hqb).elim

lemma Smooth.of_dvd {P n d : ℕ} (hs : Smooth P n) (hd : d ∣ n) : Smooth P d :=
  fun q hq h => hs q hq (dvd_trans h hd)

/-- The prime factors of an index `k` with `pY k` smooth are at most `R`. -/
theorem smooth_index {σ : ℤ} (hσ : (a : ℤ) ^ 2 - D * b ^ 2 = σ) (hσ1 : σ = 1 ∨ σ = -1)
    (ha : 1 ≤ a) (hb : 1 ≤ b) {P R k : ℕ}
    (hrank : ∀ q, q.Prime → q ∣ P → ∃ r, 0 < r ∧ r ≤ R ∧ q ∣ pY D a b r)
    (hbR : ∀ p, p.Prime → p ∣ b → p ≤ R) (hs : Smooth P (pY D a b k)) :
    ∀ p, p.Prime → p ∣ k → p ≤ R := by
  intro p hp hpk
  by_contra hlt
  push Not at hlt
  have hsp : Smooth P (pY D a b p) := hs.of_dvd (pY_dvd_pY hpk)
  have hpb : ¬ p ∣ b := fun h => by have := hbR p hp h; omega
  have hcop : Nat.Coprime p b := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpb
  have hall : ∀ q, q.Prime → q ∣ pY D a b p → q ∣ b := by
    intro q hq hqY
    obtain ⟨r, hr0, hrR, hqr⟩ := hrank q hq (hsp q hq hqY)
    have hpr : ¬ p ∣ r := fun h => by have := Nat.le_of_dvd hr0 h; omega
    have hg : Nat.gcd p r = 1 := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpr
    have := prime_dvd_pY_gcd hσ hσ1 hq p r hqY hqr
    rwa [hg, pY_one] at this
  have := eq_one_of_primes_dvd hσ hσ1 ha hb hcop hall
  exact hp.one_lt.ne' this

/-- An explicit factor `m ≥ 2` of `pY j` that is prime to `P` shows `¬ j ∣ k`. -/
lemma not_dvd_of_split {P k j s m : ℕ} (hs : Smooth P (pY D a b k))
    (hY : pY D a b j = s * m) (hm : 2 ≤ m) (hc : Nat.Coprime m P) : ¬ j ∣ k := by
  intro hj
  obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  have hqY : q ∣ pY D a b k := dvd_trans (hY ▸ dvd_mul_of_dvd_right hqm s) (pY_dvd_pY hj)
  have hqP := hs q hq hqY
  exact hq.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc hqm hqP)

end TuringTask
