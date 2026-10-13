import Mathlib

/-!
# Periods and zeros of the Fibonacci numbers modulo `m`

* `Per m k`: `F_k ≡ 0` and `F_(k+1) ≡ 1 (mod m)`, the statement of the task.
* `Zer m k`: `m ∣ F_k`.
* `per_shift`: a period shifts every index, so periods are closed under sums, multiples and
  differences, and the least period divides every period (`per_dvd_of_min`). The same holds for
  zeros by `Nat.fib_gcd` (`zer_dvd_of_min`).
* `per_mul_iff`, `zer_mul_iff`: coprime moduli combine.
* the periods modulo `2, 3, 4, 5, 8` are `3, 8, 6, 20, 12` and the first zeros modulo
  `2, 3, 4, 5` are `3, 4, 6, 5`.
-/

namespace TuringTask

/-- `k` is a period of the Fibonacci numbers modulo `m`. -/
def Per (m k : ℕ) : Prop := Nat.fib k ≡ 0 [MOD m] ∧ Nat.fib (k + 1) ≡ 1 [MOD m]

/-- `m` divides `F_k`. -/
def Zer (m k : ℕ) : Prop := m ∣ Nat.fib k

variable {m a b k : ℕ}

lemma per_zero (m : ℕ) : Per m 0 := by
  simp [Per, Nat.ModEq]

lemma per_shift (h : Per m a) (c : ℕ) : Nat.fib (a + c) ≡ Nat.fib c [MOD m] := by
  rcases c with _ | c
  · simpa using h.1
  · rw [← add_assoc, Nat.fib_add]
    have := (h.1.mul_right (Nat.fib c)).add (h.2.mul_right (Nat.fib (c + 1)))
    simpa using this

lemma per_add (ha : Per m a) (hb : Per m b) : Per m (a + b) :=
  ⟨(per_shift ha b).trans hb.1, by rw [add_assoc]; exact (per_shift ha (b + 1)).trans hb.2⟩

lemma per_mul (h : Per m a) (t : ℕ) : Per m (a * t) := by
  induction t with
  | zero => simpa using per_zero m
  | succ t ih => rw [mul_add, mul_one]; exact per_add ih h

lemma per_sub (ha : Per m a) (hb : Per m b) (hab : a ≤ b) : Per m (b - a) := by
  have e1 := per_shift ha (b - a)
  have e2 := per_shift ha (b - a + 1)
  rw [Nat.add_sub_cancel' hab] at e1
  rw [← add_assoc, Nat.add_sub_cancel' hab] at e2
  exact ⟨e1.symm.trans hb.1, e2.symm.trans hb.2⟩

/-- The least positive period divides every period. -/
lemma per_dvd_of_min {P : ℕ} (hP : 0 < P) (h : Per m P)
    (hmin : ∀ k, 0 < k → k < P → ¬ Per m k) (hk : Per m k) : P ∣ k := by
  have hmod : Per m (k % P) := by
    rw [Nat.mod_eq_sub_mul_div]
    exact per_sub (per_mul h (k / P)) hk (Nat.mul_div_le k P)
  by_contra hd
  exact hmin (k % P) (Nat.pos_of_ne_zero fun h0 => hd (Nat.dvd_of_mod_eq_zero h0))
    (Nat.mod_lt k hP) hmod

lemma Per.of_dvd {d : ℕ} (h : Per m k) (hd : d ∣ m) : Per d k :=
  ⟨Nat.ModEq.of_dvd hd h.1, Nat.ModEq.of_dvd hd h.2⟩

lemma per_mul_iff {m₁ m₂ : ℕ} (hc : Nat.Coprime m₁ m₂) :
    Per (m₁ * m₂) k ↔ Per m₁ k ∧ Per m₂ k := by
  unfold Per
  rw [← Nat.modEq_and_modEq_iff_modEq_mul hc, ← Nat.modEq_and_modEq_iff_modEq_mul hc]
  tauto

lemma per_one (k : ℕ) : Per 1 k := ⟨Nat.modEq_one, Nat.modEq_one⟩

lemma Per.zer (h : Per m k) : Zer m k := (Nat.modEq_zero_iff_dvd).mp h.1

lemma zer_mul (h : Zer m a) (t : ℕ) : Zer m (a * t) :=
  dvd_trans h (Nat.fib_dvd a (a * t) (dvd_mul_right a t))

lemma zer_gcd (ha : Zer m a) (hb : Zer m b) : Zer m (Nat.gcd a b) := by
  unfold Zer
  rw [Nat.fib_gcd]
  exact Nat.dvd_gcd ha hb

/-- The least positive zero divides every zero. -/
lemma zer_dvd_of_min {Z : ℕ} (hZ : 0 < Z) (h : Zer m Z)
    (hmin : ∀ k, 0 < k → k < Z → ¬ Zer m k) (hk : Zer m k) : Z ∣ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact dvd_zero Z
  have hg := zer_gcd h hk
  have hpos : 0 < Nat.gcd Z k := Nat.gcd_pos_of_pos_left k hZ
  have hle : Nat.gcd Z k ≤ Z := Nat.le_of_dvd hZ (Nat.gcd_dvd_left Z k)
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact absurd hg (hmin _ hpos hlt)
  · rw [← heq]; exact Nat.gcd_dvd_right Z k

lemma Zer.of_dvd {d : ℕ} (h : Zer m k) (hd : d ∣ m) : Zer d k := dvd_trans hd h

lemma zer_mul_iff {m₁ m₂ : ℕ} (hc : Nat.Coprime m₁ m₂) :
    Zer (m₁ * m₂) k ↔ Zer m₁ k ∧ Zer m₂ k :=
  ⟨fun h => ⟨dvd_trans (dvd_mul_right _ _) h, dvd_trans (dvd_mul_left _ _) h⟩,
    fun h => hc.mul_dvd_of_dvd_of_dvd h.1 h.2⟩

/-! ### Small moduli -/

lemma per_2 : Per 2 3 := by unfold Per; decide
lemma per_3 : Per 3 8 := by unfold Per; decide
lemma per_4 : Per 4 6 := by unfold Per; decide
lemma per_5 : Per 5 20 := by unfold Per; decide
lemma per_8 : Per 8 12 := by unfold Per; decide

lemma per_2_dvd (h : Per 2 k) : 3 ∣ k :=
  per_dvd_of_min (by norm_num) per_2 (by
    intro j h1 h2; interval_cases j <;> (unfold Per; decide)) h

lemma per_3_dvd (h : Per 3 k) : 8 ∣ k :=
  per_dvd_of_min (by norm_num) per_3 (by
    intro j h1 h2; interval_cases j <;> (unfold Per; decide)) h

lemma per_4_dvd (h : Per 4 k) : 6 ∣ k :=
  per_dvd_of_min (by norm_num) per_4 (by
    intro j h1 h2; interval_cases j <;> (unfold Per; decide)) h

lemma per_5_dvd (h : Per 5 k) : 20 ∣ k :=
  per_dvd_of_min (by norm_num) per_5 (by
    intro j h1 h2; interval_cases j <;> (unfold Per; decide)) h

lemma per_8_dvd (h : Per 8 k) : 12 ∣ k :=
  per_dvd_of_min (by norm_num) per_8 (by
    intro j h1 h2; interval_cases j <;> (unfold Per; decide)) h

lemma zer_2 : Zer 2 3 := by unfold Zer; decide
lemma zer_3 : Zer 3 4 := by unfold Zer; decide
lemma zer_4 : Zer 4 6 := by unfold Zer; decide
lemma zer_5 : Zer 5 5 := by unfold Zer; decide

lemma zer_2_dvd (h : Zer 2 k) : 3 ∣ k :=
  zer_dvd_of_min (by norm_num) zer_2 (by
    intro j h1 h2; interval_cases j <;> (unfold Zer; decide)) h

lemma zer_3_dvd (h : Zer 3 k) : 4 ∣ k :=
  zer_dvd_of_min (by norm_num) zer_3 (by
    intro j h1 h2; interval_cases j <;> (unfold Zer; decide)) h

lemma zer_4_dvd (h : Zer 4 k) : 6 ∣ k :=
  zer_dvd_of_min (by norm_num) zer_4 (by
    intro j h1 h2; interval_cases j <;> (unfold Zer; decide)) h

lemma zer_5_dvd (h : Zer 5 k) : 5 ∣ k :=
  zer_dvd_of_min (by norm_num) zer_5 (by
    intro j h1 h2; interval_cases j <;> (unfold Zer; decide)) h

end TuringTask
