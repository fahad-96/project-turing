import Mathlib
import TuringTask.FibPer

/-!
# Fibonacci numbers in `ℤ[ω]`, `ω ^ 2 = ω + 1`

`Phi` is Mathlib's `QuadraticAlgebra ℤ 1 1` and `ω = ⟨0, 1⟩`, so `ω ^ (k + 1) = F_k + F_(k+1) ω`.
* `per_iff`, `zer_iff`: `Per m k` means `m ∣ ω ^ k - 1`, and `Zer m k` means `m ∣ im (ω ^ k)`.
* `pow_of_eq_add`: if `x = c + m u` and `p ∣ m`, then `x ^ p = c ^ p + p m v`.
* `per_lift`, `zer_lift`: for `p ∣ m`, a period (zero) modulo `m` times `p` is a period (zero)
  modulo `p m`; `per_pow`, `zer_pow` iterate this for prime powers.
* `fib_five_mul`: `F_(5k) = 25 F_k ^ 5 + 25 (-1) ^ k F_k ^ 3 + 5 F_k`, from the norm of `ω ^ k`.
* `five_pow_dvd_of_zer`, `zer_five_pow`: `5 ^ j ∣ F_k` exactly when `5 ^ j ∣ k`.
-/

namespace TuringTask

open QuadraticAlgebra

/-- `ℤ[ω]` with `ω ^ 2 = 1 + ω`. -/
abbrev Phi : Type := QuadraticAlgebra ℤ 1 1

/-- The element `ω`. -/
def om : Phi := ⟨0, 1⟩

lemma om_pow_succ (k : ℕ) : om ^ (k + 1) = ⟨(Nat.fib k : ℤ), (Nat.fib (k + 1) : ℤ)⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, ih]
    ext
    · simp [om]
    · simp [om, Nat.fib_add_two]

lemma im_om_pow (k : ℕ) : (om ^ k).im = Nat.fib k := by
  rcases k with _ | k
  · simp
  · rw [om_pow_succ]

lemma om_mul_om_sub_one : om * (om - 1) = 1 := by
  ext <;> simp [om]

lemma intCast_dvd_iff (c : ℤ) (x : Phi) : (c : Phi) ∣ x ↔ c ∣ x.re ∧ c ∣ x.im := by
  constructor
  · rintro ⟨w, rfl⟩
    simp
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    exact ⟨⟨u, v⟩, by ext <;> simp [hu, hv]⟩

lemma per_iff (m k : ℕ) : Per m k ↔ ((m : ℤ) : Phi) ∣ om ^ k - 1 := by
  have e : om ^ (k + 1) - om = om * (om ^ k - 1) := by ring
  have h1 : ((m : ℤ) : Phi) ∣ om ^ (k + 1) - om ↔ ((m : ℤ) : Phi) ∣ om ^ k - 1 := by
    rw [e]
    constructor
    · intro h
      have := dvd_mul_of_dvd_right h (om - 1)
      rwa [show (om - 1) * (om * (om ^ k - 1)) = (om * (om - 1)) * (om ^ k - 1) by ring,
        om_mul_om_sub_one, one_mul] at this
    · intro h; exact dvd_mul_of_dvd_right h om
  rw [← h1, intCast_dvd_iff, om_pow_succ]
  have hre : ((⟨(Nat.fib k : ℤ), (Nat.fib (k + 1) : ℤ)⟩ : Phi) - om).re = Nat.fib k := by
    simp [om]
  have him : ((⟨(Nat.fib k : ℤ), (Nat.fib (k + 1) : ℤ)⟩ : Phi) - om).im =
      Nat.fib (k + 1) - 1 := by
    simp [om]
  rw [hre, him]
  unfold Per
  rw [Nat.modEq_iff_dvd, Nat.modEq_iff_dvd]
  push_cast
  rw [zero_sub, dvd_neg, dvd_sub_comm]

lemma zer_iff (m k : ℕ) : Zer m k ↔ (m : ℤ) ∣ (om ^ k).im := by
  rw [im_om_pow, Int.natCast_dvd_natCast]; rfl

/-- `(c + m u) ^ p = c ^ p + p m v` when `p ∣ m`. -/
lemma pow_of_eq_add {x u : Phi} {c m : ℤ} {p : ℕ} (hx : x = (c : Phi) + (m : Phi) * u)
    (hp : (p : ℤ) ∣ m) : ∃ v : Phi, x ^ p = ((c ^ p : ℤ) : Phi) + ((p * m : ℤ) : Phi) * v := by
  rw [hx, add_pow, Finset.sum_range_succ]
  simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one]
  have hdiv : ((p * m : ℤ) : Phi) ∣ ∑ j ∈ Finset.range p,
      (c : Phi) ^ j * ((m : Phi) * u) ^ (p - j) * (p.choose j : Phi) := by
    apply Finset.dvd_sum
    intro j hj
    rw [Finset.mem_range] at hj
    have hz : (p * m : ℤ) ∣ m ^ (p - j) * (p.choose j : ℤ) := by
      rcases Nat.lt_or_ge (p - j) 2 with hj1 | hj2
      · have hpj : p - j = 1 := by omega
        have hj' : j = p - 1 := by omega
        rw [hpj, hj', Nat.choose_symm (by omega), Nat.choose_one_right]
        rw [pow_one, mul_comm]
      · have h1 : (p : ℤ) ∣ m ^ (p - j - 1) := dvd_pow hp (by omega)
        have h2 : m ^ (p - j) = m ^ (p - j - 1) * m := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega)]
        rw [h2]
        exact Dvd.dvd.mul_right (mul_dvd_mul h1 (dvd_refl m)) _
    obtain ⟨w, hw⟩ := hz
    refine ⟨(w : Phi) * u ^ (p - j) * (c : Phi) ^ j, ?_⟩
    have hw' : ((m : Phi)) ^ (p - j) * (p.choose j : Phi) = ((p * m : ℤ) : Phi) * (w : Phi) := by
      have := congrArg (Int.cast : ℤ → Phi) hw
      push_cast at this ⊢
      exact this
    calc (c : Phi) ^ j * ((m : Phi) * u) ^ (p - j) * (p.choose j : Phi)
        = ((m : Phi) ^ (p - j) * (p.choose j : Phi)) * (u ^ (p - j) * (c : Phi) ^ j) := by
          ring
      _ = _ := by rw [hw']; ring
  obtain ⟨v, hv⟩ := hdiv
  exact ⟨v, by rw [hv]; push_cast; ring⟩

lemma per_lift {m k p : ℕ} (h : Per m k) (hp : p ∣ m) : Per (p * m) (p * k) := by
  rw [per_iff] at h ⊢
  obtain ⟨u, hu⟩ := h
  have hx : om ^ k = ((1 : ℤ) : Phi) + (((m : ℕ) : ℤ) : Phi) * u := by
    rw [Int.cast_one, ← hu]; ring
  obtain ⟨v, hv⟩ := pow_of_eq_add hx (p := p) (by exact_mod_cast hp)
  refine ⟨v, ?_⟩
  rw [mul_comm p k, pow_mul, hv]
  push_cast
  ring

lemma zer_lift {m k p : ℕ} (h : Zer m k) (hp : p ∣ m) : Zer (p * m) (p * k) := by
  rw [zer_iff] at h ⊢
  obtain ⟨y, hy⟩ := h
  have hx : om ^ k = (((om ^ k).re : ℤ) : Phi) + (((m : ℕ) : ℤ) : Phi) * ⟨0, y⟩ := by
    ext
    · simp
    · simp [hy]
  obtain ⟨v, hv⟩ := pow_of_eq_add hx (p := p) (by exact_mod_cast hp)
  rw [mul_comm p k, pow_mul, hv]
  refine ⟨v.im, ?_⟩
  rw [im_add, im_intCast, zero_add]
  simp [im_mul]

lemma per_pow {p M : ℕ} (h : Per p M) (e : ℕ) : Per (p ^ (e + 1)) (p ^ e * M) := by
  induction e with
  | zero => simpa using h
  | succ e ih =>
    have := per_lift ih (dvd_pow_self p (Nat.succ_ne_zero e))
    rw [← pow_succ'] at this
    rwa [← mul_assoc, ← pow_succ'] at this

lemma zer_pow {p M : ℕ} (h : Zer p M) (e : ℕ) : Zer (p ^ (e + 1)) (p ^ e * M) := by
  induction e with
  | zero => simpa using h
  | succ e ih =>
    have := zer_lift ih (dvd_pow_self p (Nat.succ_ne_zero e))
    rw [← pow_succ'] at this
    rwa [← mul_assoc, ← pow_succ'] at this

/-! ### The prime `5` -/

lemma norm_om_pow (k : ℕ) :
    (om ^ k).re ^ 2 + (om ^ k).re * (om ^ k).im - (om ^ k).im ^ 2 = (-1) ^ k := by
  have h := map_pow QuadraticAlgebra.norm om k
  have hn : QuadraticAlgebra.norm om = -1 := by simp [norm_def, om]
  rw [hn, norm_def] at h
  linear_combination h

lemma im_pow_five (c a : ℤ) : ((⟨c, a⟩ : Phi) ^ 5).im =
    25 * a ^ 5 + 25 * a ^ 3 * (c ^ 2 + c * a - a ^ 2) + 5 * a * (c ^ 2 + c * a - a ^ 2) ^ 2 := by
  simp only [pow_succ, pow_zero, one_mul, im_mul, re_mul]
  ring

lemma fib_five_mul (k : ℕ) :
    (Nat.fib (5 * k) : ℤ) = 25 * Nat.fib k ^ 5 + 25 * (-1) ^ k * Nat.fib k ^ 3 +
      5 * Nat.fib k := by
  have hN := norm_om_pow k
  have h5 : (Nat.fib (5 * k) : ℤ) = ((om ^ k) ^ 5).im := by
    rw [← im_om_pow, mul_comm, pow_mul]
  rw [h5, ← im_om_pow k]
  rw [show om ^ k = ⟨(om ^ k).re, (om ^ k).im⟩ from rfl, im_pow_five, hN]
  have hs : ((-1 : ℤ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  linear_combination 5 * (om ^ k).im * hs

/-- `5 ^ j ∣ F_k` forces `5 ^ j ∣ k`. -/
lemma five_pow_dvd_of_zer : ∀ j k : ℕ, Zer (5 ^ j) k → 5 ^ j ∣ k := by
  intro j
  induction j with
  | zero => intro k _; simp
  | succ j ih =>
    intro k hk
    have h5 : Zer 5 k := hk.of_dvd (dvd_pow_self 5 (Nat.succ_ne_zero j))
    obtain ⟨k', rfl⟩ := zer_5_dvd h5
    have hq := fib_five_mul k'
    set W : ℤ := 5 * Nat.fib k' ^ 4 + 5 * (-1) ^ k' * Nat.fib k' ^ 2 + 1 with hW
    have hF : (Nat.fib (5 * k') : ℤ) = 5 * (Nat.fib k' * W) := by rw [hq, hW]; ring
    have hdiv : ((5 : ℤ) ^ (j + 1)) ∣ 5 * (Nat.fib k' * W) := by
      rw [← hF]; exact_mod_cast hk
    rw [pow_succ', mul_dvd_mul_iff_left (by norm_num)] at hdiv
    have hcop : IsCoprime ((5 : ℤ) ^ j) W := by
      apply IsCoprime.pow_left
      refine ⟨-(Nat.fib k' ^ 4 + (-1) ^ k' * Nat.fib k' ^ 2), 1, ?_⟩
      rw [hW]; ring
    have h2 : ((5 : ℤ) ^ j) ∣ Nat.fib k' := hcop.dvd_of_dvd_mul_right hdiv
    have h3 := ih k' (by unfold Zer; exact_mod_cast h2)
    rw [pow_succ']
    exact mul_dvd_mul_left 5 h3

lemma zer_five_pow (j : ℕ) : Zer (5 ^ j) (5 ^ j) := by
  rcases j with _ | j
  · simp [Zer]
  · have := zer_pow zer_5 j
    rwa [← pow_succ] at this

/-- `Per (5 ^ j) k` with `j ≥ 1` forces `4 * 5 ^ j ∣ k`. -/
lemma per_five_pow_dvd {j k : ℕ} (hj : 1 ≤ j) (h : Per (5 ^ j) k) : 4 * 5 ^ j ∣ k := by
  have h1 : 5 ^ j ∣ k := five_pow_dvd_of_zer j k h.zer
  have h2 : 20 ∣ k := per_5_dvd (h.of_dvd (dvd_pow_self 5 (by omega)))
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow_right _ (by norm_num))
    (dvd_trans (by norm_num) h2) h1

lemma per_five_pow (j : ℕ) : Per (5 ^ j) (4 * 5 ^ j) := by
  rcases j with _ | j
  · simpa using per_one 4
  · have := per_pow per_5 j
    rwa [show 5 ^ j * 20 = 4 * 5 ^ (j + 1) by ring] at this

end TuringTask

/-!
# Fibonacci numbers modulo a prime `p ≥ 7`

In `S = QuadraticAlgebra (ZMod p) 1 1` with `w = ⟨0, 1⟩` we have `w ^ (k + 1) = F_k + F_(k+1) w`.
The element `s = 2 w - 1` has `s ^ 2 = 5`, so `s ^ p = e s` with `e = 5 ^ ((p - 1) / 2)`, and the
Frobenius map gives `s ^ p = 2 w ^ p - 1`. Hence `F_p = e` and `2 F_(p-1) = 1 - e`, where
`e ^ 2 = 1`.
* `e = 1`: `w ^ p = w`, so `p - 1` is a period.
* `e = -1`: `w ^ (p + 1) = -1`, so `p ∣ F_(p+1)` and `2 (p + 1)` is a period.
-/

namespace TuringTask

open QuadraticAlgebra

variable {p : ℕ}

lemma zom_pow_succ (k : ℕ) : (⟨0, 1⟩ : QuadraticAlgebra (ZMod p) 1 1) ^ (k + 1) =
    ⟨(Nat.fib k : ZMod p), (Nat.fib (k + 1) : ZMod p)⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    ext
    · simp
    · simp [Nat.fib_add_two]

lemma modEq_of_zmod {a b : ℕ} (h : (a : ZMod p) = (b : ZMod p)) : a ≡ b [MOD p] :=
  (ZMod.natCast_eq_natCast_iff a b p).mp h

/-- The two cases for a prime `p ≥ 7`. -/
theorem apparition (hp : p.Prime) (h7 : 7 ≤ p) :
    Per p (p - 1) ∨ (Per p (2 * (p + 1)) ∧ Zer p (p + 1)) := by
  haveI := Fact.mk hp
  haveI : CharP (QuadraticAlgebra (ZMod p) 1 1) p :=
    charP_of_injective_algebraMap QuadraticAlgebra.algebraMap_injective p
  set w : QuadraticAlgebra (ZMod p) 1 1 := ⟨0, 1⟩ with hw
  obtain ⟨q, hq⟩ : ∃ q, p = 2 * q + 1 := ⟨(p - 1) / 2, by
    have := hp.eq_one_or_self_of_dvd 2
    rcases Nat.even_or_odd p with ⟨r, hr⟩ | ⟨r, hr⟩
    · exfalso
      have h2 : 2 ∣ p := ⟨r, by omega⟩
      rcases this h2 with h | h <;> omega
    · omega⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have h5 : (5 : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 5 p).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  -- `w ^ p` in coordinates
  have hwp := zom_pow_succ (p := p) (p - 1)
  rw [Nat.sub_add_cancel hp.one_lt.le] at hwp
  set A : ZMod p := (Nat.fib (p - 1) : ZMod p) with hA
  set B : ZMod p := (Nat.fib p : ZMod p) with hB
  -- the element `s = 2 w - 1`
  have hs2 : (⟨-1, 2⟩ : QuadraticAlgebra (ZMod p) 1 1) ^ 2 = ⟨5, 0⟩ := by
    ext <;> simp [sq] <;> ring
  have hfrob : (⟨-1, 2⟩ : QuadraticAlgebra (ZMod p) 1 1) ^ p = ⟨2 * A - 1, 2 * B⟩ := by
    have e : (⟨-1, 2⟩ : QuadraticAlgebra (ZMod p) 1 1) =
        algebraMap (ZMod p) _ (-1) + algebraMap (ZMod p) _ 2 * w := by
      ext <;> simp [hw, QuadraticAlgebra.algebraMap_eq]
    rw [e, add_pow_char, mul_pow, ← map_pow, ← map_pow, ZMod.pow_card, ZMod.pow_card, hwp]
    ext
    · simp; ring
    · simp
  have hpow : (⟨-1, 2⟩ : QuadraticAlgebra (ZMod p) 1 1) ^ p =
      ⟨-(5 : ZMod p) ^ q, 2 * 5 ^ q⟩ := by
    have hpq : (⟨-1, 2⟩ : QuadraticAlgebra (ZMod p) 1 1) ^ p =
        (⟨-1, 2⟩ : QuadraticAlgebra (ZMod p) 1 1) ^ (2 * q + 1) :=
      congrArg (fun n => (⟨-1, 2⟩ : QuadraticAlgebra (ZMod p) 1 1) ^ n) hq
    rw [hpq, pow_succ, pow_mul, hs2]
    have : (⟨5, 0⟩ : QuadraticAlgebra (ZMod p) 1 1) ^ q = algebraMap (ZMod p) _ (5 ^ q) := by
      rw [map_pow]; rfl
    rw [this]
    ext
    · simp [QuadraticAlgebra.algebraMap_eq]
    · simp [QuadraticAlgebra.algebraMap_eq]; ring
  rw [hfrob] at hpow
  have hB' : B = 5 ^ q := by
    have := congrArg QuadraticAlgebra.im hpow
    simp only at this
    exact mul_left_cancel₀ h2 this
  have hA' : 2 * A = 1 - 5 ^ q := by
    have := congrArg QuadraticAlgebra.re hpow
    simp only at this
    linear_combination this
  have he : ((5 : ZMod p) ^ q) ^ 2 = 1 := by
    have hp1 : p - 1 = 2 * q := by omega
    calc ((5 : ZMod p) ^ q) ^ 2 = 5 ^ (p - 1) := by rw [hp1]; ring
      _ = 1 := ZMod.pow_card_sub_one_eq_one h5
  rcases sq_eq_one_iff.mp he with he1 | he1
  · -- `e = 1`
    left
    have hA0 : A = 0 := by
      have : 2 * A = 0 := by rw [hA', he1]; ring
      exact (mul_eq_zero.mp this).resolve_left h2
    refine ⟨modEq_of_zmod ?_, modEq_of_zmod ?_⟩
    · rw [← hA] at *; simpa using hA0
    · rw [Nat.sub_add_cancel hp.one_lt.le]; push_cast; rw [← hB, hB', he1]
  · -- `e = -1`
    right
    have hA1 : A = 1 := by
      have : 2 * A = 2 * 1 := by rw [hA', he1]; ring
      exact mul_left_cancel₀ h2 this
    have hF1 : (Nat.fib (p + 1) : ZMod p) = 0 := by
      have e1 : Nat.fib (p + 1) = Nat.fib (p - 1) + Nat.fib p := by
        have := Nat.fib_add_two (n := p - 1)
        rwa [show p - 1 + 2 = p + 1 by omega, show p - 1 + 1 = p by omega] at this
      rw [e1]; push_cast; rw [← hA, ← hB, hA1, hB', he1]; ring
    have hF2 : (Nat.fib (p + 2) : ZMod p) = -1 := by
      rw [Nat.fib_add_two]; push_cast; rw [← hB, hB', he1, hF1]; ring
    have hw1 : w ^ (p + 1) = -1 := by
      rw [hw, zom_pow_succ, ← hB, hB', he1, hF1]
      ext <;> simp
    have hw2 := zom_pow_succ (p := p) (2 * (p + 1))
    rw [show 2 * (p + 1) + 1 = 2 * (p + 1) + 1 from rfl] at hw2
    have hsq : w ^ (2 * (p + 1) + 1) = w := by
      rw [pow_succ, mul_comm 2 (p + 1), pow_mul, hw1]; simp
    rw [← hw, hsq] at hw2
    have hre := congrArg QuadraticAlgebra.re hw2
    have him := congrArg QuadraticAlgebra.im hw2
    simp only [hw] at hre him
    refine ⟨⟨modEq_of_zmod ?_, modEq_of_zmod ?_⟩, modEq_of_zmod ?_ |> Nat.modEq_zero_iff_dvd.mp⟩
    · push_cast; exact hre.symm
    · push_cast; exact him.symm
    · push_cast; exact hF1

end TuringTask
