import Mathlib
import TuringTask.Dedekind

/-!
# Integer formulas for `s(h, k)` with `gcd(h, k) = 1`

Write `ρ(r) = h r mod k`, `q(r) = ⌊h r / k⌋`, so `ρ(r) = h r - k q(r)`, and put
`S₂ = ∑ r q(r)`, `Q = ∑ q(r)^2`, `Σq = ∑ q(r)` (sums over `r < k`). Since `r ↦ ρ(r)` permutes
`{0, …, k - 1}`, `∑ ρ = ∑ r` and `∑ ρ² = ∑ r²`.
* `twelve_k_dsum`: `12 k s(h, k) = 2 h (k - 1)(2 k - 1) - 12 S₂ - 3 k (k - 1)`.
* `twelve_h_S2`: `12 h S₂ = (h² - 1)(k - 1)(2 k - 1) + 6 k Q` (from `∑ ρ² = ∑ r²`).
* `two_Sq`: `2 Σq = (h - 1)(k - 1)` (from `∑ ρ = ∑ r`).
* `h_twelve_k_dsum`: `12 h k s(h, k) = h² + 1 + k M` with an explicit integer `M`.
-/

namespace TuringTask

open Finset

/-- `S₂(h, k) = ∑_{r < k} r ⌊h r / k⌋`. -/
def dS2 (h k : ℕ) : ℕ := ∑ r ∈ range k, r * (h * r / k)

/-- `Q(h, k) = ∑_{r < k} ⌊h r / k⌋²`. -/
def dQ (h k : ℕ) : ℕ := ∑ r ∈ range k, (h * r / k) ^ 2

/-- `Σq(h, k) = ∑_{r < k} ⌊h r / k⌋`. -/
def dSq (h k : ℕ) : ℕ := ∑ r ∈ range k, h * r / k

lemma sum_range_id_rat (k : ℕ) : ∑ r ∈ range k, (r : ℚ) = k * (k - 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

lemma sum_range_sq_rat (k : ℕ) : ∑ r ∈ range k, (r : ℚ) ^ 2 = k * (k - 1) * (2 * k - 1) / 6 := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

lemma rho_eq (h k r : ℕ) : ((h * r % k : ℕ) : ℚ) = h * r - k * ((h * r / k : ℕ) : ℚ) := by
  have := Nat.mod_add_div (h * r) k
  have h' : ((h * r % k : ℕ) : ℚ) + k * ((h * r / k : ℕ) : ℚ) = ((h * r : ℕ) : ℚ) := by
    exact_mod_cast this
  push_cast at h' ⊢
  linarith

lemma sum_rho {h k : ℕ} (hhk : Nat.Coprime h k) (F : ℕ → ℚ) :
    ∑ r ∈ range k, F (h * r % k) = ∑ r ∈ range k, F r := by
  have := sum_range_mul_mod F hhk
  rw [← this]
  apply sum_congr rfl
  intro r _
  rw [mul_comm]

lemma rho_ne_zero {h k r : ℕ} (hhk : Nat.Coprime h k) (hr0 : 0 < r) (hrk : r < k) :
    h * r % k ≠ 0 := by
  intro h0
  have hdvd : k ∣ h * r := Nat.dvd_of_mod_eq_zero h0
  have := (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hhk) hdvd)
  have := Nat.le_of_dvd hr0 this
  omega

/-- `s(h, k) = (∑ r ρ(r)) / k² - (k - 1)/4`. -/
lemma dsum_eq_sum_mul {h k : ℕ} (hhk : Nat.Coprime h k) (hk : 0 < k) :
    dsum h k = (∑ r ∈ range k, (r : ℚ) * ((h * r % k : ℕ) : ℚ)) / k ^ 2 - (k - 1) / 4 := by
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hk0 : (0 : ℚ) < k := by exact_mod_cast hk
  have hterm : ∀ r ∈ range k, saw ((r : ℚ) / k) * saw (((h * r : ℕ) : ℚ) / k) =
      (r : ℚ) * ((h * r % k : ℕ) : ℚ) / k ^ 2 - (r : ℚ) / (2 * k) -
        ((h * r % k : ℕ) : ℚ) / (2 * k) + 1 / 4 - (if r = 0 then 1 / 4 else 0) := by
    intro r hr
    have hrk := mem_range.mp hr
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0; simp [saw]
    · rw [saw_of_mem_Ioo (by positivity) (by rw [div_lt_one hk0]; exact_mod_cast hrk),
        saw_natCast_div _ _ hk, if_neg (rho_ne_zero hhk h0 hrk), if_neg h0.ne']
      field_simp
      ring
  unfold dsum
  rw [sum_congr rfl hterm]
  simp only [sum_sub_distrib, sum_add_distrib, ← sum_div, sum_const, card_range]
  rw [sum_rho hhk (fun r => (r : ℚ)), sum_ite_eq' (range k) 0 (fun _ => (1 : ℚ) / 4),
    if_pos (mem_range.mpr hk), sum_range_id_rat]
  field_simp
  ring

lemma sum_mul_rho {h k : ℕ} :
    ∑ r ∈ range k, (r : ℚ) * ((h * r % k : ℕ) : ℚ) =
      h * ∑ r ∈ range k, (r : ℚ) ^ 2 - k * (dS2 h k : ℚ) := by
  unfold dS2
  push_cast
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro r _
  rw [rho_eq]
  ring

lemma twelve_k_dsum {h k : ℕ} (hhk : Nat.Coprime h k) (hk : 0 < k) :
    12 * k * dsum h k = 2 * h * (k - 1) * (2 * k - 1) - 12 * (dS2 h k : ℚ) - 3 * k * (k - 1) := by
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [dsum_eq_sum_mul hhk hk, sum_mul_rho, sum_range_sq_rat]
  field_simp
  ring

lemma twelve_h_S2 {h k : ℕ} (hhk : Nat.Coprime h k) (hk : 0 < k) :
    12 * h * (dS2 h k : ℚ) = (h ^ 2 - 1) * (k - 1) * (2 * k - 1) + 6 * k * (dQ h k : ℚ) := by
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hsq := sum_rho hhk (fun r => (r : ℚ) ^ 2)

  have hexp : ∑ r ∈ range k, ((h * r % k : ℕ) : ℚ) ^ 2 =
      h ^ 2 * ∑ r ∈ range k, (r : ℚ) ^ 2 - 2 * h * k * (dS2 h k : ℚ) + k ^ 2 * (dQ h k : ℚ) := by
    unfold dS2 dQ
    push_cast
    rw [mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro r _
    rw [rho_eq]
    ring
  rw [hexp, sum_range_sq_rat] at hsq
  have : k * (12 * h * (dS2 h k : ℚ)) =
      k * ((h ^ 2 - 1) * (k - 1) * (2 * k - 1) + 6 * k * (dQ h k : ℚ)) := by
    linear_combination (-6 : ℚ) * hsq
  exact mul_left_cancel₀ hk' this

lemma two_Sq {h k : ℕ} (hhk : Nat.Coprime h k) (hk : 0 < k) :
    2 * (dSq h k : ℚ) = (h - 1) * (k - 1) := by
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hlin := sum_rho hhk (fun r => (r : ℚ))

  have hexp : ∑ r ∈ range k, ((h * r % k : ℕ) : ℚ) =
      h * ∑ r ∈ range k, (r : ℚ) - k * (dSq h k : ℚ) := by
    unfold dSq
    push_cast
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro r _
    rw [rho_eq]
  rw [hexp, sum_range_id_rat] at hlin
  have : k * (2 * (dSq h k : ℚ)) = k * ((h - 1) * (k - 1)) := by linear_combination (-2 : ℚ) * hlin
  exact mul_left_cancel₀ hk' this

/-- `12 h k s(h, k) = h² + 1 + k M`. -/
lemma h_twelve_k_dsum {h k : ℕ} (hhk : Nat.Coprime h k) (hk : 0 < k) :
    h * (12 * k * dsum h k) = h ^ 2 + 1 +
      k * ((h ^ 2 + 1) * (2 * k - 3) - 6 * (dQ h k : ℚ) - 3 * h * (k - 1)) := by
  rw [twelve_k_dsum hhk hk]
  linear_combination (-1 : ℚ) * twelve_h_S2 hhk hk

end TuringTask
