import TuringTask.Jump

/-!
# Flatness of `Φ_{pqr}` when `r ≡ ±1 (mod pq)`

Let `D = (p - 1)(q - 1)` be the degree of `Φ_{pq}`, so `D + p + q = pq + 1`.
* `flat_head`: for every `σ` and `K`,
  `|∑_{j < pq, j ≤ K} b_j ℓ((σ - j) mod pq)| ≤ 1`. For `σ mod pq ≠ 0` the sum equals the four-term
  expression of `four_term`; for `σ ≡ 0` it equals `1 - [D ≤ K]`.
* `full_sum`: without the cut-off the same sum is `0` (the uncut differences cancel).
* `coeff_reflect`: `b_{D - j} = b_j`, from the closed form and `alp (D - j) ≡ u - 1 - alp j`.
* If `r ≡ 1`, Kaplan's formula is exactly `flat_head` with `σ = k`, `K = ⌊k / r⌋`.
* If `r ≡ -1`, reflecting `j ↦ D - j` turns it into `full_sum` minus a `flat_head` sum.
-/

namespace TuringTask

open Polynomial Finset

/-- The cut-off sum `∑_{j < n, j ≤ K} b_j ℓ((σ - j) mod n)` with `n = pq`. -/
noncomputable def headSum (p q σ K : ℕ) : ℤ :=
  ∑ j ∈ range (p * q),
    (if j ≤ K then (cyclotomic (p * q) ℤ).coeff j else 0) * ell p q (rho (p * q) 1 σ j)

lemma rho_one_eq {n σ j : ℕ} (hσ : σ < n) (hj : j < n) :
    rho n 1 σ j = if j ≤ σ then σ - j else σ + n - j := by
  unfold rho
  rw [Nat.cast_one, one_mul]
  split_ifs with h
  · rw [← Nat.cast_sub h, ZMod.val_natCast_of_lt (by omega)]
  · rw [show ((σ : ZMod n) - j) = ((σ + n - j : ℕ) : ZMod n) by
      rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, add_zero],
      ZMod.val_natCast_of_lt (by omega)]

lemma rho_one_mod (n σ j : ℕ) : rho n 1 σ j = rho n 1 (σ % n) j := by
  unfold rho; rw [ZMod.natCast_mod]

section

variable {p q u v : ℕ} (hp : p.Prime) (hq : q.Prime) (hu : u * p % q = 1) (hv : v * q % p = 1)
  (huq : u < q) (hvp : v < p)

include hp hq hu in
lemma deg_eq : (cyclotomic (p * q) ℤ).natDegree = (p - 1) * (q - 1) := by
  rw [natDegree_cyclotomic, Nat.totient_mul (coprime_pq hp hq hu), Nat.totient_prime hp,
    Nat.totient_prime hq]

include hp hq in
lemma deg_add : (p - 1) * (q - 1) + p + q = p * q + 1 := by
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, q = b + 1 := ⟨q - 1, by have := hq.two_le; omega⟩
  simp only [Nat.add_sub_cancel]
  ring

include hp hq hu in
lemma coeff_above {j : ℕ} (hj : (p - 1) * (q - 1) < j) : (cyclotomic (p * q) ℤ).coeff j = 0 :=
  coeff_eq_zero_of_natDegree_lt (by rw [deg_eq hp hq hu]; exact hj)

include hp hq hu in
lemma coeff_deg : (cyclotomic (p * q) ℤ).coeff ((p - 1) * (q - 1)) = 1 := by
  rw [← deg_eq hp hq hu]
  exact (cyclotomic.monic (p * q) ℤ).coeff_natDegree

include hp hq in
/-- The value of `ℓ((σ - j) mod pq)` below the degree. -/
lemma ell_rho {σ j : ℕ} (hσ : σ < p * q) (hj : j ≤ (p - 1) * (q - 1)) :
    ell p q (rho (p * q) 1 σ j) =
      (if j < σ + 1 then 1 else 0) - (if j < σ + 1 - p then 1 else 0) -
        (if j < σ + 1 - q then 1 else 0) + (if j < σ + 1 - p - q then 1 else 0) -
          (if σ = 0 ∧ j = (p - 1) * (q - 1) then 1 else 0) := by
  have hd := deg_add hp hq
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hD1 : 0 < (p - 1) * (q - 1) := Nat.mul_pos (by omega) (by omega)
  rw [rho_one_eq hσ (by omega)]
  unfold ell
  split_ifs <;> omega

lemma sum_head_lt (K : ℕ) {x : ℕ} (hx : x ≤ p * q) :
    ∑ j ∈ range (p * q), (if j < x then
      (if j ≤ K then (cyclotomic (p * q) ℤ).coeff j else 0) else 0) = qsum p q K x := by
  rw [← sum_filter, show (range (p * q)).filter (· < x) = range x by
    ext j; simp only [mem_filter, mem_range]; omega, ← sum_filter, qsum, psum]
  congr 1
  ext j; simp only [mem_filter, mem_range]; omega

include hp hq hu in
/-- The cut-off sum in terms of truncated partial sums. -/
lemma headSum_eq (K : ℕ) {σ : ℕ} (hσ : σ < p * q) : headSum p q σ K =
    qsum p q K (σ + 1) - qsum p q K (σ + 1 - p) - qsum p q K (σ + 1 - q) +
      qsum p q K (σ + 1 - p - q) - (if σ = 0 ∧ (p - 1) * (q - 1) ≤ K then 1 else 0) := by
  have hd := deg_add hp hq
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  unfold headSum
  have hterm : ∀ j ∈ range (p * q),
      (if j ≤ K then (cyclotomic (p * q) ℤ).coeff j else 0) * ell p q (rho (p * q) 1 σ j) =
      (if j ≤ K then (cyclotomic (p * q) ℤ).coeff j else 0) *
        ((if j < σ + 1 then 1 else 0) - (if j < σ + 1 - p then 1 else 0) -
          (if j < σ + 1 - q then 1 else 0) + (if j < σ + 1 - p - q then 1 else 0) -
            (if σ = 0 ∧ j = (p - 1) * (q - 1) then 1 else 0)) := by
    intro j _
    by_cases hj : j ≤ (p - 1) * (q - 1)
    · rw [ell_rho hp hq hσ hj]
    · rw [coeff_above hp hq hu (by omega)]; simp
  rw [sum_congr rfl hterm]
  simp only [mul_sub, mul_add, mul_ite, mul_one, mul_zero, sum_sub_distrib, sum_add_distrib]
  rw [sum_head_lt K (by omega), sum_head_lt K (by omega),
    sum_head_lt K (by omega), sum_head_lt K (by omega)]
  congr 1
  by_cases h0 : σ = 0
  · simp only [h0, true_and]
    rw [sum_ite_eq' (range (p * q)) ((p - 1) * (q - 1)), if_pos (mem_range.2 (by omega))]
    split_ifs with h1 <;> simp [coeff_deg hp hq hu]
  · simp [h0]

include hp hq hu hv in
/-- The cut-off sums are at most `1` in absolute value. -/
theorem flat_head (σ K : ℕ) : |headSum p q σ K| ≤ 1 := by
  have hn : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  have hs : headSum p q σ K = headSum p q (σ % (p * q)) K := by
    unfold headSum; simp only [rho_one_mod (p * q) σ]
  rw [hs, headSum_eq hp hq hu K (Nat.mod_lt _ hn)]
  by_cases h0 : σ % (p * q) = 0
  · have hp2 := hp.two_le
    have hq2 := hq.two_le
    simp only [h0, zero_add, true_and, show 1 - p = 0 by omega, show 1 - q = 0 by omega,
      Nat.zero_sub]
    have h1 : qsum p q K 1 = 1 := by
      simp [qsum, psum, cyclotomic_coeff_zero ℤ (show 1 < p * q by nlinarith)]
    have h00 : qsum p q K 0 = 0 := by simp [qsum, psum]
    rw [h1, h00]
    split_ifs <;> norm_num
  · simp only [h0, false_and, if_false, sub_zero]
    exact four_term hp hq hu hv K (by have := Nat.mod_lt σ hn; omega)

include hp hq hu hv huq hvp in
/-- Without the cut-off the sum vanishes. -/
theorem full_sum (σ : ℕ) : ∑ j ∈ range (p * q),
    (cyclotomic (p * q) ℤ).coeff j * ell p q (rho (p * q) 1 σ j) = 0 := by
  haveI := nezero_pq hp hq
  have h1 : ((1 : ℕ) : ZMod (p * q)) * (1 : ℕ) = 1 := by simp
  rw [reindex h1 σ (fun j => (cyclotomic (p * q) ℤ).coeff j) (ell p q),
    sum_mul_ell (two_add_le hp hq), ← sum_sub_distrib]
  exact uncut_sum hp hq hu hv huq hvp h1 σ

/-- Reflecting an indicator: if `x ≡ a - 1 - y (mod m)` then `x < a ↔ y < a`. -/
lemma refl_ind {m a x y : ℕ} (ha1 : 1 ≤ a) (ham : a ≤ m) (hx : x < m) (hy : y < m)
    (h : (x : ZMod m) = (a : ZMod m) - 1 - y) : x < a ↔ y < a := by
  haveI : NeZero m := ⟨by omega⟩
  have hval : ∀ w, w < m → (w : ZMod m) = (a : ZMod m) - 1 - y → x = w := by
    intro w hw hw'
    rw [← hw'] at h
    rw [← ZMod.val_natCast_of_lt hx, h, ZMod.val_natCast_of_lt hw]
  by_cases hya : y < a
  · have := hval (a - 1 - y) (by omega) (by rw [Nat.cast_sub (by omega), Nat.cast_sub ha1]; simp)
    omega
  · have := hval (a + m - 1 - y) (by omega) (by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self]
      simp)
    omega

include hp hq hu hv huq hvp in
/-- The palindromic symmetry `b_{D - j} = b_j`. -/
lemma coeff_reflect {j : ℕ} (hj : j ≤ (p - 1) * (q - 1)) :
    (cyclotomic (p * q) ℤ).coeff ((p - 1) * (q - 1) - j) = (cyclotomic (p * q) ℤ).coeff j := by
  have hd := deg_add hp hq
  have hu1 : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with rfl | h
    · simp at hu
    · exact h
  have hv1 : 1 ≤ v := by
    rcases Nat.eq_zero_or_pos v with rfl | h
    · simp at hv
    · exact h
  have hup : (u : ZMod q) * p = 1 := by
    rw [← Nat.cast_mul, ← ZMod.natCast_mod, hu, Nat.cast_one]
  have hvq : (v : ZMod p) * q = 1 := by
    rw [← Nat.cast_mul, ← ZMod.natCast_mod, hv, Nat.cast_one]
  have hDq : ((p - 1 : ℕ) : ZMod q) * ((q - 1 : ℕ) : ZMod q) = 1 - p := by
    have := congrArg (fun n : ℕ => (n : ZMod q)) hd
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero,
      Nat.cast_one] at this
    linear_combination this
  have hDp : ((p - 1 : ℕ) : ZMod p) * ((q - 1 : ℕ) : ZMod p) = 1 - q := by
    have := congrArg (fun n : ℕ => (n : ZMod p)) hd
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero,
      Nat.cast_one] at this
    linear_combination this
  have ha : alp q u ((p - 1) * (q - 1) - j) < u ↔ alp q u j < u := by
    apply refl_ind hu1 huq.le (Nat.mod_lt _ hq.pos) (Nat.mod_lt _ hq.pos)
    rw [ZMod.natCast_mod, ZMod.natCast_mod]
    simp only [Nat.cast_mul, Nat.cast_sub hj]
    linear_combination (u : ZMod q) * hDq - hup
  have hb : bet p v ((p - 1) * (q - 1) - j) < v ↔ bet p v j < v := by
    apply refl_ind hv1 hvp.le (Nat.mod_lt _ hp.pos) (Nat.mod_lt _ hp.pos)
    rw [ZMod.natCast_mod, ZMod.natCast_mod]
    simp only [Nat.cast_mul, Nat.cast_sub hj]
    linear_combination (v : ZMod p) * hDp - hvq
  rw [coeff_binary_closed hp hq hu hv huq hvp (by omega),
    coeff_binary_closed hp hq hu hv huq hvp (by omega)]
  simp only [ha, hb]

variable {r : ℕ} (hr : r.Prime) (hrp : r ≠ p) (hrq : r ≠ q)

include hp hq hu hr hrp hrq in
/-- Kaplan's formula with the cut-off `i ≤ ⌊k / r⌋`. -/
lemma kaplan_div (k : ℕ) : (cyclotomic (p * q * r) ℤ).coeff k = ∑ i ∈ range (p * q),
    (if i ≤ k / r then (cyclotomic (p * q) ℤ).coeff i else 0) * ell p q (rho (p * q) r k i) := by
  rw [kaplan hp hq hu hr hrp hrq]
  refine sum_congr rfl fun i _ => ?_
  have hdiv : i ≤ k / r ↔ r * i ≤ k := by rw [Nat.le_div_iff_mul_le hr.pos, mul_comm]
  by_cases h : r * i ≤ k
  · rw [if_pos h, if_pos (hdiv.2 h)]
    unfold rho
    rw [← ZMod.val_natCast, Nat.cast_sub h, Nat.cast_mul]
  · rw [if_neg h, if_neg (fun h' => h (hdiv.1 h')), zero_mul]

include hp hq hu hv hr hrp hrq in
/-- Flatness when `r ≡ 1 (mod pq)`. -/
theorem flat_one (hr1 : r % (p * q) = 1) (k : ℕ) : |(cyclotomic (p * q * r) ℤ).coeff k| ≤ 1 := by
  have hr1' : (r : ZMod (p * q)) = 1 := by rw [← ZMod.natCast_mod, hr1, Nat.cast_one]
  rw [kaplan_div hp hq hu hr hrp hrq]
  have h : ∀ i, rho (p * q) r k i = rho (p * q) 1 k i := by
    intro i; unfold rho; rw [hr1', Nat.cast_one]
  simp only [h]
  exact flat_head hp hq hu hv k (k / r)

include hp hq in
lemma sum_extend {f : ℕ → ℤ} (hf : ∀ j, (p - 1) * (q - 1) < j → f j = 0) :
    ∑ j ∈ range ((p - 1) * (q - 1) + 1), f j = ∑ j ∈ range (p * q), f j := by
  have hd := deg_add hp hq
  have := hp.two_le
  have := hq.two_le
  apply sum_subset
  · intro j hj; rw [mem_range] at hj ⊢; omega
  · intro j _ hj; rw [mem_range] at hj; exact hf j (by omega)

include hp hq hu hv huq hvp hr hrp hrq in
/-- Flatness when `r ≡ -1 (mod pq)`. -/
theorem flat_neg (hrm : r % (p * q) + 1 = p * q) (k : ℕ) :
    |(cyclotomic (p * q * r) ℤ).coeff k| ≤ 1 := by
  have hrm' : (r : ZMod (p * q)) = -1 := by
    have := congrArg (fun x : ℕ => (x : ZMod (p * q))) hrm
    simp only [Nat.cast_add, ZMod.natCast_mod, ZMod.natCast_self, Nat.cast_one] at this
    linear_combination this
  set D := (p - 1) * (q - 1) with hD
  set K := k / r with hK
  rw [kaplan_div hp hq hu hr hrp hrq]
  rw [← sum_extend hp hq (fun j hj => by rw [coeff_above hp hq hu hj]; simp)]
  rw [← sum_range_reflect]
  simp only [Nat.add_sub_cancel]
  have hterm : ∀ j ∈ range (D + 1),
      (if D - j ≤ K then (cyclotomic (p * q) ℤ).coeff (D - j) else 0) *
        ell p q (rho (p * q) r k (D - j)) =
      (if D - j ≤ K then (cyclotomic (p * q) ℤ).coeff j else 0) *
        ell p q (rho (p * q) 1 (k + D) j) := by
    intro j hj
    rw [mem_range] at hj
    rw [coeff_reflect hp hq hu hv huq hvp (by omega)]
    congr 2
    unfold rho
    rw [hrm', Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    ring_nf
  rw [sum_congr rfl hterm]
  by_cases hDK : D ≤ K
  · have h0 : ∀ j ∈ range (D + 1), (if D - j ≤ K then (cyclotomic (p * q) ℤ).coeff j else 0) *
        ell p q (rho (p * q) 1 (k + D) j) =
        (cyclotomic (p * q) ℤ).coeff j * ell p q (rho (p * q) 1 (k + D) j) :=
      fun j _ => by rw [if_pos (by omega)]
    rw [sum_congr rfl h0, sum_extend hp hq (fun j hj => by rw [coeff_above hp hq hu hj]; simp),
      full_sum hp hq hu hv huq hvp]
    simp
  · have h0 : ∀ j ∈ range (D + 1), (if D - j ≤ K then (cyclotomic (p * q) ℤ).coeff j else 0) *
        ell p q (rho (p * q) 1 (k + D) j) =
        (cyclotomic (p * q) ℤ).coeff j * ell p q (rho (p * q) 1 (k + D) j) -
        (if j ≤ D - K - 1 then (cyclotomic (p * q) ℤ).coeff j else 0) *
          ell p q (rho (p * q) 1 (k + D) j) := by
      intro j hj
      rw [mem_range] at hj
      by_cases h : D - j ≤ K
      · rw [if_pos h, if_neg (by omega)]; ring
      · rw [if_neg h, if_pos (by omega)]; ring
    rw [sum_congr rfl h0, sum_sub_distrib,
      sum_extend hp hq (fun j hj => by rw [coeff_above hp hq hu hj]; simp),
      sum_extend hp hq (fun j hj => by rw [coeff_above hp hq hu hj]; simp),
      full_sum hp hq hu hv huq hvp, zero_sub, abs_neg]
    exact flat_head hp hq hu hv (k + D) (D - K - 1)

end

end TuringTask
