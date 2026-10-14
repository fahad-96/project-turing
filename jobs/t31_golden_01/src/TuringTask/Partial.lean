import TuringTask.Binary

/-!
# Partial sums of binary cyclotomic coefficients

Let `G = ∑_{a < q, b < p} X^{ap + bq}`. Then `Φ_{pq} (X^{pq} - 1) = (X - 1) G`, so for `x < pq`
the partial sum `∑_{i ≤ x} a_{pq}(i)` equals the coefficient of `X^x` in `G`. That coefficient is
`1` exactly when `x = ap + bq` with `a, b ≥ 0`, and `0` otherwise.

* `sum_range_coeff_mem`: every partial sum lies in `{0, 1}` (theorem 1).
* `card_coeff_eq_one`: exactly `u v` coefficients equal `1` (theorem 2).
* `four_term`: with `Q(x) = ∑_{i < x, i ≤ K} a_{pq}(i)` and `1 ≤ N ≤ pq`,
  `|Q(N) - Q(N - p) - Q(N - q) + Q(N - p - q)| ≤ 1`.
-/

namespace TuringTask

open Polynomial Finset

/-- The polynomial `∑_{a < q, b < p} X^{ap + bq}`. -/
noncomputable def gpoly (p q : ℕ) : ℤ[X] := ∑ a ∈ range q, ∑ b ∈ range p, X ^ (a * p + b * q)

/-- `n` is a nonnegative integer combination of `p` and `q`. -/
def CombPQ (p q n : ℕ) : Prop := ∃ a b : ℕ, a * p + b * q = n

/-- The partial sum `∑_{i < y} a_{pq}(i)`. -/
noncomputable def psum (p q y : ℕ) : ℤ := ∑ i ∈ range y, (cyclotomic (p * q) ℤ).coeff i

/-- The truncated partial sum `∑_{i < x, i ≤ K} a_{pq}(i)`. -/
noncomputable def qsum (p q K x : ℕ) : ℤ := psum p q (min x (K + 1))

lemma xpow_sub_one_ne {n : ℕ} (hn : 0 < n) : (X ^ n - 1 : ℤ[X]) ≠ 0 := by
  simpa using X_pow_sub_C_ne_zero hn (1 : ℤ)

lemma gpoly_mul (p q : ℕ) : gpoly p q * (X ^ p - 1) * (X ^ q - 1) = (X ^ (p * q) - 1) ^ 2 := by
  have h1 : gpoly p q = (∑ a ∈ range q, (X ^ p) ^ a) * ∑ b ∈ range p, (X ^ q) ^ b := by
    unfold gpoly
    rw [sum_mul_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [← pow_mul, ← pow_mul, ← pow_add, mul_comm p a, mul_comm q b]
  have g1 := geom_sum_mul (X ^ p : ℤ[X]) q
  have g2 := geom_sum_mul (X ^ q : ℤ[X]) p
  rw [← pow_mul] at g1 g2
  rw [mul_comm q p] at g2
  rw [h1]
  linear_combination (∑ b ∈ range p, (X ^ q) ^ b) * (X ^ q - 1) * g1 + (X ^ (p * q) - 1) * g2

section

variable {p q u v : ℕ} (hp : p.Prime) (hq : q.Prime) (hu : u * p % q = 1) (hv : v * q % p = 1)
  (huq : u < q) (hvp : v < p)

include hp hq hu in
lemma cyc_gpoly : cyclotomic (p * q) ℤ * (X ^ (p * q) - 1) = (X - 1) * gpoly p q := by
  have hc := cyc_mul hp hq hu
  have hg := gpoly_mul p q
  have hM : (X ^ p - 1 : ℤ[X]) * (X ^ q - 1) ≠ 0 :=
    mul_ne_zero (xpow_sub_one_ne hp.pos) (xpow_sub_one_ne hq.pos)
  apply mul_right_cancel₀ hM
  linear_combination (X ^ (p * q) - 1) * hc - (X - 1) * hg

include hp hq hu hv in
lemma coeff_gpoly (n : ℕ) : (gpoly p q).coeff n =
    if alp q u n * p + bet p v n * q = n then 1 else 0 := by
  unfold gpoly
  simp only [finsetSum_coeff, coeff_X_pow]
  have h : ∀ a ∈ range q, ∀ b ∈ range p, (n = a * p + b * q) ↔
      (a = alp q u n ∧ b = bet p v n ∧ alp q u n * p + bet p v n * q = n) := by
    intro a ha b hb
    rw [mem_range] at ha hb
    constructor
    · rintro rfl
      rw [alp_rep hq hu ha, bet_rep hp hv hb]
      exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨rfl, rfl, h⟩; exact h.symm
  rw [sum_congr rfl (fun a ha => sum_congr rfl (fun b hb => if_congr (h a ha b hb) rfl rfl)),
    sum_sum_ite]
  apply if_congr _ rfl rfl
  rw [mem_range, mem_range]
  exact ⟨fun h => h.2.2, fun h => ⟨Nat.mod_lt _ hq.pos, Nat.mod_lt _ hp.pos, h⟩⟩

include hp hq hu in
lemma coeff_rel {n : ℕ} (hn : n < p * q) : (cyclotomic (p * q) ℤ).coeff n =
    (gpoly p q).coeff n - (X * gpoly p q).coeff n := by
  have h := congrArg (fun f => f.coeff n) (cyc_gpoly hp hq hu)
  simp only [mul_sub, mul_one, sub_mul, one_mul, coeff_sub, coeff_mul_X_pow',
    if_neg (not_le.2 hn)] at h
  linarith

include hp hq hu in
lemma psum_succ {x : ℕ} (hx : x < p * q) : psum p q (x + 1) = (gpoly p q).coeff x := by
  induction x with
  | zero => simp [psum, coeff_rel hp hq hu (show 0 < p * q by omega)]
  | succ x ih =>
    rw [psum, sum_range_succ, ← psum, ih (by omega), coeff_rel hp hq hu hx, coeff_X_mul]
    ring

lemma psum_zero : psum p q 0 = 0 := by simp [psum]

include hp hq hu hv in
lemma gpoly_eq_one_iff {n : ℕ} (hn : n < p * q) : (gpoly p q).coeff n = 1 ↔ CombPQ p q n := by
  rw [coeff_gpoly hp hq hu hv]
  split_ifs with h
  · exact ⟨fun _ => ⟨_, _, h⟩, fun _ => rfl⟩
  · simp only [zero_ne_one, false_iff]
    rintro ⟨a, b, rfl⟩
    have ha : a < q := by
      by_contra ha
      have : q * p ≤ a * p := Nat.mul_le_mul_right _ (by omega)
      rw [mul_comm q p] at this
      omega
    have hb : b < p := by
      by_contra hb
      have : p * q ≤ b * q := Nat.mul_le_mul_right _ (by omega)
      omega
    exact h (by rw [alp_rep hq hu ha, bet_rep hp hv hb])

include hp hq hu hv in
lemma psum_cases {y : ℕ} (hy : y ≤ p * q) : psum p q y = 0 ∨ psum p q y = 1 := by
  rcases y with _ | y
  · exact Or.inl psum_zero
  · rw [psum_succ hp hq hu (by omega), coeff_gpoly hp hq hu hv]
    split_ifs <;> simp

include hp hq hu hv in
lemma psum_eq_one_iff {y : ℕ} (hy1 : 1 ≤ y) (hy : y ≤ p * q) :
    psum p q y = 1 ↔ CombPQ p q (y - 1) := by
  obtain ⟨x, rfl⟩ : ∃ x, y = x + 1 := ⟨y - 1, by omega⟩
  rw [psum_succ hp hq hu (by omega), Nat.add_sub_cancel]
  exact gpoly_eq_one_iff hp hq hu hv (by omega)

include hp hq hu hv huq hvp in
/-- Theorem 1 for given `u` and `v`: every partial sum lies in `{0, 1}`. -/
theorem sum_range_coeff_mem (k : ℕ) :
    (∑ i ∈ range (k + 1), (cyclotomic (p * q) ℤ).coeff i) ∈ ({0, 1} : Finset ℤ) := by
  have hpq : 1 ≤ p * q := Nat.mul_pos hp.pos hq.pos
  have key : ∀ x, x < p * q → psum p q (x + 1) ∈ ({0, 1} : Finset ℤ) := by
    intro x hx
    rw [psum_succ hp hq hu hx, coeff_gpoly hp hq hu hv]
    split_ifs <;> simp
  by_cases hk : k < p * q
  · exact key k hk
  · have h : (∑ i ∈ range (k + 1), (cyclotomic (p * q) ℤ).coeff i) = psum p q (p * q - 1 + 1) := by
      rw [Nat.sub_add_cancel hpq, psum, ← sum_range_add_sum_Ico _ (show p * q ≤ k + 1 by omega)]
      rw [add_eq_left]
      exact sum_eq_zero fun i hi => coeff_binary_of_ge hp hq hu hv huq hvp (mem_Ico.1 hi).1
    rw [h]
    exact key _ (by omega)

include hp hq hu hv huq hvp in
/-- Theorem 2: exactly `u v` coefficients equal `1`. -/
theorem card_coeff_eq_one :
    ((range (p * q)).filter (fun m => (cyclotomic (p * q) ℤ).coeff m = 1)).card = u * v := by
  rw [← card_range u, ← card_range v, ← card_product]
  apply card_nbij' (fun m => (alp q u m, bet p v m)) (fun ab => ab.1 * p + ab.2 * q)
  · intro m hm
    simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hm
    rw [coeff_binary_eq_one_iff hp hq hu hv huq hvp] at hm
    simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio]
    exact ⟨hm.2.2.1, hm.2.2.2⟩
  · intro ab hab
    simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio] at hab
    simp only [coe_filter, mem_range, Set.mem_setOf_eq]
    have ha := alp_rep (p := p) (β := ab.2) hq hu (show ab.1 < q by omega)
    have hb := bet_rep (q := q) (α := ab.1) hp hv (show ab.2 < p by omega)
    have hlt := E_pos_lt hp hq hu hv huq hvp (m := ab.1 * p + ab.2 * q) (by rw [ha]; exact hab.1)
      (by rw [hb]; exact hab.2)
    rw [ha, hb] at hlt
    refine ⟨by omega, ?_⟩
    rw [coeff_binary_eq_one_iff hp hq hu hv huq hvp, ha, hb]
    exact ⟨by omega, hab.1, hab.2⟩
  · intro m hm
    simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hm
    rw [coeff_binary_eq_one_iff hp hq hu hv huq hvp] at hm
    exact E_eq_of_pos hp hq hu hv huq hvp hm.2.1 hm.2.2.1 hm.2.2.2
  · intro ab hab
    simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio] at hab
    dsimp only
    rw [alp_rep hq hu (show ab.1 < q by omega), bet_rep hp hv (show ab.2 < p by omega)]


include hp hq hu hv in
lemma psum_up {y z : ℕ} (hz : z ≤ p * q) (hy : psum p q y = 1) (hyz : z = y + p ∨ z = y + q) :
    psum p q z = 1 := by
  have hy1 : 1 ≤ y := by
    rcases Nat.eq_zero_or_pos y with rfl | h
    · rw [psum_zero] at hy; exact absurd hy zero_ne_one
    · exact h
  have hyq : y ≤ p * q := by omega
  obtain ⟨a, b, hab⟩ := (psum_eq_one_iff hp hq hu hv hy1 hyq).1 hy
  rw [psum_eq_one_iff hp hq hu hv (by omega) hz]
  rcases hyz with rfl | rfl
  · exact ⟨a + 1, b, by rw [add_mul, one_mul]; omega⟩
  · exact ⟨a, b + 1, by rw [add_mul, one_mul]; omega⟩

include hp hq hu hv in
lemma not_plus_two {K N : ℕ} (hN : N ≤ p * q) (h1 : qsum p q K N = 1)
    (h2 : qsum p q K (N - p) = 0) (h3 : qsum p q K (N - q) = 0)
    (h4 : qsum p q K (N - p - q) = 1) : False := by
  unfold qsum at h1 h2 h3 h4
  have hx1 : 1 ≤ N - p - q := by
    by_contra hx
    rw [show N - p - q = 0 by omega, Nat.zero_min, psum_zero] at h4
    exact zero_ne_one h4
  by_cases hK : K + 1 ≤ N - p - q
  · rw [min_eq_right hK] at h4
    rw [min_eq_right (by omega)] at h3
    rw [h3] at h4; exact zero_ne_one h4
  rw [min_eq_left (by omega)] at h4
  by_cases hp' : N - q ≤ K + 1
  · rw [min_eq_left hp', psum_up hp hq hu hv (by omega) h4 (Or.inl (by omega))] at h3
    exact one_ne_zero h3
  by_cases hq' : N - p ≤ K + 1
  · rw [min_eq_left hq', psum_up hp hq hu hv (by omega) h4 (Or.inr (by omega))] at h2
    exact one_ne_zero h2
  rw [min_eq_right (by omega)] at h1 h3
  rw [h3] at h1; exact zero_ne_one h1

include hp hq hu hv in
lemma not_minus_two {K N : ℕ} (hN : N ≤ p * q) (h1 : qsum p q K N = 0)
    (h2 : qsum p q K (N - p) = 1) (h3 : qsum p q K (N - q) = 1)
    (h4 : qsum p q K (N - p - q) = 0) : False := by
  unfold qsum at h1 h2 h3 h4
  have side : ∀ m, m = p ∨ m = q → psum p q (min (N - m) (K + 1)) = 1 →
      1 ≤ N - m ∧ N - m ≤ K := by
    intro m hm h
    refine ⟨?_, ?_⟩
    · by_contra hx
      rw [show N - m = 0 by omega, Nat.zero_min, psum_zero] at h
      exact zero_ne_one h
    · by_contra hx
      rw [min_eq_right (by omega)] at h
      rw [min_eq_right (by omega)] at h1
      rw [h1] at h; exact zero_ne_one h
  obtain ⟨a1, a2⟩ := side p (Or.inl rfl) h2
  obtain ⟨b1, b2⟩ := side q (Or.inr rfl) h3
  rw [min_eq_left (by omega)] at h2 h3 h4
  obtain ⟨a, b, hab⟩ := (psum_eq_one_iff hp hq hu hv a1 (by omega)).1 h2
  obtain ⟨a', b', hab'⟩ := (psum_eq_one_iff hp hq hu hv b1 (by omega)).1 h3
  have hb : b = 0 := by
    by_contra hb
    obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
    have hq2 := hq.two_le
    rw [Nat.succ_mul] at hab
    have h5 : psum p q (N - p - q) = 1 :=
      (psum_eq_one_iff hp hq hu hv (by omega) (by omega)).2 ⟨a, c, by omega⟩
    rw [h4] at h5; exact zero_ne_one h5
  have ha' : a' = 0 := by
    by_contra ha'
    obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha'
    have hp2 := hp.two_le
    rw [Nat.succ_mul] at hab'
    have h5 : psum p q (N - p - q) = 1 :=
      (psum_eq_one_iff hp hq hu hv (by omega) (by omega)).2 ⟨c, b', by omega⟩
    rw [h4] at h5; exact zero_ne_one h5
  subst hb ha'
  have hdp : p ∣ N - 1 := ⟨a + 1, by rw [mul_add, mul_one, mul_comm]; omega⟩
  have hdq : q ∣ N - 1 := ⟨b' + 1, by rw [mul_add, mul_one, mul_comm]; omega⟩
  have hd := Nat.Coprime.mul_dvd_of_dvd_of_dvd (coprime_pq hp hq hu) hdp hdq
  have h0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
  have hp2 := hp.two_le
  omega

include hp hq hu hv in
lemma qsum_cases (K : ℕ) {x : ℕ} (hx : x ≤ p * q) : qsum p q K x = 0 ∨ qsum p q K x = 1 :=
  psum_cases hp hq hu hv (le_trans (min_le_left _ _) hx)

include hp hq hu hv in
/-- The four-term bound for truncated partial sums. -/
theorem four_term (K : ℕ) {N : ℕ} (hN : N ≤ p * q) :
    |qsum p q K N - qsum p q K (N - p) - qsum p q K (N - q) + qsum p q K (N - p - q)| ≤ 1 := by
  have c1 := qsum_cases hp hq hu hv K hN
  have c2 := qsum_cases hp hq hu hv K (show N - p ≤ p * q by omega)
  have c3 := qsum_cases hp hq hu hv K (show N - q ≤ p * q by omega)
  have c4 := qsum_cases hp hq hu hv K (show N - p - q ≤ p * q by omega)
  have np := fun a b c d => not_plus_two hp hq hu hv (K := K) hN a b c d
  have nm := fun a b c d => not_minus_two hp hq hu hv (K := K) hN a b c d
  rw [abs_le]
  rcases c1 with c1 | c1 <;> rcases c2 with c2 | c2 <;> rcases c3 with c3 | c3 <;>
    rcases c4 with c4 | c4 <;> rw [c1, c2, c3, c4] <;> norm_num
  · exact nm c1 c2 c3 c4
  · exact np c1 c2 c3 c4

end

end TuringTask
