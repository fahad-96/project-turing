import TuringTask.Bang

/-!
# Consecutive ternary coefficients differ by at most one

Write `F(x) = c (k + 1 - x) mod pq`. Comparing Kaplan's residue form at `k + 1` and at `k`
(whose residues are `F(m + 1)`) leaves only four terms:
`a_{k+1} - a_k = B_{k+1}(F 0) - B_k(F q) - B_k(F p) + B_k(F (p + q))`.
The pairs `(F 0, F q)` and `(F p, F (p + q))` share `alp`, and the pairs `(F 0, F p)` and
`(F q, F (p + q))` share `bet`, so the uncut values cancel. A difference of size `2` would need
all four points in the positive region or all four in the negative region; then
`F 0 + F (p + q) = F p + F q`, which contradicts the cut-off inequalities.
-/

namespace TuringTask

open Polynomial Finset

lemma cA_eq_one_iff {q u i : ℕ} : cA q u i = 1 ↔ alp q u i < u := by
  unfold cA; split_ifs with h <;> simp [h]

lemma cA_eq_zero_iff {q u i : ℕ} : cA q u i = 0 ↔ u ≤ alp q u i := by
  unfold cA; split_ifs with h <;> simp [h]; omega

lemma cB_eq_one_iff {p v i : ℕ} : cB p v i = 1 ↔ bet p v i < v := by
  unfold cB; split_ifs with h <;> simp [h]

lemma cB_eq_zero_iff {p v i : ℕ} : cB p v i = 0 ↔ v ≤ bet p v i := by
  unfold cB; split_ifs with h <;> simp [h]; omega

lemma fc_succ (n c k m : ℕ) : fc n c k m = fc n c (k + 1) (m + 1) := by
  unfold fc; push_cast; ring_nf

lemma Gk_succ_sub (p q r k i : ℕ) : Gk p q r (k + 1) i - Gk p q r k i =
    if r * i = k + 1 then (cyclotomic (p * q) ℤ).coeff i else 0 := by
  unfold Gk; split_ifs <;> omega

section

variable {p q u v : ℕ} (hp : p.Prime) (hq : q.Prime) (hu : u * p % q = 1) (hv : v * q % p = 1)
  (huq : u < q) (hvp : v < p)
  {r : ℕ} (hr : r.Prime) (hrp : r ≠ p) (hrq : r ≠ q)

include hp hq in
lemma r_fc_ne {c : ℕ} (hc : (c : ZMod (p * q)) * r = 1) (k : ℕ) {x : ℕ} (hx : x < p * q)
    (hx0 : x ≠ 0) : r * fc (p * q) c (k + 1) x ≠ k + 1 := by
  haveI := nezero_pq hp hq
  intro h
  have h2 := congrArg (fun n : ℕ => (n : ZMod (p * q))) h
  simp only [Nat.cast_mul, fc, ZMod.natCast_zmod_val] at h2
  rw [← mul_assoc, mul_comm (r : ZMod (p * q)), hc, one_mul] at h2
  have h3 : ((x : ℕ) : ZMod (p * q)) = 0 := by
    have : ((k + 1 : ℕ) : ZMod (p * q)) - x - (k + 1 : ℕ) = 0 := by rw [h2]; ring
    simpa using this
  rw [ZMod.natCast_eq_zero_iff] at h3
  exact hx0 (Nat.eq_zero_of_dvd_of_lt h3 hx)

include hp hq hu hr hrp hrq in
lemma jump_formula {c : ℕ} (hc : (c : ZMod (p * q)) * r = 1) (k : ℕ) :
    (cyclotomic (p * q * r) ℤ).coeff (k + 1) - (cyclotomic (p * q * r) ℤ).coeff k =
      Gk p q r (k + 1) (fc (p * q) c (k + 1) 0) - Gk p q r k (fc (p * q) c (k + 1) q) -
        Gk p q r k (fc (p * q) c (k + 1) p) + Gk p q r k (fc (p * q) c (k + 1) (p + q)) := by
  have h2 := two_add_le hp hq
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  set F := fun x => fc (p * q) c (k + 1) x with hF
  have hk : (cyclotomic (p * q * r) ℤ).coeff k = ∑ m ∈ range p,
      (Gk p q r k (F (m + 1)) - Gk p q r k (F (m + 1 + q))) := by
    rw [kaplan_res hp hq hu hr hrp hrq hc k]
    refine sum_congr rfl fun m _ => ?_
    simp only [hF]
    rw [fc_succ (p * q) c k m, fc_succ (p * q) c k (m + q), add_right_comm]
  have hshift := sum_range_succ' (fun m => Gk p q r k (F m) - Gk p q r k (F (m + q))) p
  rw [sum_range_succ] at hshift
  rw [hk, kaplan_res hp hq hu hr hrp hrq hc (k + 1)]
  have hsum : ∑ m ∈ range p, ((Gk p q r (k + 1) (F m) - Gk p q r (k + 1) (F (m + q))) -
      (Gk p q r k (F m) - Gk p q r k (F (m + q)))) =
      Gk p q r (k + 1) (F 0) - Gk p q r k (F 0) := by
    rw [sum_eq_single 0]
    · have := Gk_succ_sub p q r k (F q)
      rw [if_neg (r_fc_ne hp hq hc k (by omega) (by omega))] at this
      simp only [zero_add]
      linarith
    · intro m hm hm0
      have e1 := Gk_succ_sub p q r k (F m)
      have e2 := Gk_succ_sub p q r k (F (m + q))
      rw [mem_range] at hm
      rw [if_neg (r_fc_ne hp hq hc k (by omega) hm0)] at e1
      rw [if_neg (r_fc_ne hp hq hc k (by omega) (by omega))] at e2
      linarith
    · intro h; exact absurd (mem_range.2 (by omega)) h
  have hsub := sum_sub_distrib (s := range p)
    (f := fun m => Gk p q r (k + 1) (F m) - Gk p q r (k + 1) (F (m + q)))
    (g := fun m => Gk p q r k (F m) - Gk p q r k (F (m + q)))
  rw [hsub] at hsum
  simp only [hF] at hsum hshift ⊢
  rw [zero_add] at hshift
  linarith

include hp hq hu hv huq hvp in
lemma pos_rel {c k : ℕ} (h1 : u > alp q u (fc (p * q) c (k + 1) 0))
    (h2 : u > alp q u (fc (p * q) c (k + 1) p)) (h3 : v > bet p v (fc (p * q) c (k + 1) 0))
    (h4 : v > bet p v (fc (p * q) c (k + 1) q)) :
    fc (p * q) c (k + 1) 0 + fc (p * q) c (k + 1) (p + q) =
      fc (p * q) c (k + 1) p + fc (p * q) c (k + 1) q := by
  have a1 := alp_fc_add (u := u) hp hq c (k + 1) 0
  have a2 := alp_fc_add (u := u) hp hq c (k + 1) p
  have b1 := bet_fc_add (v := v) hp hq c (k + 1) 0
  have b2 := bet_fc_add (v := v) hp hq c (k + 1) q
  rw [zero_add] at a1 b1
  rw [add_comm q p] at b2
  have hlt := fun x => fc_lt hp hq c (k + 1) x
  have e0 := E_eq_of_pos hp hq hu hv huq hvp (hlt 0) h1 h3
  have e1 := E_eq_of_pos hp hq hu hv huq hvp (hlt q) (a1 ▸ h1) h4
  have e2 := E_eq_of_pos hp hq hu hv huq hvp (hlt p) h2 (b1 ▸ h3)
  have e3 := E_eq_of_pos hp hq hu hv huq hvp (hlt (p + q)) (a2 ▸ h2) (b2 ▸ h4)
  rw [a1] at e1; rw [b1] at e2; rw [a2, b2] at e3
  omega

include hp hq hu hv huq hvp in
lemma neg_rel {c k : ℕ} (h1 : u ≤ alp q u (fc (p * q) c (k + 1) 0))
    (h2 : u ≤ alp q u (fc (p * q) c (k + 1) p)) (h3 : v ≤ bet p v (fc (p * q) c (k + 1) 0))
    (h4 : v ≤ bet p v (fc (p * q) c (k + 1) q)) :
    fc (p * q) c (k + 1) 0 + fc (p * q) c (k + 1) (p + q) =
      fc (p * q) c (k + 1) p + fc (p * q) c (k + 1) q := by
  have a1 := alp_fc_add (u := u) hp hq c (k + 1) 0
  have a2 := alp_fc_add (u := u) hp hq c (k + 1) p
  have b1 := bet_fc_add (v := v) hp hq c (k + 1) 0
  have b2 := bet_fc_add (v := v) hp hq c (k + 1) q
  rw [zero_add] at a1 b1
  rw [add_comm q p] at b2
  have hlt := fun x => fc_lt hp hq c (k + 1) x
  have e0 := E_eq_of_neg hp hq hu hv huq hvp (hlt 0) h1 h3
  have e1 := E_eq_of_neg hp hq hu hv huq hvp (hlt q) (a1 ▸ h1) h4
  have e2 := E_eq_of_neg hp hq hu hv huq hvp (hlt p) h2 (b1 ▸ h3)
  have e3 := E_eq_of_neg hp hq hu hv huq hvp (hlt (p + q)) (a2 ▸ h2) (b2 ▸ h4)
  rw [a1] at e1; rw [b1] at e2; rw [a2, b2] at e3
  omega

end

/-- The four-term bound once the indicators are known. -/
lemma four_bound {A1 A2 C1 C2 : ℤ} (hA1 : A1 = 0 ∨ A1 = 1) (hA2 : A2 = 0 ∨ A2 = 1)
    (hC1 : C1 = 0 ∨ C1 = 1) (hC2 : C2 = 0 ∨ C2 = 1) {y0 yq yp ypq k : ℕ}
    (hrel : (A1 = 1 ∧ A2 = 1 ∧ C1 = 1 ∧ C2 = 1) ∨ (A1 = 0 ∧ A2 = 0 ∧ C1 = 0 ∧ C2 = 0) →
      y0 + ypq = yp + yq) :
    |(if y0 ≤ k + 1 then A1 + C1 - 1 else 0) - (if yq ≤ k then A1 + C2 - 1 else 0) -
      (if yp ≤ k then A2 + C1 - 1 else 0) + (if ypq ≤ k then A2 + C2 - 1 else 0)| ≤ 1 := by
  rw [abs_le]
  rcases hA1 with rfl | rfl <;> rcases hA2 with rfl | rfl <;> rcases hC1 with rfl | rfl <;>
    rcases hC2 with rfl | rfl <;> norm_num at hrel <;> split_ifs <;> omega

section

variable {p q u v : ℕ} (hp : p.Prime) (hq : q.Prime) (hu : u * p % q = 1) (hv : v * q % p = 1)
  (huq : u < q) (hvp : v < p)
  {r : ℕ} (hr : r.Prime) (hrp : r ≠ p) (hrq : r ≠ q)

include hp hq hu hv huq hvp hr hrp hrq in
/-- Consecutive coefficients of `Φ_{pqr}` differ by at most `1`, for distinct primes. -/
theorem jump {c : ℕ} (hc : (c : ZMod (p * q)) * r = 1) (k : ℕ) :
    |(cyclotomic (p * q * r) ℤ).coeff (k + 1) - (cyclotomic (p * q * r) ℤ).coeff k| ≤ 1 := by
  rw [jump_formula hp hq hu hr hrp hrq hc k]
  have hb := fun x => coeff_fc hp hq hu hv huq hvp c (k + 1) x
  have a1 : cA q u (fc (p * q) c (k + 1) q) = cA q u (fc (p * q) c (k + 1) 0) := by
    unfold cA; rw [← alp_fc_add hp hq c (k + 1) 0, zero_add]
  have a2 : cA q u (fc (p * q) c (k + 1) (p + q)) = cA q u (fc (p * q) c (k + 1) p) := by
    unfold cA; rw [← alp_fc_add hp hq c (k + 1) p]
  have b1 : cB p v (fc (p * q) c (k + 1) p) = cB p v (fc (p * q) c (k + 1) 0) := by
    unfold cB; rw [← bet_fc_add hp hq c (k + 1) 0, zero_add]
  have b2 : cB p v (fc (p * q) c (k + 1) (p + q)) = cB p v (fc (p * q) c (k + 1) q) := by
    unfold cB; rw [← bet_fc_add hp hq c (k + 1) q, add_comm q p]
  unfold Gk
  rw [hb 0, hb q, hb p, hb (p + q), a1, a2, b1, b2]
  apply four_bound (cA_cases _ _ _) (cA_cases _ _ _) (cB_cases _ _ _) (cB_cases _ _ _)
  rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
  · rw [← mul_add, ← mul_add, pos_rel hp hq hu hv huq hvp (cA_eq_one_iff.1 h1)
      (cA_eq_one_iff.1 h2) (cB_eq_one_iff.1 h3) (cB_eq_one_iff.1 h4)]
  · rw [← mul_add, ← mul_add, neg_rel hp hq hu hv huq hvp (cA_eq_zero_iff.1 h1)
      (cA_eq_zero_iff.1 h2) (cB_eq_zero_iff.1 h3) (cB_eq_zero_iff.1 h4)]

end

end TuringTask
