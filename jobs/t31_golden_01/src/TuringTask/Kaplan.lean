import TuringTask.Partial

/-!
# Kaplan's lemma for ternary cyclotomic polynomials

Let `p, q, r` be distinct primes and write `b_i` for the coefficients of `Φ_{pq}` and `a_k` for
those of `Φ_{pqr}`. With `L = (1 + X + ... + X^{p-1}) (1 - X^q)` one has `Φ_{pq} L = 1 - X^{pq}`
and `Φ_{pq}(X^r) = Φ_{pqr} Φ_{pq}`, hence `Φ_{pqr} (1 - X^{pq}) = Φ_{pq}(X^r) L`. Comparing
coefficients and telescoping gives
`a_k = ∑_{i < pq, r i ≤ k} b_i ℓ((k - r i) mod pq)`, where `ℓ` is the coefficient sequence of `L`.

Reindexing by the residue `m = (k - r i) mod pq` turns this into
`a_k = ∑_{m < p} (B(f(m)) - B(f(m + q)))`, where `f(m) = c (k - m) mod pq` for an inverse `c`
of `r` modulo `pq`, and `B(i) = b_i` if `r i ≤ k` and `0` otherwise.
-/

namespace TuringTask

open Polynomial Finset

/-- The coefficients of `L = (1 + X + ... + X^{p-1}) (1 - X^q)`. -/
def ell (p q n : ℕ) : ℤ := (if n < p then 1 else 0) - (if q ≤ n ∧ n < q + p then 1 else 0)

/-- The polynomial `L = (1 + X + ... + X^{p-1}) (1 - X^q)`. -/
noncomputable def Lp (p q : ℕ) : ℤ[X] := (∑ m ∈ range p, X ^ m) * (1 - X ^ q)

/-- The residue of `k - w i` modulo `n`. -/
def rho (n w k i : ℕ) : ℕ := ((k : ZMod n) - w * i).val

/-- The residue of `c (k - m)` modulo `n`. -/
def fc (n c k m : ℕ) : ℕ := ((c : ZMod n) * ((k : ZMod n) - m)).val

/-- The cut-off coefficient `B(i)`: `b_i` if `r i ≤ k`, else `0`. -/
noncomputable def Gk (p q r k i : ℕ) : ℤ := if r * i ≤ k then (cyclotomic (p * q) ℤ).coeff i else 0

lemma coeff_Lp (p q n : ℕ) : (Lp p q).coeff n = ell p q n := by
  unfold Lp ell
  rw [mul_sub, mul_one, coeff_sub, sum_mul, finsetSum_coeff, finsetSum_coeff]
  simp only [← pow_add, coeff_X_pow]
  congr 1
  · rw [sum_ite_eq]; simp only [mem_range]
  · split_ifs with h
    · rw [sum_eq_single (n - q) (fun m _ hne => if_neg (by omega))
        (fun h' => absurd (mem_range.2 (by omega)) h'), if_pos (by omega)]
    · exact sum_eq_zero fun m hm => if_neg (by rw [mem_range] at hm; omega)

lemma ell_zero_of_ge {p q n : ℕ} (h : p + q ≤ n) : ell p q n = 0 := by
  unfold ell; rw [if_neg (by omega), if_neg (by omega)]; rfl

/-- Splitting a sum against `ℓ`. -/
lemma sum_mul_ell {p q n : ℕ} (h : p + q ≤ n) (g : ℕ → ℤ) :
    ∑ m ∈ range n, g m * ell p q m = ∑ m ∈ range p, g m - ∑ m ∈ range p, g (m + q) := by
  unfold ell
  simp only [mul_sub, mul_ite, mul_one, mul_zero, sum_sub_distrib]
  rw [← sum_filter, ← sum_filter]
  congr 1
  · congr 1; ext m; simp only [mem_filter, mem_range]; omega
  · rw [show (range n).filter (fun m => q ≤ m ∧ m < q + p) = Ico q (q + p) by
      ext m; simp only [mem_filter, mem_range, mem_Ico]; omega, sum_Ico_eq_sum_range,
      Nat.add_sub_cancel_left]
    exact sum_congr rfl fun m _ => by rw [add_comm]

/-- Reindexing a sum over residues by `i ↦ (k - w i) mod n`. -/
lemma reindex {n c w : ℕ} [NeZero n] (hcw : (c : ZMod n) * w = 1) (k : ℕ) (g F : ℕ → ℤ) :
    ∑ i ∈ range n, g i * F (rho n w k i) = ∑ m ∈ range n, g (fc n c k m) * F m := by
  have left : ∀ i, i < n → fc n c k (rho n w k i) = i := by
    intro i hi
    unfold fc rho
    rw [ZMod.natCast_zmod_val, sub_sub_cancel, ← mul_assoc, hcw, one_mul,
      ZMod.val_natCast_of_lt hi]
  apply sum_nbij' (fun i => rho n w k i) (fun m => fc n c k m)
  · intro i _; exact mem_range.2 (ZMod.val_lt _)
  · intro m _; exact mem_range.2 (ZMod.val_lt _)
  · intro i hi; exact left i (mem_range.1 hi)
  · intro m hm
    unfold fc rho
    rw [ZMod.natCast_zmod_val, ← mul_assoc, mul_comm (w : ZMod n), hcw, one_mul,
      sub_sub_cancel, ZMod.val_natCast_of_lt (mem_range.1 hm)]
  · intro i hi; rw [left i (mem_range.1 hi)]

lemma two_add_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime) : p + q ≤ p * q := by
  have := hp.two_le; have := hq.two_le; nlinarith

section

variable {p q u : ℕ} (hp : p.Prime) (hq : q.Prime) (hu : u * p % q = 1)
  {r : ℕ} (hr : r.Prime) (hrp : r ≠ p) (hrq : r ≠ q)

include hp hq hu in
lemma cyc_mul_Lp : cyclotomic (p * q) ℤ * Lp p q = 1 - X ^ (p * q) := by
  have hc := cyc_mul hp hq hu
  have hg := geom_sum_mul (X : ℤ[X]) p
  have hX : (X - 1 : ℤ[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : ℤ)
  apply mul_right_cancel₀ hX
  unfold Lp
  linear_combination (cyclotomic (p * q) ℤ * (1 - X ^ q)) * hg - hc

include hp hq hu hr hrp hrq in
lemma ternary_id : cyclotomic (p * q * r) ℤ * (1 - X ^ (p * q)) =
    expand ℤ r (cyclotomic (p * q) ℤ) * Lp p q := by
  have hd : ¬ r ∣ p * q := by
    intro h
    rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).1 h)
    · exact hrq ((Nat.prime_dvd_prime_iff_eq hr hq).1 h)
  rw [cyclotomic_expand_eq_cyclotomic_mul hr hd, mul_assoc (cyclotomic (p * q * r) ℤ),
    cyc_mul_Lp hp hq hu]

include hp hq in
lemma natDegree_lt : (cyclotomic (p * q) ℤ).natDegree < p * q := by
  rw [natDegree_cyclotomic]
  exact Nat.totient_lt _ (by have := two_add_le hp hq; have := hp.two_le; omega)

include hp hq hu hr hrp hrq in
lemma kaplan_step (k : ℕ) : (cyclotomic (p * q * r) ℤ).coeff k -
    (if p * q ≤ k then (cyclotomic (p * q * r) ℤ).coeff (k - p * q) else 0) =
    ∑ i ∈ range (p * q), if r * i ≤ k then
      (cyclotomic (p * q) ℤ).coeff i * ell p q (k - r * i) else 0 := by
  have hexp : expand ℤ r (cyclotomic (p * q) ℤ) =
      ∑ i ∈ range (p * q), C ((cyclotomic (p * q) ℤ).coeff i) * X ^ (r * i) := by
    conv_lhs => rw [as_sum_range' (cyclotomic (p * q) ℤ) (p * q) (natDegree_lt hp hq)]
    simp only [map_sum, ← C_mul_X_pow_eq_monomial, map_mul, expand_C, map_pow, expand_X, ← pow_mul]
  have h := congrArg (fun f => f.coeff k) (ternary_id hp hq hu hr hrp hrq)
  simp only [mul_sub, mul_one, coeff_sub, coeff_mul_X_pow'] at h
  rw [h, hexp, sum_mul, finsetSum_coeff]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_Lp, mul_ite, mul_zero]

include hp hq hu hr hrp hrq in
/-- Kaplan's formula. -/
theorem kaplan (k : ℕ) : (cyclotomic (p * q * r) ℤ).coeff k =
    ∑ i ∈ range (p * q), if r * i ≤ k then
      (cyclotomic (p * q) ℤ).coeff i * ell p q ((k - r * i) % (p * q)) else 0 := by
  have h2 := two_add_le hp hq
  have hp2 := hp.two_le
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hs := kaplan_step hp hq hu hr hrp hrq k
    by_cases hk : p * q ≤ k
    · rw [if_pos hk, ih (k - p * q) (by omega)] at hs
      rw [eq_add_of_sub_eq hs, ← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      split_ifs with h1 h3
      · rw [ell_zero_of_ge (by omega : p + q ≤ k - r * i),
          show k - r * i = (k - p * q - r * i) + p * q by omega, Nat.add_mod_right]
        ring
      · rw [Nat.mod_eq_of_lt (show k - r * i < p * q by omega)]; ring
      · omega
      · rfl
    · rw [if_neg hk, sub_zero] at hs
      rw [hs]
      refine sum_congr rfl fun i _ => ?_
      split_ifs with h1
      · rw [Nat.mod_eq_of_lt (show k - r * i < p * q by omega)]
      · rfl

include hp hq hu hr hrp hrq in
/-- Kaplan's formula in residue form. -/
theorem kaplan_res {c : ℕ} (hc : (c : ZMod (p * q)) * r = 1) (k : ℕ) :
    (cyclotomic (p * q * r) ℤ).coeff k = ∑ m ∈ range p,
      (Gk p q r k (fc (p * q) c k m) - Gk p q r k (fc (p * q) c k (m + q))) := by
  haveI : NeZero (p * q) := ⟨by have := hp.two_le; have := hq.two_le; positivity⟩
  rw [kaplan hp hq hu hr hrp hrq, sum_sub_distrib,
    ← sum_mul_ell (two_add_le hp hq) (fun m => Gk p q r k (fc (p * q) c k m)),
    ← reindex hc k (Gk p q r k) (ell p q)]
  refine sum_congr rfl fun i _ => ?_
  unfold Gk rho
  split_ifs with h
  · rw [← ZMod.val_natCast, Nat.cast_sub h, Nat.cast_mul]
  · rw [zero_mul]

end

end TuringTask
