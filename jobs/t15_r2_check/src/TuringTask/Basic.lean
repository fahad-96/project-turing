/-
Polya-Vinogradov character sum bounds and applications.

This file proves five results about character sums modulo a prime `p`:

1. `charSum_norm_le`      : `|∑_{n=1}^N χ(n)| ≤ √p · log p` for a non-principal `χ`.
2. `legendreSum_le`       : the same bound for the Legendre symbol.
3. `exists_not_pow_le`    : a small `k`-th power non-residue exists.
4. `card_residues_sub_le` : the count `R` of quadratic residues in `[1,N]` satisfies
                            `|2R - N| ≤ √p · log p`.
5. `exists_prime_nonresidue_le` : a small *prime* quadratic non-residue exists.

The proof of (1) is the classical Polya-Vinogradov argument:
expand `χ(n)` via Gauss sums, swap the order of summation, bound each inner
geometric sum by `1 / sin(π t / p)`, and estimate
`∑_{t=1}^{p-1} 1/sin(π t/p) ≤ p · log p` using Jordan's inequality together with
the harmonic-sum bound `∑_{k=1}^m 1/k ≤ log(2m+1)`.

Results (2)-(5) are deduced from (1).
-/
import Mathlib

open Finset Real Complex

namespace TuringTask

/-! ### Elementary estimates -/

theorem harmonicSum_le_log (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 m, (k : ℝ)⁻¹ ≤ Real.log (2 * m + 1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have ha : (0:ℝ) < (2 * (m:ℝ) + 1) / 2 := by positivity
    have hs := Real.hasSum_log_one_add_inv ha
    have h0 := le_hasSum hs 0 (fun j _ => by positivity)
    have e1 : (1 : ℝ) + ((2 * (m:ℝ) + 1)/2)⁻¹ = (2 * ((m:ℝ)+1) + 1) / (2 * (m:ℝ) + 1) := by
      field_simp; ring
    rw [e1, Real.log_div (by positivity) (by positivity)] at h0
    have e2 : (2:ℝ) * (1 / (2 * ((0:ℕ):ℝ) + 1)) * (1 / (2 * ((2 * (m:ℝ) + 1)/2) + 1)) ^ (2 * 0 + 1)
        = ((m:ℝ) + 1)⁻¹ := by
      have : (2:ℝ) * ((2 * (m:ℝ) + 1)/2) + 1 = 2 * ((m:ℝ) + 1) := by ring
      rw [this]; norm_num; rw [mul_comm]; field_simp
    rw [e2] at h0
    push_cast
    linarith

theorem split_Icc (m : ℕ) (f : ℕ → ℝ) :
    ∑ t ∈ Finset.Icc 1 (2*m), f t
      = ∑ t ∈ Finset.Icc 1 m, f t + ∑ t ∈ Finset.Icc 1 m, f (2*m+1 - t) := by
  have hsplit : Finset.Icc 1 (2*m) = Finset.Icc 1 m ∪ Finset.Icc (m+1) (2*m) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  rw [hsplit, Finset.sum_union (by
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_Icc] at ha hb; omega)]
  congr 1
  refine Finset.sum_nbij' (i := fun t => 2*m+1-t) (j := fun s => 2*m+1-s) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [Finset.mem_Icc] at *; omega
  · intro a ha; simp only [Finset.mem_Icc] at *; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; congr 1; omega

theorem sin_inv_sum_le (m : ℕ) (hm : 1 ≤ m) :
    ∑ t ∈ Finset.Icc 1 (2*m), (Real.sin (π * t / (2*(m:ℝ)+1)))⁻¹
      ≤ (2*(m:ℝ)+1) * Real.log (2*(m:ℝ)+1) := by
  have hsym : ∀ t ∈ Finset.Icc 1 m,
      (Real.sin (π * ((2*m+1 - t : ℕ):ℝ) / (2*(m:ℝ)+1)))⁻¹
        = (Real.sin (π * t / (2*(m:ℝ)+1)))⁻¹ := by
    intro t ht
    simp only [Finset.mem_Icc] at ht
    have hc : ((2*m+1 - t : ℕ) : ℝ) = (2*(m:ℝ)+1) - t := by
      have hle : t ≤ 2*m+1 := by omega
      push_cast [Nat.cast_sub hle]; ring
    rw [hc]
    congr 1
    have e : π * ((2*(m:ℝ)+1) - t) / (2*(m:ℝ)+1) = π - π * t / (2*(m:ℝ)+1) := by field_simp
    rw [e, Real.sin_pi_sub]
  have hjord : ∀ t ∈ Finset.Icc 1 m,
      (Real.sin (π * t / (2*(m:ℝ)+1)))⁻¹ ≤ (2*(m:ℝ)+1) / 2 * (t:ℝ)⁻¹ := by
    intro t ht
    simp only [Finset.mem_Icc] at ht
    have htpos : (0:ℝ) < t := by exact_mod_cast ht.1
    have h1 : (0:ℝ) ≤ π * t / (2*(m:ℝ)+1) := by positivity
    have h2 : π * (t:ℝ) / (2*(m:ℝ)+1) ≤ π / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have ht2 : (t:ℝ) ≤ m := by exact_mod_cast ht.2
      nlinarith [Real.pi_pos]
    have hlb : 2 * (t:ℝ)/(2*(m:ℝ)+1) ≤ Real.sin (π * t / (2*(m:ℝ)+1)) := by
      have hj := Real.mul_le_sin h1 h2
      calc 2 * (t:ℝ)/(2*(m:ℝ)+1) = 2 / π * (π * t / (2*(m:ℝ)+1)) := by field_simp
        _ ≤ _ := hj
    have hpos : (0:ℝ) < 2 * (t:ℝ)/(2*(m:ℝ)+1) := by positivity
    rw [inv_le_iff_one_le_mul₀ (lt_of_lt_of_le hpos hlb)]
    calc (1:ℝ) = ((2*(m:ℝ)+1) / 2 * (t:ℝ)⁻¹) * (2 * (t:ℝ)/(2*(m:ℝ)+1)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlb (by positivity)
  rw [split_Icc m (fun t => (Real.sin (π * t / (2*(m:ℝ)+1)))⁻¹)]
  rw [Finset.sum_congr rfl hsym]
  have hbd : ∑ t ∈ Finset.Icc 1 m, (Real.sin (π * t / (2*(m:ℝ)+1)))⁻¹
      ≤ (2*(m:ℝ)+1) / 2 * ∑ t ∈ Finset.Icc 1 m, (t:ℝ)⁻¹ := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum hjord
  have hH := harmonicSum_le_log m
  nlinarith [hbd, hH, Real.log_nonneg (show (1:ℝ) ≤ 2*(m:ℝ)+1 by
    have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m; linarith)]

/-! ### Auxiliary inequality -/

theorem sqrt_mul_log_lt (x : ℝ) (hx : 3 ≤ x) : Real.sqrt x * Real.log x < x - 1 := by
  have hx0 : (0:ℝ) < x := by linarith
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hs3 : Real.sqrt 3 ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
  have hs3' : (1.7320508 : ℝ) < Real.sqrt 3 := by
    rw [show (1.7320508:ℝ) = Real.sqrt (1.7320508^2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hspos : (0:ℝ) < Real.sqrt x := by linarith
  have hkey : Real.log (Real.sqrt x) - Real.log 2 ≤ Real.sqrt x / 2 - 1 := by
    rw [← Real.log_div (ne_of_gt hspos) (by norm_num)]
    exact Real.log_le_sub_one_of_pos (by positivity)
  have hlx : Real.log x = 2 * Real.log (Real.sqrt x) := by rw [Real.log_sqrt hx0.le]; ring
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  calc Real.sqrt x * Real.log x = 2 * Real.sqrt x * Real.log (Real.sqrt x) := by rw [hlx]; ring
    _ ≤ 2 * Real.sqrt x * (Real.sqrt x / 2 + Real.log 2 - 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = x + 2 * Real.sqrt x * (Real.log 2 - 1) := by nlinarith [hsq]
    _ < x - 1 := by nlinarith [hs3, hs3', hl2, hspos]

/-! ### Complex-analytic ingredients -/

theorem geom_Icc (z : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, z ^ n = (∑ n ∈ Finset.range (N+1), z ^ n) - 1 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]; ring

theorem norm_geom_Icc_le (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, z ^ n‖ ≤ 2 / ‖z - 1‖ := by
  have hzz : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hzn : (0:ℝ) < ‖z - 1‖ := norm_pos_iff.mpr hzz
  rw [geom_Icc, geom_sum_eq hz1]
  have e : (z ^ (N+1) - 1) / (z - 1) - 1 = (z^(N+1) - z) / (z - 1) := by field_simp; ring
  rw [e, norm_div, div_le_div_iff_of_pos_right hzn]
  calc ‖z ^ (N+1) - z‖ ≤ ‖z ^ (N+1)‖ + ‖z‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hz]; norm_num

theorem norm_exp_mul_I_sub_one (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  have hns : Complex.normSq (Complex.exp ((θ : ℂ) * Complex.I) - 1) = 2 - 2 * Real.cos θ := by
    rw [Complex.exp_mul_I]
    simp [Complex.normSq_apply, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    ring_nf
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hcos : Real.cos θ = 1 - 2 * Real.sin (θ/2) ^ 2 := by
    have h2 : Real.cos θ = Real.cos (2 * (θ/2)) := by rw [show (2:ℝ) * (θ/2) = θ by ring]
    rw [h2, Real.cos_two_mul']
    nlinarith [Real.sin_sq_add_cos_sq (θ/2)]
  have h : ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ 2 = (2 * |Real.sin (θ/2)|) ^ 2 := by
    rw [Complex.sq_norm, hns, hcos, mul_pow, sq_abs]; ring
  nlinarith [h, norm_nonneg (Complex.exp ((θ : ℂ) * Complex.I) - 1),
    abs_nonneg (Real.sin (θ/2))]

theorem norm_stdAddChar_sub_one (p : ℕ) [NeZero p] (t : ZMod p) :
    ‖ZMod.stdAddChar t - 1‖ = 2 * Real.sin (π * t.val / p) := by
  have hv : ((t.val : ℕ) : ZMod p) = t := ZMod.natCast_zmod_val t
  have he : ZMod.stdAddChar t = Complex.exp (((2 * π * t.val / p : ℝ) : ℂ) * Complex.I) := by
    have h1 := ZMod.stdAddChar_coe (N := p) ((t.val : ℕ) : ℤ)
    push_cast at h1
    rw [hv] at h1
    rw [h1]; congr 1; push_cast; ring
  rw [he, norm_exp_mul_I_sub_one]
  congr 1
  have harg : (2 * π * (t.val:ℝ) / p) / 2 = π * t.val / p := by ring
  have hp : (0:ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hvnn : (0:ℝ) ≤ (t.val:ℝ) := Nat.cast_nonneg _
  have hvle : (t.val : ℝ) ≤ p := by exact_mod_cast (ZMod.val_lt t).le
  rw [harg, abs_of_nonneg]
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · positivity
  · rw [div_le_iff₀ hp]; nlinarith [Real.pi_pos]

/-! ### Gauss sums -/

theorem norm_gaussSum_eq (p : ℕ) [Fact p.Prime] (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) :
    ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hprim := ZMod.isPrimitive_stdAddChar p
  have h := gaussSum_mul_gaussSum_eq_card (R := ZMod p) hχ hprim
  rw [ZMod.card] at h
  have hstar : (starRingEnd ℂ) (gaussSum χ ZMod.stdAddChar) = gaussSum χ⁻¹ ZMod.stdAddChar⁻¹ :=
    star_gaussSum_eq _ _
  have h2 : ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = (p : ℝ) := by
    have hmc := Complex.mul_conj (gaussSum χ ZMod.stdAddChar)
    rw [hstar, h] at hmc
    have hp2 : (p : ℝ) = Complex.normSq (gaussSum χ ZMod.stdAddChar) := by exact_mod_cast hmc
    rw [Complex.sq_norm]; exact hp2.symm
  rw [← h2, Real.sqrt_sq (norm_nonneg _)]

theorem sum_ZMod_eq_sum_range {M : Type*} [AddCommMonoid M] (p : ℕ) [NeZero p] (f : ZMod p → M) :
    ∑ t : ZMod p, f t = ∑ v ∈ Finset.range p, f (v : ZMod p) := by
  apply Finset.sum_nbij' (i := fun t => (ZMod.val t)) (j := fun v => ((v : ℕ) : ZMod p))
  · intro a _; simp [Finset.mem_range, ZMod.val_lt]
  · intro a _; exact Finset.mem_univ _
  · intro a _; simp
  · intro a ha; simp only [Finset.mem_range] at ha; exact ZMod.val_cast_of_lt ha
  · intro a _; rw [ZMod.natCast_zmod_val]

theorem key_identity (p : ℕ) [Fact p.Prime] (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (n : ZMod p) :
    χ n * gaussSum χ⁻¹ ZMod.stdAddChar = ∑ t : ZMod p, χ⁻¹ t * ZMod.stdAddChar (t * n) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hrhs : ∑ t : ZMod p, χ⁻¹ t * ZMod.stdAddChar (t * n)
      = gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift n) := by
    unfold gaussSum
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [AddChar.mulShift_apply]
    ring_nf
  rw [hrhs]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [AddChar.mulShift_zero, MulChar.map_nonunit _ (by simp), zero_mul]
    refine (gaussSum_one_right ?_).symm
    intro h
    apply hχ
    have hinv : χ = (χ⁻¹)⁻¹ := by simp
    rw [hinv, h, inv_one]
  · obtain ⟨u, rfl⟩ := Ne.isUnit hn
    rw [gaussSum_mulShift_eq χ⁻¹ ZMod.stdAddChar u]
    simp

/-! ### Main Polya-Vinogradov bound -/

theorem charSum_norm_le_aux (p : ℕ) [hp : Fact p.Prime] (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1)
    (N : ℕ) : ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod p)‖ ≤ Real.sqrt p * Real.log p := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hppos : 0 < p := hp.out.pos
  have hpR : (0:ℝ) < p := by exact_mod_cast hppos
  -- `p` is odd, write `p = 2m+1`
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hχ (MulChar.ext fun a => by
      have ha : a = 1 := Units.ext (by revert a; decide)
      simp [ha])
  obtain ⟨m, hm1, hpm⟩ : ∃ m : ℕ, 1 ≤ m ∧ p = 2 * m + 1 := by
    obtain ⟨k, hk⟩ := hp.out.odd_of_ne_two hp2
    refine ⟨k, ?_, hk⟩
    rcases Nat.eq_zero_or_pos k with rfl | h
    · subst hk; simp at hp; exact absurd hp.out (by decide)
    · omega
  -- abbreviations
  set g : ℂ := gaussSum χ⁻¹ ZMod.stdAddChar with hg
  have hχinv : χ⁻¹ ≠ 1 := by
    intro h
    exact hχ (by rw [show χ = (χ⁻¹)⁻¹ by simp, h, inv_one])
  have hgn : ‖g‖ = Real.sqrt p := norm_gaussSum_eq p χ⁻¹ hχinv
  have hgne : g ≠ 0 := by
    intro h
    rw [h, norm_zero] at hgn
    exact absurd hgn.symm (ne_of_gt (Real.sqrt_pos.mpr hpR))
  -- Step 1: expand using the key identity and swap the order of summation
  have hexp : (∑ n ∈ Finset.Icc 1 N, χ (n : ZMod p)) * g
      = ∑ t : ZMod p, χ⁻¹ t * (∑ n ∈ Finset.Icc 1 N, (ZMod.stdAddChar t) ^ n) := by
    rw [Finset.sum_mul]
    have e1 : ∀ n ∈ Finset.Icc 1 N, χ (n : ZMod p) * g
        = ∑ t : ZMod p, χ⁻¹ t * ZMod.stdAddChar (t * (n : ZMod p)) :=
      fun n _ => key_identity p χ hχ _
    rw [Finset.sum_congr rfl e1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    rw [show t * ((n : ℕ) : ZMod p) = n • t by rw [nsmul_eq_mul]; ring]
    exact AddChar.map_nsmul_eq_pow _ _ _
  -- Step 2: the t = 0 term vanishes
  have hzero : χ⁻¹ (0 : ZMod p) * (∑ n ∈ Finset.Icc 1 N, (ZMod.stdAddChar (0 : ZMod p)) ^ n) = 0 := by
    rw [MulChar.map_nonunit _ (by simp), zero_mul]
  -- Step 3: bound each term with t ≠ 0
  have hterm : ∀ t : ZMod p, t ≠ 0 →
      ‖χ⁻¹ t * (∑ n ∈ Finset.Icc 1 N, (ZMod.stdAddChar t) ^ n)‖
        ≤ (Real.sin (π * t.val / p))⁻¹ := by
    intro t ht
    have hcn : ‖χ⁻¹ t‖ = 1 := by
      obtain ⟨u, rfl⟩ := Ne.isUnit ht
      exact norm_eq_one_of_mem_rootsOfUnity ((χ⁻¹).apply_mem_rootsOfUnity u)
    have hz1 : ZMod.stdAddChar t ≠ 1 := by
      intro h
      exact ht ((ZMod.isPrimitive_stdAddChar p).zmod_char_eq_one_iff p t |>.mp h)
    have hzn : ‖ZMod.stdAddChar t‖ = 1 := AddChar.norm_apply _ _
    have hb := norm_geom_Icc_le (ZMod.stdAddChar t) hzn hz1 N
    rw [norm_stdAddChar_sub_one p t] at hb
    rw [norm_mul, hcn, one_mul]
    calc ‖∑ n ∈ Finset.Icc 1 N, (ZMod.stdAddChar t) ^ n‖
        ≤ 2 / (2 * Real.sin (π * t.val / p)) := hb
      _ = (Real.sin (π * t.val / p))⁻¹ := by rw [eq_comm, inv_eq_iff_eq_inv]; field_simp
  -- Step 4: combine
  have hmain : ‖(∑ n ∈ Finset.Icc 1 N, χ (n : ZMod p)) * g‖
      ≤ ∑ t ∈ Finset.Icc 1 (2*m), (Real.sin (π * t / (2*(m:ℝ)+1)))⁻¹ := by
    rw [hexp]
    calc ‖∑ t : ZMod p, χ⁻¹ t * (∑ n ∈ Finset.Icc 1 N, (ZMod.stdAddChar t) ^ n)‖
        ≤ ∑ t : ZMod p, ‖χ⁻¹ t * (∑ n ∈ Finset.Icc 1 N, (ZMod.stdAddChar t) ^ n)‖ :=
          norm_sum_le _ _
      _ = ∑ v ∈ Finset.range p, ‖χ⁻¹ (v : ZMod p) *
            (∑ n ∈ Finset.Icc 1 N, (ZMod.stdAddChar ((v : ℕ) : ZMod p)) ^ n)‖ := by
          exact sum_ZMod_eq_sum_range p
            (fun t => (‖χ⁻¹ t * (∑ n ∈ Finset.Icc 1 N, (ZMod.stdAddChar t) ^ n)‖ : ℝ))
      _ ≤ ∑ t ∈ Finset.Icc 1 (2*m), (Real.sin (π * t / (2*(m:ℝ)+1)))⁻¹ := by
          have hrange : Finset.range p = insert 0 (Finset.Icc 1 (2*m)) := by
            ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
          rw [hrange, Finset.sum_insert (by simp)]
          have h0 : ‖χ⁻¹ ((0:ℕ) : ZMod p) *
              (∑ n ∈ Finset.Icc 1 N, (ZMod.stdAddChar (((0:ℕ) : ℕ) : ZMod p)) ^ n)‖ = 0 := by
            rw [Nat.cast_zero, MulChar.map_nonunit _ (by simp), zero_mul, norm_zero]
          rw [h0, zero_add]
          refine Finset.sum_le_sum fun v hv => ?_
          simp only [Finset.mem_Icc] at hv
          have hvlt : v < p := by omega
          have hvne : ((v:ℕ) : ZMod p) ≠ 0 := by
            intro h
            have hd : (p:ℕ) ∣ v := (ZMod.natCast_eq_zero_iff v p).mp h
            have := Nat.le_of_dvd (by omega) hd
            omega
          have ht := hterm ((v:ℕ) : ZMod p) hvne
          rw [ZMod.val_cast_of_lt hvlt] at ht
          have hpc : ((p:ℕ):ℝ) = 2*(m:ℝ)+1 := by rw [hpm]; push_cast; ring
          rw [hpc] at ht
          exact ht
  -- Step 5: divide by ‖g‖ = √p and use the sine-sum estimate
  have hsin := sin_inv_sum_le m hm1
  have hpm' : (p:ℝ) = 2*(m:ℝ)+1 := by rw [hpm]; push_cast; ring
  rw [norm_mul, hgn] at hmain
  have hsq : (0:ℝ) < Real.sqrt p := Real.sqrt_pos.mpr hpR
  have hfinal : ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod p)‖ * Real.sqrt p ≤ (p:ℝ) * Real.log p := by
    refine hmain.trans ?_
    rw [hpm']
    exact hsin
  have hps : Real.sqrt p * Real.sqrt p = (p:ℝ) := Real.mul_self_sqrt hpR.le
  have hlog : (0:ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.out.one_lt.le)
  rw [← le_div_iff₀ hsq] at hfinal
  refine hfinal.trans (le_of_eq ?_)
  rw [div_eq_iff (ne_of_gt hsq)]
  nlinarith [hps]

/-! ### Legendre symbol as a complex multiplicative character -/

noncomputable def legChar (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

theorem legChar_apply (p : ℕ) [Fact p.Prime] (n : ℕ) :
    legChar p (n : ZMod p) = ((legendreSym p n : ℤ) : ℂ) := by
  rw [legChar, MulChar.ringHomComp_apply, legendreSym]
  norm_cast

theorem legChar_ne_one (p : ℕ) [Fact p.Prime] (h2 : p ≠ 2) : legChar p ≠ 1 := by
  rw [legChar]
  intro h
  have hq : quadraticChar (ZMod p) ≠ 1 :=
    quadraticChar_ne_one (by rw [ZMod.ringChar_zmod_n]; exact h2)
  apply hq
  apply MulChar.ext
  intro a
  have hc := congrFun (congrArg (fun (c : MulChar (ZMod p) ℂ) => (c : ZMod p → ℂ)) h) (a : ZMod p)
  simp only [MulChar.ringHomComp_apply, MulChar.one_apply a.isUnit] at hc
  have hinj : Function.Injective (Int.castRingHom ℂ) := fun x y hxy => by
    have hxy' : ((x:ℤ):ℂ) = ((y:ℤ):ℂ) := hxy
    exact_mod_cast hxy'
  rw [MulChar.one_apply a.isUnit]
  exact hinj (by rw [hc]; simp)

/-! ## Theorem 1 -/

theorem charSum_norm_le (p : Nat) (hp : p.Prime) (chi : MulChar (ZMod p) Complex)
    (h : Not (chi = 1)) (N : Nat) :
    Norm.norm ((Finset.Icc 1 N).sum (fun n => chi (n : ZMod p))) <= Real.sqrt p * Real.log p := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact charSum_norm_le_aux p chi h N

/-! ## Theorem 2 -/

theorem legendreSum_le (p : Nat) [hp : Fact p.Prime] (h2 : Not (p = 2)) (N : Nat) :
    abs (((Finset.Icc 1 N).sum (fun n => legendreSym p (n : Int)) : Int) : Real) <=
      Real.sqrt p * Real.log p := by
  have key := charSum_norm_le_aux p (legChar p) (legChar_ne_one p h2) N
  have heq : (Finset.Icc 1 N).sum (fun n => legChar p (n : ZMod p))
      = (((Finset.Icc 1 N).sum (fun n => legendreSym p (n : Int)) : Int) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun n _ => legChar_apply p n
  rw [heq] at key
  calc |((((Finset.Icc 1 N).sum (fun n => legendreSym p (n : Int))) : Int) : Real)|
      = ‖((((Finset.Icc 1 N).sum (fun n => legendreSym p (n : Int))) : Int) : ℂ)‖ := by
        rw [Complex.norm_intCast]
    _ ≤ Real.sqrt p * Real.log p := key

/-! ## Theorem 3 -/

theorem exists_not_pow_le (p k : Nat) (hp : p.Prime) (hk : 2 <= k) (hkp : (p - 1) % k = 0) :
    exists n : Nat, 1 <= n /\ (n : Real) <= Real.sqrt p * Real.log p + 1 /\
      forall x : ZMod p, Not (x ^ k = (n : ZMod p)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hkd : k ∣ p - 1 := Nat.dvd_of_mod_eq_zero hkp
  have hk0 : k ≠ 0 := by omega
  -- `p ≥ 3`
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · interval_cases p
      · simp at hkd; omega
    · exact h
  have hpR : (3:ℝ) ≤ p := by exact_mod_cast hp3
  -- a character of order `k`
  obtain ⟨χ, hord⟩ : ∃ χ : MulChar (ZMod p) ℂ, orderOf χ = k :=
    MulChar.exists_mulChar_orderOf (ZMod p) (by rwa [ZMod.card])
      (Complex.isPrimitiveRoot_exp k hk0)
  have hχ : χ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  -- setup
  set B : ℝ := Real.sqrt p * Real.log p with hB
  have hBnn : 0 ≤ B :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by linarith))
  have hBlt : B < (p:ℝ) - 1 := sqrt_mul_log_lt (p:ℝ) hpR
  set N : ℕ := ⌊B⌋₊ + 1 with hN
  have hNB : B < (N:ℝ) := by rw [hN]; push_cast; exact Nat.lt_floor_add_one B
  have hNle : (N:ℝ) ≤ B + 1 := by
    rw [hN]; push_cast
    have := Nat.floor_le hBnn
    linarith
  have hNp : N < p := by
    have : (N:ℝ) < (p:ℝ) := by linarith
    exact_mod_cast this
  -- if some `n ≤ N` has `χ n ≠ 1`, it is not a `k`-th power
  by_contra hcon
  push Not at hcon
  have hall : ∀ n : ℕ, 1 ≤ n → n ≤ N → χ (n : ZMod p) = 1 := by
    intro n hn1 hnN
    have hnR : (n : ℝ) ≤ B + 1 := by
      have : (n:ℝ) ≤ (N:ℝ) := by exact_mod_cast hnN
      linarith
    obtain ⟨x, hx⟩ := hcon n hn1 hnR
    have hnz : ((n:ℕ) : ZMod p) ≠ 0 := by
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      have := Nat.le_of_dvd (by omega) h
      omega
    have hxu : IsUnit x := by
      rcases eq_or_ne x 0 with rfl | h
      · exact absurd (by rw [← hx, zero_pow hk0]) hnz
      · exact Ne.isUnit h
    obtain ⟨u, rfl⟩ := hxu
    rw [← hx, map_pow, ← hord]
    calc χ (u : ZMod p) ^ orderOf χ = (χ ^ orderOf χ) (u : ZMod p) := by
          rw [MulChar.pow_apply_coe]
      _ = 1 := by rw [pow_orderOf_eq_one χ]; exact MulChar.one_apply u.isUnit
  -- the character sum is then `N`, contradicting Polya-Vinogradov
  have hsum : (Finset.Icc 1 N).sum (fun n => χ (n : ZMod p)) = (N : ℂ) := by
    rw [Finset.sum_congr rfl (fun n hn => by
      simp only [Finset.mem_Icc] at hn
      exact hall n hn.1 hn.2)]
    simp
  have hbd := charSum_norm_le_aux p χ hχ N
  rw [hsum, Complex.norm_natCast] at hbd
  linarith


/-! ## Theorem 4 -/

theorem card_residues_sub_le (p : Nat) [hp : Fact p.Prime] (h2 : Not (p = 2)) (N : Nat)
    (hN : N < p) :
    abs (2 * (((Finset.Icc 1 N).filter (fun n : Nat => legendreSym p (n : Int) = 1)).card : Real) -
        N) <= Real.sqrt p * Real.log p := by
  classical
  have hid : ((Finset.Icc 1 N).sum (fun n => legendreSym p (n : Int)) : Int)
      = 2 * (((Finset.Icc 1 N).filter (fun n : ℕ => legendreSym p (n : Int) = 1)).card : ℤ)
        - N := by
    set S := Finset.Icc 1 N with hS
    set T := S.filter (fun n : ℕ => legendreSym p (n : Int) = 1) with hT
    have hpm : ∀ n ∈ S, legendreSym p (n : Int) = 1 ∨ legendreSym p (n : Int) = -1 := by
      intro n hn
      simp only [hS, Finset.mem_Icc] at hn
      apply legendreSym.eq_one_or_neg_one
      intro h
      have hz : ((n:ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at hz
      have := Nat.le_of_dvd (by omega) hz
      omega
    rw [← Finset.sum_filter_add_sum_filter_not S (fun n : ℕ => legendreSym p (n : Int) = 1)]
    have h1 : ∑ n ∈ T, legendreSym p (n : Int) = (T.card : ℤ) := by
      rw [Finset.sum_congr rfl (fun n hn => by
        simp only [hT, Finset.mem_filter] at hn; exact hn.2)]
      simp
    have h2' : ∑ n ∈ S.filter (fun n : ℕ => ¬ (legendreSym p (n : Int) = 1)),
        legendreSym p (n : Int)
        = -((S.filter (fun n : ℕ => ¬ (legendreSym p (n : Int) = 1))).card : ℤ) := by
      rw [Finset.sum_congr rfl (fun n hn => by
        simp only [Finset.mem_filter] at hn
        rcases hpm n hn.1 with h | h
        · exact absurd h hn.2
        · exact h)]
      simp
    rw [h1, h2']
    have hcard := Finset.card_filter_add_card_filter_not
      (s := S) (p := fun n : ℕ => legendreSym p (n : Int) = 1)
    have hSc : S.card = N := by simp [hS]
    rw [hSc, ← hT] at hcard
    omega
  have key := legendreSum_le p h2 N
  rw [hid] at key
  push_cast at key
  exact key

/-- For an odd prime `p` there is a non-residue `n` with `1 ≤ n ≤ √p log p + 1`. -/
theorem exists_nonresidue_le (p : ℕ) [hp : Fact p.Prime] (h2 : p ≠ 2) :
    ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) ≤ Real.sqrt p * Real.log p + 1 ∧
      legendreSym p (n : ℤ) = -1 := by
  classical
  have hp3 : 3 ≤ p := by
    have h2le := hp.out.two_le
    omega
  have hpR : (3:ℝ) ≤ p := by exact_mod_cast hp3
  set B : ℝ := Real.sqrt p * Real.log p with hB
  have hBnn : 0 ≤ B := by
    apply mul_nonneg (Real.sqrt_nonneg _)
    exact Real.log_nonneg (by linarith)
  have hBlt : B < (p:ℝ) - 1 := sqrt_mul_log_lt (p:ℝ) hpR
  set N : ℕ := ⌊B⌋₊ + 1 with hN
  have hNB : B < (N:ℝ) := by rw [hN]; push_cast; exact Nat.lt_floor_add_one B
  have hNle : (N:ℝ) ≤ B + 1 := by
    rw [hN]; push_cast
    have := Nat.floor_le hBnn
    linarith
  have hNp : N < p := by
    have : (N:ℝ) < (p:ℝ) := by linarith
    exact_mod_cast this
  by_contra hcon
  push Not at hcon
  -- every n in [1, N] is a residue
  have hall : ∀ n ∈ Finset.Icc 1 N, legendreSym p (n : Int) = 1 := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hnR : (n : ℝ) ≤ B + 1 := by
      have : (n:ℝ) ≤ (N:ℝ) := by exact_mod_cast hn.2
      linarith
    have hne : legendreSym p (n : Int) ≠ -1 := hcon n hn.1 hnR
    have hnz : ((n:ℕ) : ZMod p) ≠ 0 := by
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      have := Nat.le_of_dvd (by omega) h
      omega
    rcases legendreSym.eq_one_or_neg_one p (a := (n:ℤ)) (by exact_mod_cast hnz) with h | h
    · exact h
    · exact absurd h hne
  have hcard : ((Finset.Icc 1 N).filter (fun n : ℕ => legendreSym p (n : Int) = 1)).card = N := by
    rw [Finset.filter_true_of_mem hall]; simp
  have hb := card_residues_sub_le p h2 N hNp
  rw [hcard] at hb
  have : (N:ℝ) ≤ B := by
    rw [show (2:ℝ) * (N:ℝ) - (N:ℝ) = (N:ℝ) by ring] at hb
    calc (N:ℝ) ≤ |(N:ℝ)| := le_abs_self _
      _ ≤ B := hb
  linarith

/-! ## Theorem 5 -/

theorem exists_prime_nonresidue_le (p : Nat) [hp : Fact p.Prime] (h2 : Not (p = 2)) :
    exists q : Nat, q.Prime /\ (q : Real) <= Real.sqrt p * Real.log p + 1 /\
      legendreSym p (q : Int) = -1 := by
  classical
  obtain ⟨n₀, hn₀1, hn₀B, hn₀r⟩ := exists_nonresidue_le p h2
  -- take the least non-residue
  have hex : ∃ n : ℕ, 1 ≤ n ∧ legendreSym p (n : Int) = -1 := ⟨n₀, hn₀1, hn₀r⟩
  classical
  obtain ⟨q, hqdef⟩ : ∃ q, q = Nat.find hex := ⟨_, rfl⟩
  obtain ⟨hq1, hqr⟩ : 1 ≤ q ∧ legendreSym p (q : Int) = -1 := hqdef ▸ Nat.find_spec hex
  have hqmin : ∀ m, 1 ≤ m → m < q → legendreSym p (m : Int) = 1 := by
    intro m hm1 hmq
    have hnm := Nat.find_min hex (hqdef ▸ hmq)
    push Not at hnm
    have hne := hnm hm1
    have hnz : ((m:ℕ) : ZMod p) ≠ 0 := by
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      have hle := Nat.le_of_dvd (by omega) h
      have hqle : q ≤ n₀ := hqdef ▸ Nat.find_le ⟨hn₀1, hn₀r⟩
      have hpR : ((p:ℕ):ℝ) ≤ (n₀:ℝ) := by
        have : (p:ℕ) ≤ m := hle
        have h1 : (m:ℝ) ≤ (q:ℝ) := by exact_mod_cast hmq.le
        have h2' : (q:ℝ) ≤ (n₀:ℝ) := by exact_mod_cast hqle
        have h3 : ((p:ℕ):ℝ) ≤ (m:ℝ) := by exact_mod_cast this
        linarith
      have hp3 : (3:ℝ) ≤ p := by
        have : 3 ≤ p := by
          have h2le := hp.out.two_le
          omega
        exact_mod_cast this
      have := sqrt_mul_log_lt (p:ℝ) hp3
      linarith
    rcases legendreSym.eq_one_or_neg_one p (a := (m:ℤ)) (by exact_mod_cast hnz) with h | h
    · exact h
    · exact absurd h hne
  have hqle : q ≤ n₀ := hqdef ▸ Nat.find_le ⟨hn₀1, hn₀r⟩
  have hqprime : q.Prime := by
    have hq2 : 2 ≤ q := by
      rcases Nat.lt_or_ge q 2 with h | h
      · interval_cases q
        · simp [legendreSym.at_one] at hqr
      · exact h
    by_contra hnp
    obtain ⟨a, ha, ha2, haq⟩ := Nat.exists_dvd_of_not_prime2 hq2 hnp
    obtain ⟨b, rfl⟩ := ha
    have hb2 : 2 ≤ b := by nlinarith
    have hbq : b < a * b := by nlinarith
    have e1 := hqmin a (by omega) haq
    have e2 := hqmin b (by omega) hbq
    rw [show ((a*b : ℕ) : ℤ) = (a:ℤ) * (b:ℤ) by push_cast; ring, legendreSym.mul, e1, e2] at hqr
    norm_num at hqr
  refine ⟨q, hqprime, ?_, hqr⟩
  have : (q:ℝ) ≤ (n₀:ℝ) := by exact_mod_cast hqle
  linarith


end TuringTask
