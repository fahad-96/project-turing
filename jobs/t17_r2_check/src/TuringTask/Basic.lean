import Mathlib

/-!
# Densities of squarefree integers, coprime pairs, and totient sums

This file proves five classical density estimates with explicit error terms.
-/

namespace TuringTask

open Finset ArithmeticFunction

local notation "μ" => ArithmeticFunction.moebius

/-! ## Part 0: elementary reindexing helpers -/

lemma sum_Icc_eq_range (D : ℕ) (f : ℕ → ℝ) (hf0 : f 0 = 0) :
    ∑ d ∈ Icc 1 D, f d = ∑ d ∈ range (D + 1), f d := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), hf0, zero_add,
    show 0 + 1 = 1 from rfl, Ico_add_one_right_eq_Icc]

/-! ## Part 1: the value of `∑ μ(d)/d²` -/

lemma abs_moeb_le (d : ℕ) : |((μ d : ℝ)) / (d : ℝ) ^ 2| ≤ (1 : ℝ) / (d : ℝ) ^ 2 := by
  rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((d : ℝ)) ^ 2)]
  have h1 : |((μ d : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := d))
  have h2 : |((μ d : ℝ))| ≤ 1 := by simpa using h1
  gcongr

lemma summable_invsq : Summable (fun d : ℕ => (1 : ℝ) / (d : ℝ) ^ 2) :=
  (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)

lemma summable_moeb : Summable (fun d : ℕ => ((μ d : ℝ)) / (d : ℝ) ^ 2) :=
  Summable.of_abs <| Summable.of_nonneg_of_le (fun _ => abs_nonneg _) abs_moeb_le summable_invsq

/-- The Möbius series `∑ μ(d)/d²` sums to `6/π²`, i.e. `1/ζ(2)`. -/
lemma hasSum_moebius_div_sq :
    HasSum (fun d : ℕ => ((μ d : ℝ)) / (d : ℝ) ^ 2) (6 / Real.pi ^ 2) := by
  have hs : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have h2 := LSeries_zeta_mul_Lseries_moebius (s := 2) hs
  rw [LSeries_zeta_eq_riemannZeta hs, riemannZeta_two] at h2
  have hpi : ((Real.pi : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
  have hL : LSeries (fun n => ((μ n : ℤ) : ℂ)) 2 = ((6 / Real.pi ^ 2 : ℝ) : ℂ) := by
    push_cast
    field_simp at h2 ⊢
    linear_combination h2
  have hsum : HasSum (LSeries.term (fun n => ((μ n : ℤ) : ℂ)) 2) (((6 / Real.pi ^ 2 : ℝ) : ℂ)) := by
    rw [← hL]
    exact (LSeriesSummable_moebius_iff.mpr hs).hasSum
  rw [← Complex.hasSum_ofReal]
  refine hsum.congr_fun fun d => ?_
  rw [LSeries.term_def]
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  · rw [if_neg hd]
    push_cast
    rw [← Complex.cpow_natCast (n := 2)]
    norm_num

/-! ## Part 2: tail estimates -/

lemma sum_inv_sq_shift_le (D : ℕ) (hD : 1 ≤ D) :
    ∑' i : ℕ, (1 : ℝ) / (((i + (D + 1)) : ℕ) : ℝ) ^ 2 ≤ (1 : ℝ) / D := by
  have hsummable : Summable (fun i : ℕ => (1 : ℝ) / (((i + (D + 1)) : ℕ) : ℝ) ^ 2) :=
    summable_invsq.comp_injective (add_left_injective (D + 1))
  refine hsummable.tsum_le_of_sum_range_le fun n => ?_
  have key : ∑ i ∈ range n, (1 : ℝ) / (((i + (D + 1)) : ℕ) : ℝ) ^ 2
      = ∑ j ∈ Ioc D (D + n), ((j : ℝ) ^ 2)⁻¹ := by
    rw [Finset.sum_nbij' (i := fun i => i + D + 1) (j := fun j => j - D - 1)]
    · intro a ha; simp only [mem_range] at ha; simp only [mem_Ioc]; omega
    · intro a ha; simp only [mem_Ioc] at ha; simp only [mem_range]; omega
    · intro a ha; simp only [mem_range] at ha; omega
    · intro a ha; simp only [mem_Ioc] at ha; omega
    · intro a ha; push_cast; rw [one_div]; ring_nf
  rw [key]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.add_zero, Ioc_self, sum_empty]; positivity
  · refine (sum_Ioc_inv_sq_le_sub (by omega) (by omega)).trans ?_
    rw [one_div]
    have : (0 : ℝ) ≤ (((D + n : ℕ)) : ℝ)⁻¹ := by positivity
    linarith

/-- Truncating the Möbius series at `D` costs at most `1/D`. -/
lemma moeb_tail_le (D : ℕ) (hD : 1 ≤ D) :
    |(∑ d ∈ Icc 1 D, ((μ d : ℝ)) / (d : ℝ) ^ 2) - (6 / Real.pi ^ 2)| ≤ (1 : ℝ) / D := by
  have hz : ((μ 0 : ℝ)) / (((0 : ℕ)) : ℝ) ^ 2 = 0 := by norm_num
  rw [sum_Icc_eq_range D _ hz]
  have hsplit := summable_moeb.sum_add_tsum_nat_add (D + 1)
  rw [hasSum_moebius_div_sq.tsum_eq] at hsplit
  rw [show (∑ d ∈ range (D + 1), ((μ d : ℝ)) / (d : ℝ) ^ 2) - (6 / Real.pi ^ 2)
      = -∑' i : ℕ, ((μ (i + (D + 1)) : ℝ)) / ((i + (D + 1) : ℕ) : ℝ) ^ 2 by
    push_cast at hsplit ⊢; linarith]
  rw [abs_neg]
  set g : ℕ → ℝ := fun i => ((μ (i + (D + 1)) : ℝ)) / ((i + (D + 1) : ℕ) : ℝ) ^ 2 with hg
  have habs : Summable (fun i : ℕ => |g i|) :=
    (summable_moeb.comp_injective (add_left_injective (D + 1))).abs
  have h1 : |∑' i : ℕ, g i| ≤ ∑' i : ℕ, |g i| := by
    simpa [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := g) (by simpa [Real.norm_eq_abs] using habs)
  refine h1.trans (le_trans ?_ (sum_inv_sq_shift_le D hD))
  exact Summable.tsum_le_tsum (fun i => abs_moeb_le _) habs
    (summable_invsq.comp_injective (add_left_injective (D + 1)))

/-! ## Part 3: the square part of a natural number -/

/-- `sqrtPart n` is the largest `m` with `m ^ 2 ∣ n`. -/
noncomputable def sqrtPart (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)

lemma sqrtPart_ne_zero {n : ℕ} (_hn : n ≠ 0) : sqrtPart n ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hx => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hx).ne_zero

lemma sqrtPart_factorization {n : ℕ} (_hn : n ≠ 0) (q : ℕ) :
    (sqrtPart n).factorization q = n.factorization q / 2 := by
  rw [sqrtPart, Nat.factorization_prod
    (fun x hx => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hx).ne_zero), Finset.sum_apply']
  have h : ∀ x ∈ n.primeFactors, ((x ^ (n.factorization x / 2)).factorization) q
      = if q = x then n.factorization x / 2 else 0 := by
    intro x hx
    rw [(Nat.prime_of_mem_primeFactors hx).factorization_pow]
    simp [Finsupp.single_apply, eq_comm]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq]
  by_cases hq : q ∈ n.primeFactors
  · simp [hq]
  · have h0 : n.factorization q = 0 := by
      rw [← Nat.support_factorization] at hq
      simpa using Finsupp.notMem_support_iff.mp hq
    simp [hq, h0]

lemma sqrtPart_eq_one_iff {n : ℕ} (hn : n ≠ 0) : sqrtPart n = 1 ↔ Squarefree n := by
  rw [Nat.squarefree_iff_factorization_le_one hn]
  constructor
  · intro h q
    have h2 := sqrtPart_factorization hn q
    rw [h, Nat.factorization_one] at h2
    simp only [Finsupp.coe_zero, Pi.zero_apply] at h2
    omega
  · intro h
    have hz : ∀ q, (sqrtPart n).factorization q = 0 := by
      intro q; rw [sqrtPart_factorization hn]; have := h q; omega
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have hpos := Nat.Prime.factorization_pos_of_dvd hp (sqrtPart_ne_zero hn) hpd
    have := hz p
    omega

lemma sq_dvd_iff_dvd_sqrtPart {n d : ℕ} (hn : n ≠ 0) (hd : d ≠ 0) :
    d ^ 2 ∣ n ↔ d ∣ sqrtPart n := by
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero _ hd) hn,
      ← Nat.factorization_le_iff_dvd hd (sqrtPart_ne_zero hn)]
  simp only [Finsupp.le_def, Nat.factorization_pow, sqrtPart_factorization hn]
  constructor
  · intro h q
    have := h q
    simp only [Finsupp.smul_apply, smul_eq_mul] at this
    omega
  · intro h q
    have := h q
    simp only [Finsupp.smul_apply, smul_eq_mul]
    omega

/-- The squarefree indicator expressed as a Möbius sum over `d` with `d² ∣ n`. -/
lemma sum_moebius_sq_dvd (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ (Icc 1 n).filter (fun d => d ^ 2 ∣ n), (μ d : ℤ) = if Squarefree n then 1 else 0 := by
  have hfilter : (Icc 1 n).filter (fun d => d ^ 2 ∣ n) = (sqrtPart n).divisors := by
    ext d
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨(sq_dvd_iff_dvd_sqrtPart hn (by omega)).mp h3, sqrtPart_ne_zero hn⟩
    · rintro ⟨h1, h2⟩
      have hd0 : d ≠ 0 := by
        rintro rfl
        exact h2 (Nat.eq_zero_of_zero_dvd h1)
      have hsq : d ^ 2 ∣ n := (sq_dvd_iff_dvd_sqrtPart hn hd0).mpr h1
      refine ⟨⟨by omega, ?_⟩, hsq⟩
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ((dvd_pow_self d two_ne_zero).trans hsq)
  rw [hfilter]
  have hmz := ArithmeticFunction.coe_mul_zeta_apply (f := (μ : ArithmeticFunction ℤ))
    (x := sqrtPart n)
  rw [ArithmeticFunction.moebius_mul_coe_zeta] at hmz
  rw [← hmz, ArithmeticFunction.one_apply]
  simp only [sqrtPart_eq_one_iff hn]

/-! ## Part 4: elementary real estimates -/

lemma abs_div_sub (N d : ℕ) (hd : 0 < d) : |((N / d : ℕ) : ℝ) - (N : ℝ) / (d : ℝ)| ≤ 1 := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hup : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
  have hlow : (N : ℝ) / (d : ℝ) - 1 < ((N / d : ℕ) : ℝ) := by
    have hnat : N < (N / d + 1) * d := by
      have h := Nat.div_add_mod N d
      have h2 := Nat.mod_lt N hd
      nlinarith [h, h2]
    have hR : (N : ℝ) < ((N / d : ℕ) : ℝ) * d + d := by
      calc (N : ℝ) < ((N / d + 1 : ℕ) : ℝ) * d := by exact_mod_cast hnat
        _ = ((N / d : ℕ) : ℝ) * d + d := by push_cast; ring
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hdR]
    linarith
  rw [abs_le]; constructor <;> linarith

lemma sqrt_nat_le (N : ℕ) : (N.sqrt : ℝ) ≤ Real.sqrt N := by
  rw [Real.le_sqrt (by positivity) (by positivity)]
  exact_mod_cast Nat.sqrt_le' N

lemma real_sqrt_le_two (N : ℕ) (hN : 1 ≤ N) : Real.sqrt N ≤ 2 * (N.sqrt : ℝ) := by
  have h1 : 1 ≤ N.sqrt := by simpa using Nat.sqrt_le_sqrt hN
  have h2 : Real.sqrt N < (N.sqrt : ℝ) + 1 := by
    have hlt : N < (N.sqrt + 1) ^ 2 := Nat.lt_succ_sqrt' N
    calc Real.sqrt N < Real.sqrt (((N.sqrt + 1) ^ 2 : ℕ)) := by
          exact Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hlt)
      _ = ((N.sqrt + 1 : ℕ) : ℝ) := by push_cast; rw [Real.sqrt_sq (by positivity)]
      _ = (N.sqrt : ℝ) + 1 := by push_cast; ring
  have h3 : (1 : ℝ) ≤ (N.sqrt : ℝ) := by exact_mod_cast h1
  linarith

lemma div_sq_eq_zero {N d : ℕ} (h : N.sqrt < d) : N / d ^ 2 = 0 := by
  apply Nat.div_eq_of_lt
  calc N < (N.sqrt + 1) ^ 2 := Nat.lt_succ_sqrt' N
    _ ≤ d ^ 2 := Nat.pow_le_pow_left h 2

/-! ## Part 5: the exact Möbius formula for the squarefree count -/

lemma card_squarefree_eq (N : ℕ) :
    (((Icc 1 N).filter (fun n : ℕ => Squarefree n)).card : ℤ)
      = ∑ d ∈ Icc 1 N, (μ d : ℤ) * ((N / d ^ 2 : ℕ) : ℤ) := by
  rw [← Finset.sum_boole]
  have e1 : ∀ n ∈ Icc 1 N, (if Squarefree n then (1 : ℤ) else 0)
      = ∑ d ∈ (Icc 1 N).filter (fun d => d ^ 2 ∣ n), (μ d : ℤ) := by
    intro n hn
    simp only [mem_Icc] at hn
    rw [← sum_moebius_sq_dvd n (by omega)]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, le_trans (Nat.le_of_dvd (by omega)
        ((dvd_pow_self d two_ne_zero).trans h3)) hn.2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, Nat.le_of_dvd (by omega) ((dvd_pow_self d two_ne_zero).trans h3)⟩, h3⟩
  rw [Finset.sum_congr rfl e1]
  rw [Finset.sum_comm' (t' := Icc 1 N) (s' := fun d => (Icc 1 N).filter (fun n => d ^ 2 ∣ n))
    (by intro x y; simp only [mem_filter]; tauto)]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  rw [show Icc 1 N = Ioc 0 N from rfl]
  exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.Ioc_filter_dvd_card_eq_div N (d ^ 2))

/-! ## Part 6: the main estimate scheme -/

lemma decomp (D N : ℕ) :
    (∑ d ∈ Icc 1 D, (μ d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ)) - 6 / Real.pi ^ 2 * (N : ℝ)
      = (∑ d ∈ Icc 1 D, (μ d : ℝ) * (((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) / (d : ℝ) ^ 2))
        + (N : ℝ) * ((∑ d ∈ Icc 1 D, ((μ d : ℝ)) / (d : ℝ) ^ 2) - (6 / Real.pi ^ 2)) := by
  have h : (N : ℝ) * (∑ d ∈ Icc 1 D, ((μ d : ℝ)) / (d : ℝ) ^ 2)
      = ∑ d ∈ Icc 1 D, (N : ℝ) * ((μ d : ℝ) / (d : ℝ) ^ 2) := Finset.mul_sum _ _ _
  have h2 : (∑ d ∈ Icc 1 D, (μ d : ℝ) * (((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) / (d : ℝ) ^ 2))
      + ∑ d ∈ Icc 1 D, (N : ℝ) * ((μ d : ℝ) / (d : ℝ) ^ 2)
      = ∑ d ∈ Icc 1 D, (μ d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun d hd => by ring
  rw [mul_sub, h]
  linarith

lemma bd1 (D N : ℕ) :
    |∑ d ∈ Icc 1 D, (μ d : ℝ) * (((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) / (d : ℝ) ^ 2)| ≤ (D : ℝ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ d ∈ Icc 1 D, |(μ d : ℝ) * (((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) / (d : ℝ) ^ 2)| ≤ 1 := by
    intro d hd
    simp only [mem_Icc] at hd
    rw [abs_mul]
    have h1 : |((μ d : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := d))
    have hm : |((μ d : ℝ))| ≤ 1 := by simpa using h1
    have hd2 : 0 < d ^ 2 := by have : 0 < d := by omega
                               positivity
    have hq := abs_div_sub N (d ^ 2) hd2
    rw [show (((d ^ 2 : ℕ)) : ℝ) = (d : ℝ) ^ 2 by push_cast; ring] at hq
    nlinarith [abs_nonneg ((μ d : ℝ)), abs_nonneg (((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) / (d : ℝ) ^ 2)]
  calc _ ≤ ∑ d ∈ Icc 1 D, (1 : ℝ) := Finset.sum_le_sum hb
    _ = (D : ℝ) := by simp

/-! ## Theorem 1: the count of squarefree integers -/

theorem card_squarefree_sub_le (N : Nat) (hN : 1 <= N) :
    abs ((((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : Real) -
        6 / Real.pi ^ 2 * N) <= 3 * Real.sqrt N := by
  set D := N.sqrt with hDdef
  have hD1 : 1 ≤ D := by simpa [hDdef] using Nat.sqrt_le_sqrt hN
  -- rewrite the cardinality as a truncated Möbius sum
  have hcard : (((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : ℝ)
      = ∑ d ∈ Icc 1 D, (μ d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ) := by
    have h := card_squarefree_eq N
    have hR : (((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : ℝ)
        = ∑ d ∈ Icc 1 N, (μ d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ) := by
      have := congrArg (Int.cast : ℤ → ℝ) h
      push_cast at this
      exact this
    rw [hR]
    refine (Finset.sum_subset (Finset.Icc_subset_Icc_right (Nat.sqrt_le_self N)) ?_).symm
    intro x hx hnx
    simp only [mem_Icc] at hx hnx
    rw [div_sq_eq_zero (show N.sqrt < x by omega)]
    simp
  rw [hcard, decomp D N]
  have hNR : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hb1 := bd1 D N
  have hb2 := moeb_tail_le D hD1
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD1
  -- total error ≤ D + N/D
  have hmain : |(∑ d ∈ Icc 1 D, (μ d : ℝ) * (((N / d ^ 2 : ℕ) : ℝ) - (N : ℝ) / (d : ℝ) ^ 2))
      + (N : ℝ) * ((∑ d ∈ Icc 1 D, ((μ d : ℝ)) / (d : ℝ) ^ 2) - (6 / Real.pi ^ 2))|
      ≤ (D : ℝ) + (N : ℝ) / D := by
    refine (abs_add_le _ _).trans ?_
    have h2 : |(N : ℝ) * ((∑ d ∈ Icc 1 D, ((μ d : ℝ)) / (d : ℝ) ^ 2) - (6 / Real.pi ^ 2))|
        ≤ (N : ℝ) / D := by
      rw [abs_mul, abs_of_nonneg hNR]
      calc (N : ℝ) * |(∑ d ∈ Icc 1 D, ((μ d : ℝ)) / (d : ℝ) ^ 2) - (6 / Real.pi ^ 2)|
          ≤ (N : ℝ) * ((1 : ℝ) / D) := by gcongr
        _ = (N : ℝ) / D := by ring
    linarith
  refine hmain.trans ?_
  -- now D ≤ √N and N/D ≤ 2√N
  have hDle : (D : ℝ) ≤ Real.sqrt N := sqrt_nat_le N
  have hsqrtN : Real.sqrt N ≤ 2 * (D : ℝ) := real_sqrt_le_two N hN
  have hNeq : (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt hNR).symm
  have hNdiv : (N : ℝ) / D ≤ 2 * Real.sqrt N := by
    rw [div_le_iff₀ hDR]
    nlinarith [Real.sqrt_nonneg (N : ℝ), hNeq, hsqrtN]
  linarith

/-! ## Part 7: harmonic sums -/

lemma harm (N : ℕ) : ∑ d ∈ Icc 1 N, (1 : ℝ) / d = ((harmonic N : ℚ) : ℝ) := by
  rw [harmonic]
  push_cast
  rw [Finset.sum_nbij' (i := fun d => d - 1) (j := fun i => i + 1)]
  · intro a ha; simp only [mem_Icc] at ha; simp only [mem_range]; omega
  · intro a ha; simp only [mem_range] at ha; simp only [mem_Icc]; omega
  · intro a ha; simp only [mem_Icc] at ha; omega
  · intro a ha; simp only [mem_range] at ha; omega
  · intro a ha
    simp only [mem_Icc] at ha
    have h : ((a - 1 : ℕ) : ℝ) + 1 = (a : ℝ) := by
      have hh : (a - 1 : ℕ) + 1 = a := by omega
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hh
    rw [one_div, h]

lemma harm_le (N : ℕ) : ∑ d ∈ Icc 1 N, (1 : ℝ) / d ≤ Real.log N + 1 := by
  rw [harm]
  have := harmonic_le_one_add_log N
  have h2 : ((harmonic N : ℚ) : ℝ) ≤ 1 + Real.log N := by exact_mod_cast this
  linarith

/-! ## Part 8: the coprime pair count -/

lemma cop_ind (a b : ℕ) :
    ∑ d ∈ (Nat.gcd a b).divisors, (μ d : ℤ) = if Nat.Coprime a b then 1 else 0 := by
  have hmz := ArithmeticFunction.coe_mul_zeta_apply (f := (μ : ArithmeticFunction ℤ))
    (x := Nat.gcd a b)
  rw [ArithmeticFunction.moebius_mul_coe_zeta] at hmz
  rw [← hmz, ArithmeticFunction.one_apply]

lemma gcd_div (a b N : ℕ) (ha : 1 ≤ a) (haN : a ≤ N) (hb : 1 ≤ b) :
    (Nat.gcd a b).divisors = (Icc 1 N).filter (fun d => d ∣ a ∧ d ∣ b) := by
  ext d
  simp only [Nat.mem_divisors, mem_filter, mem_Icc, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨Nat.pos_of_ne_zero (by rintro rfl; simp at h1; omega),
      le_trans (Nat.le_of_dvd (by omega) h1) haN⟩, h1, h2⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h3, h4⟩, Nat.gcd_ne_zero_left (by omega)⟩

lemma prod_filter_card (N d : ℕ) :
    (((Finset.product (Icc 1 N) (Icc 1 N)).filter
      (fun p : ℕ × ℕ => d ∣ p.1 ∧ d ∣ p.2)).card) = (N / d) * (N / d) := by
  rw [Finset.product_eq_sprod]
  rw [show (Icc 1 N ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => d ∣ p.1 ∧ d ∣ p.2)
      = ((Icc 1 N).filter (fun a => d ∣ a)) ×ˢ ((Icc 1 N).filter (fun b => d ∣ b)) by
    ext p
    simp only [mem_filter, Finset.mem_product, mem_filter]
    tauto]
  rw [Finset.card_product]
  congr 1 <;>
  · rw [show Icc 1 N = Ioc 0 N from rfl]
    exact Nat.Ioc_filter_dvd_card_eq_div N d

lemma card_coprime_eq (N : ℕ) :
    (((Finset.product (Icc 1 N) (Icc 1 N)).filter
        (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2)).card : ℤ)
      = ∑ d ∈ Icc 1 N, (μ d : ℤ) * ((N / d : ℕ) : ℤ) * ((N / d : ℕ) : ℤ) := by
  rw [← Finset.sum_boole]
  have e1 : ∀ p ∈ Finset.product (Icc 1 N) (Icc 1 N),
      (if Nat.Coprime p.1 p.2 then (1 : ℤ) else 0)
      = ∑ d ∈ (Icc 1 N).filter (fun d => d ∣ p.1 ∧ d ∣ p.2), (μ d : ℤ) := by
    intro p hp
    rw [Finset.product_eq_sprod, Finset.mem_product] at hp
    simp only [mem_Icc] at hp
    rw [← cop_ind p.1 p.2, gcd_div p.1 p.2 N hp.1.1 hp.1.2 hp.2.1]
  rw [Finset.sum_congr rfl e1]
  rw [Finset.sum_comm' (t' := Icc 1 N)
    (s' := fun d => (Finset.product (Icc 1 N) (Icc 1 N)).filter (fun p => d ∣ p.1 ∧ d ∣ p.2))
    (by intro x y; simp only [mem_filter]; tauto)]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.sum_const, nsmul_eq_mul, prod_filter_card N d]
  push_cast
  ring

lemma decomp2 (N : ℕ) :
    (∑ d ∈ Icc 1 N, (μ d : ℝ) * ((N / d : ℕ) : ℝ) * ((N / d : ℕ) : ℝ))
        - 6 / Real.pi ^ 2 * (N : ℝ) ^ 2
      = (∑ d ∈ Icc 1 N, (μ d : ℝ) * (((((N / d : ℕ)) : ℝ)) ^ 2 - ((N : ℝ) / (d : ℝ)) ^ 2))
        + (N : ℝ) ^ 2 * ((∑ d ∈ Icc 1 N, ((μ d : ℝ)) / (d : ℝ) ^ 2) - (6 / Real.pi ^ 2)) := by
  have h : (N : ℝ) ^ 2 * (∑ d ∈ Icc 1 N, ((μ d : ℝ)) / (d : ℝ) ^ 2)
      = ∑ d ∈ Icc 1 N, (N : ℝ) ^ 2 * ((μ d : ℝ) / (d : ℝ) ^ 2) := Finset.mul_sum _ _ _
  have h2 : (∑ d ∈ Icc 1 N, (μ d : ℝ) * (((((N / d : ℕ)) : ℝ)) ^ 2 - ((N : ℝ) / (d : ℝ)) ^ 2))
      + ∑ d ∈ Icc 1 N, (N : ℝ) ^ 2 * ((μ d : ℝ) / (d : ℝ) ^ 2)
      = ∑ d ∈ Icc 1 N, (μ d : ℝ) * ((N / d : ℕ) : ℝ) * ((N / d : ℕ) : ℝ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [mem_Icc] at hd
    have hdR : (d : ℝ) ≠ 0 := by
      have : 0 < d := by omega
      positivity
    field_simp
    ring
  rw [mul_sub, h]
  linarith

lemma bd2 (N : ℕ) :
    |∑ d ∈ Icc 1 N, (μ d : ℝ) * (((((N / d : ℕ)) : ℝ)) ^ 2 - ((N : ℝ) / (d : ℝ)) ^ 2)|
      ≤ 2 * (N : ℝ) * (Real.log N + 1) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ d ∈ Icc 1 N, |(μ d : ℝ) * (((((N / d : ℕ)) : ℝ)) ^ 2 - ((N : ℝ) / (d : ℝ)) ^ 2)|
      ≤ 2 * (N : ℝ) * (1 / (d : ℝ)) := by
    intro d hd
    simp only [mem_Icc] at hd
    have hd0 : 0 < d := by omega
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    rw [abs_mul]
    have h1 : |((μ d : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := d))
    have hm : |((μ d : ℝ))| ≤ 1 := by simpa using h1
    set x := ((N / d : ℕ) : ℝ)
    set y := (N : ℝ) / (d : ℝ)
    have hxy : |x - y| ≤ 1 := abs_div_sub N d hd0
    have hx : 0 ≤ x := by positivity
    have hy : 0 ≤ y := by positivity
    have hle : x ≤ y := Nat.cast_div_le
    have hsq : |x ^ 2 - y ^ 2| ≤ 2 * y := by
      have he : x ^ 2 - y ^ 2 = (x - y) * (x + y) := by ring
      rw [he, abs_mul]
      have h2 : |x + y| ≤ 2 * y := by rw [abs_of_nonneg (by linarith)]; linarith
      nlinarith [abs_nonneg (x - y), abs_nonneg (x + y)]
    have hyv : 2 * y = 2 * (N : ℝ) * (1 / (d : ℝ)) := by rw [div_eq_mul_one_div]; ring
    rw [← hyv]
    nlinarith [abs_nonneg ((μ d : ℝ)), abs_nonneg (x ^ 2 - y ^ 2)]
  calc _ ≤ ∑ d ∈ Icc 1 N, 2 * (N : ℝ) * (1 / (d : ℝ)) := Finset.sum_le_sum hb
    _ = 2 * (N : ℝ) * ∑ d ∈ Icc 1 N, (1 : ℝ) / (d : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 2 * (N : ℝ) * (Real.log N + 1) :=
        mul_le_mul_of_nonneg_left (harm_le N) (by positivity)

/-! ## Theorem 2: the count of coprime pairs -/

theorem card_coprime_sub_le (N : Nat) (hN : 1 <= N) :
    abs ((((Finset.product (Finset.Icc 1 N) (Finset.Icc 1 N)).filter
        (fun p : Prod Nat Nat => Nat.Coprime p.1 p.2)).card : Real) - 6 / Real.pi ^ 2 * N ^ 2) <=
      6 * N * (Real.log N + 1) := by
  have hcard : ((((Finset.product (Finset.Icc 1 N) (Finset.Icc 1 N)).filter
        (fun p : Prod Nat Nat => Nat.Coprime p.1 p.2)).card : ℝ))
      = ∑ d ∈ Icc 1 N, (μ d : ℝ) * ((N / d : ℕ) : ℝ) * ((N / d : ℕ) : ℝ) := by
    have h := congrArg (Int.cast : ℤ → ℝ) (card_coprime_eq N)
    push_cast at h
    exact h
  rw [hcard, decomp2 N]
  have hNR : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hNR1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hNR1
  have hb2 := bd2 N
  have htail := moeb_tail_le N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hterm2 : |(N : ℝ) ^ 2 * ((∑ d ∈ Icc 1 N, ((μ d : ℝ)) / (d : ℝ) ^ 2) - (6 / Real.pi ^ 2))|
      ≤ (N : ℝ) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2)]
    calc (N : ℝ) ^ 2 * |(∑ d ∈ Icc 1 N, ((μ d : ℝ)) / (d : ℝ) ^ 2) - (6 / Real.pi ^ 2)|
        ≤ (N : ℝ) ^ 2 * ((1 : ℝ) / N) := by gcongr
      _ = (N : ℝ) := by field_simp
  refine (abs_add_le _ _).trans ?_
  have : (N : ℝ) ≤ (N : ℝ) * (Real.log N + 1) := by nlinarith
  linarith

/-! ## Part 9: the totient sum -/

lemma gauss (m : ℕ) : (∑ i ∈ Icc 1 m, (i : ℝ)) = m * (m + 1) / 2 := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [← Ico_add_one_right_eq_Icc, Finset.sum_Ico_succ_top (by omega),
        Ico_add_one_right_eq_Icc, ih]
      push_cast; ring

lemma totient_moeb : ∀ n > 0,
    ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℤ) * (x.2 : ℤ) = (n.totient : ℤ) := by
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun n => (n.totient : ℤ)) (g := fun n => (n : ℤ))).mp
  intro n hn
  rw [← Nat.cast_sum]
  exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.sum_totient n)

lemma sum_totient_eq (N : ℕ) :
    ∑ n ∈ Icc 1 N, (n.totient : ℤ)
      = ∑ d ∈ Icc 1 N, (μ d : ℤ) * ∑ m ∈ Icc 1 (N / d), (m : ℤ) := by
  have e1 : ∀ n ∈ Icc 1 N, (n.totient : ℤ)
      = ∑ d ∈ (Icc 1 N).filter (fun d => d ∣ n), (μ d : ℤ) * ((n / d : ℕ) : ℤ) := by
    intro n hn
    simp only [mem_Icc] at hn
    rw [← totient_moeb n (by omega), Nat.sum_divisorsAntidiagonal (fun a b => (μ a : ℤ) * (b : ℤ))]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨Nat.pos_of_ne_zero (by rintro rfl; simp at h1; omega),
        le_trans (Nat.le_of_dvd (by omega) h1) hn.2⟩, h1⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h3, by omega⟩
  rw [Finset.sum_congr rfl e1]
  rw [Finset.sum_comm' (t' := Icc 1 N) (s' := fun d => (Icc 1 N).filter (fun n => d ∣ n))
    (by intro x y; simp only [mem_filter]; tauto)]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [mem_Icc] at hd
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (i := fun n => n / d) (j := fun m => d * m) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_Icc] at ha ⊢
    exact ⟨Nat.one_le_div_iff (by omega) |>.mpr (Nat.le_of_dvd (by omega) ha.2),
      Nat.div_le_div_right ha.1.2⟩
  · intro a ha
    simp only [mem_Icc] at ha
    simp only [mem_filter, mem_Icc]
    refine ⟨⟨by nlinarith, ?_⟩, Dvd.intro a rfl⟩
    have h := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp ha.2
    rwa [Nat.mul_comm] at h
  · intro a ha; simp only [mem_filter] at ha; exact Nat.mul_div_cancel' ha.2
  · intro a ha; simp only [mem_Icc] at ha; exact Nat.mul_div_cancel_left a (by omega)
  · intro a ha; simp only [mem_filter] at ha; rfl

lemma gauss_err (x y : ℝ) (hxy : |x - y| ≤ 1) (hx : 0 ≤ x) (hle : x ≤ y) :
    |x * (x + 1) / 2 - y ^ 2 / 2| ≤ 3 * y / 2 := by
  have h1 : x * (x + 1) / 2 - y ^ 2 / 2 = (x ^ 2 - y ^ 2) / 2 + x / 2 := by ring
  rw [h1]
  have h2 : |x ^ 2 - y ^ 2| ≤ 2 * y := by
    have he : x ^ 2 - y ^ 2 = (x - y) * (x + y) := by ring
    rw [he, abs_mul]
    have h3 : |x + y| ≤ 2 * y := by rw [abs_of_nonneg (by linarith)]; linarith
    nlinarith [abs_nonneg (x - y), abs_nonneg (x + y)]
  have h4 : |x / 2| = x / 2 := abs_of_nonneg (by linarith)
  calc |(x ^ 2 - y ^ 2) / 2 + x / 2| ≤ |(x ^ 2 - y ^ 2) / 2| + |x / 2| := abs_add_le _ _
    _ = |x ^ 2 - y ^ 2| / 2 + x / 2 := by rw [abs_div, h4]; norm_num
    _ ≤ (2 * y) / 2 + y / 2 := by linarith
    _ = 3 * y / 2 := by ring

lemma decomp3 (N : ℕ) :
    (∑ d ∈ Icc 1 N, (μ d : ℝ) * (((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2))
        - 3 / Real.pi ^ 2 * (N : ℝ) ^ 2
      = (∑ d ∈ Icc 1 N, (μ d : ℝ) * ((((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2)
          - ((N : ℝ) / (d : ℝ)) ^ 2 / 2))
        + ((N : ℝ) ^ 2 / 2) * ((∑ d ∈ Icc 1 N, ((μ d : ℝ)) / (d : ℝ) ^ 2)
          - (6 / Real.pi ^ 2)) := by
  have h : ((N : ℝ) ^ 2 / 2) * (∑ d ∈ Icc 1 N, ((μ d : ℝ)) / (d : ℝ) ^ 2)
      = ∑ d ∈ Icc 1 N, ((N : ℝ) ^ 2 / 2) * ((μ d : ℝ) / (d : ℝ) ^ 2) := Finset.mul_sum _ _ _
  have h2 : (∑ d ∈ Icc 1 N, (μ d : ℝ) * ((((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2)
          - ((N : ℝ) / (d : ℝ)) ^ 2 / 2))
      + ∑ d ∈ Icc 1 N, ((N : ℝ) ^ 2 / 2) * ((μ d : ℝ) / (d : ℝ) ^ 2)
      = ∑ d ∈ Icc 1 N, (μ d : ℝ) * (((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [mem_Icc] at hd
    have hdR : (d : ℝ) ≠ 0 := by
      have : 0 < d := by omega
      positivity
    field_simp
    ring
  have hpi : (3 : ℝ) / Real.pi ^ 2 * (N : ℝ) ^ 2
      = ((N : ℝ) ^ 2 / 2) * (6 / Real.pi ^ 2) := by ring
  rw [hpi, mul_sub, h]
  linarith

/-! ## Theorem 3: the sum of Euler's totient -/

theorem sum_totient_sub_le (N : Nat) (hN : 1 <= N) :
    abs ((Finset.Icc 1 N).sum (fun n => (Nat.totient n : Real)) - 3 / Real.pi ^ 2 * N ^ 2) <=
      4 * N * (Real.log N + 1) := by
  have hsum : (Finset.Icc 1 N).sum (fun n => (Nat.totient n : Real))
      = ∑ d ∈ Icc 1 N, (μ d : ℝ) * (((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2) := by
    have h := congrArg (Int.cast : ℤ → ℝ) (sum_totient_eq N)
    push_cast at h
    rw [h]
    refine Finset.sum_congr rfl fun d hd => ?_
    congr 1
    have hg := gauss (N / d)
    rw [hg]
  rw [hsum, decomp3 N]
  have hNR1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hNR1
  -- bound the first sum
  have hb1 : |∑ d ∈ Icc 1 N, (μ d : ℝ) * ((((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2)
      - ((N : ℝ) / (d : ℝ)) ^ 2 / 2)| ≤ (3 / 2) * (N : ℝ) * (Real.log N + 1) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hb : ∀ d ∈ Icc 1 N, |(μ d : ℝ) * ((((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2)
        - ((N : ℝ) / (d : ℝ)) ^ 2 / 2)| ≤ (3 / 2) * (N : ℝ) * (1 / (d : ℝ)) := by
      intro d hd
      simp only [mem_Icc] at hd
      have hd0 : 0 < d := by omega
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
      rw [abs_mul]
      have h1 : |((μ d : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := d))
      have hm : |((μ d : ℝ))| ≤ 1 := by simpa using h1
      set x := ((N / d : ℕ) : ℝ)
      set y := (N : ℝ) / (d : ℝ)
      have hg := gauss_err x y (abs_div_sub N d hd0) (by positivity) Nat.cast_div_le
      have hyv : 3 * y / 2 = (3 / 2) * (N : ℝ) * (1 / (d : ℝ)) := by
        rw [show y = (N : ℝ) / (d : ℝ) from rfl, div_eq_mul_one_div]; ring
      rw [← hyv]
      nlinarith [abs_nonneg ((μ d : ℝ)), abs_nonneg (x * (x + 1) / 2 - y ^ 2 / 2),
        le_trans (abs_nonneg (x * (x + 1) / 2 - y ^ 2 / 2)) hg]
    calc _ ≤ ∑ d ∈ Icc 1 N, (3 / 2) * (N : ℝ) * (1 / (d : ℝ)) := Finset.sum_le_sum hb
      _ = (3 / 2) * (N : ℝ) * ∑ d ∈ Icc 1 N, (1 : ℝ) / (d : ℝ) := by rw [Finset.mul_sum]
      _ ≤ (3 / 2) * (N : ℝ) * (Real.log N + 1) :=
          mul_le_mul_of_nonneg_left (harm_le N) (by positivity)
  have htail := moeb_tail_le N hN
  have hb2 : |((N : ℝ) ^ 2 / 2) * ((∑ d ∈ Icc 1 N, ((μ d : ℝ)) / (d : ℝ) ^ 2)
      - (6 / Real.pi ^ 2))| ≤ (N : ℝ) / 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2 / 2)]
    calc ((N : ℝ) ^ 2 / 2) * |(∑ d ∈ Icc 1 N, ((μ d : ℝ)) / (d : ℝ) ^ 2) - (6 / Real.pi ^ 2)|
        ≤ ((N : ℝ) ^ 2 / 2) * ((1 : ℝ) / N) := by gcongr
      _ = (N : ℝ) / 2 := by field_simp
  refine (abs_add_le _ _).trans ?_
  have hNle : (N : ℝ) ≤ (N : ℝ) * (Real.log N + 1) := by nlinarith
  linarith

/-! ## Part 10: the normalized totient sum -/

lemma tot_div (n : ℕ) (hn : 0 < n) :
    ((n.totient : ℝ)) / (n : ℝ) = ∑ d ∈ n.divisors, (μ d : ℝ) / (d : ℝ) := by
  have h := congrArg (Int.cast : ℤ → ℝ) (totient_moeb n hn)
  push_cast at h
  rw [Nat.sum_divisorsAntidiagonal (fun a b => (μ a : ℝ) * (b : ℝ))] at h
  rw [← h, Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Nat.mem_divisors] at hd
  have hd0 : d ≠ 0 := by rintro rfl; exact hd.2 (Nat.eq_zero_of_zero_dvd hd.1)
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [show ((n / d : ℕ) : ℝ) = (n : ℝ) / (d : ℝ) by rw [Nat.cast_div hd.1 hdR]]
  field_simp

lemma sum_tot_div_eq (N : ℕ) :
    ∑ n ∈ Icc 1 N, ((n.totient : ℝ)) / (n : ℝ)
      = ∑ d ∈ Icc 1 N, ((μ d : ℝ) / (d : ℝ)) * ((N / d : ℕ) : ℝ) := by
  have e1 : ∀ n ∈ Icc 1 N, ((n.totient : ℝ)) / (n : ℝ)
      = ∑ d ∈ (Icc 1 N).filter (fun d => d ∣ n), (μ d : ℝ) / (d : ℝ) := by
    intro n hn
    simp only [mem_Icc] at hn
    rw [tot_div n (by omega)]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨Nat.pos_of_ne_zero (by rintro rfl; simp at h1; omega),
        le_trans (Nat.le_of_dvd (by omega) h1) hn.2⟩, h1⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h3, by omega⟩
  rw [Finset.sum_congr rfl e1]
  rw [Finset.sum_comm' (t' := Icc 1 N) (s' := fun d => (Icc 1 N).filter (fun n => d ∣ n))
    (by intro x y; simp only [mem_filter]; tauto)]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  rw [show Icc 1 N = Ioc 0 N from rfl]
  exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Nat.Ioc_filter_dvd_card_eq_div N d)

lemma decomp4 (N : ℕ) :
    (∑ d ∈ Icc 1 N, ((μ d : ℝ) / (d : ℝ)) * ((N / d : ℕ) : ℝ)) - 6 / Real.pi ^ 2 * (N : ℝ)
      = (∑ d ∈ Icc 1 N, ((μ d : ℝ) / (d : ℝ)) * (((N / d : ℕ) : ℝ) - (N : ℝ) / (d : ℝ)))
        + (N : ℝ) * ((∑ d ∈ Icc 1 N, ((μ d : ℝ)) / (d : ℝ) ^ 2) - (6 / Real.pi ^ 2)) := by
  have h : (N : ℝ) * (∑ d ∈ Icc 1 N, ((μ d : ℝ)) / (d : ℝ) ^ 2)
      = ∑ d ∈ Icc 1 N, (N : ℝ) * ((μ d : ℝ) / (d : ℝ) ^ 2) := Finset.mul_sum _ _ _
  have h2 : (∑ d ∈ Icc 1 N, ((μ d : ℝ) / (d : ℝ)) * (((N / d : ℕ) : ℝ) - (N : ℝ) / (d : ℝ)))
      + ∑ d ∈ Icc 1 N, (N : ℝ) * ((μ d : ℝ) / (d : ℝ) ^ 2)
      = ∑ d ∈ Icc 1 N, ((μ d : ℝ) / (d : ℝ)) * ((N / d : ℕ) : ℝ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [mem_Icc] at hd
    have hdR : (d : ℝ) ≠ 0 := by
      have : 0 < d := by omega
      positivity
    field_simp
    ring
  rw [mul_sub, h]
  linarith

/-! ## Theorem 4: the sum of `φ(n)/n` -/

theorem sum_totient_div_sub_le (N : Nat) (hN : 1 <= N) :
    abs ((Finset.Icc 1 N).sum (fun n => (Nat.totient n : Real) / n) - 6 / Real.pi ^ 2 * N) <=
      Real.log N + 2 := by
  rw [show (Finset.Icc 1 N).sum (fun n => (Nat.totient n : Real) / n)
      = ∑ n ∈ Icc 1 N, ((n.totient : ℝ)) / (n : ℝ) from rfl, sum_tot_div_eq N, decomp4 N]
  have hNR1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hNR1
  -- first sum: each term is bounded by 1/d
  have hb1 : |∑ d ∈ Icc 1 N, ((μ d : ℝ) / (d : ℝ)) * (((N / d : ℕ) : ℝ) - (N : ℝ) / (d : ℝ))|
      ≤ Real.log N + 1 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hb : ∀ d ∈ Icc 1 N,
        |((μ d : ℝ) / (d : ℝ)) * (((N / d : ℕ) : ℝ) - (N : ℝ) / (d : ℝ))| ≤ 1 / (d : ℝ) := by
      intro d hd
      simp only [mem_Icc] at hd
      have hd0 : 0 < d := by omega
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
      rw [abs_mul, abs_div, abs_of_nonneg hdR.le]
      have h1 : |((μ d : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := d))
      have hm : |((μ d : ℝ))| ≤ 1 := by simpa using h1
      have hq := abs_div_sub N d hd0
      have hmd : |((μ d : ℝ))| / (d : ℝ) ≤ 1 / (d : ℝ) := by gcongr
      calc |((μ d : ℝ))| / (d : ℝ) * |((N / d : ℕ) : ℝ) - (N : ℝ) / (d : ℝ)|
          ≤ (1 / (d : ℝ)) * 1 := by
            apply mul_le_mul hmd hq (abs_nonneg _) (by positivity)
        _ = 1 / (d : ℝ) := by ring
    calc _ ≤ ∑ d ∈ Icc 1 N, (1 : ℝ) / (d : ℝ) := Finset.sum_le_sum hb
      _ ≤ Real.log N + 1 := harm_le N
  have htail := moeb_tail_le N hN
  have hb2 : |(N : ℝ) * ((∑ d ∈ Icc 1 N, ((μ d : ℝ)) / (d : ℝ) ^ 2) - (6 / Real.pi ^ 2))|
      ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ))]
    calc (N : ℝ) * |(∑ d ∈ Icc 1 N, ((μ d : ℝ)) / (d : ℝ) ^ 2) - (6 / Real.pi ^ 2)|
        ≤ (N : ℝ) * ((1 : ℝ) / N) := by gcongr
      _ = 1 := by field_simp
  refine (abs_add_le _ _).trans ?_
  linarith

/-! ## Theorem 5: the density of squarefree integers -/

theorem tendsto_card_squarefree_div :
    Filter.Tendsto (fun N : Nat => (((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card :
        Real) / N) Filter.atTop (nhds (6 / Real.pi ^ 2)) := by
  -- it suffices to show the difference tends to `0`
  have hdiff : Filter.Tendsto
      (fun N : ℕ => (((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : ℝ) / N
        - 6 / Real.pi ^ 2) Filter.atTop (nhds 0) := by
    have hbound : Filter.Tendsto (fun N : ℕ => 3 / Real.sqrt N) Filter.atTop (nhds 0) := by
      have h : Filter.Tendsto (fun N : ℕ => Real.sqrt N) Filter.atTop Filter.atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      exact Filter.Tendsto.div_atTop tendsto_const_nhds h
    -- the estimate holds eventually (for `N ≥ 1`)
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hsq : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNR
    have key := card_squarefree_sub_le N hN
    rw [Real.norm_eq_abs]
    rw [show (((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : ℝ) / N
        - 6 / Real.pi ^ 2
        = ((((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : ℝ)
          - 6 / Real.pi ^ 2 * N) / N by field_simp]
    rw [abs_div, abs_of_pos hNR, div_le_div_iff₀ hNR hsq]
    have hNeq : (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt hNR.le).symm
    calc |(((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : ℝ)
            - 6 / Real.pi ^ 2 * N| * Real.sqrt N
        ≤ (3 * Real.sqrt N) * Real.sqrt N := by gcongr
      _ = 3 * (N : ℝ) := by nlinarith [hNeq]
  have := hdiff.add_const (6 / Real.pi ^ 2)
  simpa using this

end TuringTask
