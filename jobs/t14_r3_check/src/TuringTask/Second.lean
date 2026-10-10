import TuringTask.First

set_option maxHeartbeats 800000

namespace TuringTask

open scoped BigOperators
open Research

private lemma sqrt_pos_of_pos₂ {N : ℕ} (hN : 1 ≤ N) : 1 ≤ N.sqrt := by
  exact (Nat.sqrt_pos.2 (by omega))

private lemma sqrt_le_self_of_pos₂ {N : ℕ} (_hN : 1 ≤ N) : N.sqrt ≤ N := by
  exact Nat.sqrt_le_self N

private lemma latticePoints_eq_hyperbola_union₂ (N : ℕ) :
    let m := N.sqrt
    let L := latticePoints N
    L = L.filter (fun p => p.1 ≤ m) ∪ L.filter (fun p => p.2 ≤ m) := by
  dsimp only
  ext p
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hp
    by_cases hp1 : p.1 ≤ N.sqrt
    · exact Or.inl ⟨hp, hp1⟩
    · right
      refine ⟨hp, ?_⟩
      by_contra hp2
      have hsquare : N.sqrt.succ * N.sqrt.succ ≤ p.1 * p.2 :=
        Nat.mul_le_mul (by omega) (by omega)
      have hpN : p.1 * p.2 ≤ N := by
        rw [latticePoints] at hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
        exact hp.2
      exact (Nat.not_le_of_lt (Nat.lt_succ_sqrt N)) (hsquare.trans hpN)
  · rintro (⟨hp, -⟩ | ⟨hp, -⟩) <;> exact hp

private lemma hyperbola_intersection₂ (N : ℕ) (hN : 1 ≤ N) :
    (latticePoints N).filter (fun p => p.1 ≤ N.sqrt) ∩
        (latticePoints N).filter (fun p => p.2 ≤ N.sqrt) =
      Finset.Icc 1 N.sqrt ×ˢ Finset.Icc 1 N.sqrt := by
  ext p
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hpL, hp1m⟩, -, hp2m⟩
    have hpbox : (1 ≤ p.1 ∧ p.1 ≤ N) ∧ (1 ≤ p.2 ∧ p.2 ≤ N) := by
      rw [latticePoints] at hpL
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hpL
      exact hpL.1
    exact ⟨⟨hpbox.1.1, hp1m⟩, ⟨hpbox.2.1, hp2m⟩⟩
  · rintro ⟨⟨hp11, hp1m⟩, ⟨hp21, hp2m⟩⟩
    have hmN : N.sqrt ≤ N := sqrt_le_self_of_pos₂ hN
    have hprod : p.1 * p.2 ≤ N :=
      (Nat.mul_le_mul hp1m hp2m).trans (Nat.sqrt_le N)
    have hpL : p ∈ latticePoints N := by
      simp only [latticePoints, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Icc]
      exact ⟨⟨⟨hp11, hp1m.trans hmN⟩, ⟨hp21, hp2m.trans hmN⟩⟩, hprod⟩
    exact ⟨⟨hpL, hp1m⟩, hpL, hp2m⟩

private lemma weighted_first_half (N : ℕ) (hN : 1 ≤ N) :
    ((latticePoints N).filter (fun p => p.1 ≤ N.sqrt)).sum
        (fun p => (1 : ℝ) / (p.1 * p.2)) =
      (Finset.Icc 1 N.sqrt).sum (fun a => (harmonic (N / a) : ℝ) / a) := by
  let m := N.sqrt
  calc
    ((latticePoints N).filter (fun p => p.1 ≤ m)).sum
          (fun p => (1 : ℝ) / (p.1 * p.2)) =
        (latticePoints N).sum (fun p =>
          if p.1 ≤ m then (1 : ℝ) / (p.1 * p.2) else 0) := by
      rw [Finset.sum_filter]
    _ = (Finset.Icc 1 N).sum (fun a =>
          (Finset.Icc 1 (N / a)).sum (fun b =>
            if a ≤ m then (1 : ℝ) / (a * b) else 0)) := by
      exact sum_lattice_eq_sum_div N
        (fun a b => if a ≤ m then (1 : ℝ) / (a * b) else 0)
    _ = (Finset.Icc 1 N).sum (fun a =>
          if a ≤ m then (harmonic (N / a) : ℝ) / a else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs with ham
      · rw [harmonic_real_eq_sum_Icc]
        simp only [div_eq_mul_inv, mul_inv_rev, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b hb
        ac_rfl
      · simp
    _ = ((Finset.Icc 1 N).filter (fun a => a ≤ m)).sum
          (fun a => (harmonic (N / a) : ℝ) / a) := by
      rw [Finset.sum_filter]
    _ = (Finset.Icc 1 m).sum
          (fun a => (harmonic (N / a) : ℝ) / a) := by
      congr 1
      ext a
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨ha1, haN⟩, ham⟩
        exact ⟨ha1, ham⟩
      · rintro ⟨ha1, ham⟩
        exact ⟨⟨ha1, ham.trans (sqrt_le_self_of_pos₂ hN)⟩, ham⟩

private lemma weighted_second_half (N : ℕ) :
    ((latticePoints N).filter (fun p => p.2 ≤ N.sqrt)).sum
        (fun p => (1 : ℝ) / (p.1 * p.2)) =
      ((latticePoints N).filter (fun p => p.1 ≤ N.sqrt)).sum
        (fun p => (1 : ℝ) / (p.1 * p.2)) := by
  let A := (latticePoints N).filter (fun p => p.1 ≤ N.sqrt)
  let B := (latticePoints N).filter (fun p => p.2 ≤ N.sqrt)
  let swap : ℕ × ℕ → ℕ × ℕ := fun p => (p.2, p.1)
  have hBA : B = A.image swap := by
    ext p
    simp only [B, A, swap, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hpL, hp2⟩
      refine ⟨(p.2, p.1), ?_, rfl⟩
      refine ⟨?_, hp2⟩
      rw [latticePoints] at hpL ⊢
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hpL ⊢
      exact ⟨⟨hpL.1.2, hpL.1.1⟩, by simpa [Nat.mul_comm] using hpL.2⟩
    · rintro ⟨q, ⟨hqL, hq1⟩, hqp⟩
      subst p
      refine ⟨?_, hq1⟩
      rw [latticePoints] at hqL ⊢
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hqL ⊢
      exact ⟨⟨hqL.1.2, hqL.1.1⟩, by simpa [Nat.mul_comm] using hqL.2⟩
  change B.sum _ = A.sum _
  rw [hBA, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro p hp
    simp only [swap]
    congr 1
    ring
  · intro p hp q hq hpq
    exact Prod.ext (congrArg Prod.snd hpq) (congrArg Prod.fst hpq)

private lemma weighted_square (m : ℕ) :
    (Finset.Icc 1 m ×ˢ Finset.Icc 1 m).sum
        (fun p => (1 : ℝ) / (p.1 * p.2)) = (harmonic m : ℝ) ^ 2 := by
  rw [Finset.sum_product, harmonic_real_eq_sum_Icc]
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  calc
    (Finset.Icc 1 m).sum (fun x =>
        (Finset.Icc 1 m).sum (fun y => (y : ℝ)⁻¹ * (x : ℝ)⁻¹)) =
        (Finset.Icc 1 m).sum (fun x =>
          ((Finset.Icc 1 m).sum (fun y => (y : ℝ)⁻¹)) * (x : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_mul]
    _ = ((Finset.Icc 1 m).sum (fun y => (y : ℝ)⁻¹)) ^ 2 := by
      rw [← Finset.mul_sum]
      ring
    _ = ((Finset.Icc 1 m).sum (fun x => (x : ℝ)⁻¹)) ^ 2 := rfl

/-- The exact weighted Dirichlet hyperbola identity. -/
lemma sum_card_divisors_div_hyperbola (N : ℕ) (hN : 1 ≤ N) :
    (Finset.Icc 1 N).sum (fun n => (n.divisors.card : ℝ) / n) =
      2 * (Finset.Icc 1 N.sqrt).sum
          (fun a => (harmonic (N / a) : ℝ) / a) -
        (harmonic N.sqrt : ℝ) ^ 2 := by
  let L := latticePoints N
  let A := L.filter (fun p => p.1 ≤ N.sqrt)
  let B := L.filter (fun p => p.2 ≤ N.sqrt)
  let w : ℕ × ℕ → ℝ := fun p => (1 : ℝ) / (p.1 * p.2)
  have hunion : L = A ∪ B := latticePoints_eq_hyperbola_union₂ N
  have hsum := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := w)
  have hA : A.sum w = (Finset.Icc 1 N.sqrt).sum
      (fun a => (harmonic (N / a) : ℝ) / a) := weighted_first_half N hN
  have hB : B.sum w = A.sum w := weighted_second_half N
  have hinter : (A ∩ B).sum w = (harmonic N.sqrt : ℝ) ^ 2 := by
    rw [hyperbola_intersection₂ N hN]
    exact weighted_square N.sqrt
  rw [← hunion, hB, hA, hinter] at hsum
  rw [sum_card_divisors_div_eq_sum_lattice]
  change L.sum w = _
  linarith

private lemma floor_harmonic_approx (N a : ℕ) (hN : 1 ≤ N)
    (ha : a ∈ Finset.Icc 1 N.sqrt) :
    |(harmonic (N / a) : ℝ) - Real.log ((N : ℝ) / a) -
        Real.eulerMascheroniConstant| ≤ (N.sqrt : ℝ)⁻¹ := by
  let m := N.sqrt
  let k := N / a
  have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
  have ham : a ≤ m := (Finset.mem_Icc.mp ha).2
  have hm1 : 1 ≤ m := by simpa [m] using sqrt_pos_of_pos₂ hN
  have hmaN : m * a ≤ N := by
    calc
      m * a ≤ m * m := Nat.mul_le_mul_left m ham
      _ ≤ N := by simpa [m] using Nat.sqrt_le N
  have hmk : m ≤ k := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < a)]
    simpa [Nat.mul_comm] using hmaN
  have hk1 : 1 ≤ k := hm1.trans hmk
  have haR : (0 : ℝ) < a := by exact_mod_cast ha1
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
  have hqR : (0 : ℝ) < (N : ℝ) / a := by positivity
  have hkq : (k : ℝ) ≤ (N : ℝ) / a := by
    simpa [k] using (Nat.cast_div_le (α := ℝ) (m := N) (n := a))
  have hqk1 : (N : ℝ) / a < (k : ℝ) + 1 := by
    have hmod : ((N % a : ℕ) : ℝ) < a := by
      exact_mod_cast Nat.mod_lt N (by omega : 0 < a)
    have hdecomp : (N : ℝ) = a * (k : ℝ) + (N % a : ℕ) := by
      dsimp only [k]
      exact_mod_cast (Nat.div_add_mod N a).symm
    rw [div_lt_iff₀ haR]
    nlinarith
  have hlogkq : Real.log k ≤ Real.log ((N : ℝ) / a) :=
    Real.strictMonoOn_log.monotoneOn (show 0 < (k : ℝ) from hkR)
      (show 0 < (N : ℝ) / a from hqR) hkq
  have hlogqk1 : Real.log ((N : ℝ) / a) ≤ Real.log ((k : ℝ) + 1) :=
    (Real.strictMonoOn_log hqR (by linarith : 0 < (k : ℝ) + 1) hqk1).le
  have hkNe : (k : ℝ) ≠ 0 := ne_of_gt hkR
  have hloggap : Real.log ((k : ℝ) + 1) - Real.log k ≤ (k : ℝ)⁻¹ := by
    have heq : Real.log ((k : ℝ) + 1) - Real.log k =
        Real.log (1 + (k : ℝ)⁻¹) := by
      rw [← Real.log_div (by positivity : (k : ℝ) + 1 ≠ 0) hkNe]
      congr 1
      field_simp
    rw [heq]
    have hp : 0 < 1 + (k : ℝ)⁻¹ := by positivity
    linarith [Real.log_le_sub_one_of_pos hp]
  have herr0 := harmonic_error_nonneg k hk1
  have herrLe := abs_harmonic_error_le_inv k hk1
  rw [abs_of_nonneg herr0] at herrLe
  have hlower : -(k : ℝ)⁻¹ ≤
      (harmonic k : ℝ) - Real.log ((N : ℝ) / a) -
        Real.eulerMascheroniConstant := by
    linarith
  have hupper : (harmonic k : ℝ) - Real.log ((N : ℝ) / a) -
      Real.eulerMascheroniConstant ≤ (k : ℝ)⁻¹ := by
    linarith
  have hinv : (k : ℝ)⁻¹ ≤ (m : ℝ)⁻¹ := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
    have hmkR : (m : ℝ) ≤ k := by exact_mod_cast hmk
    exact (inv_le_inv₀ hkR hmR).2 hmkR
  dsimp only [k] at hlower hupper hinv ⊢
  rw [abs_le]
  constructor <;> linarith

private lemma weighted_approximation (N : ℕ) (hN : 1 ≤ N) :
    let m := N.sqrt
    let γ := Real.eulerMascheroniConstant
    let E := (Finset.Icc 1 m).sum (fun a =>
      ((harmonic (N / a) : ℝ) - (Real.log ((N : ℝ) / a) + γ)) / a)
    |E| ≤ 1 := by
  dsimp only
  rw [abs_le]
  have hm1 : 1 ≤ N.sqrt := sqrt_pos_of_pos₂ hN
  have hsumAbs : (Finset.Icc 1 N.sqrt).sum (fun a =>
      |((harmonic (N / a) : ℝ) -
        (Real.log ((N : ℝ) / a) + Real.eulerMascheroniConstant)) / a|) ≤ 1 := by
    calc
      _ ≤ (Finset.Icc 1 N.sqrt).sum (fun a =>
          (N.sqrt : ℝ)⁻¹ / a) := by
        apply Finset.sum_le_sum
        intro a ha
        rw [abs_div]
        have ha0 : (0 : ℝ) ≤ a := by positivity
        rw [abs_of_nonneg ha0]
        exact div_le_div_of_nonneg_right (by
          simpa only [sub_sub] using floor_harmonic_approx N a hN ha) ha0
      _ = (N.sqrt : ℝ)⁻¹ * (harmonic N.sqrt : ℝ) := by
        rw [harmonic_real_eq_sum_Icc]
        simp only [div_eq_mul_inv, Finset.mul_sum, one_mul]
      _ ≤ (N.sqrt : ℝ)⁻¹ * N.sqrt := by
        gcongr
        rw [harmonic_real_eq_sum_Icc]
        calc
          (Finset.Icc 1 N.sqrt).sum (fun i => (1 : ℝ) / i) ≤
              (Finset.Icc 1 N.sqrt).sum (fun _ => (1 : ℝ)) := by
            apply Finset.sum_le_sum
            intro i hi
            have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (Finset.mem_Icc.mp hi).1
            calc
              (1 : ℝ) / i ≤ 1 / 1 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hi1
              _ = 1 := by norm_num
          _ = N.sqrt := by simp
      _ = 1 := by
        field_simp
  constructor
  · calc
      -1 ≤ -(Finset.Icc 1 N.sqrt).sum (fun a =>
          |((harmonic (N / a) : ℝ) -
            (Real.log ((N : ℝ) / a) + Real.eulerMascheroniConstant)) / a|) :=
        neg_le_neg hsumAbs
      _ ≤ (Finset.Icc 1 N.sqrt).sum (fun a =>
          ((harmonic (N / a) : ℝ) -
            (Real.log ((N : ℝ) / a) + Real.eulerMascheroniConstant)) / a) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_le_sum
        intro a ha
        exact neg_abs_le _
  · exact (Finset.sum_le_sum fun a ha => le_abs_self _).trans hsumAbs

private lemma hasDerivAt_log_div (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.log y / y)
      ((1 - Real.log x) / x ^ 2) x := by
  have h := (Real.hasDerivAt_log hx).div (hasDerivAt_id x) hx
  have heq : (1 - Real.log x) / x ^ 2 =
      (x⁻¹ * x - Real.log x * 1) / x ^ 2 := by
    field_simp [hx]
  rw [heq]
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => rfl)

private lemma antitoneOn_log_div :
    AntitoneOn (fun x : ℝ => Real.log x / x) (Set.Ici 3) := by
  apply antitoneOn_of_deriv_nonpos (D := Set.Ici 3)
    (convex_Ici (𝕜 := ℝ) (3 : ℝ))
  · apply ContinuousOn.div
    · exact Real.continuousOn_log.mono (by
        intro x hx
        simp only [Set.mem_Ici] at hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith)
    · exact continuousOn_id
    · intro x hx
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) hx)
  · intro x hx
    exact (hasDerivAt_log_div x (by
      have : 3 < x := by simpa only [interior_Ici, Set.mem_Ioi] using hx
      positivity)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx3 : 3 < x := by simpa only [interior_Ici, Set.mem_Ioi] using hx
    have hlog3 : 1 < Real.log 3 := by linarith [Real.log_three_gt_d9]
    have hlogx : 1 ≤ Real.log x := by
      have hx0 : (0 : ℝ) < x := by linarith
      have := (Real.strictMonoOn_log (by norm_num : (0 : ℝ) < 3) hx0 hx3).le
      linarith
    rw [(hasDerivAt_log_div x (by positivity)).deriv]
    have hxSq : 0 < x ^ 2 := sq_pos_of_pos (by positivity)
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hxSq.le

private lemma integral_log_div_three (m : ℕ) (hm : 3 ≤ m) :
    ∫ x : ℝ in 3..m, Real.log x / x =
      Real.log m ^ 2 / 2 - Real.log 3 ^ 2 / 2 := by
  have hderiv : ∀ x ∈ Set.uIcc (3 : ℝ) (m : ℝ),
      HasDerivAt (fun y : ℝ => Real.log y ^ 2 / 2) (Real.log x / x) x := by
    intro x hx
    have hx3 : (3 : ℝ) ≤ x := by
      rw [Set.uIcc_of_le (by exact_mod_cast hm)] at hx
      exact hx.1
    have hx0 : x ≠ 0 := ne_of_gt (by linarith)
    have h := ((Real.hasDerivAt_log hx0).pow 2).div_const 2
    have heq : Real.log x / x = 2 * Real.log x * x⁻¹ / 2 := by
      field_simp
    rw [heq]
    simpa [div_eq_mul_inv] using h
  have hint : IntervalIntegrable (fun x : ℝ => Real.log x / x)
      MeasureTheory.volume 3 m := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · exact Real.continuousOn_log.mono (by
        intro x hx
        rw [Set.uIcc_of_le (by exact_mod_cast hm)] at hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith [hx.1])
    · exact continuousOn_id
    · intro x hx
      rw [Set.uIcc_of_le (by exact_mod_cast hm)] at hx
      exact ne_of_gt (by linarith [hx.1])
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

private lemma shifted_log_sum (m : ℕ) :
    (Finset.Ico 3 m).sum (fun i => Real.log (i + 1 : ℕ) / (i + 1 : ℕ)) =
      (Finset.Icc 4 m).sum (fun i => Real.log i / i) := by
  apply Finset.sum_bij (fun i _ => i + 1)
  · intro i hi
    simp only [Finset.mem_Ico, Finset.mem_Icc] at hi ⊢
    omega
  · intro i₁ hi₁ i₂ hi₂ heq
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    refine ⟨j - 1, ?_, ?_⟩
    · simp only [Finset.mem_Ico]
      omega
    · omega
  · intro i hi
    norm_num

private lemma log_sum_discrepancy (m : ℕ) (hm : 3 ≤ m) :
    |Real.log m ^ 2 -
      2 * (Finset.Icc 1 m).sum (fun a => Real.log a / a)| ≤ (2 : ℝ) / 3 := by
  let f : ℝ → ℝ := fun x => Real.log x / x
  let S : ℝ := (Finset.Icc 1 m).sum (fun a => Real.log a / a)
  have hanti : AntitoneOn f (Set.Icc (3 : ℝ) m) :=
    antitoneOn_log_div.mono (by
      intro x hx
      exact hx.1)
  have hint : ∫ x : ℝ in 3..m, f x =
      Real.log m ^ 2 / 2 - Real.log 3 ^ 2 / 2 := by
    simpa [f] using integral_log_div_three m hm
  have hnonneg : ∀ i : ℕ, i ∈ Finset.Icc 1 m → 0 ≤ Real.log i / i := by
    intro i hi
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hi).1)) (by positivity)
  have hsplitLower : S = Real.log 2 / 2 +
      (Finset.Icc 3 m).sum (fun a => Real.log a / a) := by
    have hset : Finset.Icc 1 m = Finset.Icc 1 2 ∪ Finset.Icc 3 m := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_union]
      omega
    have hdis : Disjoint (Finset.Icc 1 2) (Finset.Icc 3 m) := by
      rw [Finset.disjoint_left]
      intro i hi hj
      simp only [Finset.mem_Icc] at hi hj
      omega
    dsimp only [S]
    rw [hset, Finset.sum_union hdis]
    norm_num [show Finset.Icc 1 2 = {1, 2} by decide, Real.log_one]
  have hIcoLe : (Finset.Ico 3 m).sum (fun a => Real.log a / a) ≤
      (Finset.Icc 3 m).sum (fun a => Real.log a / a) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [Finset.mem_Ico, Finset.mem_Icc] at hi ⊢
      omega
    · intro i hiAll hiSub
      apply hnonneg i
      simp only [Finset.mem_Icc] at hiAll ⊢
      omega
  have hlowerSum : Real.log 2 / 2 +
      (Real.log m ^ 2 / 2 - Real.log 3 ^ 2 / 2) ≤ S := by
    have hcomp := AntitoneOn.integral_le_sum_Ico hm hanti
    norm_num only [Nat.cast_ofNat] at hcomp
    rw [hint] at hcomp
    rw [hsplitLower]
    linarith
  have hsplitUpper : S = Real.log 2 / 2 + Real.log 3 / 3 +
      (Finset.Icc 4 m).sum (fun a => Real.log a / a) := by
    have hset : Finset.Icc 1 m = Finset.Icc 1 3 ∪ Finset.Icc 4 m := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_union]
      omega
    have hdis : Disjoint (Finset.Icc 1 3) (Finset.Icc 4 m) := by
      rw [Finset.disjoint_left]
      intro i hi hj
      simp only [Finset.mem_Icc] at hi hj
      omega
    dsimp only [S]
    rw [hset, Finset.sum_union hdis]
    norm_num [show Finset.Icc 1 3 = {1, 2, 3} by decide, Real.log_one]
  have hupperSum : S ≤ Real.log 2 / 2 + Real.log 3 / 3 +
      (Real.log m ^ 2 / 2 - Real.log 3 ^ 2 / 2) := by
    have hcomp := AntitoneOn.sum_le_integral_Ico hm hanti
    norm_num only [Nat.cast_ofNat] at hcomp
    change (Finset.Ico 3 m).sum
        (fun i => Real.log (i + 1 : ℕ) / (i + 1 : ℕ)) ≤
      ∫ x : ℝ in 3..m, f x at hcomp
    rw [hint, shifted_log_sum m] at hcomp
    rw [hsplitUpper]
    linarith
  have hlog2lo := Real.log_two_gt_d9
  have hlog2hi := Real.log_two_lt_d9
  have hlog3lo := Real.log_three_gt_d9
  have hlog3hi := Real.log_three_lt_d9
  rw [abs_le]
  constructor <;> nlinarith

theorem sum_card_divisors_div_sub_le_aux (N : Nat) (hN : 1 <= N) :
    abs ((Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real) / n) - Real.log N ^ 2 / 2 -
        2 * Real.eulerMascheroniConstant * Real.log N) <= 4 := by
  rw [sum_card_divisors_div_hyperbola N hN]
  let m : ℕ := N.sqrt
  let L : ℝ := Real.log N
  let x : ℝ := Real.log m
  let γ : ℝ := Real.eulerMascheroniConstant
  let H : ℝ := harmonic m
  let S : ℝ := (Finset.Icc 1 m).sum (fun a => Real.log a / a)
  let T : ℝ := (Finset.Icc 1 m).sum (fun a => (harmonic (N / a) : ℝ) / a)
  let E : ℝ := (Finset.Icc 1 m).sum (fun a =>
    ((harmonic (N / a) : ℝ) - (Real.log ((N : ℝ) / a) + γ)) / a)
  let δ : ℝ := H - x - γ
  let u : ℝ := L - 2 * x
  let R : ℝ := (x ^ 2 - 2 * S + γ ^ 2) +
    2 * (x + u) * δ - δ ^ 2 - u ^ 2 / 2
  change |2 * T - H ^ 2 - L ^ 2 / 2 - 2 * γ * L| ≤ 4
  have hm1 : 1 ≤ m := by simpa [m] using sqrt_pos_of_pos₂ hN
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
  have hE : |E| ≤ 1 := by
    simpa [m, γ, E] using weighted_approximation N hN
  have hsumMain : T = (L + γ) * H - S + E := by
    calc
      T = (Finset.Icc 1 m).sum (fun a =>
          (Real.log ((N : ℝ) / a) + γ) / a +
            ((harmonic (N / a) : ℝ) -
              (Real.log ((N : ℝ) / a) + γ)) / a) := by
        dsimp only [T]
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = (Finset.Icc 1 m).sum (fun a =>
          ((L + γ) / a - Real.log a / a) +
            ((harmonic (N / a) : ℝ) -
              (Real.log ((N : ℝ) / a) + γ)) / a) := by
        apply Finset.sum_congr rfl
        intro a ha
        have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
        have haNe : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha1)
        have hNNe : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
        rw [Real.log_div hNNe haNe]
        dsimp only [L]
        ring
      _ = (L + γ) * H - S + E := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        dsimp only [S, E, H]
        rw [harmonic_real_eq_sum_Icc]
        simp only [div_eq_mul_inv, ← Finset.mul_sum]
        ring
  have herror : 2 * T - H ^ 2 - L ^ 2 / 2 - 2 * γ * L = 2 * E + R := by
    rw [hsumMain]
    dsimp only [R, δ, u]
    ring
  have hgamma0 : 0 ≤ γ := by
    dsimp only [γ]
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hgammaLe : γ ≤ (2 : ℝ) / 3 := by
    dsimp only [γ]
    exact Real.eulerMascheroniConstant_lt_two_thirds.le
  have hdelta0 : 0 ≤ δ := by
    simpa [δ, H, x, γ] using harmonic_error_nonneg m hm1
  have hdeltaLe : δ ≤ (m : ℝ)⁻¹ := by
    have h := abs_harmonic_error_le_inv m hm1
    rw [abs_of_nonneg (harmonic_error_nonneg m hm1)] at h
    simpa [δ, H, x, γ] using h
  have hmSqNat : m ^ 2 ≤ N := by
    simpa [m, pow_two] using Nat.sqrt_le N
  have hNupperNat : N ≤ m ^ 2 + 2 * m := by
    have hlt := Nat.lt_succ_sqrt N
    dsimp only [m]
    nlinarith
  have hratioPos : 0 < (N : ℝ) / (m : ℝ) ^ 2 := by positivity
  have hlogRatio : u = Real.log ((N : ℝ) / (m : ℝ) ^ 2) := by
    dsimp only [u, L, x]
    rw [Real.log_div (by positivity : (N : ℝ) ≠ 0)
      (pow_ne_zero 2 (ne_of_gt hmR)), Real.log_pow]
    ring
  have hratioOne : (1 : ℝ) ≤ (N : ℝ) / (m : ℝ) ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hmR)]
    have hcast : (m : ℝ) ^ 2 ≤ N := by exact_mod_cast hmSqNat
    simpa only [one_mul] using hcast
  have hratioUpper : (N : ℝ) / (m : ℝ) ^ 2 ≤ 1 + 2 / (m : ℝ) := by
    rw [div_le_iff₀ (sq_pos_of_pos hmR)]
    have hcast : (N : ℝ) ≤ (m : ℝ) ^ 2 + 2 * m := by exact_mod_cast hNupperNat
    field_simp
    nlinarith
  have hu0 : 0 ≤ u := by
    rw [hlogRatio]
    exact Real.log_nonneg hratioOne
  have huLe : u ≤ 2 / (m : ℝ) := by
    rw [hlogRatio]
    calc
      Real.log ((N : ℝ) / (m : ℝ) ^ 2) ≤
          (N : ℝ) / (m : ℝ) ^ 2 - 1 :=
        Real.log_le_sub_one_of_pos hratioPos
      _ ≤ 2 / (m : ℝ) := by linarith
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    exact Real.log_nonneg (by exact_mod_cast hm1)
  have hR : |R| ≤ 2 := by
    have hcases : m = 1 ∨ m = 2 ∨ 3 ≤ m := by omega
    rcases hcases with hmEq | hmEq | hm3
    · have hxEq : x = 0 := by simp [x, hmEq]
      have hSEq : S = 0 := by simp [S, hmEq]
      have hHEq : H = 1 := by norm_num [H, hmEq, harmonic]
      have hdeltaEq : δ = 1 - γ := by
        dsimp only [δ]
        rw [hHEq, hxEq]
        ring
      have huLe' : u ≤ 2 := by simpa [hmEq] using huLe
      have hfirst : 0 ≤ 2 * γ - 1 := by
        dsimp only [γ]
        linarith [Real.one_half_lt_eulerMascheroniConstant]
      have hfirstLe : 2 * γ - 1 ≤ (1 : ℝ) / 3 := by linarith only [hgammaLe]
      have hconcave : 2 * u * (1 - γ) - u ^ 2 / 2 ≤
          2 * (1 - γ) ^ 2 := by
        nlinarith only [sq_nonneg (u - 2 * (1 - γ))]
      have honeSq : (1 - γ) ^ 2 ≤ (1 : ℝ) / 4 := by
        nlinarith only [hgamma0, hgammaLe,
          Real.one_half_lt_eulerMascheroniConstant.le]
      have hlowerConcave : -(2 : ℝ) / 3 ≤
          2 * u * (1 - γ) - u ^ 2 / 2 := by
        have hp₁ : 0 ≤ u * (2 - u) :=
          mul_nonneg hu0 (by linarith only [huLe'])
        have hp₂ : 0 ≤ u * ((1 - γ) - (1 : ℝ) / 3) :=
          mul_nonneg hu0 (by linarith only [hgammaLe])
        nlinarith only [hp₁, hp₂]
      dsimp only [R]
      rw [hxEq, hSEq, hdeltaEq]
      rw [abs_le]
      constructor <;> nlinarith only [hfirst, hfirstLe, hconcave,
        honeSq, hlowerConcave]
    · have hxEq : x = Real.log 2 := by simp [x, hmEq]
      have hSEq : S = Real.log 2 / 2 := by
        simp [S, hmEq, show Finset.Icc 1 2 = {1, 2} by decide, Real.log_one]
      have huLe' : u ≤ 1 := by simpa [hmEq] using huLe
      have hdLe' : δ ≤ (1 : ℝ) / 2 := by simpa [hmEq] using hdeltaLe
      have hxLo : (0 : ℝ) ≤ x := hx0
      have hxLe : x ≤ 1 := by rw [hxEq]; linarith [Real.log_two_lt_d9]
      have huLeX : u ≤ x := by
        have hratioTwo : (N : ℝ) / (m : ℝ) ^ 2 ≤ 2 := by
          have := hratioUpper
          norm_num [hmEq] at this ⊢
          exact this
        have hlogLe : Real.log ((N : ℝ) / (m : ℝ) ^ 2) ≤ Real.log 2 :=
          Real.strictMonoOn_log.monotoneOn hratioPos (by norm_num)
            hratioTwo
        calc
          u = Real.log ((N : ℝ) / (m : ℝ) ^ 2) := hlogRatio
          _ ≤ Real.log 2 := hlogLe
          _ = x := hxEq.symm
      have hquad : -(1 : ℝ) / 4 ≤ x ^ 2 - x := by
        nlinarith only [sq_nonneg (x - 1 / 2)]
      have hquadUpper : x ^ 2 - x ≤ 0 := by
        nlinarith only [hxLo, hxLe]
      have hcross : 0 ≤ 2 * (x + u) * δ := by positivity
      have hxuLe : x + u ≤ (3 : ℝ) / 2 := by
        have hxTight : x < (7 : ℝ) / 10 := by
          rw [hxEq]
          linarith [Real.log_two_lt_d9]
        linarith only [huLeX, hxTight]
      have hcrossUpper : 2 * (x + u) * δ ≤ (3 : ℝ) / 2 := by
        have hp : 0 ≤ (x + u) * (1 - 2 * δ) :=
          mul_nonneg (by linarith only [hxLo, hu0]) (by linarith only [hdLe'])
        nlinarith only [hp, hxuLe]
      have hgammaSq : γ ^ 2 ≤ (4 : ℝ) / 9 := by
        nlinarith only [hgamma0, hgammaLe]
      have hdSq : δ ^ 2 ≤ (1 : ℝ) / 4 := by
        nlinarith only [hdelta0, hdLe']
      have huSq : u ^ 2 ≤ 1 := by
        nlinarith only [hu0, huLe']
      dsimp only [R]
      have htwiceS : 2 * S = x := by rw [hSEq, hxEq]; ring
      rw [htwiceS]
      rw [abs_le]
      constructor
      · nlinarith only [hquad, hcross, hdSq, huSq, sq_nonneg γ]
      · nlinarith only [hquadUpper, hcrossUpper, hgammaSq,
          sq_nonneg δ, sq_nonneg u]
    · have hdisc := log_sum_discrepancy m hm3
      have hdisc' : -(2 : ℝ) / 3 ≤ x ^ 2 - 2 * S ∧
          x ^ 2 - 2 * S ≤ (2 : ℝ) / 3 := by
        rw [abs_le] at hdisc
        constructor
        · dsimp only [x, S]
          linarith [hdisc.1]
        · simpa [x, S] using hdisc.2
      let c : ℝ := (m : ℝ)⁻¹
      have hc0 : 0 ≤ c := by positivity
      have hcLe : c ≤ (1 : ℝ) / 3 := by
        dsimp only [c]
        have hm3R : (3 : ℝ) ≤ m := by exact_mod_cast hm3
        simpa only [one_div] using
          ((inv_le_inv₀ hmR (by norm_num : (0 : ℝ) < 3)).2 hm3R)
      have hdeltaLe' : δ ≤ c := by simpa [c] using hdeltaLe
      have huLe' : u ≤ 2 * c := by simpa [c, div_eq_mul_inv] using huLe
      have hxm : x * c ≤ Real.log 3 / 3 := by
        have hmMem : (m : ℝ) ∈ Set.Ici (3 : ℝ) := by
          show (3 : ℝ) ≤ m
          exact_mod_cast hm3
        have hmono := antitoneOn_log_div (by norm_num : (3 : ℝ) ∈ Set.Ici 3)
          hmMem (by exact_mod_cast hm3 : (3 : ℝ) ≤ m)
        dsimp only [x, c]
        simpa [div_eq_mul_inv] using hmono
      have hcSq : c ^ 2 ≤ (1 : ℝ) / 9 := by nlinarith
      have hxuLarge : c + δ ≤ 2 * (x + u) := by
        have hxLarge : 1 ≤ x := by
          dsimp only [x]
          have hlogm : Real.log 3 ≤ Real.log m :=
            Real.strictMonoOn_log.monotoneOn (by norm_num)
              (show (0 : ℝ) < m from hmR)
              (by exact_mod_cast hm3)
          linarith [Real.log_three_gt_d9]
        nlinarith
      have hdeltaPart : 2 * (x + u) * δ - δ ^ 2 ≤
          2 * (x + u) * c - c ^ 2 := by
        have hp : 0 ≤ (c - δ) * (2 * (x + u) - c - δ) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith
      have huPart : 2 * u * c - u ^ 2 / 2 ≤ 2 * c ^ 2 := by
        nlinarith [sq_nonneg (u - 2 * c)]
      have htailUpper : 2 * (x + u) * δ - δ ^ 2 - u ^ 2 / 2 ≤
          (8 : ℝ) / 9 := by
        have hlog3 : Real.log 3 ≤ (7 : ℝ) / 6 := by
          linarith [Real.log_three_lt_d9]
        nlinarith
      have htailLower : -(1 : ℝ) / 3 ≤
          2 * (x + u) * δ - δ ^ 2 - u ^ 2 / 2 := by
        have hcross : 0 ≤ 2 * (x + u) * δ := by positivity
        have hdSq : δ ^ 2 ≤ c ^ 2 := by nlinarith
        have huSq : u ^ 2 ≤ 4 * c ^ 2 := by nlinarith
        nlinarith
      have hgammaSq : γ ^ 2 ≤ (4 : ℝ) / 9 := by nlinarith
      dsimp only [R]
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg γ]
  rw [herror]
  rw [abs_le] at hE hR ⊢
  constructor <;> linarith

end TuringTask
