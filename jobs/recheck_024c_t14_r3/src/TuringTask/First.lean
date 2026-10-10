import TuringTask.Research

namespace TuringTask

open scoped BigOperators
open Research

private lemma sqrt_pos_of_pos {N : ℕ} (hN : 1 ≤ N) : 1 ≤ N.sqrt := by
  exact (Nat.sqrt_pos.2 (by omega))

private lemma sqrt_le_self_of_pos {N : ℕ} (_hN : 1 ≤ N) : N.sqrt ≤ N := by
  exact Nat.sqrt_le_self N

private lemma latticePoints_eq_hyperbola_union (N : ℕ) :
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

private lemma card_first_half (N : ℕ) (hN : 1 ≤ N) :
    ((latticePoints N).filter (fun p => p.1 ≤ N.sqrt)).card =
      (Finset.Icc 1 N.sqrt).sum (fun a => N / a) := by
  let m := N.sqrt
  calc
    ((latticePoints N).filter (fun p => p.1 ≤ m)).card =
        (latticePoints N).sum (fun p => if p.1 ≤ m then 1 else 0) := by simp
    _ = (Finset.Icc 1 N).sum (fun a =>
          (Finset.Icc 1 (N / a)).sum (fun _ => if a ≤ m then 1 else 0)) := by
      exact sum_lattice_eq_sum_div N (fun a _ => if a ≤ m then 1 else 0)
    _ = (Finset.Icc 1 N).sum (fun a => if a ≤ m then N / a else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs <;> simp_all
    _ = ((Finset.Icc 1 N).filter (fun a => a ≤ m)).sum (fun a => N / a) := by
      rw [Finset.sum_filter]
    _ = (Finset.Icc 1 m).sum (fun a => N / a) := by
      congr 1
      ext a
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨ha1, haN⟩, ham⟩
        exact ⟨ha1, ham⟩
      · rintro ⟨ha1, ham⟩
        exact ⟨⟨ha1, ham.trans (sqrt_le_self_of_pos hN)⟩, ham⟩

private lemma card_second_half (N : ℕ) :
    ((latticePoints N).filter (fun p => p.2 ≤ N.sqrt)).card =
      ((latticePoints N).filter (fun p => p.1 ≤ N.sqrt)).card := by
  let A := (latticePoints N).filter (fun p => p.1 ≤ N.sqrt)
  let B := (latticePoints N).filter (fun p => p.2 ≤ N.sqrt)
  have hBA : B = A.image (fun p => (p.2, p.1)) := by
    ext p
    simp only [B, A, Finset.mem_filter, Finset.mem_image]
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
  change B.card = A.card
  rw [hBA]
  exact Finset.card_image_of_injective A (by
    intro p q hpq
    exact Prod.ext (congrArg Prod.snd hpq) (congrArg Prod.fst hpq))

private lemma hyperbola_intersection (N : ℕ) (hN : 1 ≤ N) :
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
    have hmN : N.sqrt ≤ N := sqrt_le_self_of_pos hN
    have hprod : p.1 * p.2 ≤ N :=
      (Nat.mul_le_mul hp1m hp2m).trans (Nat.sqrt_le N)
    have hpL : p ∈ latticePoints N := by
      simp only [latticePoints, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Icc]
      exact ⟨⟨⟨hp11, hp1m.trans hmN⟩, ⟨hp21, hp2m.trans hmN⟩⟩, hprod⟩
    exact ⟨⟨hpL, hp1m⟩, hpL, hp2m⟩

/-- The exact finite Dirichlet hyperbola identity. -/
lemma sum_card_divisors_hyperbola (N : ℕ) (hN : 1 ≤ N) :
    (Finset.Icc 1 N).sum (fun n => (n.divisors.card : ℝ)) =
      2 * (Finset.Icc 1 N.sqrt).sum (fun a => ((N / a : ℕ) : ℝ)) -
        (N.sqrt : ℝ) ^ 2 := by
  let L := latticePoints N
  let A := L.filter (fun p => p.1 ≤ N.sqrt)
  let B := L.filter (fun p => p.2 ≤ N.sqrt)
  have hunion : L = A ∪ B := latticePoints_eq_hyperbola_union N
  have hcard := Finset.card_union_add_card_inter A B
  have hA : A.card = (Finset.Icc 1 N.sqrt).sum (fun a => N / a) :=
    card_first_half N hN
  have hB : B.card = A.card := card_second_half N
  have hinter : (A ∩ B).card = N.sqrt ^ 2 := by
    rw [hyperbola_intersection N hN]
    simp [pow_two]
  rw [← hunion] at hcard
  rw [hB, hA, hinter] at hcard
  have hcardR := congrArg (fun n : ℕ => (n : ℝ)) hcard
  push_cast at hcardR
  rw [sum_card_divisors_eq_card_lattice]
  linarith

private lemma cast_div_lower (N a : ℕ) (ha : 1 ≤ a) :
    (N : ℝ) / a - 1 ≤ ((N / a : ℕ) : ℝ) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hmod : ((N % a : ℕ) : ℝ) < a := by
    exact_mod_cast Nat.mod_lt N (by omega : 0 < a)
  have hdecomp : (N : ℝ) = a * (N / a : ℕ) + (N % a : ℕ) := by
    exact_mod_cast (Nat.div_add_mod N a).symm
  rw [sub_le_iff_le_add, div_le_iff₀ haR]
  nlinarith

private lemma short_floor_sum_bounds (N : ℕ) (_hN : 1 ≤ N) :
    let m := N.sqrt
    let S := (Finset.Icc 1 m).sum (fun a => ((N / a : ℕ) : ℝ))
    (N : ℝ) * (harmonic m : ℝ) - m ≤ S ∧
      S ≤ (N : ℝ) * (harmonic m : ℝ) := by
  dsimp only
  have hlower : (Finset.Icc 1 N.sqrt).sum
        (fun a => (N : ℝ) / a - 1) ≤
      (Finset.Icc 1 N.sqrt).sum (fun a => ((N / a : ℕ) : ℝ)) := by
    apply Finset.sum_le_sum
    intro a ha
    exact cast_div_lower N a (Finset.mem_Icc.mp ha).1
  have hupper : (Finset.Icc 1 N.sqrt).sum (fun a => ((N / a : ℕ) : ℝ)) ≤
      (Finset.Icc 1 N.sqrt).sum (fun a => (N : ℝ) / a) := by
    apply Finset.sum_le_sum
    intro a ha
    exact Nat.cast_div_le
  rw [Finset.sum_sub_distrib] at hlower
  simp at hlower
  rw [harmonic_real_eq_sum_Icc]
  simp only [div_eq_mul_inv, ← Finset.mul_sum] at hlower hupper ⊢
  constructor
  · simpa only [one_mul] using (show
      (N : ℝ) * (Finset.Icc 1 N.sqrt).sum (fun i => (i : ℝ)⁻¹) - N.sqrt ≤
        (Finset.Icc 1 N.sqrt).sum (fun a => ((N / a : ℕ) : ℝ)) by linarith)
  · simpa only [one_mul] using hupper

private lemma geometric_term_bounds (N : ℕ) (hN : 1 ≤ N) :
    let x := (N : ℝ)
    let y := (N.sqrt : ℝ)
    let d := x - y ^ 2
    let G := x * (1 - Real.log (x / y ^ 2)) - y ^ 2
    (-(d ^ 2 / y ^ 2) ≤ G) ∧ G ≤ 0 := by
  dsimp only
  have hyNat : 1 ≤ N.sqrt := sqrt_pos_of_pos hN
  have hy : (0 : ℝ) < (N.sqrt : ℝ) := by exact_mod_cast hyNat
  have hx : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hy2 : (0 : ℝ) < (N.sqrt : ℝ) ^ 2 := sq_pos_of_pos hy
  have hratio : (0 : ℝ) < (N : ℝ) / (N.sqrt : ℝ) ^ 2 := div_pos hx hy2
  have hinvRatio : (0 : ℝ) < (N.sqrt : ℝ) ^ 2 / (N : ℝ) := div_pos hy2 hx
  have hlogUpper := Real.log_le_sub_one_of_pos hratio
  have hlogInv := Real.log_le_sub_one_of_pos hinvRatio
  have hlogRecip :
      Real.log ((N.sqrt : ℝ) ^ 2 / (N : ℝ)) =
        -Real.log ((N : ℝ) / (N.sqrt : ℝ) ^ 2) := by
    rw [Real.log_div (ne_of_gt hy2) (ne_of_gt hx),
      Real.log_div (ne_of_gt hx) (ne_of_gt hy2)]
    ring
  have hlowerLog :
      1 - (N.sqrt : ℝ) ^ 2 / (N : ℝ) ≤
        Real.log ((N : ℝ) / (N.sqrt : ℝ) ^ 2) := by
    rw [hlogRecip] at hlogInv
    linarith
  constructor
  · calc
      -(((N : ℝ) - (N.sqrt : ℝ) ^ 2) ^ 2 / (N.sqrt : ℝ) ^ 2) =
          (N : ℝ) * (1 - ((N : ℝ) / (N.sqrt : ℝ) ^ 2 - 1)) -
            (N.sqrt : ℝ) ^ 2 := by
              field_simp
              ring
      _ ≤ (N : ℝ) *
            (1 - Real.log ((N : ℝ) / (N.sqrt : ℝ) ^ 2)) -
          (N.sqrt : ℝ) ^ 2 := by
            gcongr
  · have hmul := mul_le_mul_of_nonneg_left hlowerLog (le_of_lt hx)
    calc
      (N : ℝ) * (1 - Real.log ((N : ℝ) / (N.sqrt : ℝ) ^ 2)) -
          (N.sqrt : ℝ) ^ 2 ≤
          (N : ℝ) * (1 - (1 - (N.sqrt : ℝ) ^ 2 / (N : ℝ))) -
            (N.sqrt : ℝ) ^ 2 := by linarith
      _ = 0 := by
        field_simp
        ring

private lemma sqrt_floor_ratio_bound (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) / (N.sqrt : ℝ) ≤ 2 * Real.sqrt N := by
  have hyNat : 1 ≤ N.sqrt := sqrt_pos_of_pos hN
  have hy : (0 : ℝ) < (N.sqrt : ℝ) := by exact_mod_cast hyNat
  have hy1 : (1 : ℝ) ≤ (N.sqrt : ℝ) := by exact_mod_cast hyNat
  have hx0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hs0 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hsSq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := Real.sq_sqrt hx0
  have hNupperNat : N ≤ N.sqrt ^ 2 + 2 * N.sqrt := by
    have hlt := Nat.lt_succ_sqrt N
    nlinarith
  have hNupper : (N : ℝ) ≤ (N.sqrt : ℝ) ^ 2 + 2 * (N.sqrt : ℝ) := by
    exact_mod_cast hNupperNat
  have hfour : (N : ℝ) ≤ 4 * (N.sqrt : ℝ) ^ 2 := by nlinarith
  have hs_le : Real.sqrt (N : ℝ) ≤ 2 * (N.sqrt : ℝ) := by
    nlinarith
  rw [div_le_iff₀ hy]
  nlinarith

theorem sum_card_divisors_sub_le_aux (N : Nat) (hN : 1 <= N) :
    abs ((Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real)) - (N : Real) * Real.log N -
        (2 * Real.eulerMascheroniConstant - 1) * N) <= 4 * Real.sqrt N := by
  rw [sum_card_divisors_hyperbola N hN]
  let m : ℕ := N.sqrt
  let x : ℝ := N
  let y : ℝ := m
  let H : ℝ := harmonic m
  let S : ℝ := (Finset.Icc 1 m).sum (fun a => ((N / a : ℕ) : ℝ))
  let γ : ℝ := Real.eulerMascheroniConstant
  let d : ℝ := x - y ^ 2
  let G : ℝ := x * (1 - Real.log (x / y ^ 2)) - y ^ 2
  change |2 * S - y ^ 2 - x * Real.log x - (2 * γ - 1) * x| ≤
    4 * Real.sqrt x
  have hmNat : 1 ≤ m := by simpa [m] using sqrt_pos_of_pos hN
  have hy : 0 < y := by
    dsimp only [y]
    positivity
  have hx : 0 < x := by
    dsimp only [x]
    positivity
  have hfloor : x * H - y ≤ S ∧ S ≤ x * H := by
    simpa [m, x, y, H, S] using short_floor_sum_bounds N hN
  have hdelta0 : 0 ≤ H - Real.log y - γ := by
    simpa [H, y, γ] using harmonic_error_nonneg m hmNat
  have hdeltaLe : H - Real.log y - γ ≤ 1 / y := by
    have habs := abs_harmonic_error_le_inv m hmNat
    rw [abs_of_nonneg (harmonic_error_nonneg m hmNat)] at habs
    simpa [H, y, γ, one_div] using habs
  have hgeom : -(d ^ 2 / y ^ 2) ≤ G ∧ G ≤ 0 := by
    simpa [x, y, d, G, m] using geometric_term_bounds N hN
  have hlogRatio : Real.log (x / y ^ 2) = Real.log x - 2 * Real.log y := by
    rw [Real.log_div (ne_of_gt hx) (pow_ne_zero 2 (ne_of_gt hy)), Real.log_pow]
    ring
  have herror :
      2 * S - y ^ 2 - x * Real.log x - (2 * γ - 1) * x =
        2 * (S - x * H) + 2 * x * (H - Real.log y - γ) + G := by
    dsimp only [G]
    rw [hlogRatio]
    ring
  have hupper :
      2 * S - y ^ 2 - x * Real.log x - (2 * γ - 1) * x ≤ 2 * x / y := by
    rw [herror]
    have hdeltaMul := mul_le_mul_of_nonneg_left hdeltaLe (by positivity : 0 ≤ 2 * x)
    calc
      2 * (S - x * H) + 2 * x * (H - Real.log y - γ) + G ≤
          2 * x * (1 / y) := by nlinarith [hfloor.2, hgeom.2]
      _ = 2 * x / y := by ring
  have hNupperNat : N ≤ m ^ 2 + 2 * m := by
    have hlt := Nat.lt_succ_sqrt N
    dsimp only [m]
    nlinarith
  have hNupper : x ≤ y ^ 2 + 2 * y := by
    dsimp only [x, y]
    exact_mod_cast hNupperNat
  have hd0 : 0 ≤ d := by
    have hsquare : m ^ 2 ≤ N := by simpa [m, pow_two] using Nat.sqrt_le N
    have hsquareR : (m : ℝ) ^ 2 ≤ (N : ℝ) := by exact_mod_cast hsquare
    dsimp only [d, x, y]
    linarith
  have hdLe : d ≤ 2 * y := by
    dsimp only [d]
    linarith
  have hdSq : d ^ 2 ≤ 2 * d * y := by
    nlinarith
  have hfrac : d ^ 2 / y ^ 2 ≤ 2 * d / y := by
    calc
      d ^ 2 / y ^ 2 ≤ (2 * d * y) / y ^ 2 :=
        div_le_div_of_nonneg_right hdSq (sq_nonneg y)
      _ = 2 * d / y := by
        field_simp
  have hpenalty : 2 * y + d ^ 2 / y ^ 2 ≤ 2 * x / y := by
    calc
      2 * y + d ^ 2 / y ^ 2 ≤ 2 * y + 2 * d / y := by linarith
      _ = 2 * x / y := by
        dsimp only [d]
        field_simp
        ring
  have hlower :
      -(2 * x / y) ≤
        2 * S - y ^ 2 - x * Real.log x - (2 * γ - 1) * x := by
    rw [herror]
    have hdeltaMul := mul_nonneg (by positivity : 0 ≤ 2 * x) hdelta0
    nlinarith [hfloor.1, hgeom.1, hpenalty]
  have hratio : x / y ≤ 2 * Real.sqrt x := by
    simpa [x, y, m] using sqrt_floor_ratio_bound N hN
  have hbudget : 2 * x / y ≤ 4 * Real.sqrt x := by
    calc
      2 * x / y = 2 * (x / y) := by ring
      _ ≤ 2 * (2 * Real.sqrt x) := by gcongr
      _ = 4 * Real.sqrt x := by ring
  rw [abs_le]
  constructor
  · exact (neg_le_neg hbudget).trans hlower
  · exact hupper.trans hbudget

end TuringTask
