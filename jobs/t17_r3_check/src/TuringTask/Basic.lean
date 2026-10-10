import Mathlib
import TuringTask.TotientEstimates

namespace TuringTask

theorem card_squarefree_sub_le (N : Nat) (hN : 1 <= N) :
    abs ((((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : Real) -
        6 / Real.pi ^ 2 * N) <= 3 * Real.sqrt N := by
  let K := N.sqrt
  let A : Real := ∑ d ∈ Finset.Icc 1 K,
    mur d * ((N / d ^ 2 : Nat) : Real)
  let S : Real := ∑ d ∈ Finset.Icc 1 K, mur d / (d : Real) ^ 2
  let C : Real := 6 / Real.pi ^ 2
  have hK : 1 ≤ K := by
    dsimp [K]
    exact Nat.le_sqrt.mpr (by simpa using hN)
  have hfloor : |A - (N : Real) * S| ≤ (K : Real) := by
    simpa [A, S] using abs_floor_sum_sub_le N K
  have hpartial : |S - C| ≤ 1 / (K : Real) := by
    simpa [S, C] using abs_partial_mur_sub_le K hK
  have hmain : |(N : Real) * S - C * N| ≤ (N : Real) / K := by
    rw [show (N : Real) * S - C * N = (N : Real) * (S - C) by ring]
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    calc
      (N : Real) * |S - C| ≤ (N : Real) * (1 / (K : Real)) :=
        mul_le_mul_of_nonneg_left hpartial (Nat.cast_nonneg N)
      _ = (N : Real) / K := by ring
  have hcount :
      (((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : Real) = A := by
    simpa [A, K] using card_squarefree_eq_sum_real N
  rw [hcount]
  change |A - C * N| ≤ 3 * Real.sqrt N
  calc
    |A - C * N| = |(A - (N : Real) * S) + ((N : Real) * S - C * N)| := by ring_nf
    _ ≤ |A - (N : Real) * S| + |(N : Real) * S - C * N| := abs_add_le _ _
    _ ≤ (K : Real) + (N : Real) / K := add_le_add hfloor hmain
    _ ≤ Real.sqrt N + 2 * Real.sqrt N := by
      gcongr
      · simpa [K] using (Real.nat_sqrt_le_real_sqrt (a := N))
      · simpa [K] using div_nat_sqrt_le_two_sqrt N hN
    _ = 3 * Real.sqrt N := by ring

theorem card_coprime_sub_le (N : Nat) (hN : 1 <= N) :
    abs ((((Finset.product (Finset.Icc 1 N) (Finset.Icc 1 N)).filter
        (fun p : Prod Nat Nat => Nat.Coprime p.1 p.2)).card : Real) - 6 / Real.pi ^ 2 * N ^ 2) <=
      6 * N * (Real.log N + 1) := by
  let A : Real := ∑ d ∈ Finset.Icc 1 N, mur d * ((N / d : Nat) : Real) ^ 2
  let S : Real := ∑ d ∈ Finset.Icc 1 N, mur d / (d : Real) ^ 2
  let C : Real := 6 / Real.pi ^ 2
  have hfloor : |A - (N : Real) ^ 2 * S| ≤ 2 * N * (harmonic N : Real) := by
    simpa [A, S] using abs_coprime_floor_sum_sub_le N
  have hpartial : |S - C| ≤ 1 / (N : Real) := by
    simpa [S, C] using abs_partial_mur_sub_le N hN
  have hmain : |(N : Real) ^ 2 * S - C * N ^ 2| ≤ (N : Real) := by
    rw [show (N : Real) ^ 2 * S - C * N ^ 2 = (N : Real) ^ 2 * (S - C) by ring]
    rw [abs_mul, abs_of_nonneg (sq_nonneg (N : Real))]
    calc
      (N : Real) ^ 2 * |S - C| ≤ (N : Real) ^ 2 * (1 / (N : Real)) :=
        mul_le_mul_of_nonneg_left hpartial (sq_nonneg _)
      _ = (N : Real) := by
        have hNr : (N : Real) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
        field_simp
  have hcount :
      (((Finset.product (Finset.Icc 1 N) (Finset.Icc 1 N)).filter
        (fun p : Prod Nat Nat => Nat.Coprime p.1 p.2)).card : Real) = A := by
    simpa [A] using card_coprime_eq_mur_floor_sum N
  have hlog : 0 ≤ Real.log (N : Real) := Real.log_nonneg (by exact_mod_cast hN)
  have hharm : (harmonic N : Real) ≤ Real.log N + 1 := by
    simpa [add_comm] using harmonic_le_one_add_log N
  rw [hcount]
  change |A - C * (N : Real) ^ 2| ≤ _
  calc
    |A - C * (N : Real) ^ 2| =
        |(A - (N : Real) ^ 2 * S) + ((N : Real) ^ 2 * S - C * N ^ 2)| := by ring_nf
    _ ≤ |A - (N : Real) ^ 2 * S| + |(N : Real) ^ 2 * S - C * N ^ 2| :=
      abs_add_le _ _
    _ ≤ 2 * N * (harmonic N : Real) + N := add_le_add hfloor hmain
    _ ≤ 2 * N * (Real.log N + 1) + N := by
      gcongr
    _ ≤ 6 * N * (Real.log N + 1) := by
      have hNr : (0 : Real) ≤ N := Nat.cast_nonneg N
      nlinarith

theorem sum_totient_sub_le (N : Nat) (hN : 1 <= N) :
    abs ((Finset.Icc 1 N).sum (fun n => (Nat.totient n : Real)) - 3 / Real.pi ^ 2 * N ^ 2) <=
      4 * N * (Real.log N + 1) := by
  let A : Real := ∑ d ∈ Finset.Icc 1 N, mur d *
    (((N / d : Nat) : Real) * ((N / d : Nat) + 1) / 2)
  let S : Real := ∑ d ∈ Finset.Icc 1 N, mur d / (d : Real) ^ 2
  let C : Real := 6 / Real.pi ^ 2
  have hfloor : |A - ((N : Real) ^ 2 / 2) * S| ≤
      (3 / 2 : Real) * N * (harmonic N : Real) := by
    simpa [A, S] using abs_totient_triangle_sum_sub_le N
  have hpartial : |S - C| ≤ 1 / (N : Real) := by
    simpa [S, C] using abs_partial_mur_sub_le N hN
  have hmain : |((N : Real) ^ 2 / 2) * S - (C / 2) * N ^ 2| ≤ (N : Real) / 2 := by
    rw [show ((N : Real) ^ 2 / 2) * S - (C / 2) * N ^ 2 =
        ((N : Real) ^ 2 / 2) * (S - C) by ring]
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (N : Real) ^ 2 / 2)]
    calc
      ((N : Real) ^ 2 / 2) * |S - C| ≤
          ((N : Real) ^ 2 / 2) * (1 / (N : Real)) :=
        mul_le_mul_of_nonneg_left hpartial (by positivity)
      _ = (N : Real) / 2 := by
        have hNr : (N : Real) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
        field_simp
  have hsum :
      (Finset.Icc 1 N).sum (fun n => (Nat.totient n : Real)) = A := by
    simpa [A] using sum_totient_eq_mur_triangle_sum N
  have hcoef : (3 / Real.pi ^ 2 : Real) = C / 2 := by
    dsimp [C]
    ring
  have hlog : 0 ≤ Real.log (N : Real) := Real.log_nonneg (by exact_mod_cast hN)
  have hharm : (harmonic N : Real) ≤ Real.log N + 1 := by
    simpa [add_comm] using harmonic_le_one_add_log N
  rw [hsum, hcoef]
  change |A - (C / 2) * (N : Real) ^ 2| ≤ _
  calc
    |A - (C / 2) * (N : Real) ^ 2| =
        |(A - ((N : Real) ^ 2 / 2) * S) +
          (((N : Real) ^ 2 / 2) * S - (C / 2) * N ^ 2)| := by ring_nf
    _ ≤ |A - ((N : Real) ^ 2 / 2) * S| +
        |((N : Real) ^ 2 / 2) * S - (C / 2) * N ^ 2| := abs_add_le _ _
    _ ≤ (3 / 2 : Real) * N * (harmonic N : Real) + N / 2 :=
      add_le_add hfloor hmain
    _ ≤ (3 / 2 : Real) * N * (Real.log N + 1) + N / 2 := by
      gcongr
    _ ≤ 4 * N * (Real.log N + 1) := by
      have hNr : (0 : Real) ≤ N := Nat.cast_nonneg N
      nlinarith

theorem sum_totient_div_sub_le (N : Nat) (hN : 1 <= N) :
    abs ((Finset.Icc 1 N).sum (fun n => (Nat.totient n : Real) / n) - 6 / Real.pi ^ 2 * N) <=
      Real.log N + 2 := by
  let A : Real := ∑ d ∈ Finset.Icc 1 N, mur d / (d : Real) * (N / d : Nat)
  let S : Real := ∑ d ∈ Finset.Icc 1 N, mur d / (d : Real) ^ 2
  let C : Real := 6 / Real.pi ^ 2
  have hfloor : |A - (N : Real) * S| ≤ (harmonic N : Real) := by
    simpa [A, S] using abs_totient_div_floor_sum_sub_le N
  have hpartial : |S - C| ≤ 1 / (N : Real) := by
    simpa [S, C] using abs_partial_mur_sub_le N hN
  have hmain : |(N : Real) * S - C * N| ≤ 1 := by
    rw [show (N : Real) * S - C * N = (N : Real) * (S - C) by ring]
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    calc
      (N : Real) * |S - C| ≤ (N : Real) * (1 / (N : Real)) :=
        mul_le_mul_of_nonneg_left hpartial (Nat.cast_nonneg N)
      _ = 1 := by
        have hNr : (N : Real) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
        field_simp
  have hsum :
      (Finset.Icc 1 N).sum (fun n => (Nat.totient n : Real) / n) = A := by
    simpa [A] using sum_totient_div_eq_mur_floor_sum N
  have hharm : (harmonic N : Real) ≤ Real.log N + 1 := by
    simpa [add_comm] using harmonic_le_one_add_log N
  rw [hsum]
  change |A - C * (N : Real)| ≤ _
  calc
    |A - C * (N : Real)| = |(A - (N : Real) * S) + ((N : Real) * S - C * N)| := by
      ring_nf
    _ ≤ |A - (N : Real) * S| + |(N : Real) * S - C * N| := abs_add_le _ _
    _ ≤ (harmonic N : Real) + 1 := add_le_add hfloor hmain
    _ ≤ Real.log N + 2 := by linarith

theorem tendsto_card_squarefree_div :
    Filter.Tendsto (fun N : Nat => (((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card :
        Real) / N) Filter.atTop (nhds (6 / Real.pi ^ 2)) := by
  let C : Real := 6 / Real.pi ^ 2
  have hsqrt : Filter.Tendsto (fun N : Nat => Real.sqrt (N : Real))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Filter.Tendsto (fun N : Nat => (Real.sqrt (N : Real))⁻¹)
      Filter.atTop (nhds 0) := tendsto_inv_atTop_zero.comp hsqrt
  have herr : Filter.Tendsto (fun N : Nat => 3 * (Real.sqrt (N : Real))⁻¹)
      Filter.atTop (nhds 0) := by
    simpa using hinv.const_mul (3 : Real)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hevent : ∀ᶠ N : Nat in Filter.atTop,
      3 * (Real.sqrt (N : Real))⁻¹ < ε :=
    (tendsto_order.1 herr).2 ε hε
  have hboth : ∀ᶠ N : Nat in Filter.atTop,
      3 * (Real.sqrt (N : Real))⁻¹ < ε ∧ 1 ≤ N :=
    hevent.and (Filter.eventually_ge_atTop 1)
  rcases (Filter.eventually_atTop.1 hboth) with ⟨M, hM⟩
  refine ⟨M, fun N hNM => ?_⟩
  rcases hM N hNM with ⟨herror, hN⟩
  rw [Real.dist_eq]
  have hNr : (0 : Real) < N := by exact_mod_cast hN
  have hbound := card_squarefree_sub_le N hN
  have heq :
      (((((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : Real) / N) - C) =
        (((((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : Real) - C * N) / N) := by
    field_simp
  rw [heq, abs_div, abs_of_pos hNr]
  calc
    |(((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : Real) - C * N| /
        (N : Real) ≤ (3 * Real.sqrt N) / N :=
      div_le_div_of_nonneg_right (by simpa [C] using hbound) hNr.le
    _ = 3 * (Real.sqrt (N : Real))⁻¹ := by
      rw [mul_div_assoc, Real.sqrt_div_self]
    _ < ε := herror

end TuringTask
