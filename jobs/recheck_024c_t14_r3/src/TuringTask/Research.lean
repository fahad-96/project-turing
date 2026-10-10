import Mathlib

namespace TuringTask.Research

open scoped BigOperators

/-- Positive lattice points below the hyperbola `a * b = N`. -/
def latticePoints (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter fun p => p.1 * p.2 ≤ N

lemma biUnion_divisorsAntidiagonal (N : ℕ) :
    (Finset.Icc 1 N).biUnion Nat.divisorsAntidiagonal = latticePoints N := by
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal,
    latticePoints, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨n, ⟨hn1, hnN⟩, hprod, hn0⟩
    subst n
    have hp1 : 1 ≤ p.1 := by
      by_contra h
      have : p.1 = 0 := by omega
      simp [this] at hn0
    have hp2 : 1 ≤ p.2 := by
      by_contra h
      have : p.2 = 0 := by omega
      simp [this] at hn0
    have hp1prod : p.1 ≤ p.1 * p.2 := by
      simpa using Nat.mul_le_mul_left p.1 hp2
    have hp2prod : p.2 ≤ p.1 * p.2 := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left p.2 hp1
    exact ⟨⟨⟨hp1, hp1prod.trans hnN⟩, ⟨hp2, hp2prod.trans hnN⟩⟩, hnN⟩
  · rintro ⟨⟨⟨hp1, hpN1⟩, ⟨hp2, hpN2⟩⟩, hpN⟩
    refine ⟨p.1 * p.2, ⟨Nat.mul_pos hp1 hp2, hpN⟩, rfl, ?_⟩
    exact Nat.ne_of_gt (Nat.mul_pos hp1 hp2)

lemma pairwiseDisjoint_divisorsAntidiagonal (N : ℕ) :
    ((Finset.Icc 1 N : Finset ℕ) : Set ℕ).PairwiseDisjoint Nat.divisorsAntidiagonal := by
  intro m hm n hn hmn
  change Disjoint (Nat.divisorsAntidiagonal m) (Nat.divisorsAntidiagonal n)
  rw [Finset.disjoint_left]
  intro p hpm hpn
  have hm' := (Nat.mem_divisorsAntidiagonal.mp hpm).1
  have hn' := (Nat.mem_divisorsAntidiagonal.mp hpn).1
  exact hmn (hm'.symm.trans hn')

/-- Finite Dirichlet convolution is a sum over positive lattice points. -/
lemma sum_divisors_eq_sum_lattice {M : Type*} [AddCommMonoid M]
    (N : ℕ) (f : ℕ → ℕ → M) :
    (Finset.Icc 1 N).sum (fun n => n.divisors.sum fun d => f d (n / d)) =
      (latticePoints N).sum fun p => f p.1 p.2 := by
  rw [← biUnion_divisorsAntidiagonal N,
    Finset.sum_biUnion (pairwiseDisjoint_divisorsAntidiagonal N)]
  apply Finset.sum_congr rfl
  intro n hn
  exact (Nat.sum_divisorsAntidiagonal f).symm

/-- Slice the finite hyperbola region by its first coordinate. -/
lemma sum_lattice_eq_sum_div {M : Type*} [AddCommMonoid M]
    (N : ℕ) (f : ℕ → ℕ → M) :
    (latticePoints N).sum (fun p => f p.1 p.2) =
      (Finset.Icc 1 N).sum (fun a =>
        (Finset.Icc 1 (N / a)).sum fun b => f a b) := by
  rw [latticePoints, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
  rw [← Finset.sum_filter]
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hb1, hbN⟩, hab⟩
    exact ⟨hb1, (Nat.le_div_iff_mul_le (by omega : 0 < a)).2 (by simpa [Nat.mul_comm] using hab)⟩
  · rintro ⟨hb1, hbdiv⟩
    have hab : a * b ≤ N := by
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le (by omega : 0 < a)).1 hbdiv
    have hbN : b ≤ N := (Nat.le_trans (by
      rw [Nat.mul_comm]
      simpa using Nat.mul_le_mul_left b ha1) hab)
    exact ⟨⟨hb1, hbN⟩, hab⟩

lemma card_divisors_eq_sum_antidiagonal (n : ℕ) :
    (n.divisors.card : ℝ) = n.divisorsAntidiagonal.sum (fun _ => (1 : ℝ)) := by
  simpa using
    (Nat.sum_divisorsAntidiagonal (M := ℝ) (fun _ _ => (1 : ℝ)) (n := n)).symm

/-- Exact lattice-point interpretation of the first summatory function. -/
lemma sum_card_divisors_eq_card_lattice (N : ℕ) :
    (Finset.Icc 1 N).sum (fun n => (n.divisors.card : ℝ)) =
      ((latticePoints N).card : ℝ) := by
  calc
    (Finset.Icc 1 N).sum (fun n => (n.divisors.card : ℝ)) =
        (Finset.Icc 1 N).sum
          (fun n => n.divisorsAntidiagonal.sum (fun _ => (1 : ℝ))) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact card_divisors_eq_sum_antidiagonal n
    _ = (latticePoints N).sum (fun _ => (1 : ℝ)) := by
      rw [← biUnion_divisorsAntidiagonal N,
        Finset.sum_biUnion (pairwiseDisjoint_divisorsAntidiagonal N)]
    _ = ((latticePoints N).card : ℝ) := by simp

/-- The elementary full-range floor-sum identity for the divisor summatory function. -/
lemma sum_card_divisors_eq_sum_div (N : ℕ) :
    (Finset.Icc 1 N).sum (fun n => (n.divisors.card : ℝ)) =
      (Finset.Icc 1 N).sum (fun a => ((N / a : ℕ) : ℝ)) := by
  calc
    (Finset.Icc 1 N).sum (fun n => (n.divisors.card : ℝ)) =
        (latticePoints N).sum (fun _ => (1 : ℝ)) := by
          rw [sum_card_divisors_eq_card_lattice]
          simp
    _ = (Finset.Icc 1 N).sum (fun a =>
        (Finset.Icc 1 (N / a)).sum fun _ => (1 : ℝ)) :=
      sum_lattice_eq_sum_div N (fun _ _ => (1 : ℝ))
    _ = (Finset.Icc 1 N).sum (fun a => ((N / a : ℕ) : ℝ)) := by simp

/-- Exact lattice-point interpretation of the reciprocal-weighted sum. -/
lemma sum_card_divisors_div_eq_sum_lattice (N : ℕ) :
    (Finset.Icc 1 N).sum (fun n => (n.divisors.card : ℝ) / n) =
      (latticePoints N).sum (fun p => (1 : ℝ) / (p.1 * p.2)) := by
  calc
    (Finset.Icc 1 N).sum (fun n => (n.divisors.card : ℝ) / n) =
        (Finset.Icc 1 N).sum (fun n => n.divisors.sum
          (fun d => (1 : ℝ) / ((d * (n / d) : ℕ) : ℝ))) := by
            apply Finset.sum_congr rfl
            intro n hn
            calc
              (n.divisors.card : ℝ) / n =
                  n.divisors.sum (fun _ => (1 : ℝ) / n) := by
                    simp [div_eq_mul_inv, mul_comm]
              _ = n.divisors.sum
                  (fun d => (1 : ℝ) / ((d * (n / d) : ℕ) : ℝ)) := by
                apply Finset.sum_congr rfl
                intro d hd
                rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
    _ = (latticePoints N).sum (fun p => (1 : ℝ) / (p.1 * p.2)) := by
      simpa [Nat.cast_mul] using
        (sum_divisors_eq_sum_lattice N (fun a b => (1 : ℝ) / ((a * b : ℕ) : ℝ)))

lemma harmonic_real_eq_sum_Icc (n : ℕ) :
    (harmonic n : ℝ) = (Finset.Icc 1 n).sum (fun i => (1 : ℝ) / i) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  simp [div_eq_mul_inv]

/-- The exact harmonic convolution behind the reciprocal-weighted theorem. -/
lemma sum_card_divisors_div_eq_harmonic_sum (N : ℕ) :
    (Finset.Icc 1 N).sum (fun n => (n.divisors.card : ℝ) / n) =
      (Finset.Icc 1 N).sum (fun a => (harmonic (N / a) : ℝ) / a) := by
  calc
    (Finset.Icc 1 N).sum (fun n => (n.divisors.card : ℝ) / n) =
        (latticePoints N).sum (fun p => (1 : ℝ) / (p.1 * p.2)) :=
      sum_card_divisors_div_eq_sum_lattice N
    _ = (Finset.Icc 1 N).sum (fun a =>
        (Finset.Icc 1 (N / a)).sum fun b => (1 : ℝ) / (a * b)) :=
      sum_lattice_eq_sum_div N (fun a b => (1 : ℝ) / (a * b))
    _ = (Finset.Icc 1 N).sum (fun a => (harmonic (N / a) : ℝ) / a) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [harmonic_real_eq_sum_Icc]
      simp only [div_eq_mul_inv, mul_inv_rev, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      ac_rfl

/-- The two standard Euler--Mascheroni approximants give a sharp interval. -/
lemma harmonic_sub_log_bounds (n : ℕ) (hn : 1 ≤ n) :
    (harmonic n : ℝ) - Real.log (n + 1) ≤ Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant ≤ (harmonic n : ℝ) - Real.log n := by
  constructor
  · exact (Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n).le
  · have h := (Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n).le
    simpa [Real.eulerMascheroniSeq'.eq_1, Nat.ne_of_gt hn] using h

lemma harmonic_error_nonneg (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant := by
  linarith [((harmonic_sub_log_bounds n hn).2)]

lemma harmonic_error_le_log_one_add_inv (n : ℕ) (hn : 1 ≤ n) :
    (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant ≤
      Real.log (1 + (n : ℝ)⁻¹) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hlog : Real.log (n + 1) - Real.log n = Real.log (1 + (n : ℝ)⁻¹) := by
    rw [← Real.log_div (by positivity : (n : ℝ) + 1 ≠ 0) hnR]
    congr 1
    field_simp
  linarith [((harmonic_sub_log_bounds n hn).1)]

lemma abs_harmonic_error_le_inv (n : ℕ) (hn : 1 ≤ n) :
    |(harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant| ≤ (n : ℝ)⁻¹ := by
  rw [abs_of_nonneg (harmonic_error_nonneg n hn)]
  calc
    (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant ≤
        Real.log (1 + (n : ℝ)⁻¹) := harmonic_error_le_log_one_add_inv n hn
    _ ≤ (n : ℝ)⁻¹ := by
      have hpos : 0 < 1 + (n : ℝ)⁻¹ := by positivity
      linarith [Real.log_le_sub_one_of_pos hpos]

end TuringTask.Research
