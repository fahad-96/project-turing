import Mathlib

open scoped BigOperators

noncomputable section

def mur (n : Nat) : Real := ArithmeticFunction.moebius n

lemma squarefree_iff_floorRoot_two_eq_one {n : Nat} (_hn : n ≠ 0) :
    Squarefree n ↔ Nat.floorRoot 2 n = 1 := by
  constructor
  · intro hs
    have hu : IsUnit (Nat.floorRoot 2 n) := hs _ (by
      simpa [pow_two] using (Nat.floorRoot_pow_dvd (a := n) (n := 2)))
    simpa [Nat.isUnit_iff] using hu
  · intro hr d hd
    have hdiv : d ∣ Nat.floorRoot 2 n := Nat.pow_dvd_iff_dvd_floorRoot.mp (by
      simpa [pow_two] using hd)
    rw [hr] at hdiv
    simpa [Nat.isUnit_iff] using hdiv

lemma sum_moebius_divisors (k : Nat) (hk : k ≠ 0) :
    (∑ d ∈ k.divisors, ArithmeticFunction.moebius d) = if k = 1 then 1 else 0 := by
  have h := DFunLike.congr_fun ArithmeticFunction.moebius_mul_coe_zeta k
  rw [ArithmeticFunction.mul_apply] at h
  calc
    (∑ d ∈ k.divisors, ArithmeticFunction.moebius d) =
        ∑ d ∈ k.divisors,
          ArithmeticFunction.moebius d * (ArithmeticFunction.zeta (k / d) : Int) := by
            apply Finset.sum_congr rfl
            intro d hd
            have hdiv := (Nat.mem_divisors.mp hd).1
            have hpos := Nat.pos_of_dvd_of_pos hdiv (Nat.pos_of_ne_zero hk)
            have hdk : d ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero hk) hdiv
            have hq : k / d ≠ 0 := Nat.ne_of_gt (Nat.div_pos hdk hpos)
            simp [ArithmeticFunction.zeta_apply, hq]
    _ = ∑ x ∈ k.divisorsAntidiagonal,
          ArithmeticFunction.moebius x.1 * (ArithmeticFunction.zeta x.2 : Int) := by
            symm
            exact Nat.sum_divisorsAntidiagonal
              (fun a b => ArithmeticFunction.moebius a * (ArithmeticFunction.zeta b : Int))
    _ = if k = 1 then 1 else 0 := by
      simpa [ArithmeticFunction.one_apply] using h

lemma sum_moebius_square_dvd (N n : Nat) (hn : n ∈ Finset.Icc 1 N) :
    (∑ d ∈ Finset.Icc 1 N.sqrt,
        if d ^ 2 ∣ n then ArithmeticFunction.moebius d else 0) =
      if Squarefree n then 1 else 0 := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
  have hn0 : n ≠ 0 := by omega
  let k := Nat.floorRoot 2 n
  have hk0 : k ≠ 0 := (Nat.floorRoot_ne_zero.mpr (by omega))
  have hsets : (Finset.Icc 1 N.sqrt).filter (fun d => d ^ 2 ∣ n) = k.divisors := by
    ext d
    rw [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · intro hd
      rcases hd with ⟨⟨_, _⟩, hd⟩
      exact ⟨by simpa [k] using Nat.pow_dvd_iff_dvd_floorRoot.mp hd, hk0⟩
    · rintro ⟨hd, _⟩
      have hpow : d ^ 2 ∣ n := Nat.pow_dvd_iff_dvd_floorRoot.mpr (by simpa [k] using hd)
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hk0)
      have hpowle : d * d ≤ n := Nat.le_of_dvd (by omega) (by simpa [pow_two] using hpow)
      have hdroot : d ≤ N.sqrt := Nat.le_sqrt.mpr (hpowle.trans hnN)
      exact ⟨⟨hdpos, hdroot⟩, hpow⟩
  rw [← Finset.sum_filter, hsets, sum_moebius_divisors k hk0]
  simp only [squarefree_iff_floorRoot_two_eq_one hn0]
  rfl

lemma card_multiples_in_Icc (N q : Nat) :
    ((Finset.Icc 1 N).filter (fun n => q ∣ n)).card = N / q := by
  have hinterval : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hinterval]
  exact Nat.Ioc_filter_dvd_card_eq_div N q

lemma card_squarefree_eq_sum (N : Nat) :
    (((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : Int) =
      ∑ d ∈ Finset.Icc 1 N.sqrt,
        ArithmeticFunction.moebius d * (N / d ^ 2 : Nat) := by
  calc
    (((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : Int) =
        ∑ n ∈ Finset.Icc 1 N, if Squarefree n then 1 else 0 := by simp
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N.sqrt,
          if d ^ 2 ∣ n then ArithmeticFunction.moebius d else 0 := by
            apply Finset.sum_congr rfl
            intro n hn
            symm
            exact sum_moebius_square_dvd N n hn
    _ = ∑ d ∈ Finset.Icc 1 N.sqrt, ∑ n ∈ Finset.Icc 1 N,
          if d ^ 2 ∣ n then ArithmeticFunction.moebius d else 0 := by
            exact Finset.sum_comm
    _ = ∑ d ∈ Finset.Icc 1 N.sqrt,
          ArithmeticFunction.moebius d * (N / d ^ 2 : Nat) := by
            apply Finset.sum_congr rfl
            intro d _
            rw [← Finset.sum_filter]
            simp [card_multiples_in_Icc]
            rw [mul_comm]

lemma summable_one_div_nat_sq : Summable (fun n : Nat => 1 / (n : Real) ^ 2) :=
  (Real.summable_one_div_nat_pow).2 (by norm_num)

lemma tsum_one_div_nat_add_sq_le (K : Nat) (hK : 1 ≤ K) :
    (∑' n : Nat, 1 / ((n + K + 1 : Nat) : Real) ^ 2) ≤ 1 / (K : Real) := by
  let g : Nat → Real := fun n =>
    1 / ((n + K : Nat) : Real) - 1 / ((n + K + 1 : Nat) : Real)
  have hshift : Summable (fun n : Nat => 1 / ((n + K : Nat) : Real) ^ 2) := by
    simpa [Nat.cast_add] using
      (summable_nat_add_iff K).2 summable_one_div_nat_sq
  have hg_nonneg : ∀ n, 0 ≤ g n := by
    intro n
    dsimp [g]
    have ha : 0 < ((n + K : Nat) : Real) := by positivity
    have hb : 0 < ((n + K + 1 : Nat) : Real) := by positivity
    field_simp
    norm_num
  have hg_le : ∀ n, g n ≤ 1 / ((n + K : Nat) : Real) ^ 2 := by
    intro n
    dsimp [g]
    have ha : 0 < ((n + K : Nat) : Real) := by positivity
    have hb : 0 < ((n + K + 1 : Nat) : Real) := by positivity
    have hab : ((n + K + 1 : Nat) : Real) = (n + K : Nat) + 1 := by
      push_cast
      ring
    field_simp
    nlinarith [hab]
  have hg : Summable g := Summable.of_nonneg_of_le hg_nonneg hg_le hshift
  have hden : Filter.Tendsto (fun n : Nat => (K : Real) + n)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_left Filter.atTop (K : Real)
      tendsto_natCast_atTop_atTop
  have hinv : Filter.Tendsto (fun n : Nat => ((K : Real) + n)⁻¹)
      Filter.atTop (nhds 0) := tendsto_inv_atTop_zero.comp hden
  have hgsum : HasSum g (1 / (K : Real)) := by
    apply hg.hasSum_iff_tendsto_nat.mpr
    have ht : Filter.Tendsto
        (fun n : Nat => 1 / (K : Real) - (((K : Real) + n)⁻¹))
        Filter.atTop (nhds (1 / (K : Real))) := by
      simpa using (tendsto_const_nhds.sub hinv)
    convert ht using 1
    · funext m
      simpa [g, Nat.cast_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Finset.sum_range_sub' (fun i : Nat => 1 / (((i + K : Nat) : Real))) m)
  have hf : Summable (fun n : Nat => 1 / ((n + K + 1 : Nat) : Real) ^ 2) := by
    simpa [Nat.add_assoc, Nat.cast_add] using
      (summable_nat_add_iff (K + 1)).2 summable_one_div_nat_sq
  have hfg : ∀ n : Nat,
      1 / ((n + K + 1 : Nat) : Real) ^ 2 ≤ g n := by
    intro n
    dsimp [g]
    have ha : 0 < ((n + K : Nat) : Real) := by positivity
    have hb : 0 < ((n + K + 1 : Nat) : Real) := by positivity
    have hab : ((n + K + 1 : Nat) : Real) = (n + K : Nat) + 1 := by
      push_cast
      ring
    field_simp
    nlinarith [hab]
  calc
    (∑' n : Nat, 1 / ((n + K + 1 : Nat) : Real) ^ 2) ≤ ∑' n, g n :=
      Summable.tsum_le_tsum hfg hf hg
    _ = 1 / (K : Real) := hgsum.tsum_eq

lemma mur_abs_le_one (n : Nat) : |mur n| ≤ 1 := by
  change |(ArithmeticFunction.moebius n : Real)| ≤ 1
  rw [← Int.cast_abs]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

lemma summable_mur_div_sq : Summable (fun n : Nat => mur n / (n : Real) ^ 2) := by
  apply Summable.of_norm_bounded summable_one_div_nat_sq
  intro n
  have hnabs : |(n : Real)| = (n : Real) := abs_of_nonneg (Nat.cast_nonneg n)
  calc
    ‖mur n / (n : Real) ^ 2‖ = |mur n| / (n : Real) ^ 2 := by
      rw [Real.norm_eq_abs, abs_div, abs_pow, hnabs]
    _ ≤ 1 / (n : Real) ^ 2 :=
      div_le_div_of_nonneg_right (mur_abs_le_one n) (sq_nonneg _)

lemma lseries_moebius_two :
    LSeries (fun n => (ArithmeticFunction.moebius n : Complex)) 2 =
      (6 / Real.pi ^ 2 : Real) := by
  have hprod := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius
    (s := (2 : Complex)) (by norm_num)
  have hz : LSeries (fun n => (ArithmeticFunction.zeta n : Complex)) 2 =
      (Real.pi ^ 2 / 6 : Real) := by
    rw [LSeries]
    have hc := Complex.ofRealCLM.hasSum hasSum_zeta_two
    have hc' : HasSum (LSeries.term (fun n =>
        (ArithmeticFunction.zeta n : Complex)) 2)
        ((Real.pi ^ 2 / 6 : Real) : Complex) := by
      apply Filter.Tendsto.congr (fun s => ?_) hc
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : n = 0
      · simp [hn, LSeries.term]
      · simp [hn, LSeries.term]
    exact hc'.tsum_eq
  rw [hz] at hprod
  apply (mul_left_cancel₀ (show ((Real.pi ^ 2 / 6 : Real) : Complex) ≠ 0 by
    exact_mod_cast div_ne_zero (pow_ne_zero 2 Real.pi_ne_zero)
      (by norm_num : (6 : Real) ≠ 0)))
  rw [hprod]
  push_cast
  field_simp

lemma hasSum_mur_div_sq :
    HasSum (fun n : Nat => mur n / (n : Real) ^ 2) (6 / Real.pi ^ 2) := by
  have htsum : (∑' n : Nat, mur n / (n : Real) ^ 2) = 6 / Real.pi ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_tsum]
    calc
      ∑' (n : Nat), ((mur n / (n : Real) ^ 2 : Real) : Complex) =
          LSeries (fun n => (ArithmeticFunction.moebius n : Complex)) 2 := by
            rw [LSeries]
            congr 1
            funext n
            by_cases hn : n = 0
            · simp [hn, mur, LSeries.term]
            · simp [hn, mur, LSeries.term]
      _ = ((6 / Real.pi ^ 2 : Real) : Complex) := lseries_moebius_two
  rw [← htsum]
  exact summable_mur_div_sq.hasSum

lemma abs_mur_tail_le (K : Nat) (hK : 1 ≤ K) :
    |∑' n : Nat, mur (n + K + 1) / ((n + K + 1 : Nat) : Real) ^ 2| ≤
      1 / (K : Real) := by
  have hmajor : Summable (fun n : Nat =>
      1 / ((n + K + 1 : Nat) : Real) ^ 2) := by
    simpa [Nat.add_assoc, Nat.cast_add] using
      (summable_nat_add_iff (K + 1)).2 summable_one_div_nat_sq
  have hnorm : Summable (fun n : Nat =>
      ‖mur (n + K + 1) / ((n + K + 1 : Nat) : Real) ^ 2‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hmajor
    intro n
    have hn : 0 ≤ (((n + K + 1 : Nat) : Real) ^ 2) := sq_nonneg _
    have hnabs : |((n + K + 1 : Nat) : Real)| = (n + K + 1 : Nat) :=
      abs_of_nonneg (Nat.cast_nonneg _)
    calc
      ‖mur (n + K + 1) / ((n + K + 1 : Nat) : Real) ^ 2‖ =
          |mur (n + K + 1)| / ((n + K + 1 : Nat) : Real) ^ 2 := by
            rw [Real.norm_eq_abs, abs_div, abs_pow, hnabs]
      _ ≤ 1 / ((n + K + 1 : Nat) : Real) ^ 2 :=
        div_le_div_of_nonneg_right (mur_abs_le_one _) hn
  calc
    |∑' n : Nat, mur (n + K + 1) / ((n + K + 1 : Nat) : Real) ^ 2| =
        ‖∑' n : Nat, mur (n + K + 1) / ((n + K + 1 : Nat) : Real) ^ 2‖ :=
          (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : Nat,
        ‖mur (n + K + 1) / ((n + K + 1 : Nat) : Real) ^ 2‖ :=
          norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : Nat, 1 / ((n + K + 1 : Nat) : Real) ^ 2 := by
      apply Summable.tsum_le_tsum _ hnorm hmajor
      intro n
      have hn : 0 ≤ (((n + K + 1 : Nat) : Real) ^ 2) := sq_nonneg _
      have hnabs : |((n + K + 1 : Nat) : Real)| = (n + K + 1 : Nat) :=
        abs_of_nonneg (Nat.cast_nonneg _)
      calc
        ‖mur (n + K + 1) / ((n + K + 1 : Nat) : Real) ^ 2‖ =
            |mur (n + K + 1)| / ((n + K + 1 : Nat) : Real) ^ 2 := by
              rw [Real.norm_eq_abs, abs_div, abs_pow, hnabs]
        _ ≤ 1 / ((n + K + 1 : Nat) : Real) ^ 2 :=
          div_le_div_of_nonneg_right (mur_abs_le_one _) hn
    _ ≤ 1 / (K : Real) := tsum_one_div_nat_add_sq_le K hK

lemma abs_partial_mur_sub_le (K : Nat) (hK : 1 ≤ K) :
    |(∑ d ∈ Finset.Icc 1 K, mur d / (d : Real) ^ 2) - 6 / Real.pi ^ 2| ≤
      1 / (K : Real) := by
  let f : Nat → Real := fun n => mur n / (n : Real) ^ 2
  have hset : Finset.Icc 1 K = Finset.Ico 1 (K + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hfinite : (∑ n ∈ Finset.range (K + 1), f n) =
      ∑ n ∈ Finset.Icc 1 K, f n := by
    rw [hset, Finset.sum_Ico_eq_sub f (by omega)]
    simp [f, mur]
  have hsplit := summable_mur_div_sq.sum_add_tsum_nat_add (K + 1)
  have heq : (∑ d ∈ Finset.Icc 1 K, f d) +
      (∑' n : Nat, f (n + K + 1)) = 6 / Real.pi ^ 2 := by
    rw [← hfinite]
    calc
      (∑ n ∈ Finset.range (K + 1), f n) + ∑' n : Nat, f (n + K + 1) =
          ∑' n : Nat, f n := by
            simpa [f, Nat.add_assoc] using hsplit
      _ = 6 / Real.pi ^ 2 := hasSum_mur_div_sq.tsum_eq
  rw [show (∑ d ∈ Finset.Icc 1 K, mur d / (d : Real) ^ 2) -
      6 / Real.pi ^ 2 = -(∑' n : Nat,
        mur (n + K + 1) / ((n + K + 1 : Nat) : Real) ^ 2) by
      change (∑ d ∈ Finset.Icc 1 K, f d) - 6 / Real.pi ^ 2 =
        -(∑' n : Nat, f (n + K + 1))
      linarith]
  rw [abs_neg]
  exact abs_mur_tail_le K hK

lemma abs_nat_div_sq_cast_sub_le_one (N d : Nat) :
    |((N / d ^ 2 : Nat) : Real) - (N : Real) / (d : Real) ^ 2| ≤ 1 := by
  have h := Nat.abs_floor_sub_le
    (a := (N : Real) / ((d ^ 2 : Nat) : Real)) (by positivity)
  rw [Nat.floor_div_natCast] at h
  simpa [Nat.cast_pow] using h

lemma abs_floor_sum_sub_le (N K : Nat) :
    |(∑ d ∈ Finset.Icc 1 K, mur d * ((N / d ^ 2 : Nat) : Real)) -
        (N : Real) * ∑ d ∈ Finset.Icc 1 K, mur d / (d : Real) ^ 2| ≤ K := by
  have heq :
      (∑ d ∈ Finset.Icc 1 K, mur d * ((N / d ^ 2 : Nat) : Real)) -
          (N : Real) * ∑ d ∈ Finset.Icc 1 K, mur d / (d : Real) ^ 2 =
        ∑ d ∈ Finset.Icc 1 K,
          mur d * (((N / d ^ 2 : Nat) : Real) - (N : Real) / (d : Real) ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [heq]
  calc
    |∑ d ∈ Finset.Icc 1 K,
        mur d * (((N / d ^ 2 : Nat) : Real) - (N : Real) / (d : Real) ^ 2)| ≤
        ∑ d ∈ Finset.Icc 1 K,
          |mur d * (((N / d ^ 2 : Nat) : Real) - (N : Real) / (d : Real) ^ 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Finset.Icc 1 K, (1 : Real) := by
      apply Finset.sum_le_sum
      intro d _
      rw [abs_mul]
      calc
        |mur d| * |((N / d ^ 2 : Nat) : Real) - (N : Real) / (d : Real) ^ 2| ≤
            1 * 1 := mul_le_mul (mur_abs_le_one d)
              (abs_nat_div_sq_cast_sub_le_one N d) (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    _ = K := by simp

lemma card_squarefree_eq_sum_real (N : Nat) :
    (((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : Real) =
      ∑ d ∈ Finset.Icc 1 N.sqrt,
        mur d * ((N / d ^ 2 : Nat) : Real) := by
  unfold mur
  have h := congrArg (fun z : Int => (z : Real)) (card_squarefree_eq_sum N)
  push_cast at h
  exact h

lemma div_nat_sqrt_le_two_sqrt (N : Nat) (hN : 1 ≤ N) :
    (N : Real) / (N.sqrt : Real) ≤ 2 * Real.sqrt N := by
  have hK : 1 ≤ N.sqrt := Nat.le_sqrt.mpr (by simpa using hN)
  have hKr : (1 : Real) ≤ (N.sqrt : Real) := by exact_mod_cast hK
  have hKpos : (0 : Real) < N.sqrt := lt_of_lt_of_le zero_lt_one hKr
  have hsqrt0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hsqrtlt : Real.sqrt N < (N.sqrt : Real) + 1 :=
    Real.real_sqrt_lt_nat_sqrt_succ
  have hsqrtle : Real.sqrt N ≤ 2 * (N.sqrt : Real) := by linarith
  apply (div_le_iff₀ hKpos).2
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg N)]
