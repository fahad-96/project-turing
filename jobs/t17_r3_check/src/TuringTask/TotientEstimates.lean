import TuringTask.SquarefreeEstimates

open scoped BigOperators

noncomputable section

lemma sum_moebius_common_divisors (N a b : Nat)
    (ha : a ∈ Finset.Icc 1 N) (_hb : b ∈ Finset.Icc 1 N) :
    (∑ d ∈ Finset.Icc 1 N,
      if d ∣ a ∧ d ∣ b then ArithmeticFunction.moebius d else 0) =
        if Nat.Coprime a b then 1 else 0 := by
  let g := Nat.gcd a b
  have hg0 : g ≠ 0 := by
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    dsimp [g]
    intro h
    rw [Nat.gcd_eq_zero_iff] at h
    omega
  have hsets : (Finset.Icc 1 N).filter (fun d => d ∣ a ∧ d ∣ b) = g.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd1, _⟩, hda, hdb⟩
      exact ⟨Nat.dvd_gcd hda hdb, hg0⟩
    · rintro ⟨hdg, _⟩
      have hda : d ∣ a := dvd_trans hdg (Nat.gcd_dvd_left a b)
      have hdb : d ∣ b := dvd_trans hdg (Nat.gcd_dvd_right a b)
      have hdpos := Nat.pos_of_dvd_of_pos hdg (Nat.pos_of_ne_zero hg0)
      have hdN : d ≤ N :=
        (Nat.le_of_dvd (Finset.mem_Icc.mp ha).1 hda).trans (Finset.mem_Icc.mp ha).2
      exact ⟨⟨hdpos, hdN⟩, hda, hdb⟩
  rw [← Finset.sum_filter, hsets, sum_moebius_divisors g hg0]

lemma sum_mur_common_divisors (N a b : Nat)
    (ha : a ∈ Finset.Icc 1 N) (hb : b ∈ Finset.Icc 1 N) :
    (∑ d ∈ Finset.Icc 1 N, if d ∣ a ∧ d ∣ b then mur d else 0) =
      if Nat.Coprime a b then 1 else 0 := by
  unfold mur
  exact_mod_cast sum_moebius_common_divisors N a b ha hb

lemma sum_common_multiples (N d : Nat) :
    (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
      if d ∣ a ∧ d ∣ b then mur d else 0) =
        mur d * ((N / d : Nat) : Real) ^ 2 := by
  calc
    (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        if d ∣ a ∧ d ∣ b then mur d else 0) =
        ∑ a ∈ Finset.Icc 1 N,
          if d ∣ a then mur d * (N / d : Nat) else 0 := by
            apply Finset.sum_congr rfl
            intro a _
            by_cases hda : d ∣ a
            · simp only [hda, true_and, if_true]
              rw [← Finset.sum_filter]
              simp [card_multiples_in_Icc, mul_comm]
            · simp [hda]
    _ = ∑ a ∈ (Finset.Icc 1 N).filter (fun a => d ∣ a),
          mur d * (N / d : Nat) := by rw [Finset.sum_filter]
    _ = mur d * ((N / d : Nat) : Real) ^ 2 := by
      rw [Finset.sum_const, card_multiples_in_Icc]
      ring

lemma card_coprime_eq_mur_floor_sum (N : Nat) :
    (((Finset.product (Finset.Icc 1 N) (Finset.Icc 1 N)).filter
      (fun p : Prod Nat Nat => Nat.Coprime p.1 p.2)).card : Real) =
        ∑ d ∈ Finset.Icc 1 N, mur d * ((N / d : Nat) : Real) ^ 2 := by
  calc
    (((Finset.product (Finset.Icc 1 N) (Finset.Icc 1 N)).filter
        (fun p : Prod Nat Nat => Nat.Coprime p.1 p.2)).card : Real) =
        ∑ p ∈ Finset.product (Finset.Icc 1 N) (Finset.Icc 1 N),
          if Nat.Coprime p.1 p.2 then 1 else 0 := by simp
    _ = ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
          if Nat.Coprime a b then 1 else 0 := by
            simpa using (Finset.sum_product (Finset.Icc 1 N) (Finset.Icc 1 N)
              (fun p : Nat × Nat => if Nat.Coprime p.1 p.2 then (1 : Real) else 0))
    _ = ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
          ∑ d ∈ Finset.Icc 1 N, if d ∣ a ∧ d ∣ b then mur d else 0 := by
            apply Finset.sum_congr rfl
            intro a ha
            apply Finset.sum_congr rfl
            intro b hb
            symm
            exact sum_mur_common_divisors N a b ha hb
    _ = ∑ a ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N,
          ∑ b ∈ Finset.Icc 1 N, if d ∣ a ∧ d ∣ b then mur d else 0 := by
            apply Finset.sum_congr rfl
            intro a _
            exact Finset.sum_comm
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ a ∈ Finset.Icc 1 N,
          ∑ b ∈ Finset.Icc 1 N, if d ∣ a ∧ d ∣ b then mur d else 0 := by
            exact Finset.sum_comm
    _ = ∑ d ∈ Finset.Icc 1 N, mur d * ((N / d : Nat) : Real) ^ 2 := by
      apply Finset.sum_congr rfl
      intro d _
      exact sum_common_multiples N d

lemma abs_nat_div_cast_sub_le_one (N d : Nat) :
    |((N / d : Nat) : Real) - (N : Real) / (d : Real)| ≤ 1 := by
  have h := Nat.abs_floor_sub_le
    (a := (N : Real) / (d : Real)) (by positivity)
  rw [Nat.floor_div_natCast] at h
  simpa using h

lemma nat_div_cast_le_div (N d : Nat) (hd : 1 ≤ d) :
    ((N / d : Nat) : Real) ≤ (N : Real) / (d : Real) := by
  have hdr : (0 : Real) < d := by exact_mod_cast hd
  apply (le_div_iff₀ hdr).2
  exact_mod_cast Nat.div_mul_le_self N d

lemma abs_nat_div_sq_sub_le (N d : Nat) (hd : 1 ≤ d) :
    |((N / d : Nat) : Real) ^ 2 - ((N : Real) / (d : Real)) ^ 2| ≤
      2 * ((N : Real) / (d : Real)) := by
  let q : Real := (N / d : Nat)
  let x : Real := (N : Real) / (d : Real)
  have hqx : q ≤ x := nat_div_cast_le_div N d hd
  have hq0 : 0 ≤ q := Nat.cast_nonneg _
  have hx0 : 0 ≤ x := by positivity
  have herr : |q - x| ≤ 1 := abs_nat_div_cast_sub_le_one N d
  calc
    |((N / d : Nat) : Real) ^ 2 - ((N : Real) / (d : Real)) ^ 2| =
        |q - x| * |q + x| := by
          rw [← abs_mul]
          dsimp [q, x]
          congr 1
          ring
    _ = |q - x| * (q + x) := by rw [abs_of_nonneg (add_nonneg hq0 hx0)]
    _ ≤ 1 * (q + x) := mul_le_mul_of_nonneg_right herr (add_nonneg hq0 hx0)
    _ ≤ 2 * x := by nlinarith
    _ = 2 * ((N : Real) / (d : Real)) := rfl

lemma real_sum_Icc_one_div (N : Nat) :
    (∑ d ∈ Finset.Icc 1 N, 1 / (d : Real)) = (harmonic N : Real) := by
  have h := congrArg (fun q : Rat => (q : Real))
    (harmonic_eq_sum_Icc (n := N))
  push_cast at h
  simpa [one_div] using h.symm

lemma abs_coprime_floor_sum_sub_le (N : Nat) :
    |(∑ d ∈ Finset.Icc 1 N, mur d * ((N / d : Nat) : Real) ^ 2) -
        (N : Real) ^ 2 * ∑ d ∈ Finset.Icc 1 N, mur d / (d : Real) ^ 2| ≤
      2 * N * (harmonic N : Real) := by
  have heq :
      (∑ d ∈ Finset.Icc 1 N, mur d * ((N / d : Nat) : Real) ^ 2) -
          (N : Real) ^ 2 * ∑ d ∈ Finset.Icc 1 N, mur d / (d : Real) ^ 2 =
        ∑ d ∈ Finset.Icc 1 N, mur d *
          (((N / d : Nat) : Real) ^ 2 - ((N : Real) / (d : Real)) ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [heq]
  calc
    |∑ d ∈ Finset.Icc 1 N, mur d *
        (((N / d : Nat) : Real) ^ 2 - ((N : Real) / (d : Real)) ^ 2)| ≤
        ∑ d ∈ Finset.Icc 1 N, |mur d *
          (((N / d : Nat) : Real) ^ 2 - ((N : Real) / (d : Real)) ^ 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 N, 2 * ((N : Real) / (d : Real)) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      calc
        |mur d| * |((N / d : Nat) : Real) ^ 2 - ((N : Real) / (d : Real)) ^ 2| ≤
            1 * (2 * ((N : Real) / (d : Real))) :=
          mul_le_mul (mur_abs_le_one d)
            (abs_nat_div_sq_sub_le N d (Finset.mem_Icc.mp hd).1)
            (abs_nonneg _) zero_le_one
        _ = 2 * ((N : Real) / (d : Real)) := one_mul _
    _ = 2 * N * (harmonic N : Real) := by
      rw [← real_sum_Icc_one_div N]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring

lemma totient_eq_card_coprime_Icc (n : Nat) (hn : 1 ≤ n) :
    Nat.totient n = ((Finset.Icc 1 n).filter (fun a => Nat.Coprime n a)).card := by
  by_cases hn1 : n = 1
  · subst n
    norm_num
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨han, hcop⟩
    have ha1 : 1 ≤ a := by
      by_contra h
      have ha0 : a = 0 := by omega
      subst a
      have : n = 1 := by simpa using hcop
      exact hn1 this
    exact ⟨⟨ha1, by omega⟩, hcop⟩
  · rintro ⟨⟨ha1, han⟩, hcop⟩
    have halt : a < n := by
      by_contra h
      have haeq : a = n := by omega
      subst a
      have : n = 1 := by simpa using hcop
      exact hn1 this
    exact ⟨halt, hcop⟩

lemma totient_eq_moebius_sum (n : Nat) (hn : 1 ≤ n) :
    (Nat.totient n : Int) = ∑ d ∈ Finset.Icc 1 n,
      if d ∣ n then ArithmeticFunction.moebius d * (n / d : Nat) else 0 := by
  calc
    (Nat.totient n : Int) = ∑ a ∈ Finset.Icc 1 n,
        if Nat.Coprime n a then 1 else 0 := by
          rw [totient_eq_card_coprime_Icc n hn]
          simp
    _ = ∑ a ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
          if d ∣ n ∧ d ∣ a then ArithmeticFunction.moebius d else 0 := by
            apply Finset.sum_congr rfl
            intro a ha
            symm
            exact sum_moebius_common_divisors n n a (by simp [hn]) ha
    _ = ∑ d ∈ Finset.Icc 1 n, ∑ a ∈ Finset.Icc 1 n,
          if d ∣ n ∧ d ∣ a then ArithmeticFunction.moebius d else 0 :=
      Finset.sum_comm
    _ = ∑ d ∈ Finset.Icc 1 n,
          if d ∣ n then ArithmeticFunction.moebius d * (n / d : Nat) else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hdn : d ∣ n
      · simp only [hdn, true_and, if_true]
        rw [← Finset.sum_filter]
        simp [card_multiples_in_Icc, mul_comm]
      · simp [hdn]

lemma totient_div_eq_mur_sum (n : Nat) (hn : 1 ≤ n) :
    (Nat.totient n : Real) / n = ∑ d ∈ Finset.Icc 1 n,
      if d ∣ n then mur d / (d : Real) else 0 := by
  have hphi : (Nat.totient n : Real) = ∑ d ∈ Finset.Icc 1 n,
      if d ∣ n then mur d * ((n / d : Nat) : Real) else 0 := by
    have h := congrArg (fun z : Int => (z : Real)) (totient_eq_moebius_sum n hn)
    simp only [Int.cast_natCast, Int.cast_sum, Int.cast_ite, Int.cast_zero,
      Int.cast_mul] at h
    simpa [mur] using h
  rw [hphi, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdn : d ∣ n
  · simp only [hdn, if_true]
    have hd0 : d ≠ 0 := by
      have hd1 := (Finset.mem_Icc.mp hd).1
      omega
    have hn0 : n ≠ 0 := by omega
    have hdr : (d : Real) ≠ 0 := by exact_mod_cast hd0
    have hnr : (n : Real) ≠ 0 := by exact_mod_cast hn0
    rw [Nat.cast_div hdn hdr]
    field_simp
  · simp [hdn]

lemma totient_div_eq_mur_sum_to (N n : Nat) (hn : n ∈ Finset.Icc 1 N) :
    (Nat.totient n : Real) / n = ∑ d ∈ Finset.Icc 1 N,
      if d ∣ n then mur d / (d : Real) else 0 := by
  rw [totient_div_eq_mur_sum n (Finset.mem_Icc.mp hn).1]
  apply Finset.sum_subset (by
    intro d hd
    simp only [Finset.mem_Icc] at hd ⊢
    exact ⟨hd.1, hd.2.trans (Finset.mem_Icc.mp hn).2⟩)
  intro d hdN hdn
  have hdlarge : n < d := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hdn
    have hd1 := (Finset.mem_Icc.mp hdN).1
    omega
  have hnotdvd : ¬d ∣ n := by
    intro hdvd
    have hdle := Nat.le_of_dvd (Finset.mem_Icc.mp hn).1 hdvd
    omega
  simp [hnotdvd]

lemma sum_totient_div_eq_mur_floor_sum (N : Nat) :
    (Finset.Icc 1 N).sum (fun n => (Nat.totient n : Real) / n) =
      ∑ d ∈ Finset.Icc 1 N, mur d / (d : Real) * (N / d : Nat) := by
  calc
    (Finset.Icc 1 N).sum (fun n => (Nat.totient n : Real) / n) =
        ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N,
          if d ∣ n then mur d / (d : Real) else 0 := by
            apply Finset.sum_congr rfl
            intro n hn
            exact totient_div_eq_mur_sum_to N n hn
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          if d ∣ n then mur d / (d : Real) else 0 := Finset.sum_comm
    _ = ∑ d ∈ Finset.Icc 1 N, mur d / (d : Real) * (N / d : Nat) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [← Finset.sum_filter]
      simp [card_multiples_in_Icc, mul_comm]

lemma abs_totient_div_floor_sum_sub_le (N : Nat) :
    |(∑ d ∈ Finset.Icc 1 N, mur d / (d : Real) * (N / d : Nat)) -
        (N : Real) * ∑ d ∈ Finset.Icc 1 N, mur d / (d : Real) ^ 2| ≤
      (harmonic N : Real) := by
  have heq :
      (∑ d ∈ Finset.Icc 1 N, mur d / (d : Real) * (N / d : Nat)) -
          (N : Real) * ∑ d ∈ Finset.Icc 1 N, mur d / (d : Real) ^ 2 =
        ∑ d ∈ Finset.Icc 1 N, mur d / (d : Real) *
          (((N / d : Nat) : Real) - (N : Real) / (d : Real)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [heq]
  calc
    |∑ d ∈ Finset.Icc 1 N, mur d / (d : Real) *
        (((N / d : Nat) : Real) - (N : Real) / (d : Real))| ≤
        ∑ d ∈ Finset.Icc 1 N, |mur d / (d : Real) *
          (((N / d : Nat) : Real) - (N : Real) / (d : Real))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 N, 1 / (d : Real) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdr : (0 : Real) ≤ d := Nat.cast_nonneg d
      rw [abs_mul, abs_div, abs_of_nonneg hdr]
      calc
        |mur d| / (d : Real) *
            |((N / d : Nat) : Real) - (N : Real) / (d : Real)| ≤
            1 / (d : Real) * 1 :=
          mul_le_mul
            (div_le_div_of_nonneg_right (mur_abs_le_one d) hdr)
            (abs_nat_div_cast_sub_le_one N d) (abs_nonneg _) (by positivity)
        _ = 1 / (d : Real) := mul_one _
    _ = (harmonic N : Real) := real_sum_Icc_one_div N

lemma image_div_multiples_Icc (N d : Nat) (hd : 1 ≤ d) :
    ((Finset.Icc 1 N).filter (fun n => d ∣ n)).image (fun n => n / d) =
      Finset.Icc 1 (N / d) := by
  ext k
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨n, ⟨⟨hn1, hnN⟩, hdn⟩, rfl⟩
    have hdnle : d ≤ n := Nat.le_of_dvd hn1 hdn
    exact ⟨Nat.div_pos hdnle (by omega), Nat.div_le_div_right hnN⟩
  · rintro ⟨hk1, hkN⟩
    refine ⟨k * d, ?_, ?_⟩
    · refine ⟨⟨Nat.mul_pos (by omega) (by omega), ?_⟩, dvd_mul_left d k⟩
      exact (Nat.mul_le_mul_right d hkN).trans (Nat.div_mul_le_self N d)
    · exact Nat.mul_div_cancel k (by omega)

lemma sum_quotients_multiples_Icc (N d : Nat) (hd : 1 ≤ d) :
    (∑ n ∈ Finset.Icc 1 N, if d ∣ n then ((n / d : Nat) : Real) else 0) =
      ∑ k ∈ Finset.Icc 1 (N / d), (k : Real) := by
  rw [← Finset.sum_filter]
  rw [← image_div_multiples_Icc N d hd]
  symm
  apply Finset.sum_image
  intro a ha b hb hab
  have hda : d ∣ a := (Finset.mem_filter.mp ha).2
  have hdb : d ∣ b := (Finset.mem_filter.mp hb).2
  change a / d = b / d at hab
  calc
    a = a / d * d := (Nat.div_mul_cancel hda).symm
    _ = b / d * d := by rw [hab]
    _ = b := Nat.div_mul_cancel hdb

lemma sum_Icc_natCast (q : Nat) :
    (∑ k ∈ Finset.Icc 1 q, (k : Real)) = (q : Real) * (q + 1) / 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ q + 1)]
      rw [ih]
      push_cast
      ring

lemma sum_totient_eq_mur_triangle_sum (N : Nat) :
    (Finset.Icc 1 N).sum (fun n => (Nat.totient n : Real)) =
      ∑ d ∈ Finset.Icc 1 N, mur d *
        (((N / d : Nat) : Real) * ((N / d : Nat) + 1) / 2) := by
  calc
    (Finset.Icc 1 N).sum (fun n => (Nat.totient n : Real)) =
        ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N,
          if d ∣ n then mur d * ((n / d : Nat) : Real) else 0 := by
            apply Finset.sum_congr rfl
            intro n hn
            have hphi : (Nat.totient n : Real) = ∑ d ∈ Finset.Icc 1 n,
                if d ∣ n then mur d * ((n / d : Nat) : Real) else 0 := by
              have h := congrArg (fun z : Int => (z : Real))
                (totient_eq_moebius_sum n (Finset.mem_Icc.mp hn).1)
              simp only [Int.cast_natCast, Int.cast_sum, Int.cast_ite, Int.cast_zero,
                Int.cast_mul] at h
              simpa [mur] using h
            rw [hphi]
            apply Finset.sum_subset (by
              intro d hd
              simp only [Finset.mem_Icc] at hd ⊢
              exact ⟨hd.1, hd.2.trans (Finset.mem_Icc.mp hn).2⟩)
            intro d hdN hdnot
            have hdlarge : n < d := by
              simp only [Finset.mem_Icc, not_and_or, not_le] at hdnot
              have hd1 := (Finset.mem_Icc.mp hdN).1
              omega
            have hnotdvd : ¬d ∣ n := by
              intro hdvd
              have := Nat.le_of_dvd (Finset.mem_Icc.mp hn).1 hdvd
              omega
            simp [hnotdvd]
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          if d ∣ n then mur d * ((n / d : Nat) : Real) else 0 := Finset.sum_comm
    _ = ∑ d ∈ Finset.Icc 1 N, mur d *
          (((N / d : Nat) : Real) * ((N / d : Nat) + 1) / 2) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hq := sum_quotients_multiples_Icc N d (Finset.mem_Icc.mp hd).1
      calc
        (∑ n ∈ Finset.Icc 1 N,
            if d ∣ n then mur d * ((n / d : Nat) : Real) else 0) =
            mur d * ∑ n ∈ Finset.Icc 1 N,
              if d ∣ n then ((n / d : Nat) : Real) else 0 := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro n _
                by_cases hdn : d ∣ n <;> simp [hdn]
        _ = mur d * (((N / d : Nat) : Real) * ((N / d : Nat) + 1) / 2) := by
          rw [hq, sum_Icc_natCast]

lemma abs_triangle_floor_sub_le (N d : Nat) (hd : 1 ≤ d) :
    |((N / d : Nat) : Real) * ((N / d : Nat) + 1) / 2 -
        ((N : Real) / (d : Real)) ^ 2 / 2| ≤
      (3 / 2 : Real) * ((N : Real) / (d : Real)) := by
  let q : Real := (N / d : Nat)
  let x : Real := (N : Real) / (d : Real)
  have hq0 : 0 ≤ q := Nat.cast_nonneg _
  have hx0 : 0 ≤ x := by positivity
  have hqx : q ≤ x := nat_div_cast_le_div N d hd
  have hsq : |q ^ 2 - x ^ 2| ≤ 2 * x := by
    simpa [q, x] using abs_nat_div_sq_sub_le N d hd
  calc
    |((N / d : Nat) : Real) * ((N / d : Nat) + 1) / 2 -
        ((N : Real) / (d : Real)) ^ 2 / 2| =
        |(q ^ 2 - x ^ 2) + q| / 2 := by
          rw [show ((N / d : Nat) : Real) * ((N / d : Nat) + 1) / 2 -
              ((N : Real) / (d : Real)) ^ 2 / 2 =
              ((q ^ 2 - x ^ 2) + q) / 2 by
                dsimp [q, x]
                ring]
          rw [abs_div]
          norm_num
    _ ≤ (|q ^ 2 - x ^ 2| + |q|) / 2 := by
      gcongr
      exact abs_add_le _ _
    _ = (|q ^ 2 - x ^ 2| + q) / 2 := by rw [abs_of_nonneg hq0]
    _ ≤ (3 / 2 : Real) * x := by nlinarith
    _ = (3 / 2 : Real) * ((N : Real) / (d : Real)) := rfl

lemma abs_totient_triangle_sum_sub_le (N : Nat) :
    |(∑ d ∈ Finset.Icc 1 N, mur d *
          (((N / d : Nat) : Real) * ((N / d : Nat) + 1) / 2)) -
        ((N : Real) ^ 2 / 2) *
          ∑ d ∈ Finset.Icc 1 N, mur d / (d : Real) ^ 2| ≤
      (3 / 2 : Real) * N * (harmonic N : Real) := by
  have heq :
      (∑ d ∈ Finset.Icc 1 N, mur d *
          (((N / d : Nat) : Real) * ((N / d : Nat) + 1) / 2)) -
          ((N : Real) ^ 2 / 2) *
            ∑ d ∈ Finset.Icc 1 N, mur d / (d : Real) ^ 2 =
        ∑ d ∈ Finset.Icc 1 N, mur d *
          (((N / d : Nat) : Real) * ((N / d : Nat) + 1) / 2 -
            ((N : Real) / (d : Real)) ^ 2 / 2) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [heq]
  calc
    |∑ d ∈ Finset.Icc 1 N, mur d *
        (((N / d : Nat) : Real) * ((N / d : Nat) + 1) / 2 -
          ((N : Real) / (d : Real)) ^ 2 / 2)| ≤
        ∑ d ∈ Finset.Icc 1 N, |mur d *
          (((N / d : Nat) : Real) * ((N / d : Nat) + 1) / 2 -
            ((N : Real) / (d : Real)) ^ 2 / 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 N,
          (3 / 2 : Real) * ((N : Real) / (d : Real)) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      calc
        |mur d| * |((N / d : Nat) : Real) * ((N / d : Nat) + 1) / 2 -
            ((N : Real) / (d : Real)) ^ 2 / 2| ≤
            1 * ((3 / 2 : Real) * ((N : Real) / (d : Real))) :=
          mul_le_mul (mur_abs_le_one d)
            (abs_triangle_floor_sub_le N d (Finset.mem_Icc.mp hd).1)
            (abs_nonneg _) zero_le_one
        _ = (3 / 2 : Real) * ((N : Real) / (d : Real)) := one_mul _
    _ = (3 / 2 : Real) * N * (harmonic N : Real) := by
      rw [← real_sum_Icc_one_div N, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring
