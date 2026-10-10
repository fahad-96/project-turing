import TuringTask.Core

namespace TuringTask

theorem legendreSum_le_core (p : Nat) [hp : Fact p.Prime] (h2 : Not (p = 2)) (N : Nat) :
    abs (((Finset.Icc 1 N).sum (fun n => legendreSym p (n : Int)) : Int) : Real) <=
      Real.sqrt p * Real.log p := by
  let χ : MulChar (ZMod p) ℂ :=
    (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
  have hχ : χ ≠ 1 := by
    exact (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr
      (quadraticChar_ne_one (by simpa [ZMod.ringChar_zmod_n] using h2))
  have hbound := charSum_norm_le_core p hp.out χ hχ N
  convert hbound using 1
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  congr 1
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  simp only [χ, MulChar.ringHomComp_apply]
  change ((legendreSym p (n : ℤ) : ℤ) : ℂ) =
    (((quadraticChar (ZMod p)) (n : ZMod p) : ℤ) : ℂ)
  apply congrArg (fun z : ℤ => (z : ℂ))
  simpa using legendreSym.eq_1 p (n : ℤ)

theorem card_residues_sub_le_core (p : Nat) [hp : Fact p.Prime] (h2 : Not (p = 2)) (N : Nat)
    (hN : N < p) :
    abs (2 * (((Finset.Icc 1 N).filter (fun n : Nat => legendreSym p (n : Int) = 1)).card : Real) -
        N) <= Real.sqrt p * Real.log p := by
  have hpoint (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      (legendreSym p (n : ℤ) : ℝ) =
        2 * (if legendreSym p (n : ℤ) = 1 then 1 else 0) - 1 := by
    have hn' := Finset.mem_Icc.mp hn
    have hnpos : 0 < n := by omega
    have hnlt : n < p := by omega
    have hn0 : (n : ZMod p) ≠ 0 := by
      intro hz
      have hdvd : p ∣ n := (ZMod.natCast_eq_zero_iff n p).mp hz
      exact (Nat.not_dvd_of_pos_of_lt hnpos hnlt) hdvd
    rcases legendreSym.eq_one_or_neg_one p (a := (n : ℤ)) (by simpa using hn0) with h | h
    · simp [h]
      norm_num
    · simp [h]
  have hsum :
      (((∑ n ∈ Finset.Icc 1 N, legendreSym p (n : ℤ) : ℤ) : ℤ) : ℝ) =
        2 * (((Finset.Icc 1 N).filter
          (fun n : Nat => legendreSym p (n : Int) = 1)).card : ℝ) - N := by
    push_cast
    calc
      (∑ n ∈ Finset.Icc 1 N, (legendreSym p (n : ℤ) : ℝ)) =
          ∑ n ∈ Finset.Icc 1 N,
            (2 * (if legendreSym p (n : ℤ) = 1 then 1 else 0) - 1 : ℝ) := by
              apply Finset.sum_congr rfl
              intro n hn
              exact hpoint n hn
      _ = 2 * (((Finset.Icc 1 N).filter
          (fun n : Nat => legendreSym p (n : Int) = 1)).card : ℝ) - N := by
            rw [Finset.sum_sub_distrib]
            rw [← Finset.mul_sum]
            rw [Finset.sum_boole]
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
            rw [Nat.card_Icc]
            simp
  rw [← hsum]
  exact legendreSum_le_core p h2 N

private lemma two_log_lt_sub_inv {y : ℝ} (hy : 1 < y) :
    2 * Real.log y < y - y⁻¹ := by
  let f : ℝ → ℝ := fun x => x - x⁻¹ - 2 * Real.log x
  have hfderivAt (x : ℝ) (hx : 0 < x) :
      HasDerivAt f (1 + x⁻¹ ^ 2 - 2 * x⁻¹) x := by
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hi := hasDerivAt_id x
    have hinv := hi.inv hx0
    have hlog := Real.hasDerivAt_log hx0
    have htwolog : HasDerivAt (fun z : ℝ => 2 * Real.log z) (2 * x⁻¹) x := by
      simpa [mul_comm] using hlog.mul_const (2 : ℝ)
    have hraw := (hi.sub hinv).sub htwolog
    convert hraw using 1
    · subsingleton
    · subsingleton
    · funext z
      simp [f]
    · simp
      ring
  have hfcont : ContinuousOn f (Set.Ici 1) := by
    intro x hx
    have hx' : 1 ≤ x := hx
    exact (hfderivAt x (by linarith)).continuousAt.continuousWithinAt
  have hfderiv : ∀ x ∈ interior (Set.Ici (1 : ℝ)), 0 < deriv f x := by
    rw [interior_Ici]
    intro x hx
    have hxpos : 0 < x := zero_lt_one.trans hx
    rw [(hfderivAt x hxpos).deriv]
    have heq : 1 + x⁻¹ ^ 2 - 2 * x⁻¹ = (x - 1) ^ 2 / x ^ 2 := by
      field_simp [ne_of_gt hxpos]
      ring
    rw [heq]
    exact div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_gt hx))) (sq_pos_of_pos hxpos)
  have hmono : StrictMonoOn f (Set.Ici 1) :=
    strictMonoOn_of_deriv_pos (convex_Ici (1 : ℝ)) hfcont hfderiv
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy.le) hy
  dsimp [f] at h
  simpa [mul_comm] using h

private lemma sqrt_mul_log_add_one_lt_nat (p : ℕ) (hp3 : 3 ≤ p) :
    Real.sqrt p * Real.log p + 1 < p := by
  have hp0 : (0 : ℝ) < p := by positivity
  have hsqrt1 : (1 : ℝ) < Real.sqrt p := by
    rw [Real.lt_sqrt (by positivity)]
    exact_mod_cast (show 1 < p by omega)
  have hlog := two_log_lt_sub_inv hsqrt1
  have hsqrtpos : 0 < Real.sqrt p := Real.sqrt_pos.2 hp0
  have hlogsqrt : Real.log p = 2 * Real.log (Real.sqrt p) := by
    calc
      Real.log p = Real.log ((Real.sqrt p) ^ 2) := by rw [Real.sq_sqrt (le_of_lt hp0)]
      _ = (2 : ℕ) * Real.log (Real.sqrt p) := Real.log_pow _ _
      _ = 2 * Real.log (Real.sqrt p) := by norm_num
  rw [hlogsqrt]
  calc
    Real.sqrt p * (2 * Real.log (Real.sqrt p)) + 1 <
        Real.sqrt p * (Real.sqrt p - (Real.sqrt p)⁻¹) + 1 := by
          gcongr
    _ = p := by
      rw [mul_sub, Real.mul_self_sqrt (le_of_lt hp0), mul_inv_cancel₀ (ne_of_gt hsqrtpos)]
      ring

theorem exists_not_pow_le_core (p k : Nat) (hp : p.Prime) (hk : 2 <= k)
    (hkp : (p - 1) % k = 0) :
    exists n : Nat, 1 <= n /\ (n : Real) <= Real.sqrt p * Real.log p + 1 /\
      forall x : ZMod p, Not (x ^ k = (n : ZMod p)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro heq
    subst p
    norm_num at hkp
    omega
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hkdiv : k ∣ Fintype.card (ZMod p) - 1 := by
    rw [ZMod.card]
    exact Nat.dvd_iff_mod_eq_zero.mpr hkp
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / k)
  have hζ : IsPrimitiveRoot ζ k := by
    exact Complex.isPrimitiveRoot_exp k (by omega)
  obtain ⟨χ, hχorder⟩ := MulChar.exists_mulChar_orderOf (ZMod p) hkdiv hζ
  have hχ : χ ≠ 1 := by
    intro heq
    have hone : orderOf χ = 1 := orderOf_eq_one_iff.mpr heq
    omega
  have hχpow : χ ^ k = 1 := by
    rw [← hχorder]
    exact pow_orderOf_eq_one χ
  let B : ℝ := Real.sqrt p * Real.log p
  let M : ℕ := ⌊B⌋₊ + 1
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hMpos : 1 ≤ M := by omega
  have hMle : (M : ℝ) ≤ B + 1 := by
    dsimp [M]
    push_cast
    linarith [Nat.floor_le hB0]
  have hMltp : M < p := by
    have hreal : (M : ℝ) < (p : ℝ) :=
      hMle.trans_lt (sqrt_mul_log_add_one_lt_nat p hp3)
    exact_mod_cast hreal
  by_contra H
  push Not at H
  have hvalue (n : ℕ) (hn : n ∈ Finset.Icc 1 M) : χ (n : ZMod p) = 1 := by
    have hn' := Finset.mem_Icc.mp hn
    have hnreal : (n : ℝ) ≤ B + 1 := by
      exact (Nat.cast_le.mpr hn'.2).trans hMle
    obtain ⟨x, hx⟩ := H n hn'.1 hnreal
    have hnlt : n < p := hn'.2.trans_lt hMltp
    have hn0 : (n : ZMod p) ≠ 0 := by
      intro hz
      have hdvd : p ∣ n := (ZMod.natCast_eq_zero_iff n p).mp hz
      exact (Nat.not_dvd_of_pos_of_lt (by omega) hnlt) hdvd
    have hx0 : x ≠ 0 := by
      intro hxzero
      subst x
      rw [zero_pow (by omega)] at hx
      exact hn0 hx.symm
    let u : (ZMod p)ˣ := (isUnit_iff_ne_zero.mpr hx0).unit
    have hu : (u : ZMod p) = x := (isUnit_iff_ne_zero.mpr hx0).unit_spec
    calc
      χ (n : ZMod p) = χ (x ^ k) := by rw [hx]
      _ = χ x ^ k := map_pow χ.toMonoidHom x k
      _ = (χ ^ k) (u : ZMod p) := by rw [MulChar.pow_apply_coe, hu]
      _ = 1 := by rw [hχpow, MulChar.one_apply_coe]
  have hsum : (∑ n ∈ Finset.Icc 1 M, χ (n : ZMod p)) = (M : ℂ) := by
    calc
      (∑ n ∈ Finset.Icc 1 M, χ (n : ZMod p)) = ∑ _n ∈ Finset.Icc 1 M, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact hvalue n hn
      _ = (M : ℂ) := by rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]; simp
  have hbound := charSum_norm_le_core p hp χ hχ M
  rw [hsum, Complex.norm_natCast] at hbound
  have hBlt : B < (M : ℝ) := by
    dsimp [M]
    simpa using Nat.lt_floor_add_one B
  exact (not_lt_of_ge hbound) hBlt

private theorem prime_factor_nonresidue
    {p n : ℕ} [Fact (Nat.Prime p)] (hn : n ≠ 0)
    (h : legendreSym p (n : ℤ) = -1) :
    ∃ q : ℕ, q.Prime ∧ q ∣ n ∧ legendreSym p (q : ℤ) = -1 := by
  let L : List ℤ := n.primeFactorsList.map (fun q : ℕ => (q : ℤ))
  have hLprod : L.prod = (n : ℤ) := by
    dsimp [L]
    change (List.map (Nat.castRingHom ℤ) n.primeFactorsList).prod = (n : ℤ)
    rw [← map_list_prod (Nat.castRingHom ℤ), Nat.prod_primeFactorsList hn]
    rfl
  have himage : (L.map (fun z : ℤ => legendreSym p z)).prod = -1 := by
    change (L.map (legendreSym.hom p)).prod = -1
    rw [← map_list_prod (legendreSym.hom p), hLprod, legendreSym.hom_apply]
    exact h
  obtain ⟨z, hzL, hz⟩ := List.mem_map.mp
    (List.neg_one_mem_of_prod_eq_neg_one himage)
  obtain ⟨q, hqfac, rfl⟩ := List.mem_map.mp (show z ∈ L from hzL)
  exact ⟨q, Nat.prime_of_mem_primeFactorsList hqfac,
    Nat.dvd_of_mem_primeFactorsList hqfac, hz⟩

theorem exists_prime_nonresidue_le_core (p : Nat) [hp : Fact p.Prime] (h2 : Not (p = 2)) :
    exists q : Nat, q.Prime /\ (q : Real) <= Real.sqrt p * Real.log p + 1 /\
      legendreSym p (q : Int) = -1 := by
  have hmod : (p - 1) % 2 = 0 := by
    obtain ⟨m, hm⟩ := hp.out.odd_of_ne_two h2
    omega
  obtain ⟨n, hn1, hnle, hnonsquare⟩ :=
    exists_not_pow_le_core p 2 hp.out (by omega) hmod
  have hnonsq : ¬IsSquare (n : ZMod p) := by
    intro hs
    obtain ⟨x, hx⟩ := hs
    apply hnonsquare x
    simpa [pow_two] using hx.symm
  have hnonsq' : ¬IsSquare ((n : ℤ) : ZMod p) := by simpa using hnonsq
  have hj : jacobiSym (n : ℤ) p = -1 :=
    ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mpr hnonsq'
  have hleg : legendreSym p (n : ℤ) = -1 := by
    simpa [jacobiSym, Nat.primeFactorsList_prime hp.out] using hj
  obtain ⟨q, hqprime, hqdiv, hqnonres⟩ :=
    prime_factor_nonresidue (show n ≠ 0 by omega) hleg
  refine ⟨q, hqprime, ?_, hqnonres⟩
  have hqn : q ≤ n := Nat.le_of_dvd (by omega) hqdiv
  have hqn' : (q : ℝ) ≤ n := by exact_mod_cast hqn
  exact hqn'.trans hnle

end TuringTask
