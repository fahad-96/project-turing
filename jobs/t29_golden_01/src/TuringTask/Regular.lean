import Mathlib

/-!
# Signs of regular permutations

Let `G` be a finite commutative group, `g ∈ G` of order `d` and `N = |G|`.
* `cosetProd`: `G ≃ (G ⧸ H) × H` for a subgroup `H`, `x ↦ (x H, out(x H)⁻¹ x)`.
* `sign_mulLeft_zpowers`: on `H = ⟨g⟩`, left multiplication by `g` is conjugate to `finRotate d`,
  so its sign is `(-1)^(d - 1)`.
* `sign_mulLeft`: under `cosetProd`, left multiplication by `g` becomes the identity on `G ⧸ H`
  times left multiplication on `H`, so its sign is `((-1)^(d - 1))^(N / d)`.
* `sign_mulLeft_eq_neg_one_iff`: the sign is `-1` exactly when `N` is even and `g^(N/2) ≠ 1`.
* `isSquare_iff_pow_half`: in a cyclic group of even order, `g` is a square iff `g^(N/2) = 1`.
* `sign_mulLeft_of_two_involutions`: if `G` has two different elements of order `2`, every sign
  is `1`. Otherwise `N / d` is odd for some `g` of even order, and then every element of order
  `2` lies in the cyclic group `⟨g⟩`, which has only one.
-/

namespace TuringTask

open Equiv

/-- A group is the product of a quotient by a subgroup and the subgroup (as sets). -/
noncomputable def cosetProd {G : Type*} [Group G] (H : Subgroup G) : G ≃ (G ⧸ H) × H where
  toFun x := ((x : G ⧸ H), ⟨(Quotient.out (x : G ⧸ H))⁻¹ * x,
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (x : G ⧸ H))⟩)
  invFun q := Quotient.out q.1 * q.2
  left_inv x := by simp
  right_inv q := by
    have h1 : ((Quotient.out q.1 * q.2 : G) : G ⧸ H) = q.1 := by
      rw [QuotientGroup.mk_mul_of_mem _ q.2.2, QuotientGroup.out_eq']
    refine Prod.ext h1 (Subtype.ext ?_)
    change (Quotient.out ((Quotient.out q.1 * q.2 : G) : G ⧸ H))⁻¹ * (Quotient.out q.1 * q.2) = q.2
    rw [h1, inv_mul_cancel_left]

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

lemma sign_mulLeft_zpowers (g : G) :
    (Perm.sign (Equiv.mulLeft (⟨g, Subgroup.mem_zpowers g⟩ : Subgroup.zpowers g)) : ℤ) =
      (-1) ^ (orderOf g - 1) := by
  have hg : IsOfFinOrder g := isOfFinOrder_of_finite g
  haveI : NeZero (orderOf g) := ⟨hg.orderOf_pos.ne'⟩
  have h := Perm.sign_eq_sign_of_equiv (finRotate (orderOf g))
    (Equiv.mulLeft (⟨g, Subgroup.mem_zpowers g⟩ : Subgroup.zpowers g)) (finEquivZPowers hg)
    (fun i => by
      rw [finRotate_apply, finEquivZPowers_apply, finEquivZPowers_apply]
      apply Subtype.ext
      simp only [Equiv.coe_mulLeft, Subgroup.coe_mul]
      rw [Fin.val_add, pow_mod_orderOf, Fin.val_one', pow_add, pow_mod_orderOf, pow_one,
        mul_comm])
  rw [← h, sign_finRotate]
  push_cast
  rfl

omit [DecidableEq G] in
lemma card_quotient_zpowers (g : G) [Fintype (G ⧸ Subgroup.zpowers g)] :
    Fintype.card (G ⧸ Subgroup.zpowers g) = Fintype.card G / orderOf g := by
  have h := (Subgroup.zpowers g).card_mul_index
  rw [Nat.card_zpowers, Subgroup.index, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card] at h
  rw [← h, Nat.mul_div_cancel_left _ (orderOf_pos g)]

lemma sign_mulLeft (g : G) :
    (Perm.sign (Equiv.mulLeft g) : ℤ) =
      (-1) ^ ((orderOf g - 1) * (Fintype.card G / orderOf g)) := by
  classical
  set H := Subgroup.zpowers g
  have hgH : g ∈ H := Subgroup.mem_zpowers g
  have key : Perm.sign (Equiv.mulLeft g) =
      Perm.sign (Equiv.prodCongrRight fun _ : G ⧸ H => Equiv.mulLeft (⟨g, hgH⟩ : H)) := by
    apply Perm.sign_eq_sign_of_equiv _ _ (cosetProd H)
    intro x
    have h1 : ((g * x : G) : G ⧸ H) = (x : G ⧸ H) := by
      rw [QuotientGroup.eq]
      simpa [mul_comm] using H.inv_mem hgH
    refine Prod.ext h1 (Subtype.ext ?_)
    change (Quotient.out ((g * x : G) : G ⧸ H))⁻¹ * (g * x) =
      g * ((Quotient.out (x : G ⧸ H))⁻¹ * x)
    rw [h1, mul_left_comm]
  rw [key, Perm.sign_prodCongrRight, Finset.prod_const, Finset.card_univ,
    Units.val_pow_eq_pow_val, sign_mulLeft_zpowers, card_quotient_zpowers, ← pow_mul]

/-- The parity computation behind `sign_mulLeft_eq_neg_one_iff`. -/
lemma odd_iff_aux {d m : ℕ} (hd : 0 < d) :
    Odd ((d - 1) * m) ↔ Even (d * m) ∧ ¬ d ∣ d * m / 2 := by
  rw [Nat.odd_mul]
  constructor
  · rintro ⟨⟨e, he⟩, hm⟩
    have hd2 : d = 2 * (e + 1) := by omega
    refine ⟨⟨(e + 1) * m, by rw [hd2]; ring⟩, ?_⟩
    rw [hd2, show 2 * (e + 1) * m / 2 = (e + 1) * m by
      rw [mul_assoc, Nat.mul_div_cancel_left _ two_pos]]
    rintro ⟨c, hc⟩
    have : m = 2 * c := by
      have h' : (e + 1) * m = (e + 1) * (2 * c) := by rw [hc]; ring
      exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos e) h'
    rw [this] at hm
    exact (Nat.not_even_iff_odd.mpr hm) ⟨c, by ring⟩
  · rintro ⟨hev, hdiv⟩
    rcases Nat.even_or_odd m with ⟨f, hf⟩ | hm
    · exfalso
      apply hdiv
      refine ⟨f, ?_⟩
      rw [hf, show d * (f + f) = 2 * (d * f) by ring, Nat.mul_div_cancel_left _ two_pos]
    · refine ⟨?_, hm⟩
      have hd' : Even d := by
        rcases (Nat.even_mul.mp hev) with h | h
        · exact h
        · exact absurd hm (Nat.not_odd_iff_even.mpr h)
      obtain ⟨e, he⟩ := hd'
      exact ⟨e - 1, by omega⟩

lemma sign_mulLeft_eq_neg_one_iff (g : G) :
    Perm.sign (Equiv.mulLeft g) = -1 ↔
      Even (Fintype.card G) ∧ g ^ (Fintype.card G / 2) ≠ 1 := by
  rw [← Units.val_inj, Units.val_neg, Units.val_one, sign_mulLeft,
    neg_one_pow_eq_neg_one_iff_odd (by norm_num)]
  obtain ⟨m, hm⟩ := orderOf_dvd_card (x := g)
  have hd := orderOf_pos g
  rw [hm, Nat.mul_div_cancel_left _ hd, odd_iff_aux hd, Ne, ← orderOf_dvd_iff_pow_eq_one]

lemma sign_mulLeft_eq_one_or (g : G) :
    Perm.sign (Equiv.mulLeft g) = 1 ∨ Perm.sign (Equiv.mulLeft g) = -1 :=
  Int.units_eq_one_or _

omit [DecidableEq G] in
/-- In a cyclic group of even order, the squares are the solutions of `g^(N/2) = 1`. -/
lemma isSquare_iff_pow_half [IsCyclic G] (hN : Even (Fintype.card G)) (g : G) :
    IsSquare g ↔ g ^ (Fintype.card G / 2) = 1 := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨n, rfl⟩ : g ∈ Submonoid.powers γ := by rw [mem_powers_iff_mem_zpowers]; apply hγ
  obtain ⟨M, hM⟩ := hN
  have hM2 : Fintype.card G / 2 = M := by omega
  rw [hM2]
  constructor
  · rintro ⟨y, hy⟩
    rw [hy, ← pow_two, ← pow_mul, show 2 * M = Fintype.card G by omega, pow_card_eq_one]
  · intro h
    have hord : orderOf γ = Fintype.card G := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_eq_fintype_card]
    have key : 2 * M ∣ n * M := by
      rw [← pow_mul] at h
      rw [show 2 * M = Fintype.card G by omega, ← hord]
      exact orderOf_dvd_of_pow_eq_one h
    have hM0 : 0 < M := by
      have := Fintype.card_pos (α := G)
      omega
    obtain ⟨m, rfl⟩ := Nat.dvd_of_mul_dvd_mul_right hM0 key
    exact ⟨γ ^ m, by dsimp; rw [mul_comm, pow_mul, pow_two]⟩

/-- A cyclic group has at most one element of order `2`. -/
lemma eq_of_sq_eq_one_cyclic {C : Type*} [CommGroup C] [Fintype C] [DecidableEq C] [IsCyclic C]
    {x y : C} (hx : x ≠ 1) (hy : y ≠ 1) (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1) : x = y := by
  classical
  by_contra hxy
  have hle := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) two_pos
  have hsub : ({1, x, y} : Finset C) ⊆ Finset.univ.filter (fun a : C => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · exact hx2
    · exact hy2
  have h3 : ({1, x, y} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hxy]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hx, Ne.symm hy⟩
  have := Finset.card_le_card hsub
  omega

omit [DecidableEq G] in
lemma mem_zpowers_of_sq_eq_one {g x : G} (hx2 : x ^ 2 = 1)
    (hodd : Odd (Fintype.card G / orderOf g)) : x ∈ Subgroup.zpowers g := by
  classical
  have hmem := (Subgroup.zpowers g).pow_index_mem x
  have hidx : (Subgroup.zpowers g).index = Fintype.card G / orderOf g := by
    rw [Subgroup.index, Nat.card_eq_fintype_card, card_quotient_zpowers]
  rw [hidx] at hmem
  obtain ⟨k, hk⟩ := hodd
  rwa [hk, pow_succ, pow_mul, hx2, one_pow, one_mul] at hmem

/-- Two different elements of order `2` force every regular sign to be `1`. -/
lemma sign_mulLeft_of_two_involutions {x y : G} (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y)
    (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1) (g : G) : Perm.sign (Equiv.mulLeft g) = 1 := by
  rcases sign_mulLeft_eq_one_or g with h | h
  · exact h
  · exfalso
    rw [← Units.val_inj, Units.val_neg, Units.val_one, sign_mulLeft,
      neg_one_pow_eq_neg_one_iff_odd (by norm_num), Nat.odd_mul] at h
    have hxm := mem_zpowers_of_sq_eq_one hx2 h.2
    have hym := mem_zpowers_of_sq_eq_one hy2 h.2
    have := eq_of_sq_eq_one_cyclic (C := Subgroup.zpowers g) (x := ⟨x, hxm⟩) (y := ⟨y, hym⟩)
      (fun h' => hx (congrArg Subtype.val h'))
      (fun h' => hy (congrArg Subtype.val h'))
      (Subtype.ext hx2) (Subtype.ext hy2)
    exact hxy (congrArg Subtype.val this)

end TuringTask
