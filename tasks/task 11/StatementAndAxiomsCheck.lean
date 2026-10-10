import TuringTask.Basic

open TuringTask

example (n m k d : Nat) (I : Fin m -> Fin n -> Bool)
    (hk : forall i, (Finset.univ.filter (fun v => I i v = true)).card = k)
    (hd : forall i, (Finset.univ.filter (fun j => Not (j = i) /\
      exists v, I i v = true /\ I j v = true)).card <= d)
    (hkd : Real.exp 1 * ((d : Real) + 1) <= 2 ^ (k - 1)) :
    exists c : Fin n -> Bool, forall i,
      (exists v, I i v = true /\ c v = true) /\ (exists v, I i v = true /\ c v = false) :=
  TuringTask.color_meet n m k d I hk hd hkd

example (n m k : Nat) (hk9 : 9 <= k) (I : Fin m -> Fin n -> Bool)
    (hk : forall i, (Finset.univ.filter (fun v => I i v = true)).card = k)
    (hdeg : forall v, (Finset.univ.filter (fun i => I i v = true)).card <= k) :
    exists c : Fin n -> Bool, forall i,
      (exists v, I i v = true /\ c v = true) /\ (exists v, I i v = true /\ c v = false) :=
  TuringTask.color_deg n m k hk9 I hk hdeg

example (n m k d : Nat) (V s : Fin m -> Fin n -> Bool)
    (hk : forall i, (Finset.univ.filter (fun v => V i v = true)).card = k)
    (hd : forall i, (Finset.univ.filter (fun j => Not (j = i) /\
      exists v, V i v = true /\ V j v = true)).card <= d)
    (hkd : Real.exp 1 * ((d : Real) + 1) <= 2 ^ k) :
    exists x : Fin n -> Bool, forall i, exists v, V i v = true /\ x v = s i v :=
  TuringTask.sat_exists n m k d V s hk hd hkd

example (n k : Nat)
    (h : Real.exp 1 * (((Nat.choose k 2 * Nat.choose n (k - 2) : Nat) : Real) + 1)
      <= 2 ^ (Nat.choose k 2 - 1)) :
    exists c : Sym2 (Fin n) -> Bool, forall s : Finset (Fin n), s.card = k ->
      2 <= (s.offDiag.image (fun q => c (Sym2.mk q.1 q.2))).card :=
  TuringTask.ramsey_color n k h

example (N k : Nat) (h : Real.exp 1 * (((k ^ 2 * N : Nat) : Real) + 1) <= 2 ^ (k - 1)) :
    exists c : Nat -> Bool, forall a r : Nat, 1 <= r -> a + (k - 1) * r < N ->
      2 <= ((Finset.range k).image (fun j => c (a + j * r))).card :=
  TuringTask.ap_color N k h

#print axioms TuringTask.color_meet
#print axioms TuringTask.color_deg
#print axioms TuringTask.sat_exists
#print axioms TuringTask.ramsey_color
#print axioms TuringTask.ap_color
