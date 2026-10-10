import TuringTask.Basic

open TuringTask

example (N : Nat) (hN : 1 <= N) :
    abs ((((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : Real) -
        6 / Real.pi ^ 2 * N) <= 3 * Real.sqrt N :=
  TuringTask.card_squarefree_sub_le N hN

example (N : Nat) (hN : 1 <= N) :
    abs ((((Finset.product (Finset.Icc 1 N) (Finset.Icc 1 N)).filter
        (fun p : Prod Nat Nat => Nat.Coprime p.1 p.2)).card : Real) - 6 / Real.pi ^ 2 * N ^ 2) <=
      6 * N * (Real.log N + 1) :=
  TuringTask.card_coprime_sub_le N hN

example (N : Nat) (hN : 1 <= N) :
    abs ((Finset.Icc 1 N).sum (fun n => (Nat.totient n : Real)) - 3 / Real.pi ^ 2 * N ^ 2) <=
      4 * N * (Real.log N + 1) :=
  TuringTask.sum_totient_sub_le N hN

example (N : Nat) (hN : 1 <= N) :
    abs ((Finset.Icc 1 N).sum (fun n => (Nat.totient n : Real) / n) - 6 / Real.pi ^ 2 * N) <=
      Real.log N + 2 :=
  TuringTask.sum_totient_div_sub_le N hN

example :
    Filter.Tendsto (fun N : Nat => (((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card :
        Real) / N) Filter.atTop (nhds (6 / Real.pi ^ 2)) :=
  TuringTask.tendsto_card_squarefree_div

#print axioms TuringTask.card_squarefree_sub_le
#print axioms TuringTask.card_coprime_sub_le
#print axioms TuringTask.sum_totient_sub_le
#print axioms TuringTask.sum_totient_div_sub_le
#print axioms TuringTask.tendsto_card_squarefree_div
