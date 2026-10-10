import TuringTask.Basic

open TuringTask

example (N : Nat) (hN : 1 <= N) :
    abs ((Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real)) - (N : Real) * Real.log N -
        (2 * Real.eulerMascheroniConstant - 1) * N) <= 4 * Real.sqrt N :=
  TuringTask.sum_card_divisors_sub_le N hN

example (N : Nat) (hN : 1 <= N) :
    abs ((Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real) / n) - Real.log N ^ 2 / 2 -
        2 * Real.eulerMascheroniConstant * Real.log N) <= 4 :=
  TuringTask.sum_card_divisors_div_sub_le N hN

example :
    Filter.Tendsto (fun N : Nat => ((Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real)) -
        (N : Real) * Real.log N) / N) Filter.atTop
      (nhds (2 * Real.eulerMascheroniConstant - 1)) :=
  TuringTask.tendsto_sum_card_divisors

example :
    Filter.Tendsto (fun N : Nat => (Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real) -
        Real.log n) / N) Filter.atTop (nhds (2 * Real.eulerMascheroniConstant)) :=
  TuringTask.tendsto_sum_card_divisors_sub_log

example :
    Filter.Tendsto (fun N : Nat => ((Finset.Icc 1 N).sum (fun n =>
        (Finset.Icc 1 n).sum (fun m => (m.divisors.card : Real))) -
        (N : Real) ^ 2 * Real.log N / 2) / (N : Real) ^ 2) Filter.atTop
      (nhds (Real.eulerMascheroniConstant - 3 / 4)) :=
  TuringTask.tendsto_sum_sum_card_divisors

#print axioms TuringTask.sum_card_divisors_sub_le
#print axioms TuringTask.sum_card_divisors_div_sub_le
#print axioms TuringTask.tendsto_sum_card_divisors
#print axioms TuringTask.tendsto_sum_card_divisors_sub_log
#print axioms TuringTask.tendsto_sum_sum_card_divisors
