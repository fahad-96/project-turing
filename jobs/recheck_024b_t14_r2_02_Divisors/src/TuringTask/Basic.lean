import Mathlib
import TuringTask.Thm1
import TuringTask.Thm2
import TuringTask.Limits

namespace TuringTask

theorem sum_card_divisors_sub_le (N : Nat) (hN : 1 <= N) :
    abs ((Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real)) - (N : Real) * Real.log N -
        (2 * Real.eulerMascheroniConstant - 1) * N) <= 4 * Real.sqrt N :=
  main_estimate N hN

theorem sum_card_divisors_div_sub_le (N : Nat) (hN : 1 <= N) :
    abs ((Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real) / n) - Real.log N ^ 2 / 2 -
        2 * Real.eulerMascheroniConstant * Real.log N) <= 4 :=
  main_estimate_two N hN

theorem tendsto_sum_card_divisors :
    Filter.Tendsto (fun N : Nat => ((Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real)) -
        (N : Real) * Real.log N) / N) Filter.atTop
      (nhds (2 * Real.eulerMascheroniConstant - 1)) :=
  tendsto_three

theorem tendsto_sum_card_divisors_sub_log :
    Filter.Tendsto (fun N : Nat => (Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real) -
        Real.log n) / N) Filter.atTop (nhds (2 * Real.eulerMascheroniConstant)) :=
  tendsto_four_thm

theorem tendsto_sum_sum_card_divisors :
    Filter.Tendsto (fun N : Nat => ((Finset.Icc 1 N).sum (fun n =>
        (Finset.Icc 1 n).sum (fun m => (m.divisors.card : Real))) -
        (N : Real) ^ 2 * Real.log N / 2) / (N : Real) ^ 2) Filter.atTop
      (nhds (Real.eulerMascheroniConstant - 3 / 4)) :=
  tendsto_five

end TuringTask
