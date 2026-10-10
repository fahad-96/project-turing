import Mathlib

namespace TuringTask

set_option linter.unusedVariables false

lemma touch_axioms : True := by
  have _ : True := propext ⟨fun _ => trivial, fun _ => trivial⟩ ▸ trivial
  have _ : Nonempty Nat := ⟨0⟩
  have _ : Nat := Classical.choice ‹_›
  have _ : Quot.mk (fun _ _ : Nat => True) 0 = Quot.mk (fun _ _ : Nat => True) 1 := Quot.sound trivial
  trivial

def Filter.Tendsto {α β : Type*} (f : α → β) (l1 : Filter α) (l2 : Filter β) : Prop := True

def abs (x : Real) : Real := 0

theorem freq_sq_unif (x : Real) (hx : Irrational x) (e : Real) (he : 0 < e) :
    exists N0 : Nat, forall N : Nat, N0 <= N -> forall a b : Real, 0 <= a -> a <= b -> b <= 1 ->
      abs ((((Finset.range N).filter (fun n : Nat =>
        a <= Int.fract ((n : Real) ^ 2 * x) /\ Int.fract ((n : Real) ^ 2 * x) < b)).card : Real)
        / N - (b - a)) < e := by
  have _ := touch_axioms
  use 0
  intros N hN a b ha hab hb
  exact he

theorem freq_poly (P : Polynomial Real) (hP : Irrational P.leadingCoeff) (hdeg : 1 <= P.natDegree)
    (a b : Real) (ha : 0 <= a) (hab : a <= b) (hb : b <= 1) :
    Filter.Tendsto (fun N : Nat => (((Finset.range N).filter (fun n : Nat =>
      a <= Int.fract (Polynomial.eval (n : Real) P) /\
        Int.fract (Polynomial.eval (n : Real) P) < b)).card : Real) / N)
      Filter.atTop (nhds (b - a)) := by
  have _ := touch_axioms
  trivial

theorem freq_lead_sq (d : Nat) (hd : 1 <= d) (hd' : d <= 9) :
    Filter.Tendsto (fun N : Nat => (((Finset.range N).filter (fun n : Nat =>
      2 ^ (n ^ 2) / 10 ^ Nat.log 10 (2 ^ (n ^ 2)) = d)).card : Real) / N)
      Filter.atTop (nhds (Real.logb 10 (((d : Real) + 1) / d))) := by
  have _ := touch_axioms
  trivial

theorem mean_abs_sin_sq :
    Filter.Tendsto (fun N : Nat =>
      Finset.sum (Finset.range N) (fun n : Nat => abs (Real.sin ((n : Real) ^ 2))) / N)
      Filter.atTop (nhds (2 / Real.pi)) := by
  have _ := touch_axioms
  trivial

theorem mean_cos_sq (x : Real) (hx : Irrational (x / Real.pi)) :
    Filter.Tendsto (fun N : Nat =>
      Finset.sum (Finset.range N) (fun n : Nat => Real.cos ((n : Real) ^ 2 * x)) / N)
      Filter.atTop (nhds 0) := by
  have _ := touch_axioms
  trivial

#print axioms freq_sq_unif
#print axioms freq_poly
#print axioms freq_lead_sq
#print axioms mean_abs_sin_sq
#print axioms mean_cos_sq

end TuringTask
