import TuringTask.Basic

open TuringTask

example (n : Nat) (hn : n % 2 = 1) :
    Finset.sum (Finset.range n) (fun k : Nat => ex ((k : Real) ^ 2 / (n : Real))) = rt n :=
  TuringTask.sum_sq n hn

example (n : Nat) (hn : n % 2 = 1) :
    Finset.sum (Finset.range n) (fun k : Nat =>
        ex ((k : Real) * ((k : Real) + 1) / (2 * (n : Real)))) =
      ex (((n : Real) - 1) / (8 * (n : Real))) * ((Real.sqrt (n : Real) : Real) : Complex) :=
  TuringTask.sum_tri n hn

example (p : Nat) [Fact p.Prime] (hp : p % 2 = 1) (a : Int) :
    Finset.sum (Finset.range p) (fun k : Nat =>
        ((legendreSym p (k : Int) : Int) : Complex) *
          ex ((a : Real) * (k : Real) / (p : Real))) =
      ((legendreSym p a : Int) : Complex) * rt p :=
  TuringTask.sum_legendre p hp a

example (p q : Nat) [Fact p.Prime] [Fact q.Prime]
    (hp : p % 2 = 1) (hq : q % 2 = 1) (hpq : Not (p = q)) :
    Finset.sum (Finset.range p) (fun j : Nat =>
        ex ((q : Real) * (j : Real) ^ 2 / (p : Real))) *
      Finset.sum (Finset.range q) (fun k : Nat =>
        ex ((p : Real) * (k : Real) ^ 2 / (q : Real))) = rt (p * q) :=
  TuringTask.sum_sq_mul p q hp hq hpq

example (p : Nat) [Fact p.Prime] (hp : p % 4 = 3) :
    Real.sqrt (p : Real) * Finset.sum (Finset.range p) (fun k : Nat =>
        ((legendreSym p (k : Int) : Int) : Real) *
          Real.cot (Real.pi * (k : Real) / (p : Real))) =
      -2 * Finset.sum (Finset.range p) (fun k : Nat =>
        (k : Real) * ((legendreSym p (k : Int) : Int) : Real)) :=
  TuringTask.sum_cot p hp

example (x : Real) : TuringTask.ex x =
    Complex.exp (2 * (Real.pi : Complex) * Complex.I * (x : Complex)) := rfl

example (n : Nat) : TuringTask.rt n =
    (if n % 4 = 1 then ((Real.sqrt (n : Real) : Real) : Complex)
     else Complex.I * ((Real.sqrt (n : Real) : Real) : Complex)) := rfl

#print axioms TuringTask.sum_sq
#print axioms TuringTask.sum_tri
#print axioms TuringTask.sum_legendre
#print axioms TuringTask.sum_sq_mul
#print axioms TuringTask.sum_cot
