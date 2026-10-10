import TuringTask.Basic

open TuringTask

example (x y z : Int) (h : x ^ 3 + y ^ 3 = 2 * z ^ 3) :
    x = y \/ x + y = 0 :=
  TuringTask.cube_add_cube_eq_two_mul_cube x y z h

example (x y : Rat) (h : y ^ 2 = x ^ 3 + 1) :
    Membership.mem ({(-1, 0), (0, 1), (0, -1), (2, 3), (2, -3)} : Finset (Prod Rat Rat))
      (x, y) :=
  TuringTask.rat_sq_eq_cube_add_one x y h

example (x y : Rat) (h : y ^ 2 = x ^ 3 - 27) :
    x = 3 /\ y = 0 :=
  TuringTask.rat_sq_eq_cube_sub_27 x y h

example (x y : Int)
    (h : x ^ 3 - 2 * y ^ 3 = 1 \/ x ^ 3 - 2 * y ^ 3 = -1) :
    Membership.mem ({(1, 0), (-1, -1), (-1, 0), (1, 1)} : Finset (Prod Int Int))
      (x, y) :=
  TuringTask.cube_sub_two_mul_cube x y h

example (n m : Nat) (h : n * (n + 1) = 2 * m ^ 3) :
    n = 0 \/ n = 1 :=
  TuringTask.mul_succ_eq_two_mul_cube n m h

#print axioms TuringTask.cube_add_cube_eq_two_mul_cube
#print axioms TuringTask.rat_sq_eq_cube_add_one
#print axioms TuringTask.rat_sq_eq_cube_sub_27
#print axioms TuringTask.cube_sub_two_mul_cube
#print axioms TuringTask.mul_succ_eq_two_mul_cube
