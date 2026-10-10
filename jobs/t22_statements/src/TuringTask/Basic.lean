import Mathlib

namespace TuringTask

theorem cube_add_cube_eq_two_mul_cube (x y z : Int) (h : x ^ 3 + y ^ 3 = 2 * z ^ 3) :
    x = y \/ x + y = 0 := by
  sorry

theorem rat_sq_eq_cube_add_one (x y : Rat) (h : y ^ 2 = x ^ 3 + 1) :
    Membership.mem ({(-1, 0), (0, 1), (0, -1), (2, 3), (2, -3)} : Finset (Prod Rat Rat))
      (x, y) := by
  sorry

theorem rat_sq_eq_cube_sub_27 (x y : Rat) (h : y ^ 2 = x ^ 3 - 27) :
    x = 3 /\ y = 0 := by
  sorry

theorem cube_sub_two_mul_cube (x y : Int)
    (h : x ^ 3 - 2 * y ^ 3 = 1 \/ x ^ 3 - 2 * y ^ 3 = -1) :
    Membership.mem ({(1, 0), (-1, -1), (-1, 0), (1, 1)} : Finset (Prod Int Int))
      (x, y) := by
  sorry

theorem mul_succ_eq_two_mul_cube (n m : Nat) (h : n * (n + 1) = 2 * m ^ 3) :
    n = 0 \/ n = 1 := by
  sorry

end TuringTask
