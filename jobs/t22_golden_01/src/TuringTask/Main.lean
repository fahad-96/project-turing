import Mathlib
import TuringTask.Apps

/-!
# The five statements

The five theorems of the task, stated as in `TuringTask/Basic.lean` and proved from
`two_cubes`, `plus1_points`, `minus27_points`, `cube_sub_two_cube` and `triangular_cube`.
-/

namespace TuringTask

theorem thm_two_cubes (x y z : Int) (h : x ^ 3 + y ^ 3 = 2 * z ^ 3) :
    x = y \/ x + y = 0 :=
  two_cubes h

theorem thm_plus1 (x y : Rat) (h : y ^ 2 = x ^ 3 + 1) :
    Membership.mem ({(-1, 0), (0, 1), (0, -1), (2, 3), (2, -3)} : Finset (Prod Rat Rat))
      (x, y) := by
  rcases plus1_points h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp

theorem thm_minus27 (x y : Rat) (h : y ^ 2 = x ^ 3 - 27) :
    x = 3 /\ y = 0 :=
  minus27_points h

theorem thm_cube_sub (x y : Int)
    (h : x ^ 3 - 2 * y ^ 3 = 1 \/ x ^ 3 - 2 * y ^ 3 = -1) :
    Membership.mem ({(1, 0), (-1, -1), (-1, 0), (1, 1)} : Finset (Prod Int Int))
      (x, y) := by
  rcases cube_sub_two_cube h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

theorem thm_triangular (n m : Nat) (h : n * (n + 1) = 2 * m ^ 3) :
    n = 0 \/ n = 1 :=
  triangular_cube h

end TuringTask
