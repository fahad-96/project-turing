import Mathlib

/-- Smoke test: if `lake build` accepts this file, Lean and Mathlib are set up correctly. -/
theorem setup_check (n : ℕ) : n + 0 = n := by
  simp
