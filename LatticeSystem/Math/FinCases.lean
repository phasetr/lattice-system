import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# Case splits for small `Fin` types

Model-agnostic enumeration lemmas for `Fin 2` and `Fin 3`.  These are used
pervasively in the `t`-`J` / Hubbard sector arguments, where site occupation
values live in `Fin 2` (empty/occupied) or `Fin 3` (empty/up/down).  They are
kept in `Math/` so the many consumers share a single copy instead of each
carrying a private duplicate.
-/

namespace LatticeSystem

/-- Every element of `Fin 2` is `0` or `1`. -/
theorem fin2_eq_zero_or_one (r : Fin 2) : r = 0 ∨ r = 1 := by
  fin_cases r <;> simp

/-- Every element of `Fin 3` is `0`, `1`, or `2`. -/
theorem fin3_eq_zero_or_one_or_two (v : Fin 3) : v = 0 ∨ v = 1 ∨ v = 2 := by
  fin_cases v <;> simp

end LatticeSystem
