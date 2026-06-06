import Mathlib.Algebra.Ring.Basic

/-!
# From anticommutation to commutation of even products

Model-agnostic ring lemmas: in any (non-commutative) ring, an element that
anticommutes with each factor of a product commutes with the *even* product, and
two even products of pairwise-anticommuting factors commute.  These capture the
elementary `(-1)^{2k} = 1` sign cancellation behind "fermionic bilinears on
disjoint mode sets commute", used by the Jordan–Wigner / Hubbard spin-operator
arguments (e.g. `Ŝ⁻_x Ŝ⁺_y = Ŝ⁺_y Ŝ⁻_x` for `x ≠ y`).  Kept in `Math/` so they
are reusable across models without importing model-specific files.
-/

namespace LatticeSystem

/-- **An element anticommuting with both factors commutes with their product.**
If `a` anticommutes with `c` and with `d` (`a*c + c*a = 0`, `a*d + d*a = 0`),
then `a` commutes with the even product `c d`: the two sign flips cancel. -/
theorem anticomm_commute_mul {α : Type*} [Ring α] {a c d : α}
    (hac : a * c + c * a = 0) (had : a * d + d * a = 0) :
    a * (c * d) = c * d * a := by
  have hac' : a * c = -(c * a) := eq_neg_of_add_eq_zero_left hac
  have had' : a * d = -(d * a) := eq_neg_of_add_eq_zero_left had
  calc a * (c * d) = a * c * d := by rw [mul_assoc]
    _ = -(c * a) * d := by rw [hac']
    _ = -(c * (a * d)) := by rw [neg_mul, mul_assoc]
    _ = -(c * -(d * a)) := by rw [had']
    _ = c * d * a := by rw [mul_neg, neg_neg, mul_assoc]

/-- **Two even products of pairwise-anticommuting factors commute.**  If each of
`a, b` anticommutes with each of `c, d`, then the even products `a b` and `c d`
commute (`(-1)^4 = +1`). -/
theorem anticomm_commute_mul_mul {α : Type*} [Ring α] {a b c d : α}
    (hac : a * c + c * a = 0) (had : a * d + d * a = 0)
    (hbc : b * c + c * b = 0) (hbd : b * d + d * b = 0) :
    a * b * (c * d) = c * d * (a * b) := by
  have ha : a * (c * d) = c * d * a := anticomm_commute_mul hac had
  have hb : b * (c * d) = c * d * b := anticomm_commute_mul hbc hbd
  calc a * b * (c * d) = a * (b * (c * d)) := by rw [mul_assoc]
    _ = a * (c * d * b) := by rw [hb]
    _ = a * (c * d) * b := by rw [← mul_assoc]
    _ = c * d * a * b := by rw [ha]
    _ = c * d * (a * b) := by rw [mul_assoc]

end LatticeSystem
