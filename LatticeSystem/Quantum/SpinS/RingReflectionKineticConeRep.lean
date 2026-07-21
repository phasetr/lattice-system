/-
The kinetic Gibbs factor is cone-representable
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 12).

In the Dyson–Lieb–Simon decomposition `H = H_L + θ(H_L) − D`, the diagonal part `H₀ = H_L + θ(H_L)`
has `H_L` (left) commuting with `θ(H_L)` (right), so its Gibbs factor factorizes:
`exp(X + θ X) = exp X · θ(exp X) = θ(exp X) · exp X` for `X` left-supported.  The right-hand side is
a single cone generator (`θ(L)·L`, `L = exp X` left-supported), so the kinetic Gibbs factor is
**cone-representable** (`coneRep_exp_add`).  Combined with the RP-weight cone, this is the kinetic
building block that the Trotter expansion of `e^{-βH}` consumes.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionExpSupport
import Mathlib.Analysis.Matrix.Normed

namespace LatticeSystem.Quantum

open Matrix

open scoped Matrix.Norms.Operator

variable {n N : ℕ}

/-- **Kinetic factorization.**  For a left-supported `X`, the Gibbs factor of `X + θ(X)` factorizes
into the cone generator `θ(exp X)·(exp X)` (using that `X` and `θ(X)` commute and that `θ` commutes
with the exponential). -/
theorem ringReflectionThetaS_exp_add_eq {X : ManyBodyOpS (Fin (2 * n)) N}
    (hX : SupportedOnLeftS n N X) :
    NormedSpace.exp (X + ringReflectionThetaS n N X)
      = ringReflectionThetaS n N (NormedSpace.exp X) * NormedSpace.exp X := by
  haveI : CompleteSpace (ManyBodyOpS (Fin (2 * n)) N) :=
    FiniteDimensional.complete ℂ (ManyBodyOpS (Fin (2 * n)) N)
  rw [NormedSpace.exp_add_of_commute (hX.mul_theta_comm hX), ← ringReflectionThetaS_exp]
  exact hX.exp.mul_theta_comm hX.exp

/-- **Asymmetric kinetic merge.**  For left-supported `X` and `Y`, the product of the left factor
`exp X` and the reflected right factor `θ(exp Y)` merges into a single exponential
`exp(X + θ Y)` (the two factors commute since `X` acts on the left half and `θ(exp Y)` on the
right).  This is the two-field analogue of `ringReflectionThetaS_exp_add_eq`, with independent left
and right generators; it lives here (where the matrix-exponential norm diamond of the Lie-product
layer is absent) so the two-field Gibbs weight can consume it as a black box. -/
theorem ringReflectionThetaS_exp_mul_theta_exp {X Y : ManyBodyOpS (Fin (2 * n)) N}
    (hX : SupportedOnLeftS n N X) (hY : SupportedOnLeftS n N Y) :
    NormedSpace.exp X * ringReflectionThetaS n N (NormedSpace.exp Y)
      = NormedSpace.exp (X + ringReflectionThetaS n N Y) := by
  haveI : CompleteSpace (ManyBodyOpS (Fin (2 * n)) N) :=
    FiniteDimensional.complete ℂ (ManyBodyOpS (Fin (2 * n)) N)
  rw [ringReflectionThetaS_exp, NormedSpace.exp_add_of_commute (hX.mul_theta_comm hY)]

/-- **The kinetic Gibbs factor is cone-representable.**  For a left-supported `X`,
`exp(X + θ X)` is cone-representable (a single cone generator `θ(L)·L`, `L = exp X`). -/
theorem coneRep_exp_add {X : ManyBodyOpS (Fin (2 * n)) N} (hX : SupportedOnLeftS n N X) :
    RPTraceConeRepS n N (NormedSpace.exp (X + ringReflectionThetaS n N X)) := by
  rw [ringReflectionThetaS_exp_add_eq hX]
  exact ⟨PUnit, inferInstance, fun _ => NormedSpace.exp X, fun _ => 1, fun _ => hX.exp,
    fun _ => zero_le_one, by simp⟩

end LatticeSystem.Quantum
