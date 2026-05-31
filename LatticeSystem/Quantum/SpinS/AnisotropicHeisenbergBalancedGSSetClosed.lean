import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergFullMinEigenvalueContinuous
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergParametricMinEigenvalue

/-!
# The set `{ t | balanced sector is the GS at γ(t) }` is closed

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) first-crossing argument.

Defines the set
`balancedGSSet J hJ N M_balanced lam' D' := { t : ℝ | hermitianMinEigenvalue (Ĥ_M_balanced(γ(t))) = hermitianMinEigenvalue (Ĥ(γ(t))) }`
and proves it is closed in `ℝ`.

This is a building block for the first-crossing argument: `t* := sSup balancedGSSet`
will be reached (closed + bounded + non-empty), and at `t*` the equality holds.

Composes:
- PR #3957 / PR #3965 (sector min eigenvalue continuous along path).
- PR #3982 (full Ĥ min eigenvalue continuous along path).
- `isClosed_eq` (mathlib, preimage of diagonal under continuous map into Hausdorff).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **The set of `t` where the balanced sector is the GS at `γ(t)`** (i.e., the
sector-`M_balanced` min eigenvalue equals the global Ĥ min eigenvalue). -/
noncomputable def balancedGSSet
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced : ℕ) [Nonempty (magConfigS Λ N M_balanced)]
    [Nonempty (Λ → Fin (N + 1))] (lam' D' : ℝ) : Set ℝ :=
  { t : ℝ |
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ N M_balanced lam' D' t =
    hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N
        (anisotropicHeisenbergParametricPath lam' D' t).1
        (anisotropicHeisenbergParametricPath lam' D' t).2) }

/-- **The balanced-GS set is closed in `ℝ`**: as the preimage of the diagonal
in `ℝ × ℝ` under the continuous map
`t ↦ (E_M_balanced(γ(t)), global Ĥ(γ(t)) min)`, which is closed in `ℝ × ℝ`
(Hausdorff). -/
theorem isClosed_balancedGSSet
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced : ℕ) [Nonempty (magConfigS Λ N M_balanced)]
    [Nonempty (Λ → Fin (N + 1))] (lam' D' : ℝ) :
    IsClosed (balancedGSSet (Λ := Λ) hJ N M_balanced lam' D') := by
  unfold balancedGSSet
  exact isClosed_eq
    (continuous_anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ N M_balanced lam' D')
    (continuous_anisotropicHeisenbergS_full_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ N lam' D')

end LatticeSystem.Quantum
