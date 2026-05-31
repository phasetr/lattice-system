import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergParametricMinEigenvalue

/-!
# Per-`M` crossing set is closed

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) first-crossing argument.

Defines the per-`M` crossing set
`perMCrossingSet J hJ N M_balanced M lam' D' := { t : ℝ | E_M(γ(t)) ≤ E_balanced(γ(t)) }`
and proves it is closed in `ℝ`.

The first-crossing argument considers the union over `M ≠ M_balanced` of these sets;
that union is closed (finite union of closed sets) and contains `t = 1` under
the obligation (2) violation hypothesis.

Composes:
- PR #3957 / PR #3965 (sector min eigenvalue continuous along path).
- `IsClosed.preimage` + `isClosed_Iic` (mathlib).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Per-`M` crossing set**: `{ t : ℝ | E_M(γ(t)) ≤ E_balanced(γ(t)) }`. -/
noncomputable def perMCrossingSet
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced M : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (magConfigS Λ N M)]
    (lam' D' : ℝ) : Set ℝ :=
  { t : ℝ |
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ N M lam' D' t ≤
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ N M_balanced lam' D' t }

/-- **Per-`M` crossing set is closed in `ℝ`**: preimage of `Iic 0` under the
continuous gap function `g(t) := E_M(γ(t)) - E_balanced(γ(t))`. -/
theorem isClosed_perMCrossingSet
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced M : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (magConfigS Λ N M)]
    (lam' D' : ℝ) :
    IsClosed (perMCrossingSet (Λ := Λ) hJ N M_balanced M lam' D') := by
  unfold perMCrossingSet
  -- { t | f(t) ≤ g(t) } = (f - g)⁻¹ (Iic 0) (closed under continuous f - g).
  have hf := continuous_anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
    (Λ := Λ) hJ N M lam' D'
  have hg := continuous_anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
    (Λ := Λ) hJ N M_balanced lam' D'
  exact isClosed_le hf hg

end LatticeSystem.Quantum
