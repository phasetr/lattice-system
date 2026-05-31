import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergParametricMinEigenvalue

/-!
# Total parametric per-sector min eigenvalue (with empty-sector fallback)

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) first-crossing argument.

The named def `anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath`
(PR #3965) requires `[Nonempty (magConfigS Λ N M)]` as a typeclass instance.
For Finset-iteration arguments (e.g., extracting the argmin of `t_first_M`
over all valid `M`), we need a **total** version that returns a default value
when the sector is empty.

This brick provides the total version + a coincidence lemma showing it equals
the partial version on non-empty sectors.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Total parametric per-sector min eigenvalue**: returns the named def value
on non-empty sectors, `0` otherwise. -/
noncomputable def anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath_total
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M : ℕ) (lam' D' : ℝ) (t : ℝ) : ℝ := by
  classical
  exact if h : Nonempty (magConfigS Λ N M) then
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ N M lam' D' t
  else 0

/-- The total version agrees with the partial version on non-empty sectors. -/
theorem anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath_total_eq
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M : ℕ) [hNE : Nonempty (magConfigS Λ N M)] (lam' D' : ℝ) (t : ℝ) :
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath_total
      (Λ := Λ) hJ N M lam' D' t =
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ N M lam' D' t := by
  unfold anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath_total
  rw [dif_pos hNE]

end LatticeSystem.Quantum
