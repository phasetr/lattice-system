import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergBalancedGSAtMinFirstCrossing

/-!
# `E_balanced(γ(sInf)) = global Ĥ min` at `sInf` (composition)

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) first-crossing argument.

Composes PR #3997 (`balanced_GS_at_first_crossing_of_argmin`) with the
`balancedGSSet` definition (PR #3983) to unpack the membership conclusion
into the explicit energy equality `E_balanced(γ(sInf)) = global Ĥ min(γ(sInf))`.

This is the precise form consumed by PR #3980's first-crossing axiom.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **`E_balanced(γ(sInf)) = global Ĥ min(γ(sInf))`** at the per-`M_chosen` first
crossing `sInf`, under the strict-GS axiom at `(1, 0)` + path-wide "balanced
IS GS below sInf" hypothesis. -/
theorem balanced_min_eq_full_at_sInf
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced M_chosen : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (magConfigS Λ N M_chosen)]
    [Nonempty (Λ → Fin (N + 1))]
    (lam' D' : ℝ)
    (hne_chosen :
      (perMCrossingSet (Λ := Λ) hJ N M_balanced M_chosen lam' D' ∩ Icc (0 : ℝ) 1).Nonempty)
    (h_GS_at_SU2 :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ N M_balanced lam' D' 0 =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N
          (anisotropicHeisenbergParametricPath lam' D' 0).1
          (anisotropicHeisenbergParametricPath lam' D' 0).2))
    (h_balanced_GS_below : ∀ t' : ℝ, t' ∈ Ico (0 : ℝ)
        (sInf (perMCrossingSet (Λ := Λ) hJ N M_balanced M_chosen lam' D' ∩ Icc (0 : ℝ) 1)) →
      t' ∈ balancedGSSet (Λ := Λ) hJ N M_balanced lam' D') :
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ N M_balanced lam' D'
        (sInf (perMCrossingSet (Λ := Λ) hJ N M_balanced M_chosen lam' D' ∩ Icc (0 : ℝ) 1)) =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N
          (anisotropicHeisenbergParametricPath lam' D'
            (sInf (perMCrossingSet (Λ := Λ) hJ N M_balanced M_chosen lam' D' ∩ Icc (0 : ℝ) 1))).1
          (anisotropicHeisenbergParametricPath lam' D'
            (sInf (perMCrossingSet (Λ := Λ) hJ N M_balanced M_chosen lam' D' ∩ Icc (0 : ℝ) 1))).2) :=
  balanced_GS_at_first_crossing_of_argmin hJ N M_balanced M_chosen lam' D'
    hne_chosen h_GS_at_SU2 h_balanced_GS_below

end LatticeSystem.Quantum
