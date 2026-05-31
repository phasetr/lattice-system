import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergParametricGapCrossingGeneric

/-!
# The IVT crossing point `t*` is strictly positive under the strict initial gap

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

Refinement of PR #3971 `anisotropicHeisenbergS_parametric_gap_crossing_generic`:
under the strict initial gap `E_{M_0}(1, 0) < E_M(1, 0)`, the IVT crossing
point `t*` satisfies `0 < t*` (not merely `t* ∈ [0, 1]`).

Proof: the IVT gives `E_{M_0}(γ(t*)) = E_M(γ(t*))`, but at `t = 0` we have
`γ(0) = (1, 0)` and `E_{M_0}(1, 0) < E_M(1, 0)` strict, so the equality fails
at `t = 0`. Hence `t* ≠ 0`, combined with `t* ≥ 0` gives `t* > 0`.

This is the analytic refinement needed to apply the spin-1/2 finrank-≤-2 bound
along the parametric path (PR #3976), which requires `t > 0` (the strict region
hypotheses fail at the SU(2) point `(1, 0)`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **IVT crossing point is strictly positive**: under the strict initial gap
hypotheses for PR #3971's IVT crossing, the crossing point `t* ∈ [0, 1]` actually
lies in `(0, 1]`. -/
theorem anisotropicHeisenbergS_parametric_gap_crossing_t_pos
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_0 M : ℕ)
    [Nonempty (magConfigS Λ N M)] [Nonempty (magConfigS Λ N M_0)]
    (lam' D' : ℝ)
    (h0 : hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M_0) hJ 1 0) <
          hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M) hJ 1 0))
    (h1 : hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M) hJ lam' D') ≤
          hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M_0) hJ lam' D')) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M_0) hJ
          (anisotropicHeisenbergParametricPath lam' D' t).1
          (anisotropicHeisenbergParametricPath lam' D' t).2) =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M) hJ
          (anisotropicHeisenbergParametricPath lam' D' t).1
          (anisotropicHeisenbergParametricPath lam' D' t).2) := by
  obtain ⟨t, htmem, heq⟩ :=
    anisotropicHeisenbergS_parametric_gap_crossing_generic
      (Λ := Λ) hJ N M_0 M lam' D' h0 h1
  refine ⟨t, ?_, htmem.2, heq⟩
  -- t > 0 from strict gap at t = 0.
  rcases lt_or_eq_of_le htmem.1 with hpos | h0_eq
  · exact hpos
  · exfalso
    -- t = 0. The crossing equality becomes the equality at γ(0) = (1, 0).
    subst h0_eq
    have hγ0 := anisotropicHeisenbergParametricPath_zero lam' D'
    rw [hγ0] at heq
    simp only at heq
    -- heq : E_{M_0}(1, 0) = E_M(1, 0). But h0 : E_{M_0}(1, 0) < E_M(1, 0).
    rw [heq] at h0
    exact lt_irrefl _ h0

end LatticeSystem.Quantum
