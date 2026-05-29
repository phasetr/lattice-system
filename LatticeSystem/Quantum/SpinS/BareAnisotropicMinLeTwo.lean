import LatticeSystem.Quantum.SpinS.BareAxisSwapMinLeTwo
import LatticeSystem.Quantum.SpinS.AxisSwapDegeneracy
import LatticeSystem.Quantum.SpinS.AxisSwapUnitarySpinHalf

/-!
# Bare anisotropic `Ĥ` eigenspace `finrank ℂ ≤ 2` at `min(per-block mins)`

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(i.8): wraps the bare `Ĥ'` `min(per-block mins) ≤ 2` (#3854) with the axis-swap unitary
equivalence (`anisotropic_axisSwapped_eigenspace_finrank_eq`, #3753 family) to lift
the bound to the bare anisotropic Hamiltonian `Ĥ`.

- General `N` version requires an `AxisSwapUnitaryS N` instance.
- Spin-1/2 (`N = 1`) instance via `axisSwapUnitarySpinHalf`.

This is the analogue of (g.5) #3837 with the per-block-min hypotheses (which feed
directly through the Hermitian spectral chain to give the unconditional bound at the
GS, once the PF eigenvalue is identified with `hermitianMinEigenvalue`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Bare anisotropic `Ĥ` eigenspace `≤ 2` at `min(per-block mins)`** via `AxisSwapUnitaryS N`. -/
theorem anisotropicHeisenbergS_eigenspace_finrank_le_two_at_min_block_mins
    (G : AxisSwapUnitaryS N)
    {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJ : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hD : D.im = 0)
    (hJself : ∀ x, J x x = 0)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    (h0 : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N).submatrix
          (fun σ : parityConfigS Λ N 0 => σ.1)
          (fun σ : parityConfigS Λ N 0 => σ.1)))
          ((hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := N) hJ hlam hD 0) : ℂ))) ≤ 1)
    (h1 : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N).submatrix
          (fun σ : parityConfigS Λ N 1 => σ.1)
          (fun σ : parityConfigS Λ N 1 => σ.1)))
          ((hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := N) hJ hlam hD 1) : ℂ))) ≤ 1) :
    finrank ℂ (End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J lam D N))
      ((min
          (hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := N) hJ hlam hD 0))
          (hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := N) hJ hlam hD 1)) : ℝ) : ℂ)) ≤ 2 := by
  rw [← G.anisotropic_axisSwapped_eigenspace_finrank_eq J lam D _]
  exact axisSwappedAnisotropicHeisenbergS_eigenspace_finrank_le_two_at_min_block_mins
    hJ hlam hD hJself h0 h1

/-- **Spin-1/2 instance** of the bare anisotropic `Ĥ` `≤ 2` at `min(per-block mins)`. -/
theorem spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_at_min_block_mins
    {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJ : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hD : D.im = 0)
    (hJself : ∀ x, J x x = 0)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (h0 : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D 1).submatrix
          (fun σ : parityConfigS Λ 1 0 => σ.1)
          (fun σ : parityConfigS Λ 1 0 => σ.1)))
          ((hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := 1) hJ hlam hD 0) : ℂ))) ≤ 1)
    (h1 : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D 1).submatrix
          (fun σ : parityConfigS Λ 1 1 => σ.1)
          (fun σ : parityConfigS Λ 1 1 => σ.1)))
          ((hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := 1) hJ hlam hD 1) : ℂ))) ≤ 1) :
    finrank ℂ (End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J lam D 1))
      ((min
          (hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := 1) hJ hlam hD 0))
          (hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := 1) hJ hlam hD 1)) : ℝ) : ℂ)) ≤ 2 :=
  anisotropicHeisenbergS_eigenspace_finrank_le_two_at_min_block_mins
    axisSwapUnitarySpinHalf hJ hlam hD hJself h0 h1

end LatticeSystem.Quantum
