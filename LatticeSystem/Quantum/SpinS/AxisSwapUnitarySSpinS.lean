import LatticeSystem.Quantum.SpinS.AxisSwapUnitarySSpinSCore

/-!
# General spin-S axis-swap unitary (Tasaki §2.5 Theorem 2.4)

Issue #3739. The `AxisSwapUnitaryS N` interface is made non-vacuous for every
`N ≥ 0` by specialising `spinSRot1 N (π/2) = exp(-iπ Ŝ¹/2)` to the `π/2`
rotation about spin-axis 1.

The conjugation lemmas
`spinSRot1 N (π/2) * Ŝ² * spinSRot1 N (-π/2) = Ŝ³` and
`spinSRot1 N (π/2) * Ŝ³ * spinSRot1 N (-π/2) = -Ŝ²`
are proven via the **ladder-eigenvector approach**: the ladder operators
`L⁺ := Ŝ² + i Ŝ³` and `L⁻ := Ŝ² - i Ŝ³` are eigenvectors of the inner
derivation `ad_{Ŝ¹}` with eigenvalues `+1` and `-1` respectively. This is
witnessed by the single commutation identities
`Ŝ¹ L⁺ = L⁺ (Ŝ¹ + 1)` and `Ŝ¹ L⁻ = L⁻ (Ŝ¹ - 1)`,
which propagate to `Ŝ¹^n L^± = L^± (Ŝ¹ ± 1)^n` by induction.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix NormedSpace Complex

variable {N : ℕ}
variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **General spin-S axis-swap degeneracy equality**: the concrete
`axisSwapUnitarySSpinS N` instance identifies every `μ`-eigenspace dimension of
the anisotropic Hamiltonian and its axis-swapped image. -/
theorem axisSwapUnitarySSpinS_anisotropic_axisSwapped_eigenspace_finrank_eq
    {N : ℕ} (J : Λ → Λ → ℂ) (lam D μ : ℂ) :
    Module.finrank ℂ (Module.End.eigenspace
        (Matrix.toLin' (axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N)) μ) =
      Module.finrank ℂ (Module.End.eigenspace
        (Matrix.toLin' (anisotropicHeisenbergS (Λ := Λ) J lam D N)) μ) :=
  (axisSwapUnitarySSpinS N).anisotropic_axisSwapped_eigenspace_finrank_eq J lam D μ

/-- **General spin-S conditional bare `Ĥ` `≤ 2` bound from parity-block intersections**:
specializes the `AxisSwapUnitaryS N`-parameterized wrapper to the concrete
`axisSwapUnitarySSpinS N` rotation. -/
theorem anisotropicHeisenbergS_eigenspace_finrank_le_two_of_blocks_le_one_general
    {N : ℕ} {J : Λ → Λ → ℂ} (hJself : ∀ x, J x x = 0) (lam D μ : ℂ)
    (heven : Module.finrank ℂ ↥(Module.End.eigenspace
        (Matrix.toLin' (axisSwappedAnisotropicHeisenbergS J lam D N)) μ ⊓
      Module.End.eigenspace (Matrix.toLin' (magParityDiagS Λ N)) 1) ≤ 1)
    (hodd : Module.finrank ℂ ↥(Module.End.eigenspace
        (Matrix.toLin' (axisSwappedAnisotropicHeisenbergS J lam D N)) μ ⊓
      Module.End.eigenspace (Matrix.toLin' (magParityDiagS Λ N)) (-1)) ≤ 1) :
    Module.finrank ℂ (Module.End.eigenspace
        (Matrix.toLin' (anisotropicHeisenbergS (Λ := Λ) J lam D N)) μ) ≤ 2 :=
  anisotropicHeisenbergS_eigenspace_finrank_le_two_of_blocks_le_one
    (axisSwapUnitarySSpinS N) hJself lam D μ heven hodd

/-- **General spin-S conditional bare `Ĥ` `≤ 2` bound from submatrix block simplicity**:
specializes the submatrix-block wrapper to the concrete `axisSwapUnitarySSpinS N`
rotation. -/
theorem anisotropicHeisenbergS_eigenspace_finrank_le_two_of_submatrix_blocks_le_one_general
    {N : ℕ} {J : Λ → Λ → ℂ} (hJself : ∀ x, J x x = 0) (lam D μ : ℂ)
    (h0 : Module.finrank ℂ ↥(Module.End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N).submatrix
          (fun σ : parityConfigS Λ N 0 => σ.1)
          (fun σ : parityConfigS Λ N 0 => σ.1))) μ) ≤ 1)
    (h1 : Module.finrank ℂ ↥(Module.End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N).submatrix
          (fun σ : parityConfigS Λ N 1 => σ.1)
          (fun σ : parityConfigS Λ N 1 => σ.1))) μ) ≤ 1) :
    Module.finrank ℂ (Module.End.eigenspace
        (Matrix.toLin' (anisotropicHeisenbergS (Λ := Λ) J lam D N)) μ) ≤ 2 :=
  anisotropicHeisenbergS_eigenspace_finrank_le_two_of_submatrix_blocks_le_one
    (axisSwapUnitarySSpinS N) hJself lam D μ h0 h1

/-- **General spin-S bare `Ĥ` `≤ 2` bound at `min(per-block mins)`**: specializes the
axis-swap min-block wrapper to the concrete `axisSwapUnitarySSpinS N` rotation. -/
theorem anisotropicHeisenbergS_eigenspace_finrank_le_two_at_min_block_mins_general
    {N : ℕ} {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJ : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hD : D.im = 0)
    (hJself : ∀ x, J x x = 0)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    (h0 : Module.finrank ℂ ↥(Module.End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N).submatrix
          (fun σ : parityConfigS Λ N 0 => σ.1)
          (fun σ : parityConfigS Λ N 0 => σ.1)))
          ((hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := N) hJ hlam hD 0) : ℂ))) ≤ 1)
    (h1 : Module.finrank ℂ ↥(Module.End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N).submatrix
          (fun σ : parityConfigS Λ N 1 => σ.1)
          (fun σ : parityConfigS Λ N 1 => σ.1)))
          ((hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := N) hJ hlam hD 1) : ℂ))) ≤ 1) :
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J lam D N))
      ((min
          (hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := N) hJ hlam hD 0))
          (hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := N) hJ hlam hD 1)) : ℝ) : ℂ)) ≤ 2 :=
  anisotropicHeisenbergS_eigenspace_finrank_le_two_at_min_block_mins
    (axisSwapUnitarySSpinS N) hJ hlam hD hJself h0 h1

/-- **General spin-S Hermitian minimum equality under axis swap**: specializes the
`AxisSwapUnitaryS N` minimum-eigenvalue bridge to `axisSwapUnitarySSpinS N`. -/
theorem axisSwapUnitarySSpinS_hermitianMinEigenvalue_anisotropic_eq_axisSwapped
    {N : ℕ} {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    {lam : ℂ} (hlam : star lam = lam) {D : ℂ} (hD : star D = D)
    [Nonempty (Λ → Fin (N + 1))] :
    hermitianMinEigenvalue
        (anisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) hJ hlam hD N) =
      hermitianMinEigenvalue
        (axisSwappedAnisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) hJ hlam hD N) :=
  (axisSwapUnitarySSpinS N).hermitianMinEigenvalue_anisotropic_eq_axisSwapped hJ hlam hD

/-- **Tasaki §2.5 Theorem 2.4 obligation (1) general spin-S, TRULY UNCONDITIONAL closure.**
For every `N ≥ 1`, the bare anisotropic Hamiltonian on a general bipartite lattice has eigenspace
`finrank ℂ ≤ 2` at `min(ν_0, ν_1)`, unconditional on any `AxisSwapUnitaryS N` hypothesis — supplied
by the `axisSwapUnitarySSpinS N` instance above. -/
theorem anisotropicHeisenbergS_eigenspace_finrank_le_two_unconditional_general
    {N : ℕ} (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)] :
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J lam D N))
      ((min
          (hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := N) hJim hlam hDim 0))
          (hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := N) hJim hlam hDim 1)) : ℝ) : ℂ)) ≤ 2 :=
  anisotropicHeisenbergS_eigenspace_finrank_le_two_truly_unconditional
    (axisSwapUnitarySSpinS N) A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos
    hc_strict hA_ne hB_ne hN

end LatticeSystem.Quantum
