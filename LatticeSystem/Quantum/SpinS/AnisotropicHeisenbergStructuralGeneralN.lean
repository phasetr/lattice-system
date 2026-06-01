import LatticeSystem.Quantum.SpinS.BareSubmatrixFinrankLeOneAtMinStructural
import LatticeSystem.Quantum.SpinS.BareAnisotropicMinLeTwo

/-!
# General-N anisotropic `Ĥ` eigenspace `finrank ℂ ≤ 2` (TRULY UNCONDITIONAL)

Issue #3887 extension (Tasaki §2.5 Theorem 2.4, general spin-S, `N ≥ 1`).

For general `N ≥ 1` with an `AxisSwapUnitaryS N` instance, the bare anisotropic
Hamiltonian `anisotropicHeisenbergS J lam D N` has eigenspace `finrank ℂ ≤ 2`
at `min(ν_0, ν_1) : ℂ`, **truly unconditional** on both `h_intermediate` and
the Collatz-Wielandt PF=min identification.

Specialises to spin-1/2 via `axisSwapUnitarySpinHalf` (already in
`AnisotropicHeisenbergSpinHalfStructural.lean` as a separate theorem).

For concrete general spin-S, `AxisSwapUnitarySSpinS.lean` now supplies the
`π/2` axis-1 rotation instance `axisSwapUnitarySSpinS N` and a no-argument
wrapper for this capstone.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **General-N anisotropic `Ĥ` `finrank ℂ ≤ 2` (TRULY UNCONDITIONAL)**.

Given `(G : AxisSwapUnitaryS N)` and `hN : 1 ≤ N` along with the canonical
hypotheses, the bare anisotropic Hamiltonian on a general bipartite lattice
has eigenspace `finrank ℂ ≤ 2` at `min(ν_0, ν_1)`. -/
theorem anisotropicHeisenbergS_eigenspace_finrank_le_two_truly_unconditional
    (G : AxisSwapUnitaryS N)
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
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
    finrank ℂ (End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J lam D N))
      ((min
          (hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := N) hJim hlam hDim 0))
          (hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := N) hJim hlam hDim 1)) : ℝ) : ℂ)) ≤ 2 := by
  -- (#3887.7) at parity 0.
  have h0 :=
    axisSwappedAnisotropicHeisenbergS_submatrix_finrank_le_one_at_hermitianMinEigenvalue
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos hc_strict hA_ne hB_ne
      hN 0
  -- (#3887.7) at parity 1.
  have h1 :=
    axisSwappedAnisotropicHeisenbergS_submatrix_finrank_le_one_at_hermitianMinEigenvalue
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos hc_strict hA_ne hB_ne
      hN 1
  -- (j.12) general capstone via AxisSwapUnitaryS N.
  exact anisotropicHeisenbergS_eigenspace_finrank_le_two_at_min_block_mins
    G hJim hlam hDim hJself h0 h1

end LatticeSystem.Quantum
