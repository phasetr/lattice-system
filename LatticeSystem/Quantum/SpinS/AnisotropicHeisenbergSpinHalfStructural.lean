import LatticeSystem.Quantum.SpinS.BareSubmatrixFinrankLeOneAtMinStructural
import LatticeSystem.Quantum.SpinS.BareAnisotropicMinLeTwo

/-!
# Spin-1/2 anisotropic `Ĥ` eigenspace `finrank ℂ ≤ 2` (TRULY UNCONDITIONAL)

Issue #3887 (Tasaki §2.5 Theorem 2.4, `h_intermediate` vacuous-at-N=1 fix).

**(#3887.8) FINAL CAPSTONE**: spin-1/2 ground-state degeneracy `≤ 2` for the
bare anisotropic Hamiltonian `Ĥ` at `N = 1`, **truly unconditional** (without
the inherited `h_intermediate` caveat that made the original (j.13.i) PR #3885
vacuous at N=1).

Combines:
- (#3887.7) structural bare submatrix `finrank ≤ 1 at hermitianMinEigenvalue`
  using `hN : 1 ≤ N`.
- (j.12) #3870 `spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_at_min_block_mins`
  spin-1/2 capstone.

At `N = 1`, `hN : 1 ≤ N` is trivially satisfied — the structural chain has no
vacuous gaps, unlike the original `h_intermediate`-bearing chain.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **(#3887.8) Spin-1/2 anisotropic `Ĥ` eigenspace `≤ 2` (TRULY UNCONDITIONAL)**.

Final closure of the (j.13)/(#3887) chain — the spin-1/2 ground-state
degeneracy bound for the Mattis-Nishimori anisotropic AFM Hamiltonian Tasaki
§2.5 Theorem 2.4, with no `h_intermediate` vacuity. -/
theorem spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_truly_unconditional
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (1 + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)] :
    finrank ℂ (End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J lam D 1))
      ((min
          (hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := 1) hJim hlam hDim 0))
          (hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := 1) hJim hlam hDim 1)) : ℝ) : ℂ)) ≤ 2 := by
  -- hN : 1 ≤ N at N = 1.
  have hN : (1 : ℕ) ≤ 1 := le_refl 1
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
  -- (j.12) capstone for spin-1/2.
  exact spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_at_min_block_mins
    hJim hlam hDim hJself h0 h1

end LatticeSystem.Quantum
