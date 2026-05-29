import LatticeSystem.Quantum.SpinS.BareSubmatrixFinrankLeOneAtMin
import LatticeSystem.Quantum.SpinS.BareAnisotropicMinLeTwo

/-!
# Spin-1/2 anisotropic `Ĥ` eigenspace `finrank ℂ ≤ 2` (PF=min UNCONDITIONAL)

Issue #3871 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

**(j.13.i) CAPSTONE**: Tasaki §2.5 Theorem 2.4 ground-state degeneracy bound
`finrank ℂ ≤ 2` for the bare anisotropic Hamiltonian `Ĥ` at `N = 1` (spin-1/2)
*unconditional on the Collatz-Wielandt PF=min identification*.

Combines:
- (j.13.h.3) #3884: bare submatrix `finrank ≤ 1 at hermitianMinEigenvalue`
  *unconditionally on PF=min* (the deferred identification is now discharged
  via the full (j.13.a)-(j.13.h) chain).
- (j.12) #3870 `spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_at_min_block_mins`:
  capstone that combines per-parity (0, 1) finrank ≤ 1 bounds via axis-swap unitary
  to give the full bare anisotropic Ĥ ≤ 2.

## ⚠ Vacuous-at-N=1 caveat (inherited from the chain)

The `h_intermediate` hypothesis (`∀ τ : Λ → Fin (N+1), ∀ x : Λ, ∃ z, A z ≠ A x ∧
(τ z).val < N`) is *unsatisfiable at N = 1* when both sublattices are non-empty:
taking the all-`1` state `τ ≡ Fin.last 1` forces every site to fail `(τ z).val < 1`.
Consequently this theorem is *vacuously true at N = 1*, and the spin-1/2 case
remains effectively open as a *non-vacuous* mathematical statement.

This is a pre-existing limitation of the entire (j.1)-(j.13) PF chain — the
`h_intermediate` hypothesis was designed for general `N ≥ 2` where saturated
configurations leave room for bipartite raise/lower moves. A *non-vacuous*
spin-1/2 closure of Theorem 2.4 requires either:
- replacing `h_intermediate` with a structural property of the lattice/coupling
  that automatically holds, or
- a separate spin-1/2-specific irreducibility argument bypassing
  `parityReachableS_total`.

Tracked as a follow-up after the (j.13) chain merge.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **(j.13.i) Spin-1/2 anisotropic `Ĥ` `finrank ℂ ≤ 2` (UNCONDITIONAL)**.

Tasaki §2.5 Theorem 2.4 ground-state degeneracy bound: the eigenspace of the
bare anisotropic Hamiltonian `anisotropicHeisenbergS J lam D 1` at the smaller
of the two per-parity Hermitian minimum eigenvalues has complex dimension
`≤ 2`, *unconditionally* (with no remaining `ν = hermitianMinEigenvalue`
hypothesis). -/
theorem spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_unconditional
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
    (h_intermediate : ∀ τ : Λ → Fin (1 + 1), ∀ x : Λ,
      ∃ z, A z ≠ A x ∧ (τ z).val < 1)
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
  -- (j.13.h.3) at parity 0.
  have h0 :=
    axisSwappedAnisotropicHeisenbergS_submatrix_finrank_le_one_at_hermitianMinEigenvalue
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos hc_strict hA_ne hB_ne
      h_intermediate 0
  -- (j.13.h.3) at parity 1.
  have h1 :=
    axisSwappedAnisotropicHeisenbergS_submatrix_finrank_le_one_at_hermitianMinEigenvalue
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos hc_strict hA_ne hB_ne
      h_intermediate 1
  -- (j.12) capstone for spin-1/2.
  exact spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_at_min_block_mins
    hJim hlam hDim hJself h0 h1

end LatticeSystem.Quantum
