import LatticeSystem.Quantum.SpinS.SaturatedHeisenbergSymmetric

/-!
# Explicit form of `saturatedFerromagnetEigenvalueS J N`

The saturated-FM Heisenberg eigenvalue admits the explicit form

  `saturatedFerromagnetEigenvalueS J N
    = ∑_x J(x, x) · N(N+2)/4 + ∑_{x ≠ y} J(x, y) · (N/2)²`,

i.e., the coupling-weighted sum of single-site Casimir at diagonals
plus the squared z-eigenvalue contribution at off-diagonal pairs.

Direct from PR #875's `heisenbergHamiltonianS_mulVec_allAlignedStateS_zero_eigenvalue`
formula combined with the diagonal-entry uniqueness argument
(via PR #946's intermediate work).

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- `saturatedFerromagnetEigenvalueS J N` equals the explicit
combinatorial sum. -/
theorem saturatedFerromagnetEigenvalueS_explicit (J : V → V → ℂ) :
    saturatedFerromagnetEigenvalueS (V := V) J N =
      ∑ x : V, ∑ y : V,
        J x y * (if x = y then (N : ℂ) * (N + 2) / 4
                 else (N : ℂ) / 2 * ((N : ℂ) / 2)) := by
  -- From PR #946 derivation: H_diag(σ_⊤) = E (the explicit sum).
  -- Apply the same uniqueness argument here directly.
  unfold saturatedFerromagnetEigenvalueS
  -- Use #875 + uniqueness on |σ_⊤⟩ ≠ 0.
  have hzero := heisenbergHamiltonianS_mulVec_allAlignedStateS_zero_eigenvalue
    (V := V) (N := N) J
  have hzero_diag :=
    heisenbergHamiltonianS_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero
      (V := V) (N := N) J 0
  simp only [pow_zero, Matrix.one_mulVec] at hzero_diag
  have h_eq : (∑ x : V, ∑ y : V,
        J x y * (if x = y then (N : ℂ) * (N + 2) / 4
                 else (N : ℂ) / 2 * ((N : ℂ) / 2))) •
        allAlignedStateS V N (0 : Fin (N + 1)) =
      heisenbergHamiltonianS J N (allAlignedConfigS V N 0)
        (allAlignedConfigS V N 0) •
        allAlignedStateS V N (0 : Fin (N + 1)) := hzero.symm.trans hzero_diag
  have hne := allAlignedStateS_ne_zero (V := V) (N := N) (0 : Fin (N + 1))
  by_contra h_neq
  -- (E - H_diag) • |⊤⟩ = 0; with |⊤⟩ ≠ 0, E - H_diag = 0, contradiction.
  have hsub : ((∑ x : V, ∑ y : V,
        J x y * (if x = y then (N : ℂ) * (N + 2) / 4
                 else (N : ℂ) / 2 * ((N : ℂ) / 2))) -
      heisenbergHamiltonianS J N (allAlignedConfigS V N 0)
        (allAlignedConfigS V N 0)) •
      allAlignedStateS V N (0 : Fin (N + 1)) = 0 := by
    rw [sub_smul, h_eq, sub_self]
  have hzero_sub := smul_eq_zero.mp hsub
  rcases hzero_sub with h | h
  · -- h: E - H_diag = 0, so E = H_diag, equivalently H_diag = E.
    have : heisenbergHamiltonianS J N (allAlignedConfigS V N 0)
        (allAlignedConfigS V N 0) =
      ∑ x : V, ∑ y : V,
        J x y * (if x = y then (N : ℂ) * (N + 2) / 4
                 else (N : ℂ) / 2 * ((N : ℂ) / 2)) :=
      (sub_eq_zero.mp h).symm
    exact h_neq this
  · exact hne h

end LatticeSystem.Quantum
