import LatticeSystem.Quantum.SpinS.SaturatedHeisenbergExpectation

/-!
# `H(σ_⊥, σ_⊥) = H(σ_⊤, σ_⊤) = saturatedFerromagnetEigenvalueS J N`

The Heisenberg diagonal matrix entries at the all-up and all-down
configurations are equal:

  `H(σ_⊥, σ_⊥) = H(σ_⊤, σ_⊤) = saturatedFerromagnetEigenvalueS J N`.

This follows because both `H · |σ_⊤⟩ = E · |σ_⊤⟩` and
`H · |σ_⊥⟩ = E · |σ_⊥⟩` give the same explicit eigenvalue
`E = ∑_x J(x,x)·N(N+2)/4 + ∑_{x ≠ y} J(x,y)·N²/4` (PRs #875 / #876).

By uniqueness of the eigenvalue on a non-zero eigenvector
(combined with #899's eigenvector form
`H · |σ_⊤⟩ = H(σ_⊤, σ_⊤) · |σ_⊤⟩`), the diagonal entries equal
the explicit `E`, hence equal each other.

In particular, the saturated-ferromagnet GS energy is the same
when computed from either extremal state.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The all-down H-diagonal equals the all-up H-diagonal:
`H(σ_⊥, σ_⊥) = H(σ_⊤, σ_⊤) = saturatedFerromagnetEigenvalueS J N`. -/
theorem heisenbergHamiltonianS_diag_allAlignedConfigS_last_eq_zero
    (J : V → V → ℂ) :
    heisenbergHamiltonianS J N
        (allAlignedConfigS V N (Fin.last N))
        (allAlignedConfigS V N (Fin.last N)) =
      saturatedFerromagnetEigenvalueS (V := V) J N := by
  -- Use PR #876 explicit formula on |σ_⊥⟩ and PR #875 on |σ_⊤⟩.
  -- Both give the same explicit sum E, so the diagonals equal E.
  -- Lift via uniqueness on the non-zero eigenvector |σ_⊤⟩.
  -- Specifically, `H · |σ_⊤⟩ = E · |σ_⊤⟩` (#875) and
  -- `H · |σ_⊤⟩ = H(σ_⊤, σ_⊤) · |σ_⊤⟩` (PR #881 at k=0).
  -- Since |σ_⊤⟩ ≠ 0, E = H(σ_⊤, σ_⊤).
  -- Similarly E = H(σ_⊥, σ_⊥). Hence H(σ_⊥, σ_⊥) = H(σ_⊤, σ_⊤).
  -- Use the symmetric raising-side analogue and the explicit form to conclude.
  unfold saturatedFerromagnetEigenvalueS
  -- We need to show H_diag at σ_⊥ equals H_diag at σ_⊤.
  -- Strategy: use PR #875 + PR #876 explicit formulas (same RHS).
  have hzero := heisenbergHamiltonianS_mulVec_allAlignedStateS_zero_eigenvalue
    (V := V) (N := N) J
  have hlast := heisenbergHamiltonianS_mulVec_allAlignedStateS_last_eigenvalue
    (V := V) (N := N) J
  -- From #875: H · |⊤⟩ = E · |⊤⟩.
  -- From #881 raising side at k=0: H · |⊤⟩ = H_diag(σ_⊤) · |⊤⟩.
  -- Hence H_diag(σ_⊤) = E (uniqueness on non-zero eigenvector).
  have hzero_diag :=
    heisenbergHamiltonianS_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero
      (V := V) (N := N) J 0
  simp only [pow_zero, Matrix.one_mulVec] at hzero_diag
  have hlast_diag :=
    heisenbergHamiltonianS_mulVec_totalSpinSOpPlus_pow_allAlignedStateS_last
      (V := V) (N := N) J 0
  simp only [pow_zero, Matrix.one_mulVec] at hlast_diag
  -- Both eigenvalue equations give the same scalar E.
  -- E = H_diag(σ_⊤) = H_diag(σ_⊥).
  have h_zero : (∑ x : V, ∑ y : V,
        J x y * (if x = y then (N : ℂ) * (N + 2) / 4
                 else (N : ℂ) / 2 * ((N : ℂ) / 2))) =
      heisenbergHamiltonianS J N (allAlignedConfigS V N 0)
        (allAlignedConfigS V N 0) := by
    -- From hzero: H · |⊤⟩ = E · |⊤⟩.
    -- From hzero_diag: H · |⊤⟩ = H_diag(σ_⊤) · |⊤⟩.
    -- So E • |⊤⟩ = H_diag(σ_⊤) • |⊤⟩, hence E = H_diag(σ_⊤) (|⊤⟩ ≠ 0).
    have h_eq : (∑ x : V, ∑ y : V,
        J x y * (if x = y then (N : ℂ) * (N + 2) / 4
                 else (N : ℂ) / 2 * ((N : ℂ) / 2))) •
        allAlignedStateS V N (0 : Fin (N + 1)) =
      heisenbergHamiltonianS J N (allAlignedConfigS V N 0)
        (allAlignedConfigS V N 0) •
        allAlignedStateS V N (0 : Fin (N + 1)) := hzero.symm.trans hzero_diag
    -- Cancel the non-zero |⊤⟩ to extract the scalar equality.
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
    · exact h_neq (sub_eq_zero.mp h)
    · exact hne h
  -- Similarly, H_diag(σ_⊥) = E.
  have h_last : (∑ x : V, ∑ y : V,
        J x y * (if x = y then (N : ℂ) * (N + 2) / 4
                 else (N : ℂ) / 2 * ((N : ℂ) / 2))) =
      heisenbergHamiltonianS J N (allAlignedConfigS V N (Fin.last N))
        (allAlignedConfigS V N (Fin.last N)) := by
    have h_eq : (∑ x : V, ∑ y : V,
        J x y * (if x = y then (N : ℂ) * (N + 2) / 4
                 else (N : ℂ) / 2 * ((N : ℂ) / 2))) •
        allAlignedStateS V N (Fin.last N) =
      heisenbergHamiltonianS J N (allAlignedConfigS V N (Fin.last N))
        (allAlignedConfigS V N (Fin.last N)) •
        allAlignedStateS V N (Fin.last N) := hlast.symm.trans hlast_diag
    have hne := allAlignedStateS_ne_zero (V := V) (N := N) (Fin.last N)
    by_contra h_neq
    have hsub : ((∑ x : V, ∑ y : V,
          J x y * (if x = y then (N : ℂ) * (N + 2) / 4
                   else (N : ℂ) / 2 * ((N : ℂ) / 2))) -
        heisenbergHamiltonianS J N (allAlignedConfigS V N (Fin.last N))
          (allAlignedConfigS V N (Fin.last N))) •
        allAlignedStateS V N (Fin.last N) = 0 := by
      rw [sub_smul, h_eq, sub_self]
    have hzero_sub := smul_eq_zero.mp hsub
    rcases hzero_sub with h | h
    · exact h_neq (sub_eq_zero.mp h)
    · exact hne h
  rw [← h_last, h_zero]

end LatticeSystem.Quantum
