import LatticeSystem.Quantum.SpinS.ToyHamiltonianCasimir

/-!
# Toy Hamiltonian eigenvalue on simultaneous Casimir eigenvectors

For a state `v` on the multi-site spin-`S` Hilbert space that is a
simultaneous eigenvector of the three Casimirs `(Ŝ_tot)²`, `(Ŝ_A)²`,
`(Ŝ_{¬A})²` with eigenvalues `α`, `β_A`, `β_B` respectively, the
spin-`S` MLM toy Hamiltonian acts on `v` as the scalar
`(α − β_A − β_B)`:

  `Ĥ_toy_S · v = (α − β_A − β_B) • v`.

This is a direct corollary of the Casimir decomposition
`Ĥ_toy_S = (Ŝ_tot)² − (Ŝ_A)² − (Ŝ_{¬A})²` (PR #1057 /
`heisenbergToyHamiltonianS_eq_casimir_diff`) and the linearity of
matrix-vector multiplication.

In Tasaki §2.5 Theorem 2.3 (γ-4), minimising the toy Hamiltonian
energy amounts to maximising `β_A + β_B` (capped at
`s_A(s_A+1) + s_B(s_B+1)` with `s_A = |A|·N/2`, `s_B = |¬A|·N/2`)
and minimising `α` (bounded below by the triangle inequality at
`(s_A − s_B)(s_A − s_B + 1)`). The minimum-energy configuration
gives `S_tot = ||A| − |¬A||·S`, the Theorem 2.3 prediction.

This file packages the joint-eigenvalue formula as a single
reusable lemma; subsequent γ-4 PRs will combine it with the
Casimir-eigenvalue bounds to extract the Theorem 2.3 ground-state
energy and total-spin value.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Toy Hamiltonian eigenvalue on simultaneous Casimir eigenvectors**:
for `v` a joint eigenvector of `(Ŝ_tot)²`, `(Ŝ_A)²`, `(Ŝ_{¬A})²`
with eigenvalues `α, β_A, β_B`, the toy Hamiltonian acts as the
scalar `(α − β_A − β_B)`:

  `Ĥ_toy_S · v = (α − β_A − β_B) • v`.

Direct from `heisenbergToyHamiltonianS_eq_casimir_diff` and
`Matrix.sub_mulVec`. -/
theorem heisenbergToyHamiltonianS_mulVec_of_jointCasimirEigenvector
    (A : Λ → Bool) (N : ℕ)
    (v : (Λ → Fin (N + 1)) → ℂ) (α β_A β_B : ℂ)
    (h_tot : (totalSpinSSquared Λ N).mulVec v = α • v)
    (h_A : (sublatticeSpinSquaredS N A).mulVec v = β_A • v)
    (h_B : (sublatticeSpinSquaredS N (fun x => !A x)).mulVec v =
      β_B • v) :
    (heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec v =
      (α - β_A - β_B) • v := by
  rw [heisenbergToyHamiltonianS_eq_casimir_diff N A,
      Matrix.sub_mulVec, Matrix.sub_mulVec,
      h_tot, h_A, h_B]
  rw [sub_smul, sub_smul]

/-- **Expectation value form**: for a (not necessarily eigenvector)
state `v` with simultaneous Casimir eigenvalues `(α, β_A, β_B)`,
the toy Hamiltonian expectation is `(α − β_A − β_B) · ⟨v, v⟩`.
Direct corollary of the eigenvalue identity via `dotProduct_smul`. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_via_joint
    (A : Λ → Bool) (N : ℕ)
    (v : (Λ → Fin (N + 1)) → ℂ) (α β_A β_B : ℂ)
    (h_tot : (totalSpinSSquared Λ N).mulVec v = α • v)
    (h_A : (sublatticeSpinSquaredS N A).mulVec v = β_A • v)
    (h_B : (sublatticeSpinSquaredS N (fun x => !A x)).mulVec v =
      β_B • v) :
    dotProduct (star v)
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec v) =
      (α - β_A - β_B) * dotProduct (star v) v := by
  rw [heisenbergToyHamiltonianS_mulVec_of_jointCasimirEigenvector
        A N v α β_A β_B h_tot h_A h_B,
      dotProduct_smul, smul_eq_mul]

end LatticeSystem.Quantum
