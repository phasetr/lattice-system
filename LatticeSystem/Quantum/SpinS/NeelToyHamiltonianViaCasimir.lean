import LatticeSystem.Quantum.SpinS.ToyHamiltonianJointEigenvalue
import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelBasisVecS

/-!
# Néel-state toy Hamiltonian expectation via the Casimir decomposition

The Néel state `neelStateOfS A N` is a joint eigenvector of the
sublattice Casimirs `(Ŝ_A)²` and `(Ŝ_{¬A})²` at their maximum
eigenvalues `s_A(s_A+1)` and `s_B(s_B+1)` (where
`s_A = |A|·N/2, s_B = |¬A|·N/2`), but it is *not* an eigenvector of
`(Ŝ_tot)²` (the cross-sublattice term mixes total-spin sectors).

Using the closed form `Ĥ_toy_S = (Ŝ_tot)² − (Ŝ_A)² − (Ŝ_{¬A})²`
(PR #1056) and the sublattice eigenvector properties (PR #1067), we
obtain the Néel toy-Hamiltonian expectation in the form

  `⟨Φ_Néel|Ĥ_toy_S|Φ_Néel⟩
      = ⟨Φ_Néel|(Ŝ_tot)²|Φ_Néel⟩ − s_A(s_A+1) − s_B(s_B+1)`,

where the `(Ŝ_tot)²` expectation is given by PR #1093
(`neelStateOfS_totalSpinSSquared_expectation_via_general`):
`⟨(Ŝ_tot)²⟩_Néel = (s_A − s_B)² + (s_A + s_B)`. Combining yields
the well-known value `−2 s_A s_B = −|A|·|¬A|·N²/2`, matching the
existing direct computation
(`heisenbergToyHamiltonianS_apply_diag_neel`, PR #1070).

This file packages the alternative derivation as a `via_casimir`
form that ties the Néel expectation to the PR #2774 / PR #2775
joint-Casimir-eigenspace framework. It is useful as a sanity check
and as a building block for subsequent γ-4 PRs that will compare
the Néel expectation against the predicted toy-Hamiltonian ground-
state energy.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Néel toy-Hamiltonian expectation = `(Ŝ_tot)² expectation` −
sublattice Casimirs**: the Néel state's toy Hamiltonian expectation
splits as the `(Ŝ_tot)²` expectation minus the two sublattice
Casimir eigenvalues at their maximum values.

Proof: rewrite via `heisenbergToyHamiltonianS_eq_casimir_diff`
(PR #1056), apply `Matrix.sub_mulVec` to distribute, evaluate the
two sublattice Casimirs as eigenvectors using PR #1067 / PR #1067
complement, then `dotProduct_smul` packages into the desired
expectation form. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_eq_total_minus_sublattice_casimirs
    (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N)) =
      dotProduct (star (neelStateOfS A N))
          ((totalSpinSSquared Λ N).mulVec (neelStateOfS A N)) -
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2) *
            (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                ((N : ℂ) / 2) + 1)) *
          dotProduct (star (neelStateOfS A N)) (neelStateOfS A N) -
        (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2) *
            (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                ((N : ℂ) / 2) + 1)) *
          dotProduct (star (neelStateOfS A N)) (neelStateOfS A N) := by
  rw [heisenbergToyHamiltonianS_eq_casimir_diff N A]
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec]
  rw [sublatticeSpinSquaredS_mulVec_neelStateOfS A N,
      sublatticeSpinSquaredS_complement_mulVec_neelStateOfS A N]
  rw [dotProduct_sub, dotProduct_sub, dotProduct_smul, dotProduct_smul,
      smul_eq_mul, smul_eq_mul]

end LatticeSystem.Quantum
