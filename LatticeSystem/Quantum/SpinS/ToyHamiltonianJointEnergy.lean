import LatticeSystem.Quantum.SpinS.ToyHamiltonianCasimir

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toy-Hamiltonian energy on a joint Casimir eigenvector

Scaffold for the toy-ground-state predicted-Casimir witness (Issue #3658, the
final obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

Since `Ĥ_toy = (Ŝ_tot)² − (Ŝ_A)² − (Ŝ_¬A)²`
(`heisenbergToyHamiltonianS_eq_casimir_diff`), a simultaneous eigenvector of the
three Casimirs at `(γ_tot, γ_A, γ_B)` is a `Ĥ_toy`-eigenvector at
`γ_tot − γ_A − γ_B`.  This is the energy formula underlying the variational
identification of the toy ground state's predicted total Casimir.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Toy energy on a joint Casimir eigenvector**: if `Ψ` is a simultaneous
eigenvector of `(Ŝ_tot)²`, `(Ŝ_A)²`, `(Ŝ_¬A)²` at `(γ_tot, γ_A, γ_B)`, then
`Ĥ_toy Ψ = (γ_tot − γ_A − γ_B) Ψ`. -/
theorem heisenbergToyHamiltonianS_mulVec_of_joint_casimir_eigenvector (A : Λ → Bool)
    {γ_tot γ_A γ_B : ℂ} {Ψ : (Λ → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared Λ N).mulVec Ψ = γ_tot • Ψ)
    (hA : (sublatticeSpinSquaredS N A).mulVec Ψ = γ_A • Ψ)
    (hB : (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec Ψ = γ_B • Ψ) :
    (heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec Ψ = (γ_tot - γ_A - γ_B) • Ψ := by
  rw [heisenbergToyHamiltonianS_eq_casimir_diff, Matrix.sub_mulVec, Matrix.sub_mulVec,
    htot, hA, hB, sub_smul, sub_smul]

end LatticeSystem.Quantum
