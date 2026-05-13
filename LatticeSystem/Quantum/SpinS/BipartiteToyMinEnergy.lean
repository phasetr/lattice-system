import LatticeSystem.Quantum.SpinS.ToyHamiltonianJointEigenspace
import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeel

/-!
# Predicted toy-Hamiltonian ground-state subspace and minimum energy

For a bipartite system `(Λ, A)` with `|A| ≥ |¬A|`, Tasaki §2.5
Theorem 2.3 predicts the toy-Hamiltonian ground state has

  * `(Ŝ_A)²` eigenvalue `s_A(s_A + 1)` (maximum, `s_A = |A|·N/2`),
  * `(Ŝ_{¬A})²` eigenvalue `s_B(s_B + 1)` (maximum, `s_B = |¬A|·N/2`),
  * `(Ŝ_tot)²` eigenvalue `(s_A − s_B)(s_A − s_B + 1)` (minimum
    subject to the sublattice maxima, via the angular-momentum
    triangle inequality).

The joint eigenspace at these three values is the **predicted
ground-state subspace** of the toy Hamiltonian. Its
`Ĥ_toy_S`-eigenvalue is computed directly from the Casimir
decomposition:

  `(s_A − s_B)(s_A − s_B + 1) − s_A(s_A + 1) − s_B(s_B + 1)
     = −2 s_B (s_A + 1)
     = −|A|·|¬A|·N²/2 − |¬A|·N`.

This file packages:

1. the **predicted minimum eigenvalue formula** as a
   `def` `bipartiteToyMinEnergyPredicted`;
2. the **predicted ground-state subspace** as the joint Casimir
   eigenspace at the three target values;
3. the **eigenspace inclusion** `predicted_GS_subspace ≤
   eigenspace(Ĥ_toy_S)_{predicted_min}`, an immediate corollary of
   PR #2775's `_jointCasimirEigenspace_le_eigenspace`.

The minimality of the predicted eigenvalue (i.e. the variational
lower bound `H_toy ≥ predicted_min · I` on a fixed magnetization
sector with non-empty bipartition) is the next γ-4 milestone, not
yet established here.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Predicted toy-Hamiltonian minimum energy** for the bipartite
case `|A| ≥ |¬A|`: `(s_A − s_B)(s_A − s_B + 1) − s_A(s_A + 1) −
s_B(s_B + 1)`. Algebraically equals `−2 s_B (s_A + 1)
= −|A|·|¬A|·N²/2 − |¬A|·N`. -/
noncomputable def bipartiteToyMinEnergyPredicted
    (A : Λ → Bool) (N : ℕ) : ℂ :=
  let cA : ℂ := ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ)
  let cB : ℂ := ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)
  let s_A : ℂ := cA * ((N : ℂ) / 2)
  let s_B : ℂ := cB * ((N : ℂ) / 2)
  (s_A - s_B) * ((s_A - s_B) + 1) - s_A * (s_A + 1) - s_B * (s_B + 1)

omit [DecidableEq Λ] in
/-- **Simplified form** of `bipartiteToyMinEnergyPredicted`:
`-|A|·|¬A|·N²/2 - |¬A|·N`. Direct ring computation. -/
theorem bipartiteToyMinEnergyPredicted_eq_simplified
    (A : Λ → Bool) (N : ℕ) :
    bipartiteToyMinEnergyPredicted (Λ := Λ) A N =
      -(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          ((N : ℂ) * (N : ℂ)) / 2) -
        (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          (N : ℂ)) := by
  unfold bipartiteToyMinEnergyPredicted
  ring

/-- **Predicted ground-state subspace** of the toy Hamiltonian
for `|A| ≥ |¬A|`: the joint eigenspace of `((Ŝ_tot)², (Ŝ_A)²,
(Ŝ_{¬A})²)` at the three target eigenvalues. -/
noncomputable def bipartiteToyGroundStateSubspacePredicted
    (A : Λ → Bool) (N : ℕ) :
    Submodule ℂ ((Λ → Fin (N + 1)) → ℂ) :=
  let cA : ℂ := ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ)
  let cB : ℂ := ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)
  let s_A : ℂ := cA * ((N : ℂ) / 2)
  let s_B : ℂ := cB * ((N : ℂ) / 2)
  Module.End.eigenspace (totalSpinSSquared Λ N).mulVecLin
      ((s_A - s_B) * ((s_A - s_B) + 1))
    ⊓ Module.End.eigenspace (sublatticeSpinSquaredS N A).mulVecLin
        (s_A * (s_A + 1))
    ⊓ Module.End.eigenspace
        (sublatticeSpinSquaredS N (fun x => !A x)).mulVecLin
        (s_B * (s_B + 1))

/-- **Predicted ground-state subspace lies in the predicted
minimum-energy eigenspace of the toy Hamiltonian**: direct
application of PR #2775's
`heisenbergToyHamiltonianS_jointCasimirEigenspace_le_eigenspace`
at the predicted target eigenvalues. The Casimir-decomposition
formula gives the `Ĥ_toy_S` eigenvalue at this joint subspace as
`(s_A − s_B)(s_A − s_B + 1) − s_A(s_A + 1) − s_B(s_B + 1) =
bipartiteToyMinEnergyPredicted A N`. -/
theorem bipartiteToyGroundStateSubspacePredicted_le_heisenbergToyHamiltonianS_eigenspace
    (A : Λ → Bool) (N : ℕ) :
    bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N ≤
      Module.End.eigenspace
        (heisenbergToyHamiltonianS (Λ := Λ) A N).mulVecLin
        (bipartiteToyMinEnergyPredicted (Λ := Λ) A N) := by
  unfold bipartiteToyGroundStateSubspacePredicted bipartiteToyMinEnergyPredicted
  simp only []
  exact heisenbergToyHamiltonianS_jointCasimirEigenspace_le_eigenspace
    (Λ := Λ) A N _ _ _

end LatticeSystem.Quantum
