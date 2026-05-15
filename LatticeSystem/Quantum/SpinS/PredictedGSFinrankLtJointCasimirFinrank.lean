import LatticeSystem.Quantum.SpinS.JointSublatticeCasimirStrictSupsetPredictedGS

/-!
# Predicted GS subspace finrank < joint sublattice-Casimir eigenspace
finrank at non-degenerate

PR #2923 established the strict inclusion
`bipartiteToyGroundStateSubspacePredicted A N ⊊ joint Casimir
eigenspace` at non-degenerate (`|¬A| ≤ |A|`). In the finite-
dimensional ambient space `(Λ → Fin (N+1)) → ℂ`, strict
inclusion of submodules implies strict inequality of `finrank`.

The "extra" subspace in the joint Casimir eigenspace beyond the
predicted GS consists of states with maximum sublattice spins but
the wrong total spin — a non-trivial dimensional gap quantifying
Tasaki §2.5 Theorem 2.3 (γ-4)'s prediction.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- Abbreviation: the joint sublattice-Casimir eigenspace at
max-spin eigenvalues. -/
noncomputable def jointSublatticeCasimirEigenspace
    (A : Λ → Bool) (N : ℕ) :
    Submodule ℂ ((Λ → Fin (N + 1)) → ℂ) :=
  let cA : ℂ := ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ)
  let cB : ℂ := ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)
  let s_A : ℂ := cA * ((N : ℂ) / 2)
  let s_B : ℂ := cB * ((N : ℂ) / 2)
  Module.End.eigenspace (sublatticeSpinSquaredS N A).mulVecLin
      (s_A * (s_A + 1))
    ⊓ Module.End.eigenspace
        (sublatticeSpinSquaredS N (fun x => !A x)).mulVecLin
        (s_B * (s_B + 1))

/-- **Predicted GS finrank < joint Casimir finrank** at non-deg
(`|¬A| ≤ |A|`). Direct from strict subspace inclusion in finite-
dimensional space. -/
theorem bipartiteToyGroundStateSubspacePredicted_finrank_lt_joint_eigenspace_finrank_of_nondegenerate
    (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N)
    (horient : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : Λ => A x = true)).card) :
    Module.finrank ℂ (bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N) <
      Module.finrank ℂ (jointSublatticeCasimirEigenspace (Λ := Λ) A N) := by
  have hstrict :=
    joint_sublattice_casimir_eigenspace_strict_supset_predicted_gs_of_nondegenerate
      A N hA hAc hN horient
  exact Submodule.finrank_lt_finrank_of_lt hstrict

end LatticeSystem.Quantum
