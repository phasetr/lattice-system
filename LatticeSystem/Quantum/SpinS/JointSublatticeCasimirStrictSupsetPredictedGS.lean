import LatticeSystem.Quantum.SpinS.NeelStateOfSMemJointSublatticeCasimirEigenspace
import LatticeSystem.Quantum.SpinS.NeelStateOfSNotMemBipartiteToyGSPredictedNondegenerate

/-!
# Joint sublattice-Casimir eigenspace strictly contains predicted GS
at non-degenerate

The predicted GS subspace
`bipartiteToyGroundStateSubspacePredicted A N` is defined as the
intersection of three eigenspaces:
- `(Ŝ_tot)²` at `(s_A − s_B)·((s_A − s_B) + 1)`,
- `(Ŝ_A)²` at `s_A·(s_A + 1)`,
- `(Ŝ_¬A)²` at `s_B·(s_B + 1)`.

The joint sublattice Casimir eigenspace (last two conditions only)
is a strictly larger subspace at non-degenerate configurations:
the Néel state `Φ_Néel(A, N)` is in the joint Casimir eigenspace
(PR #2913) but **not** in the predicted GS subspace (PR #2919).

This witnesses the strict inclusion

  `bipartiteToyGroundStateSubspacePredicted A N
     ⊊ eigenspace((Ŝ_A)², s_A·(s_A+1))
       ⊓ eigenspace((Ŝ_¬A)², s_B·(s_B+1))`

at non-degenerate. The "extra" subspace (the difference) consists
of states with maximum sublattice spins but the wrong total spin.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Joint sublattice-Casimir eigenspace strictly contains the predicted
GS subspace** at non-degenerate (`|¬A| ≤ |A|`). The Néel state witnesses
the strict inclusion. -/
theorem joint_sublattice_casimir_eigenspace_strict_supset_predicted_gs_of_nondegenerate
    (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N)
    (horient : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : Λ => A x = true)).card) :
    bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N <
      Module.End.eigenspace (sublatticeSpinSquaredS N A).mulVecLin
          (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) *
              (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2) + 1))
        ⊓ Module.End.eigenspace
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVecLin
            (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                ((N : ℂ) / 2) *
                (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                    ((N : ℂ) / 2) + 1)) := by
  refine lt_iff_le_and_ne.mpr ⟨?_, ?_⟩
  · -- ≤: predicted GS is the intersection of three; drop the (Ŝ_tot)² constraint.
    intro v hv
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · exact hv.1.2
    · exact hv.2
  · -- ≠: Néel witnesses a vector in the joint Casimir but not in predicted GS.
    intro heq
    have hNeel_in_joint :=
      neelStateOfS_mem_joint_sublattice_casimir_eigenspace (Λ := Λ) A N
    have hNeel_in_pred : neelStateOfS A N ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N := by
      rw [heq]; exact hNeel_in_joint
    exact
      neelStateOfS_notMem_bipartiteToyGroundStateSubspacePredicted_of_nondegenerate
        A N hA hAc hN horient hNeel_in_pred

end LatticeSystem.Quantum
