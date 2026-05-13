import LatticeSystem.Quantum.SpinS.BipartiteToyGSFinrankOppositeSaturated
import LatticeSystem.Quantum.SpinS.ToyHamiltonianJointEigenspace

/-!
# `Ĥ_toy_S`-eigenspace finrank lower bound at the opposite
saturated case

Mirror of PR #2789 for the orientation `|A| = 0`. Combines the
opposite-orientation predicted GS subspace finrank bound (PR #2788)
with the inclusion into the `Ĥ_toy_S`-eigenspace (PR #2775)
applied to the complement orientation:

  `|V|·N + 1 ≤ Module.finrank ℂ
       (eigenspace(Ĥ_toy_S(¬A))_{bipartiteToyMinEnergyPredicted (¬A) N})`

when `|A| = 0`. Since `Ĥ_toy_S(A) = Ĥ_toy_S(¬A)` (sublattice-swap
invariant, via `heisenbergToyHamiltonianS_eq_two_sublatticeSpinSDot`
+ `sublatticeSpinSDot_complement_comm`), this also applies to the
original-orientation toy Hamiltonian.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **`Ĥ_toy_S(¬A)`-eigenspace at the predicted min energy has
finrank `≥ |V|·N + 1` at the opposite saturated case**: when
`|A| = 0`, the `Ĥ_toy_S(¬A)`-eigenspace at
`bipartiteToyMinEnergyPredicted (¬A) N` has finrank
`≥ Fintype.card Λ * N + 1`.

Proof: chain PR #2775 applied to `¬A` with PR #2788 via
`Submodule.finrank_mono`. -/
theorem heisenbergToyHamiltonianS_complement_eigenspace_at_predicted_min_finrank_ge_succ_card_mul_N_of_cardA_zero
    [Nonempty Λ] (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    Fintype.card Λ * N + 1 ≤
      Module.finrank ℂ
        (Module.End.eigenspace
          (heisenbergToyHamiltonianS (Λ := Λ) (fun x => ! A x) N).mulVecLin
          (bipartiteToyMinEnergyPredicted (Λ := Λ)
            (fun x => ! A x) N)) := by
  -- Predicted GS subspace ⊆ Ĥ_toy_S(¬A) eigenspace (PR #2775).
  have h_pred_le_eigen :=
    bipartiteToyGroundStateSubspacePredicted_le_heisenbergToyHamiltonianS_eigenspace
      (Λ := Λ) (fun x => ! A x) N
  -- Predicted GS finrank ≥ |V|·N + 1 (PR #2788).
  have h_pred_finrank :=
    bipartiteToyGroundStateSubspacePredicted_complement_finrank_ge_succ_card_mul_N_of_cardA_zero
      (N := N) A h
  have h_finrank_mono := Submodule.finrank_mono h_pred_le_eigen
  exact h_pred_finrank.trans h_finrank_mono

end LatticeSystem.Quantum
