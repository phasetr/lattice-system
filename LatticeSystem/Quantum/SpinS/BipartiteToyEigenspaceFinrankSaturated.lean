import LatticeSystem.Quantum.SpinS.BipartiteToyGSFinrankSaturated
import LatticeSystem.Quantum.SpinS.ToyHamiltonianJointEigenspace

/-!
# `Ĥ_toy_S`-eigenspace finrank lower bound at the saturated case

Combining the predicted GS subspace inclusion in the
`Ĥ_toy_S`-eigenspace (PR #2775) with the saturated-case finrank
lower bound (PR #2787), the `Ĥ_toy_S`-eigenspace at the predicted
minimum energy `bipartiteToyMinEnergyPredicted A N` itself has
finrank `≥ |V|·N + 1`:

  `|V|·N + 1 ≤ Module.finrank ℂ
       (eigenspace(Ĥ_toy_S)_{bipartiteToyMinEnergyPredicted A N})`

when `|¬A| = 0`. This is the operator-level version of the
predicted Theorem 2.3 degeneracy lower bound, applied directly to
the `Ĥ_toy_S`-eigenspace.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **`Ĥ_toy_S`-eigenspace at the predicted minimum energy has
finrank `≥ |V|·N + 1` at the saturated case**: when `|¬A| = 0`,
the `Ĥ_toy_S`-eigenspace at eigenvalue
`bipartiteToyMinEnergyPredicted A N` has finrank
`≥ Fintype.card Λ * N + 1`.

Proof: chain PR #2775 (predicted GS ⊆ eigenspace) with PR #2787
(predicted GS finrank ≥ |V|·N + 1) via `Submodule.finrank_mono`. -/
theorem heisenbergToyHamiltonianS_eigenspace_at_predicted_min_finrank_ge_succ_card_mul_N_of_cardNotA_zero
    [Nonempty Λ] (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    Fintype.card Λ * N + 1 ≤
      Module.finrank ℂ
        (Module.End.eigenspace
          (heisenbergToyHamiltonianS (Λ := Λ) A N).mulVecLin
          (bipartiteToyMinEnergyPredicted (Λ := Λ) A N)) := by
  -- predicted GS subspace ⊆ Ĥ_toy_S eigenspace (PR #2775).
  have h_pred_le_eigen :=
    bipartiteToyGroundStateSubspacePredicted_le_heisenbergToyHamiltonianS_eigenspace
      (Λ := Λ) A N
  -- predicted GS finrank ≥ |V|·N + 1 (PR #2787).
  have h_pred_finrank :=
    bipartiteToyGroundStateSubspacePredicted_finrank_ge_succ_card_mul_N_of_cardNotA_zero
      (N := N) A h
  -- Chain via Submodule.finrank_mono.
  have h_finrank_mono := Submodule.finrank_mono h_pred_le_eigen
  exact h_pred_finrank.trans h_finrank_mono

end LatticeSystem.Quantum
