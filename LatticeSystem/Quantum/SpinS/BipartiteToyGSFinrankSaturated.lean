import LatticeSystem.Quantum.SpinS.SaturatedFMJointLePredictedGS
import LatticeSystem.Quantum.SpinS.SaturatedLadderSpan

/-!
# Dimension lower bound on the predicted toy-H GS subspace
(saturated edge case)

For the saturated edge case `|¬A| = 0`, the predicted toy-H GS
subspace has dimension at least `|V|·N + 1 = 2 m_max + 1`:

  `Fintype.card Λ * N + 1
     ≤ Module.finrank ℂ (bipartiteToyGroundStateSubspacePredicted A N)`.

This is the Tasaki §2.5 Theorem 2.3 degeneracy `2 S_tot + 1`
specialised to the saturated case `S_tot = m_max = (|A| − |¬A|)·S
= |V|·S`. Proof: combine the §2.4 ↔ γ-4 bridge (PR #2786) with
PR #2769's
`saturatedFerromagnetJointEigenspace_finrank_eq` via
`Submodule.finrank_mono`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **Dimension lower bound on the predicted GS subspace (saturated
case)**: when `|¬A| = 0`,
`|V|·N + 1 ≤ Module.finrank ℂ (bipartiteToyGroundStateSubspacePredicted A N)`.

Proof: combine the §2.4 ↔ γ-4 bridge (PR #2786,
`saturatedFerromagnetJointEigenspace_le_bipartiteToyGroundStateSubspacePredicted_of_cardNotA_zero`)
with PR #2769's `saturatedFerromagnetJointEigenspace_finrank_eq`
via `Submodule.finrank_mono`. Any choice of coupling `J` works
(e.g. `J = 0`). -/
theorem bipartiteToyGroundStateSubspacePredicted_finrank_ge_succ_card_mul_N_of_cardNotA_zero
    [Nonempty Λ] (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    Fintype.card Λ * N + 1 ≤
      Module.finrank ℂ
        (bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N) := by
  have h_bridge :=
    saturatedFerromagnetJointEigenspace_le_bipartiteToyGroundStateSubspacePredicted_of_cardNotA_zero
      (N := N) A (0 : Λ → Λ → ℂ) h
  have h_finrank := Submodule.finrank_mono h_bridge
  rw [saturatedFerromagnetJointEigenspace_finrank_eq] at h_finrank
  exact h_finrank

end LatticeSystem.Quantum
