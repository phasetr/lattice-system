import LatticeSystem.Quantum.SpinS.BipartiteToyGSFinrankSaturated
import LatticeSystem.Quantum.SpinS.SaturatedLadderJointEigenspace
import LatticeSystem.Quantum.SpinS.SaturatedLadderSpan

/-!
# Finrank equality on the predicted toy-H GS subspace (saturated case)

PR #2787 established `finrank(predicted GS) ≥ |V|·N + 1` at the
saturated edge case `|¬A| = 0`. This file establishes the reverse
inequality, giving equality:

  `Module.finrank ℂ (bipartiteToyGroundStateSubspacePredicted A N)
     = Fintype.card Λ * N + 1`

when `|¬A| = 0`. Proof sketch: at `|¬A| = 0`, the predicted GS
subspace is contained in the saturated-ferromagnet joint
eigenspace at `J = 0` (since the joint Casimir conditions imply
`(Ŝ_tot)²` eigenvalue `m_max(m_max+1)` and `H_0 = 0` makes the
`H_0`-eigenspace at `0` the full space). Then PR #2769 gives
`finrank(saturated FM joint) = |V|·N + 1`.

This is the operator-level confirmation that, at the saturated
case, the predicted GS subspace is *exactly* the `(2 m_max + 1)`-
dim spin-`m_max` irreducible representation, matching the
Tasaki §2.5 Theorem 2.3 degeneracy `2 S_tot + 1` with equality.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **Reverse bridge at saturated case**: when `|¬A| = 0`,
`bipartiteToyGroundStateSubspacePredicted A N ⊆
saturatedFerromagnetJointEigenspace 0 N`. Proof: the predicted
GS subspace's `(Ŝ_tot)²` eigenspace component matches
`m_max(m_max+1)` (since `m_max = s_A` when `|V| = |A|`), and the
`heisenbergHamiltonianS 0 N`-eigenspace at `0` is the full
multi-site space. -/
theorem bipartiteToyGroundStateSubspacePredicted_le_saturatedFerromagnetJointEigenspace_zero_of_cardNotA_zero
    [Nonempty Λ] (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N ≤
      saturatedFerromagnetJointEigenspace (V := Λ) (0 : Λ → Λ → ℂ) N := by
  have hcardA : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      Fintype.card Λ := by
    have h_sum :
        (Finset.univ.filter (fun x : Λ => A x = true)).card +
          (Finset.univ.filter (fun x : Λ => (! A x) = true)).card =
            Fintype.card Λ := by
      have hfilter_eq : Finset.univ.filter (fun x : Λ => (! A x) = true) =
          Finset.univ.filter (fun x : Λ => ¬ (A x = true)) := by
        congr 1; funext x; rcases A x <;> simp
      rw [hfilter_eq, ← Finset.card_univ]
      exact Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun x : Λ => A x = true)
    rw [h] at h_sum
    omega
  intro v hv
  obtain ⟨⟨h_tot, _h_A⟩, _h_B⟩ := hv
  -- Show v ∈ saturated FM joint eigenspace at J=0.
  refine ⟨?_, ?_⟩
  · -- v is in the H_0 eigenspace at saturatedFerromagnetEigenvalueS 0 N.
    -- Since H_0 = 0 (sum of 0 • spinSDot terms) and
    -- saturatedFerromagnetEigenvalueS 0 N = 0 (diagonal entry of 0),
    -- this is the eigenspace at eigenvalue 0 with operator 0,
    -- which contains everything.
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply]
    have hH_zero : heisenbergHamiltonianS (Λ := Λ) (0 : Λ → Λ → ℂ) N = 0 := by
      unfold heisenbergHamiltonianS
      simp
    have hEig_zero : saturatedFerromagnetEigenvalueS
        (V := Λ) (0 : Λ → Λ → ℂ) N = 0 := by
      unfold saturatedFerromagnetEigenvalueS
      rw [hH_zero]
      simp
    rw [hH_zero, hEig_zero, Matrix.zero_mulVec, zero_smul]
  · -- v is in the (Ŝ_tot)² eigenspace at saturatedFerromagnetCasimirEigenvalueS Λ N.
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply]
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply] at h_tot
    rw [h_tot]
    congr 1
    unfold saturatedFerromagnetCasimirEigenvalueS
    rw [hcardA, h]
    push_cast; ring

set_option linter.style.longLine false in
/-- **Finrank equality at saturated case**: when `|¬A| = 0`,
`finrank(bipartiteToyGroundStateSubspacePredicted A N) = |V|·N + 1`.
The predicted GS subspace is exactly the `(2 m_max + 1)`-dim
spin-`m_max` irreducible representation, matching the Tasaki §2.5
Theorem 2.3 degeneracy. -/
theorem bipartiteToyGroundStateSubspacePredicted_finrank_eq_succ_card_mul_N_of_cardNotA_zero
    [Nonempty Λ] (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    Module.finrank ℂ
      (bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N) =
        Fintype.card Λ * N + 1 := by
  apply le_antisymm
  · -- ≤: use the reverse bridge to saturated FM joint, then PR #2769.
    have h_le :=
      bipartiteToyGroundStateSubspacePredicted_le_saturatedFerromagnetJointEigenspace_zero_of_cardNotA_zero
        (N := N) A h
    have h_finrank_mono := Submodule.finrank_mono h_le
    rw [saturatedFerromagnetJointEigenspace_finrank_eq] at h_finrank_mono
    exact h_finrank_mono
  · -- ≥: PR #2787.
    exact bipartiteToyGroundStateSubspacePredicted_finrank_ge_succ_card_mul_N_of_cardNotA_zero
      A h

end LatticeSystem.Quantum
