import LatticeSystem.Quantum.SpinS.BipartiteToyGSEigenspaceBridge
import LatticeSystem.Quantum.SpinS.SaturatedLadderSpan
import LatticeSystem.Quantum.SpinS.SaturatedLadderJointEigenspace

/-!
# Saturated-ferromagnet joint eigenspace ⊆ predicted toy-H GS subspace
(saturated edge case `|¬A| = 0`)

For the saturated edge case `|¬A| = 0`, every saturated-
ferromagnet joint eigenspace `saturatedFerromagnetJointEigenspace J N`
(at any choice of `J`) sits inside the predicted toy-Hamiltonian
ground-state subspace `bipartiteToyGroundStateSubspacePredicted A N`:

  `saturatedFerromagnetJointEigenspace J N ⊆
     bipartiteToyGroundStateSubspacePredicted A N`.

Proof: the joint eigenspace is by definition the meet of two
eigenspaces, including the `(Ŝ_tot)²`-eigenspace at
`m_max(m_max+1)`. With `|¬A| = 0` forcing `|V| = |A|` and hence
`m_max = s_A`, PR #2785's eigenspace bridge takes any
`(Ŝ_tot)²`-eigenvector at `s_A(s_A+1)` into the predicted GS
subspace.

**Dimension lower bound corollary**: combining with PR #2768's
identification `saturatedFerromagnetJointEigenspace = span(ladderIterateUp)`
and PR #2769's finrank `2 m_max + 1`, the predicted GS subspace
has `finrank ≥ 2 m_max + 1 = 2 s_A + 1` at the saturated edge case,
matching the Tasaki §2.5 Theorem 2.3 prediction `2 S_tot + 1`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **Saturated-ferromagnet joint eigenspace ⊆ predicted GS
subspace (saturated case)**: when `|¬A| = 0`,
`saturatedFerromagnetJointEigenspace J N ⊆
bipartiteToyGroundStateSubspacePredicted A N`. -/
theorem saturatedFerromagnetJointEigenspace_le_bipartiteToyGroundStateSubspacePredicted_of_cardNotA_zero
    [Nonempty Λ] (A : Λ → Bool) (J : Λ → Λ → ℂ)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    saturatedFerromagnetJointEigenspace (V := Λ) J N ≤
      bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N := by
  -- The bridge in PR #2785 routes (Ŝ_tot)²-eigenvectors at s_A(s_A+1)
  -- into the predicted GS subspace; we need to show that the
  -- saturated FM joint eigenspace is contained in that eigenspace.
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
  -- The saturated FM joint eigenspace is contained in the
  -- (Ŝ_tot)²-eigenspace at m_max(m_max+1) by definition; with
  -- m_max = |V|·N/2 = |A|·N/2 = s_A, this matches PR #2785's bridge.
  intro v hv
  apply totalSpinSSquaredEigenspace_le_bipartiteToyGroundStateSubspacePredicted_of_cardNotA_zero
    A h
  -- Extract the (Ŝ_tot)²-eigenspace membership from the joint condition.
  obtain ⟨_, hCas⟩ := hv
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply] at hCas
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
  -- Convert the |V| eigenvalue to |A| eigenvalue using hcardA.
  rw [hCas]
  congr 1
  unfold saturatedFerromagnetCasimirEigenvalueS
  rw [hcardA]
  ring

end LatticeSystem.Quantum
