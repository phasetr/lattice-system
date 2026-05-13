import LatticeSystem.Quantum.SpinS.SublatticeEqTotalOfCardZero

/-!
# Eigenspace bridge: `(Ŝ_tot)²`-eigenspace ⊆ predicted GS subspace
(saturated edge case)

Combining the sublattice ↔ total spin identities of PR #2784 with
the definition of `bipartiteToyGroundStateSubspacePredicted`
(PR #2778), every `(Ŝ_tot)²`-eigenvector at eigenvalue
`s_A(s_A+1) = (|A|·N/2)·(|A|·N/2+1)` lies in the predicted GS
subspace when `|¬A| = 0`:

  `eigenspace((Ŝ_tot)²)_{s_A(s_A+1)}
     ⊆ bipartiteToyGroundStateSubspacePredicted A N`,

since (i) the `(Ŝ_tot)²` eigenvalue matches the predicted target
`(s_A − 0)(s_A − 0 + 1) = s_A(s_A+1)`, (ii) `Ŝ_A² = Ŝ_tot²` gives
the `(Ŝ_A)²` eigenspace condition for free, and (iii) `Ŝ_¬A² = 0`
trivially gives the `(Ŝ_¬A)²` eigenspace condition.

In particular, by PR #2768's identification
`saturatedFerromagnetJointEigenspace J N = span(ladderIterateUp V N)`,
the saturated-ferromagnet joint eigenspace is contained in the
predicted GS subspace at the saturated edge case, giving a
dimension lower bound `finrank(predicted GS) ≥ 2 m_max + 1`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Eigenspace bridge in the saturated edge case**: when
`|¬A| = 0`, every `(Ŝ_tot)²`-eigenvector at eigenvalue
`(|A|·N/2)·(|A|·N/2+1)` is in the predicted ground-state
subspace `bipartiteToyGroundStateSubspacePredicted A N`. -/
theorem totalSpinSSquaredEigenspace_le_bipartiteToyGroundStateSubspacePredicted_of_cardNotA_zero
    (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    Module.End.eigenspace (totalSpinSSquared Λ N).mulVecLin
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((N : ℂ) / 2) *
          (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2) + 1)) ≤
      bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N := by
  intro v hv
  -- Extract the (Ŝ_tot)²-eigenvector condition from hv.
  rw [Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply] at hv
  -- Show the three joint Casimir eigenspace memberships.
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- (Ŝ_tot)² · v = ((s_A - s_B)·(s_A - s_B + 1)) • v.
    -- For |¬A| = 0, the filter !A is empty, so the (s_B := card !A · N/2) = 0.
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply]
    rw [hv]
    congr 1
    rw [h]
    push_cast
    ring
  · -- (Ŝ_A)² · v = (s_A · (s_A + 1)) • v.
    -- Since Ŝ_A² = Ŝ_tot² when |¬A| = 0, this follows from hv.
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply]
    rw [sublatticeSpinSquaredS_eq_totalSpinSSquared_of_cardNotA_zero A h]
    exact hv
  · -- (Ŝ_¬A)² · v = 0 • v.
    -- Ŝ_¬A² = 0 when |¬A| = 0; and the target scalar is also 0
    -- because the cardinality of `{x | ¬A x = true}` is 0.
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply]
    rw [sublatticeSpinSquaredS_eq_zero_of_card_zero (fun x => ! A x) h]
    rw [Matrix.zero_mulVec, h]
    push_cast
    simp

end LatticeSystem.Quantum
