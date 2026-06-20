import LatticeSystem.Quantum.SpinS.ConnectedDressedPF
import LatticeSystem.Quantum.SpinS.ShiftedDressedMatrix

set_option linter.unusedSectionVars false

/-!
# Connected-graph sector irreducibility for the Theorem 2.3 chain

(Issue #4609, PR3 Step 1): the connected-graph analogue of
`isIrreducible_shiftedDressedSReMatrixOnMagSector`
(`Theorem23StructuralReach.lean`).

The complete-bipartite version builds the Perron–Frobenius irreducibility of the
shifted dressed matrix on a fixed magnetization sector from the *complete*
strict positivity hypothesis `hJ_pos` via
`exists_matrixPow_pos_length_of_magConfigS_bipartite`.  This file mirrors that
proof verbatim, replacing the complete-graph reachability/positivity by the
connected analogue `exists_matrixPow_pos_length_of_magConfigS_connected`
(PR2) so that strict positivity of `J` is required only on the edges of a
*connected* bipartite graph `G` (`hJ_pos_G`).

Since the dressed matrix `shiftedDressedSReMatrixOnMagSector A J N c M` depends
only on `J` (not on the graph), the resulting `IsIrreducible` fact has exactly
the same conclusion as the complete-graph one; the graph enters only through the
off-diagonal reachability/positivity used here.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.3, p. 42; E. Lieb, D. Mattis,
J. Math. Phys. 3 (1962) 749.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Connected-graph sector-irreducibility**.

The shifted dressed matrix on the magnetization-`M` sector is Perron–Frobenius
irreducible, where strict positivity of `J` is needed only on the edges of the
connected bipartite graph `G`.

Mirror of `isIrreducible_shiftedDressedSReMatrixOnMagSector`: the diagonal case
(`σ = τ`) uses the strict diagonal bound `hc_strict`; the off-diagonal case uses
the connected length-positivity `exists_matrixPow_pos_length_of_magConfigS_connected`. -/
theorem isIrreducible_shiftedDressedSReMatrixOnMagSector_connected
    (A : V → Bool) {G : SimpleGraph V}
    {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    (hGconn : G.Connected)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos_G : ∀ x y : V, G.Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c) :
    (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible := by
  rw [Matrix.isIrreducible_iff_exists_pow_pos
    (shiftedDressedSReMatrixOnMagSector_nonneg A N c M hJ_real hJ_nn hJ_sym
      hJ_bipartite (fun σ => le_of_lt (hc_strict σ)))]
  intro σ τ
  by_cases hne : σ = τ
  · subst hne
    refine ⟨1, Nat.one_pos, ?_⟩
    rw [pow_one, shiftedDressedSReMatrixOnMagSector_apply,
      shiftedDressedSReMatrix_apply_diag]
    linarith [hc_strict σ.1]
  · obtain ⟨k, hk_pos, hpos⟩ :=
      exists_matrixPow_pos_length_of_magConfigS_connected A c hGconn hGbip hJ_real
        hJ_pos_G hJ_nn hJ_sym hJ_bipartite (fun σ => le_of_lt (hc_strict σ))
        (Ne.symm hne)
    exact ⟨k, hk_pos, hpos⟩

end LatticeSystem.Quantum
