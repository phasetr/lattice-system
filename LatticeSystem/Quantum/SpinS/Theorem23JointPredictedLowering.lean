import LatticeSystem.Quantum.SpinS.Theorem23PFLadderLink
import LatticeSystem.Quantum.SpinS.BipartiteToyGSLadderInvariant
import LatticeSystem.Quantum.SpinS.SaturatedLadderJointEigenspace

/-!
# Lowering a joint predicted-Casimir eigenvector to the next sector

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3).

The minimal-total-spin joint eigenvector at the extremal sector (#3709) is a
simultaneous eigenvector of `(Ŝ_tot)²`, `(Ŝ_A)²`, `(Ŝ_¬A)²`.  Since the total
lowering operator `Ŝ⁻_tot` commutes with all three Casimir operators
(`totalSpinSSquared_commute_totalSpinSOpMinus`,
`sublatticeSpinSquaredS_commute_totalSpinSOpMinus`), lowering preserves all three
eigenvalues, and it does not annihilate the vector as long as the total-Casimir
value differs from the sector's lowering-kernel value
(`tasaki23_totalSpinSOpMinus_mulVec_magSectorEmbedding_ne_zero_of_casimir_ne_kernel_value`),
which holds for the predicted value in any admissible sector below the right endpoint
(`tasaki23_predictedCasimirValue_ne_lowering_kernel_value_of_mem_of_lt_right`).

Hence a joint predicted-Casimir eigenvector in an admissible sector `M < max(|A|,|¬A|)·N`
lowers to a *non-zero* joint predicted-Casimir eigenvector in the successor sector.
Iterating from the extremal base sector spreads the joint predicted-Casimir line across
the whole admissible range — the Casimir-controlled propagation that avoids any lowered
Marshall-positivity ("site-sum") input.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Lowering a joint predicted-Casimir eigenvector to the next sector**: if a
sector-`M` vector `magSectorEmbedding Φ` (admissible `M` below the right endpoint) is a
non-zero simultaneous eigenvector of `(Ŝ_tot)²` (at the predicted value), `(Ŝ_A)²` (at
`γ_A`) and `(Ŝ_¬A)²` (at `γ_B`), then `Ŝ⁻_tot · magSectorEmbedding Φ` is again a non-zero
simultaneous eigenvector at the same three eigenvalues. -/
theorem tasaki23_jointPredicted_lowering_succ
    (A : V → Bool) {M : ℕ}
    (hM_mem : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hM_lt :
      M <
        max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {γ_A γ_B : ℂ} {Φ : magConfigS V N M → ℂ}
    (hΦ_ne : magSectorEmbedding Φ ≠ 0)
    (hCas_tot :
      (totalSpinSSquared V N).mulVec (magSectorEmbedding Φ) =
        ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) • magSectorEmbedding Φ)
    (hCas_A :
      (sublatticeSpinSquaredS N A).mulVec (magSectorEmbedding Φ) =
        γ_A • magSectorEmbedding Φ)
    (hCas_B :
      (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec (magSectorEmbedding Φ) =
        γ_B • magSectorEmbedding Φ) :
    (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) ≠ 0 ∧
      (totalSpinSSquared V N).mulVec
          ((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) =
        ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) •
          (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) ∧
      (sublatticeSpinSquaredS N A).mulVec
          ((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) =
        γ_A • (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) ∧
      (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
          ((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) =
        γ_B • (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact tasaki23_totalSpinSOpMinus_mulVec_magSectorEmbedding_ne_zero_of_casimir_ne_kernel_value
      hCas_tot
      (tasaki23_predictedCasimirValue_ne_lowering_kernel_value_of_mem_of_lt_right A N hM_mem hM_lt)
      hΦ_ne
  · exact mulVec_preserves_eigenvalue_of_commuteS
      totalSpinSSquared_commute_totalSpinSOpMinus hCas_tot
  · exact mulVec_preserves_eigenvalue_of_commuteS
      (sublatticeSpinSquaredS_commute_totalSpinSOpMinus A) hCas_A
  · exact mulVec_preserves_eigenvalue_of_commuteS
      (sublatticeSpinSquaredS_commute_totalSpinSOpMinus (fun x => ! A x)) hCas_B

end LatticeSystem.Quantum
