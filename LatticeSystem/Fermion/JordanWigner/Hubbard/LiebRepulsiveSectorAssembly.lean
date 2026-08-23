import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveFermionSpinBridge
import LatticeSystem.Math.MatrixAnalysis.SubmatrixGroundState

/-!
# Hard-core/ambient sector `Equiv` and the PR-11a assembly capstone (Theorem 10.4 arc, PR-11a)

Eleventh installment of the Theorem 10.4 discharge arc (issue #5320). This file supplies the last
model-specific piece PR-11a needs: the `Equiv` between the hard-core half-filled configuration
sector and the subtype of the ambient half-filled sector cut out by the hard-core predicate, and
the pure-iff capstone combining it with `Math/MatrixAnalysis/BlockTransport.lean`'s coordinate-block
transport, `Math/MatrixAnalysis/SubmatrixGroundState.lean`'s reindexing transport, and PR-9a's
Fermion-Spin bridge capstone
(`secondOrderEffectiveHamiltonian_liebPerturbation_reindex_eq_heisenbergOnMagSector`,
`LiebRepulsiveFermionSpinBridge.lean`).

**Red stage (this PR-11a increment): type signatures only, `sorry` proofs.** Proofs land in the
implementation pass.

## Main results (Red)

* `liebHardCoreAmbientSubtypeEquiv` — the hard-core half-filled configuration sector is in
  bijection with the subtype of the ambient half-filled sector satisfying
  `liebHalfFillingHardcorePred` (`LiebRepulsivePerturbationSetup.lean`).
* `liebHardCoreAmbientSubtypeEquiv_val` — the `Equiv`'s underlying map agrees with
  `liebHardCoreToAmbientSector` (`LiebRepulsiveFermionSpinBridge.lean`) on the Fock configuration
  level.
* `isUniqueGroundStateOn_liebPerturbationH0Compressed_kernel_iff_heisenberg` — the PR-11a capstone:
  `Ĥeff`'s unique-ground-state predicate on `ker (Ĥ₀|_K)` is equivalent to the same predicate for
  the (constant-shifted) antiferromagnetic Heisenberg matrix on the magnetization sector, on `⊤`.
  A pure iff, with no Theorem 2.3 input — the Theorem 2.3 instance (PR-10b) and the ground-state
  existence witness are supplied downstream by PR-11b.

## Why the target matrix carries no further `submatrix`

Chaining `isUniqueGroundStateOn_coordinateSpan_iff_submatrix` (`BlockTransport.lean`, along the
inclusion `Subtype.val : {s // Phc s} → configSector N (liebHalfFillingPred N nUp)`) with
`isUniqueGroundStateOn_reindex_iff` (`SubmatrixGroundState.lean`, along
`e := (liebHardCoreHalfFillingSectorEquivS N nUp hnUp).symm.trans
  (liebHardCoreAmbientSubtypeEquiv N nUp) : magConfigS (Fin (N + 1)) 1 (N + 1 - nUp) ≃
  {s // liebHalfFillingHardcorePred N nUp s}`) reindexes the block-restricted `Ĥeff` along
`Subtype.val ∘ e`, which — by `liebHardCoreAmbientSubtypeEquiv_val` — equals
`liebHardCoreToAmbientSector ∘ (liebHardCoreHalfFillingSectorEquivS N nUp hnUp).symm`. Composing
PR-9a's capstone (stated as a `submatrix` along `liebHardCoreToAmbientSector` on the left and
`liebHardCoreHalfFillingSectorEquivS` on the right) with this reindexing cancels the
`liebHardCoreHalfFillingSectorEquivS`/`.symm` round trip (`Equiv.self_comp_symm`), leaving the
Heisenberg matrix directly indexed by `magConfigS`, with no residual `submatrix`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.2.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math

variable {N : ℕ}

/-! ## The hard-core/ambient sector `Equiv` -/

/-- **The hard-core/ambient sector `Equiv`** (Red): the hard-core half-filled configuration sector
`configSector N (liebHardCoreHalfFillingPred N nUp)` is in bijection with the subtype of the
ambient half-filled sector `configSector N (liebHalfFillingPred N nUp)` cut out by the hard-core
predicate `liebHalfFillingHardcorePred N nUp`. Forward direction is the inclusion
`liebHardCoreToAmbientSector` (`LiebRepulsiveFermionSpinBridge.lean`), which lands inside the
hard-core-predicate subtype by
`hubbardConfigInteractionWeight_one_eq_zero_of_singlyOccupied`; backward direction unpacks
`liebHalfFilling_site_occupation` (`LiebRepulsivePerturbationSetup.lean`). -/
noncomputable def liebHardCoreAmbientSubtypeEquiv (N nUp : ℕ) :
    configSector N (liebHardCoreHalfFillingPred N nUp) ≃
      {s : configSector N (liebHalfFillingPred N nUp) // liebHalfFillingHardcorePred N nUp s} := by
  sorry

/-- The hard-core/ambient sector `Equiv`'s underlying map agrees with `liebHardCoreToAmbientSector`
on the Fock configuration level (Red): the ambient sector element carried by
`liebHardCoreAmbientSubtypeEquiv N nUp s` equals `liebHardCoreToAmbientSector N nUp s`, for every
hard-core sector element `s`. -/
theorem liebHardCoreAmbientSubtypeEquiv_val (N nUp : ℕ)
    (s : configSector N (liebHardCoreHalfFillingPred N nUp)) :
    (liebHardCoreAmbientSubtypeEquiv N nUp s).val = liebHardCoreToAmbientSector N nUp s := by
  sorry

/-! ## The PR-11a assembly capstone -/

/-- **The PR-11a assembly capstone** (Red, pure iff, no Theorem 2.3 input): the second-order
effective Hamiltonian `Ĥeff` has a unique ground state on `ker (Ĥ₀|_K)` at energy `E` and candidate
`Φ` iff the (constant-shifted) antiferromagnetic Heisenberg matrix on the magnetization-`(N + 1 −
nUp)` sector has a unique ground state on `⊤` at the same energy `E` and the correspondingly
reindexed candidate. Combines `BlockTransport.lean`'s
`isUniqueGroundStateOn_coordinateSpan_iff_submatrix`,
`matrixKernel_liebPerturbationH0Compressed_eq_coordinateSpan`
(`LiebRepulsivePerturbationSetup.lean`), `SubmatrixGroundState.lean`'s
`isUniqueGroundStateOn_reindex_iff` along the composite `Equiv` `magConfigS ≃
{s // liebHalfFillingHardcorePred N nUp s}`, and PR-9a's capstone
`secondOrderEffectiveHamiltonian_liebPerturbation_reindex_eq_heisenbergOnMagSector`
(`LiebRepulsiveFermionSpinBridge.lean`); see the module docstring for why the target matrix carries
no residual `submatrix`. -/
theorem isUniqueGroundStateOn_liebPerturbationH0Compressed_kernel_iff_heisenberg
    (N nUp : ℕ) (hnUp : nUp ≤ N + 1) {A : Finset (Fin (N + 1))}
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hbip : HoppingRespectsBipartition A T) (hT : ∀ x y, T x y = T y x)
    (E : ℝ) (Φ : EuclideanSpace ℂ (configSector N (liebHalfFillingPred N nUp))) :
    IsUniqueGroundStateOn (LatticeSystem.Math.matrixKernel (liebPerturbationH0Compressed N nUp))
        (LatticeSystem.Math.secondOrderEffectiveHamiltonian (liebPerturbationH0Compressed N nUp)
          (liebPerturbationVCompressed N nUp A T) (liebPerturbationH0InvCompressed N nUp)) E Φ
      ↔ IsUniqueGroundStateOn
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (magConfigS (Fin (N + 1)) 1 (N + 1 - nUp))))
        (heisenbergHamiltonianSMatrixOnMagSector
              ((2 : ℂ) • bipartiteCoupling (fun x => decide (x ∈ A))) 1 (N + 1 - nUp)
          - (((A.card : ℂ) * ((N + 1 - A.card : ℕ) : ℂ))) • (1 : Matrix _ _ ℂ))
        E
        (WithLp.toLp 2 fun j =>
          (WithLp.ofLp
              (LatticeSystem.Math.coordinateRestrict (liebHalfFillingHardcorePred N nUp) Φ))
            (((liebHardCoreHalfFillingSectorEquivS N nUp hnUp).symm.trans
                (liebHardCoreAmbientSubtypeEquiv N nUp)) j)) := by
  sorry

end LatticeSystem.Fermion
