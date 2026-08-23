import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveTheorem23Instance
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveSectorAssembly
import LatticeSystem.Quantum.SpinS.Theorem24SU2GlobalUniquenessFromMLM
import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbationConvergence

/-!
# Uniqueness supply and Lemma 10.1 application (Theorem 10.4 arc, PR-11b)

Twelfth installment of the Theorem 10.4 discharge arc (issue #5320). This file (RED / scaffolding
stage: both capstones are `sorry`) supplies the two remaining pieces PR-11b owns:

1. **Uniqueness supply**: `liebRepulsive_theorem23_instance` (PR-10b,
   `LiebRepulsiveTheorem23Instance.lean`) gives a Marshall-positive sector eigenvector and its
   energy minimality but not, by itself, a genuine `IsUniqueGroundStateOn`. Combining it with the
   Perron–Frobenius `finrank ≤ 1` route
   (`heisenbergHamiltonianSMatrixOnMagSector_finrank_le_one_of_marshall_positive`,
   `Quantum/SpinS/Theorem24SectorPFFromTheorem23.lean`, generalizing the per-sector recipe of
   `tasaki23_balanced_sector_matrix_finrank_le_one_of_common_min`,
   `Theorem24SU2GlobalUniquenessFromMLM.lean:33`, without its `h_card_eq`/`hmin_eq` hypotheses) and
   PR-11a's generic builders `isUniqueGroundStateOn_of_finrank_eigenspace_le_one` /
   `isUniqueGroundStateOn_sub_smul_one_iff` (`Math/MatrixAnalysis/SubmatrixGroundState.lean`)
   promotes it to `IsUniqueGroundStateOn ⊤ (heisenbergHamiltonianSMatrixOnMagSector … - shift • 1) E
   Φ`, the exact right-hand side of PR-11a's assembly capstone
   `isUniqueGroundStateOn_liebPerturbationH0Compressed_kernel_iff_heisenberg`
   (`LiebRepulsiveSectorAssembly.lean`).
2. **Lemma 10.1 application**: feeding the `hEffGS` hypothesis so supplied (transported back along
   PR-11a's `iff` onto `ker (Ĥ₀|_K)`) into `tasaki_lemma_10_1_degenerate_perturbation`
   (`Math/MatrixAnalysis/DegeneratePerturbationConvergence.lean:428`) — every other hypothesis of
   that lemma is already discharged by PR-5/PR-6 assets
   (`liebPerturbationH0Compressed_posSemidef`, `liebPerturbationVCompressed_isHermitian`,
   `liebPerturbationH0Compressed_isReducedInverse`,
   `kernelProjection_mul_liebPerturbationVCompressed_mul_kernelProjection`) — gives the perturbed
   Hamiltonian a unique ground state for every sufficiently small `λ > 0`, converging to the
   `hEffGS` witness as `λ → 0⁺`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.1 Lemma 10.1, pp. 346–347; §2.5 Theorem 2.3, p. 42; §10.2.2 Theorem 10.4, p. 350.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math

variable {N : ℕ}

/-! ## Capstone 1: uniqueness supply -/

/-- **Uniqueness supply for the superexchange Heisenberg matrix, on the magnetization sector.**
For a nondegenerate bipartition and an admissible magnetization sector, the (constant-shifted)
antiferromagnetic Heisenberg matrix `heisenbergHamiltonianSMatrixOnMagSector J 1 (N + 1 − nUp) −
shift • 1` (`J = (2 : ℂ) • bipartiteCoupling A`, `shift = |A|(N + 1 − |A|)`, the exact shape of
PR-11a's assembly capstone `isUniqueGroundStateOn_liebPerturbationH0Compressed_kernel_iff_heisenberg`)
has a **unique** ground state on `⊤`. Derived from `liebRepulsive_theorem23_instance`'s
Marshall-positive sector eigenvector via the Perron–Frobenius `finrank ≤ 1` route and PR-11a's
generic `finrank`-to-`IsUniqueGroundStateOn` builder plus its constant-shift transport, not directly
assumed. -/
theorem liebRepulsive_isUniqueGroundStateOn_heisenbergOnMagSector
    (A : Finset (Fin (N + 1))) (hA : 1 ≤ A.card) (hB : 1 ≤ (bipartitionComplement A).card)
    (nUp : ℕ) (hnUp : nUp ≤ N + 1)
    (hM : (N + 1 - nUp) ∈ tasaki23GroundStateSectors
      (fun x => decide (x ∈ liebOrientedSublattice A)) 1) :
    ∃ (E : ℝ) (Φ : EuclideanSpace ℂ (magConfigS (Fin (N + 1)) 1 (N + 1 - nUp))),
      IsUniqueGroundStateOn
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (magConfigS (Fin (N + 1)) 1 (N + 1 - nUp))))
        (heisenbergHamiltonianSMatrixOnMagSector
              ((2 : ℂ) • bipartiteCoupling (fun x : Fin (N + 1) => decide (x ∈ A))) 1
              (N + 1 - nUp)
          - (((A.card * (N + 1 - A.card) : ℕ) : ℝ) : ℂ) • (1 : Matrix _ _ ℂ))
        E Φ := by
  sorry

/-! ## Capstone 2: Lemma 10.1 application -/

/-- **Tasaki Lemma 10.1 applied to the repulsive Hubbard superexchange model.** For a nondegenerate
bipartition, a compatible hopping matrix `T` and an admissible magnetization sector, the perturbed
Hamiltonian `Ĥ₀c + λ V̂c` (`liebPerturbationH0Compressed`, `liebPerturbationVCompressed`, the
compressed half-filled-sector model of `LiebRepulsivePerturbationSetup.lean`) has, for every
sufficiently small `λ > 0`, a unique ground state on the whole compressed sector, converging to an
effective ground state `Φeff` as `λ → 0⁺`. Combines capstone 1 above with PR-11a's assembly `iff`
(`isUniqueGroundStateOn_liebPerturbationH0Compressed_kernel_iff_heisenberg`,
`LiebRepulsiveSectorAssembly.lean`) to supply `tasaki_lemma_10_1_degenerate_perturbation`'s
`hEffGS` hypothesis; every other hypothesis of that lemma is already discharged by PR-5/PR-6
assets. -/
theorem tasaki_lemma_10_1_liebRepulsive_apply
    (A : Finset (Fin (N + 1))) (hA : 1 ≤ A.card) (hB : 1 ≤ (bipartitionComplement A).card)
    (nUp : ℕ) (hnUp : nUp ≤ N + 1)
    (hM : (N + 1 - nUp) ∈ tasaki23GroundStateSectors
      (fun x => decide (x ∈ liebOrientedSublattice A)) 1)
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hbip : HoppingRespectsBipartition A T) (hT : ∀ x y, T x y = T y x) :
    ∃ lam0 : ℝ, 0 < lam0 ∧
      ∃ Elam : ℝ → ℝ,
      ∃ Philam : ℝ → EuclideanSpace ℂ (configSector N (liebHalfFillingPred N nUp)),
      ∃ Φeff : EuclideanSpace ℂ (configSector N (liebHalfFillingPred N nUp)),
        (∀ lam : ℝ, 0 < lam → lam < lam0 →
          IsUniqueGroundStateOn
            (⊤ : Submodule ℂ (EuclideanSpace ℂ (configSector N (liebHalfFillingPred N nUp))))
            (perturbedHamiltonian (liebPerturbationH0Compressed N nUp)
              (liebPerturbationVCompressed N nUp A T) lam)
            (Elam lam) (Philam lam)) ∧
        Filter.Tendsto Philam (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds Φeff) := by
  sorry

end LatticeSystem.Fermion
