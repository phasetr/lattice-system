import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveTheorem23Instance
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveSectorAssembly
import LatticeSystem.Quantum.SpinS.Theorem24SectorPFFromTheorem23
import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbationConvergence

/-!
# Uniqueness supply and Lemma 10.1 application (Theorem 10.4 arc, PR-11b)

Twelfth installment of the Theorem 10.4 discharge arc (issue #5320). This file supplies the two
remaining pieces PR-11b owns:

1. **Uniqueness supply**: `liebRepulsive_theorem23_instance` (PR-10b,
   `LiebRepulsiveTheorem23Instance.lean`) gives a Marshall-positive sector eigenvector and its
   energy minimality but not, by itself, a genuine `IsUniqueGroundStateOn`. Combining it with the
   Perron–Frobenius `finrank ≤ 1` route
   (`heisenbergHamiltonianSMatrixOnMagSector_finrank_le_one_of_marshall_positive`,
   `Quantum/SpinS/Theorem24SectorPFFromTheorem23.lean`) and PR-11a's generic builders
   `isUniqueGroundStateOn_of_finrank_eigenspace_le_one` /
   `isUniqueGroundStateOn_sub_smul_one_iff` (`Math/MatrixAnalysis/SubmatrixGroundState.lean`)
   promotes it to `IsUniqueGroundStateOn ⊤ (heisenbergHamiltonianSMatrixOnMagSector … - shift • 1) E
   Φ`, the exact right-hand side of PR-11a's assembly capstone
   `isUniqueGroundStateOn_liebPerturbationH0Compressed_kernel_iff_heisenberg`
   (`LiebRepulsiveSectorAssembly.lean`).
2. **Lemma 10.1 application**: feeding the `hEffGS` hypothesis so supplied (transported back along
   PR-11a's `iff` onto `ker (Ĥ₀|_K)`) into `tasaki_lemma_10_1_degenerate_perturbation`
   (`Math/MatrixAnalysis/DegeneratePerturbationConvergence.lean`) — every other hypothesis of
   that lemma is already discharged by PR-5/PR-6 assets
   (`liebPerturbationH0Compressed_posSemidef`, `liebPerturbationVCompressed_isHermitian`,
   `liebPerturbationH0Compressed_isReducedInverse`,
   `kernelProjection_mul_liebPerturbationVCompressed_mul_kernelProjection`) — gives the perturbed
   Hamiltonian a unique ground state for every sufficiently small `λ > 0`, converging to an
   effective ground state `Φeff` as `λ → 0⁺`. The full export accordingly packages, alongside the
   `λ`-family uniqueness and the convergence `Philam λ → Φeff`,
   `tasaki_lemma_10_1_degenerate_perturbation`'s own conclusion transported through `hEffGS`:
   a genuine `IsUniqueGroundStateOn` of `secondOrderEffectiveHamiltonian` on `matrixKernel
   (liebPerturbationH0Compressed N nUp)` at some energy `Eeff` and witness `Φeff`, not merely the
   existence of `Φeff` as a limit point.

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
PR-11a's assembly capstone
`isUniqueGroundStateOn_liebPerturbationH0Compressed_kernel_iff_heisenberg`)
has a **unique** ground state on `⊤`. Derived from `liebRepulsive_theorem23_instance`'s
Marshall-positive sector eigenvector via the Perron–Frobenius `finrank ≤ 1` route and PR-11a's
generic `finrank`-to-`IsUniqueGroundStateOn` builder plus its constant-shift transport, not directly
assumed. -/
theorem liebRepulsive_isUniqueGroundStateOn_heisenbergOnMagSector
    (A : Finset (Fin (N + 1))) (hA : 1 ≤ A.card) (hB : 1 ≤ (bipartitionComplement A).card)
    (nUp : ℕ)
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
  classical
  haveI hne : Nonempty (magConfigS (Fin (N + 1)) 1 (N + 1 - nUp)) :=
    magConfigS_nonempty_of_le_card_mul (by simp)
  obtain ⟨hcardA, hcardB, hA_ne, hB_ne⟩ :=
    liebOrientedSublattice_theorem23_side_conditions A hA hB
  obtain ⟨cdiag, hcdiag⟩ := exists_strict_diag_bound_dressedHeisenbergSReMatrix
    (fun x : Fin (N + 1) => decide (x ∈ liebOrientedSublattice A))
    ((2 : ℂ) • bipartiteCoupling
      (fun x : Fin (N + 1) => decide (x ∈ liebOrientedSublattice A))) 1
  obtain ⟨μ, hsector, hglobal⟩ := liebRepulsive_theorem23_instance A hA hB cdiag
    (liebRepulsiveJ_hJ_real _) (liebRepulsiveJ_hJ_real' _) (liebRepulsiveJ_hJ_sym _)
    (liebRepulsiveJ_hJ_nn _) (liebRepulsiveJ_hJ_bipartite _) (liebRepulsiveJ_hJ_pos _)
    hcdiag le_rfl hcardA hcardB
  obtain ⟨v, -, hv_pos, hH, -⟩ := hsector _ hM
  -- the orientation adapter: Theorem 2.3 runs at the oriented sublattice, the target at `A`
  have hJ : ((2 : ℂ) • bipartiteCoupling
        (fun x : Fin (N + 1) => decide (x ∈ liebOrientedSublattice A)))
      = ((2 : ℂ) • bipartiteCoupling (fun x : Fin (N + 1) => decide (x ∈ A))) := by
    rw [liebOrientedSublattice_bipartiteCoupling_eq]
  have hcomplex := heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
    (M := N + 1 - nUp) _ hH
  rw [magSectorRestriction_magSectorEmbedding] at hcomplex
  have hfinrank : Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianSMatrixOnMagSector
        ((2 : ℂ) • bipartiteCoupling (fun x : Fin (N + 1) => decide (x ∈ A))) 1
        (N + 1 - nUp))) (μ : ℂ)) ≤ 1 := by
    rw [← hJ]
    exact heisenbergHamiltonianSMatrixOnMagSector_finrank_le_one_of_marshall_positive
      (V := Fin (N + 1)) (N := 1)
      (fun x : Fin (N + 1) => decide (x ∈ liebOrientedSublattice A)) cdiag
      (liebRepulsiveJ_hJ_real _) (liebRepulsiveJ_hJ_pos _) (liebRepulsiveJ_hJ_nn _)
      (liebRepulsiveJ_hJ_sym _) (liebRepulsiveJ_hJ_bipartite _) hcdiag hA_ne hB_ne le_rfl hv_pos
      (by
        simpa only [Complex.ofReal_re] using
          heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec 1
            (liebRepulsiveJ_hJ_real _) hcomplex)
  rw [hJ] at hcomplex
  have hmem : (fun τ : magConfigS (Fin (N + 1)) 1 (N + 1 - nUp) =>
        (((marshallSignS (fun x => decide (x ∈ liebOrientedSublattice A)) τ.1).re * v τ : ℝ) : ℂ))
      ∈ Module.End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianSMatrixOnMagSector
          ((2 : ℂ) • bipartiteCoupling (fun x : Fin (N + 1) => decide (x ∈ A))) 1
          (N + 1 - nUp))) (μ : ℂ) :=
    Module.End.mem_eigenspace_iff.mpr (by rw [Matrix.toLin'_apply]; exact hcomplex)
  have hne0 : (fun τ : magConfigS (Fin (N + 1)) 1 (N + 1 - nUp) =>
      (((marshallSignS (fun x => decide (x ∈ liebOrientedSublattice A)) τ.1).re * v τ : ℝ) : ℂ))
      ≠ 0 := by
    intro h0
    set τ0 := Classical.arbitrary (magConfigS (Fin (N + 1)) 1 (N + 1 - nUp))
    have hτ : (marshallSignS (fun x => decide (x ∈ liebOrientedSublattice A)) τ0.1).re * v τ0
        = 0 := by simpa using congrFun h0 τ0
    rcases marshallSignS_re_eq_one_or_neg_one
        (fun x => decide (x ∈ liebOrientedSublattice A)) τ0.1 with h | h <;>
      rw [h] at hτ <;> nlinarith [hv_pos τ0]
  have hmin : ∀ μ' : ℝ, (∃ y : magConfigS (Fin (N + 1)) 1 (N + 1 - nUp) → ℂ, y ≠ 0 ∧
      Matrix.toLin' (heisenbergHamiltonianSMatrixOnMagSector
        ((2 : ℂ) • bipartiteCoupling (fun x : Fin (N + 1) => decide (x ∈ A))) 1
        (N + 1 - nUp)) y = (μ' : ℂ) • y) → μ ≤ μ' := by
    rintro μ' ⟨y, hy0, hyeig⟩
    rw [Matrix.toLin'_apply] at hyeig
    have hlift := heisenbergHamiltonianS_mulVec_magSectorEmbedding
      ((2 : ℂ) • bipartiteCoupling (fun x : Fin (N + 1) => decide (x ∈ A))) y hyeig
    rw [← hJ] at hlift
    refine hglobal (fun hemb => hy0 ?_) hlift
    funext τ
    have hτ := congrFun hemb τ.1
    rw [magSectorEmbedding_apply_subtype] at hτ
    simpa using hτ
  exact ⟨μ - ((A.card * (N + 1 - A.card) : ℕ) : ℝ), _,
    (isUniqueGroundStateOn_sub_smul_one_iff _ _ ((A.card * (N + 1 - A.card) : ℕ) : ℝ) μ _).mp
      (isUniqueGroundStateOn_of_finrank_eigenspace_le_one _ μ _ hmem hne0 hfinrank hmin)⟩

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
assets. The export therefore also carries `tasaki_lemma_10_1_degenerate_perturbation`'s own
conclusion: `∃ Eeff Φeff, IsUniqueGroundStateOn (matrixKernel (liebPerturbationH0Compressed N nUp))
(secondOrderEffectiveHamiltonian (liebPerturbationH0Compressed N nUp)
(liebPerturbationVCompressed N nUp A T) (liebPerturbationH0InvCompressed N nUp)) Eeff Φeff`, a
genuine unique-ground-state statement for the second-order effective Hamiltonian on `ker Ĥ₀c`, not
merely the existence of `Φeff` as a limit point. -/
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
      ∃ Eeff : ℝ,
      ∃ Φeff : EuclideanSpace ℂ (configSector N (liebHalfFillingPred N nUp)),
        (∀ lam : ℝ, 0 < lam → lam < lam0 →
          IsUniqueGroundStateOn
            (⊤ : Submodule ℂ (EuclideanSpace ℂ (configSector N (liebHalfFillingPred N nUp))))
            (perturbedHamiltonian (liebPerturbationH0Compressed N nUp)
              (liebPerturbationVCompressed N nUp A T) lam)
            (Elam lam) (Philam lam)) ∧
        IsUniqueGroundStateOn (matrixKernel (liebPerturbationH0Compressed N nUp))
          (secondOrderEffectiveHamiltonian (liebPerturbationH0Compressed N nUp)
            (liebPerturbationVCompressed N nUp A T) (liebPerturbationH0InvCompressed N nUp))
          Eeff Φeff ∧
        Filter.Tendsto Philam (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds Φeff) := by
  classical
  haveI hne : Nonempty (configSector N (liebHalfFillingPred N nUp)) :=
    configSector_liebHalfFillingPred_nonempty N nUp hnUp
  obtain ⟨E, Φheis, hGS⟩ :=
    liebRepulsive_isUniqueGroundStateOn_heisenbergOnMagSector A hA hB nUp hM
  obtain ⟨Φ, hΦmem, hΦrestrict⟩ :
      ∃ Φ : EuclideanSpace ℂ (configSector N (liebHalfFillingPred N nUp)),
        Φ ∈ matrixKernel (liebPerturbationH0Compressed N nUp) ∧
          (WithLp.toLp 2 fun j =>
              (WithLp.ofLp (coordinateRestrict (liebHalfFillingHardcorePred N nUp) Φ))
                (((liebHardCoreHalfFillingSectorEquivS N nUp hnUp).symm.trans
                  (liebHardCoreAmbientSubtypeEquiv N nUp)) j)) = Φheis := by
    refine ⟨coordinateExtend (liebHalfFillingHardcorePred N nUp)
      (WithLp.toLp 2 fun t => (WithLp.ofLp Φheis)
        (((liebHardCoreHalfFillingSectorEquivS N nUp hnUp).symm.trans
          (liebHardCoreAmbientSubtypeEquiv N nUp)).symm t)), ?_, ?_⟩
    · rw [matrixKernel_liebPerturbationH0Compressed_eq_coordinateSpan]
      exact coordinateExtend_mem_coordinateSpan _
    · rw [coordinateRestrict_coordinateExtend]
      exact PiLp.ext fun j => by simp
  have hshift : (((A.card : ℂ) * ((N + 1 - A.card : ℕ) : ℂ)))
      = (((A.card * (N + 1 - A.card) : ℕ) : ℝ) : ℂ) := by push_cast; ring
  have hEffGS : IsUniqueGroundStateOn (matrixKernel (liebPerturbationH0Compressed N nUp))
      (secondOrderEffectiveHamiltonian (liebPerturbationH0Compressed N nUp)
        (liebPerturbationVCompressed N nUp A T) (liebPerturbationH0InvCompressed N nUp)) E Φ := by
    rw [isUniqueGroundStateOn_liebPerturbationH0Compressed_kernel_iff_heisenberg
      N nUp hnUp hbip hT E Φ hΦmem, hΦrestrict, hshift]
    exact hGS
  obtain ⟨lam0, hlam0, Elam, Philam, hUnique, hTend⟩ :=
    tasaki_lemma_10_1_degenerate_perturbation (liebPerturbationH0Compressed N nUp)
      (liebPerturbationVCompressed N nUp A T) (liebPerturbationH0InvCompressed N nUp)
      (liebPerturbationH0Compressed_posSemidef N nUp).1
      (liebPerturbationH0Compressed_posSemidef N nUp)
      (liebPerturbationVCompressed_isHermitian N nUp A hT)
      (liebPerturbationH0Compressed_isReducedInverse N nUp)
      (kernelProjection_mul_liebPerturbationVCompressed_mul_kernelProjection N nUp hbip)
      E Φ hEffGS
  exact ⟨lam0, hlam0, Elam, Philam, E, Φ, hUnique, hEffGS, hTend⟩

end LatticeSystem.Fermion
