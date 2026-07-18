import LatticeSystem.Quantum.SpinS.MPSTheorem75Choi
import LatticeSystem.Quantum.SpinS.MPSTheorem75Peripheral

/-!
# Corrected Tasaki Theorem 7.5

This file assembles the two word-spanning directions and the primitive transfer-spectrum
condition under the explicit faithful-dual eigenmatrix hypothesis omitted from the printed
statement.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.2.2, Theorem 7.5, eqs. (7.2.41)–(7.2.42), pp. 202–203.
-/

namespace LatticeSystem.Quantum

open Matrix Module
open scoped ComplexOrder

variable {D N : ℕ}

/-- Rescale an MPS family by the inverse square root of its positive normalization eigenvalue. -/
private noncomputable def unitNormalizedMPS (A : MPSMatrices D N) (lam : ℝ) :
    MPSMatrices D N :=
  fun σ => (((Real.sqrt lam : ℝ) : ℂ)⁻¹) • A σ

/-- The inverse-square-root rescaling has squared modulus `lam⁻¹`. -/
private theorem unitNormalizedMPS_scalar_mul_star
    {lam : ℝ} (hlam : 0 < lam) :
    (((Real.sqrt lam : ℝ) : ℂ)⁻¹) *
        star (((Real.sqrt lam : ℝ) : ℂ)⁻¹) = ((lam : ℂ)⁻¹) := by
  change (((Real.sqrt lam : ℝ) : ℂ)⁻¹) *
    (starRingEnd ℂ) (((Real.sqrt lam : ℝ) : ℂ)⁻¹) = ((lam : ℂ)⁻¹)
  rw [map_inv₀, Complex.conj_ofReal]
  have hsqrt : ((Real.sqrt lam : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hlam).ne'
  field_simp
  exact_mod_cast (Real.sq_sqrt hlam.le).symm

/-- Positive-`lam` normalization becomes unit normalization after inverse-square-root rescaling. -/
private theorem unitNormalizedMPS_isNormalized
    (A : MPSMatrices D N) (lam : ℝ) (hnorm : IsMPSNormalized A lam) :
    IsMPSNormalized (unitNormalizedMPS A lam) 1 := by
  refine ⟨zero_lt_one, ?_⟩
  norm_num
  calc
    (∑ σ, unitNormalizedMPS A lam σ *
        (unitNormalizedMPS A lam σ).conjTranspose) =
        ((((Real.sqrt lam : ℝ) : ℂ)⁻¹) *
          star (((Real.sqrt lam : ℝ) : ℂ)⁻¹)) •
            ∑ σ, A σ * (A σ).conjTranspose := by
      simp only [unitNormalizedMPS, Matrix.smul_mul, Matrix.conjTranspose_smul,
        Matrix.mul_smul, ← smul_smul, Finset.smul_sum]
      congr 1
      funext σ
      rw [smul_smul, smul_smul, mul_comm]
    _ = ((lam : ℂ)⁻¹) •
        ∑ σ, A σ * (A σ).conjTranspose := by
      rw [unitNormalizedMPS_scalar_mul_star hnorm.1]
    _ = 1 := by
      rw [hnorm.2, smul_smul]
      simp [ne_of_gt hnorm.1]

/-- A faithful dual `lam`-eigenmatrix becomes a faithful dual fixed matrix after rescaling. -/
private theorem unitNormalizedMPS_hasFaithfulDualEigenmatrix
    (A : MPSMatrices D N) (lam : ℝ) (hlam : 0 < lam)
    (hfaith : HasFaithfulDualEigenmatrix A lam) :
    HasFaithfulDualEigenmatrix (unitNormalizedMPS A lam) 1 := by
  obtain ⟨ρ, hρ, hdual⟩ := hfaith
  refine ⟨ρ, hρ, ?_⟩
  norm_num
  calc
    mpsDualTransferMap (unitNormalizedMPS A lam) ρ =
        (star (((Real.sqrt lam : ℝ) : ℂ)⁻¹) *
          (((Real.sqrt lam : ℝ) : ℂ)⁻¹)) •
            mpsDualTransferMap A ρ := by
      simp only [mpsDualTransferMap, unitNormalizedMPS, Matrix.conjTranspose_smul,
        Matrix.smul_mul, Matrix.mul_smul, ← smul_smul, Finset.smul_sum]
      congr 1
      funext σ
      rw [smul_smul, smul_smul, mul_comm]
    _ = ((lam : ℂ)⁻¹) • mpsDualTransferMap A ρ := by
      rw [mul_comm, unitNormalizedMPS_scalar_mul_star hlam]
    _ = ρ := by
      rw [hdual, smul_smul]
      simp [ne_of_gt hlam]

/-- Ordered products of the rescaled family differ by the corresponding scalar power. -/
private theorem orderedProd_unitNormalizedMPS
    (A : MPSMatrices D N) (lam : ℝ) (σs : List (Fin (N + 1))) :
    orderedProd (unitNormalizedMPS A lam) σs =
      ((((Real.sqrt lam : ℝ) : ℂ)⁻¹) ^ σs.length) • orderedProd A σs := by
  induction σs with
  | nil => simp [orderedProd]
  | cons σ σs ih =>
      simp only [orderedProd, unitNormalizedMPS, ih, List.length_cons, pow_succ']
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- Fixed-length word spanning is unchanged by positive normalization rescaling. -/
private theorem mpsProductsSpanAt_unitNormalizedMPS_iff
    (A : MPSMatrices D N) (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    mpsProductsSpanAt (unitNormalizedMPS A lam) n ↔
      mpsProductsSpanAt A n := by
  have hc : (((Real.sqrt lam : ℝ) : ℂ)⁻¹) ≠ 0 := by
    exact inv_ne_zero (by exact_mod_cast (Real.sqrt_pos.2 hlam).ne')
  unfold mpsProductsSpanAt
  have hspan :
      Submodule.span ℂ {M : Matrix (Fin D) (Fin D) ℂ |
        ∃ σs : List (Fin (N + 1)), σs.length = n ∧
          M = orderedProd (unitNormalizedMPS A lam) σs} =
      Submodule.span ℂ {M : Matrix (Fin D) (Fin D) ℂ |
        ∃ σs : List (Fin (N + 1)), σs.length = n ∧
          M = orderedProd A σs} := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro M ⟨σs, hlen, rfl⟩
      rw [orderedProd_unitNormalizedMPS, hlen]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σs, hlen, rfl⟩)
    · apply Submodule.span_le.mpr
      rintro M ⟨σs, hlen, rfl⟩
      have hscaled := Submodule.smul_mem
        (Submodule.span ℂ {M : Matrix (Fin D) (Fin D) ℂ |
          ∃ τs : List (Fin (N + 1)), τs.length = n ∧
            M = orderedProd (unitNormalizedMPS A lam) τs})
        ((((Real.sqrt lam : ℝ) : ℂ)⁻¹) ^ n)⁻¹
        (Submodule.subset_span ⟨σs, hlen, rfl⟩)
      rw [orderedProd_unitNormalizedMPS, hlen, inv_smul_smul₀ (pow_ne_zero n hc)] at hscaled
      exact hscaled
  rw [hspan]

/-- Eventual fixed-length word spanning is invariant under normalization rescaling. -/
private theorem mpsSpansForAllLarge_unitNormalizedMPS_iff
    (A : MPSMatrices D N) (lam : ℝ) (hlam : 0 < lam) :
    MPSSpansForAllLarge (unitNormalizedMPS A lam) ↔
      MPSSpansForAllLarge A := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, fun ℓ hℓ =>
      (mpsProductsSpanAt_unitNormalizedMPS_iff A lam hlam ℓ).mp (hn ℓ hℓ)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, fun ℓ hℓ =>
      (mpsProductsSpanAt_unitNormalizedMPS_iff A lam hlam ℓ).mpr (hn ℓ hℓ)⟩

/-- The transfer matrix of the normalized family is `lam⁻¹` times the original transfer. -/
private theorem mpsTransferMatrix_unitNormalizedMPS
    (A : MPSMatrices D N) (lam : ℝ) (hlam : 0 < lam) :
    mpsTransferMatrix (unitNormalizedMPS A lam) =
      ((lam : ℂ)⁻¹) • mpsTransferMatrix A := by
  ext p q
  simp only [mpsTransferMatrix, unitNormalizedMPS, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul]
  change (∑ x, ((starRingEnd ℂ)
      ((((Real.sqrt lam : ℝ) : ℂ)⁻¹) * A x p.1 q.1)) *
        ((((Real.sqrt lam : ℝ) : ℂ)⁻¹) * A x p.2 q.2)) =
    ((lam : ℂ)⁻¹) * ∑ σ, star (A σ p.1 q.1) * A σ p.2 q.2
  simp_rw [map_mul, map_inv₀, Complex.conj_ofReal]
  calc
    (∑ x, (((Real.sqrt lam : ℝ) : ℂ)⁻¹) *
        (starRingEnd ℂ) (A x p.1 q.1) *
          ((((Real.sqrt lam : ℝ) : ℂ)⁻¹) * A x p.2 q.2)) =
        ∑ x, ((((Real.sqrt lam : ℝ) : ℂ)⁻¹) *
          (((Real.sqrt lam : ℝ) : ℂ)⁻¹)) *
            ((starRingEnd ℂ) (A x p.1 q.1) * A x p.2 q.2) := by
      congr 1
      funext σ
      ring_nf
    _ = ((lam : ℂ)⁻¹) *
        ∑ σ, star (A σ p.1 q.1) * A σ p.2 q.2 := by
      have hscalar :
          (((Real.sqrt lam : ℝ) : ℂ)⁻¹) *
            (((Real.sqrt lam : ℝ) : ℂ)⁻¹) = ((lam : ℂ)⁻¹) := by
        simpa [RCLike.star_def, map_inv₀, Complex.conj_ofReal] using
          unitNormalizedMPS_scalar_mul_star hlam
      rw [hscalar, Finset.mul_sum]
      congr 1

/-- Primitive transfer-spectrum data scales exactly with the positive normalization eigenvalue. -/
private theorem hasPrimitiveTransferSpectrum_unitNormalizedMPS_iff
    (A : MPSMatrices D N) (lam : ℝ) (hlam : 0 < lam) :
    HasPrimitiveTransferSpectrum (unitNormalizedMPS A lam) 1 ↔
      HasPrimitiveTransferSpectrum A lam := by
  let l : ℂ := lam
  have hl : l ≠ 0 := by
    change (lam : ℂ) ≠ 0
    exact_mod_cast (ne_of_gt hlam)
  let u : ℂˣ := Units.mk0 l hl
  have htransfer := mpsTransferMatrix_unitNormalizedMPS A lam hlam
  have hspectrum (μ : ℂ) :
      μ ∈ spectrum ℂ (mpsTransferMatrix (unitNormalizedMPS A lam)) ↔
        l * μ ∈ spectrum ℂ (mpsTransferMatrix A) := by
    rw [htransfer]
    have h := spectrum.smul_mem_smul_iff
      (a := mpsTransferMatrix A) (s := l * μ) (r := u⁻¹)
    simpa [u, l, Units.smul_def, Units.val_inv_eq_inv_val,
      smul_eq_mul, hl] using h
  have hlin :
      (mpsTransferMatrix (unitNormalizedMPS A lam)).mulVecLin =
        l⁻¹ • (mpsTransferMatrix A).mulVecLin := by
    rw [htransfer]
    apply LinearMap.ext
    intro v
    exact Matrix.smul_mulVec _ _ _
  have hmap :
      (mpsTransferMatrix (unitNormalizedMPS A lam)).mulVecLin -
          (1 : ℂ) • LinearMap.id =
        l⁻¹ • ((mpsTransferMatrix A).mulVecLin - l • LinearMap.id) := by
    rw [hlin]
    apply LinearMap.ext
    intro v
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, one_smul,
      LinearMap.id_coe, id_eq]
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hl, one_smul]
  have hker :
      LinearMap.ker
          ((mpsTransferMatrix (unitNormalizedMPS A lam)).mulVecLin -
            (1 : ℂ) • LinearMap.id) =
        LinearMap.ker
          ((mpsTransferMatrix A).mulVecLin - l • LinearMap.id) := by
    rw [hmap, LinearMap.ker_smul _ l⁻¹ (inv_ne_zero hl)]
  have hnorml : ‖l‖ = lam := by
    dsimp [l]
    rw [Complex.norm_real, Real.norm_of_nonneg hlam.le]
  constructor
  · rintro ⟨hone, hfin, hgap⟩
    have hone' := (hspectrum 1).mp (by simpa using hone)
    refine ⟨by simpa [l] using hone', ?_, ?_⟩
    · have hfin' :
          finrank ℂ (LinearMap.ker
            ((mpsTransferMatrix (unitNormalizedMPS A lam)).mulVecLin -
              (1 : ℂ) • LinearMap.id)) = 1 := by
          simpa using hfin
      rw [hker] at hfin'
      simpa [l] using hfin'
    · intro μ hμ hμne
      have hscaledSpec := (hspectrum (l⁻¹ * μ)).mpr (by simpa [hl] using hμ)
      have hscaledNe : l⁻¹ * μ ≠ 1 := by
        intro heq
        apply hμne
        calc
          μ = l * (l⁻¹ * μ) := by rw [← mul_assoc, mul_inv_cancel₀ hl, one_mul]
          _ = l := by rw [heq, mul_one]
          _ = (lam : ℂ) := rfl
      have hscaled := hgap (l⁻¹ * μ) hscaledSpec hscaledNe
      calc
        ‖μ‖ = ‖l * (l⁻¹ * μ)‖ := by
          rw [← mul_assoc, mul_inv_cancel₀ hl, one_mul]
        _ = ‖l‖ * ‖l⁻¹ * μ‖ := norm_mul _ _
        _ < lam * 1 := by
          rw [hnorml]
          exact mul_lt_mul_of_pos_left hscaled hlam
        _ = lam := mul_one _
  · rintro ⟨hone, hfin, hgap⟩
    refine ⟨(hspectrum 1).mpr (by simpa [l] using hone), ?_, ?_⟩
    · have hfin' :
          finrank ℂ (LinearMap.ker
            ((mpsTransferMatrix A).mulVecLin - l • LinearMap.id)) = 1 := by
          simpa [l] using hfin
      rw [← hker] at hfin'
      simpa using hfin'
    · intro μ hμ hμne
      have hscaledSpec := (hspectrum μ).mp hμ
      have hscaledNe : l * μ ≠ (lam : ℂ) := by
        intro heq
        apply hμne
        apply (mul_left_cancel₀ hl)
        simpa [l] using heq
      have hscaled := hgap (l * μ) hscaledSpec hscaledNe
      have hmul : lam * ‖μ‖ < lam * 1 := by
        simpa [norm_mul, hnorml] using hscaled
      nlinarith

/-- Unit primitive transfer data supplies the concrete Kraus hypotheses of the reverse endpoint. -/
private theorem mpsSpansForAllLarge_of_unit_faithful_primitive [NeZero D]
    (A : MPSMatrices D N)
    (hnorm : IsMPSNormalized A 1)
    (hfaith : HasFaithfulDualEigenmatrix A 1)
    (hprimitive : HasPrimitiveTransferSpectrum A 1) :
    MPSSpansForAllLarge A := by
  letI : FiniteDimensional ℂ (CStarMatrix (Fin D) (Fin D) ℂ) :=
    CStarMatrix.ofMatrixₗ.finiteDimensional
  let e : CStarMatrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] ((Fin D × Fin D) → ℂ) :=
    { toFun := fun X p => X p.2 p.1
      invFun := fun v => CStarMatrix.ofMatrix fun i j => v (j, i)
      left_inv := fun X => by ext i j; rfl
      right_inv := fun v => by ext p; rfl
      map_add' := fun X Y => by ext p; rfl
      map_smul' := fun c X => by ext p; rfl }
  have hintertwine (X : CStarMatrix (Fin D) (Fin D) ℂ) :
      (mpsTransferMatrix A).mulVec (e X) = e (MPSTheorem75.Internal.finiteKrausMap A X) := by
    ext p
    simp only [mpsTransferMatrix, Matrix.mulVec, dotProduct, e, LinearEquiv.coe_mk,
      Matrix.of_apply, Fintype.sum_prod_type, MPSTheorem75.Internal.finiteKrausMap,
      LinearMap.coe_mk, AddHom.coe_mk]
    simp_rw [Finset.sum_mul]
    calc
      (∑ α' : Fin D, ∑ β' : Fin D, ∑ σ : Fin (N + 1),
          star (A σ p.1 α') * A σ p.2 β' * X β' α') =
          ∑ α' : Fin D, ∑ σ : Fin (N + 1), ∑ β' : Fin D,
            star (A σ p.1 α') * A σ p.2 β' * X β' α' := by
        apply Finset.sum_congr rfl
        intro α' _
        exact Finset.sum_comm
      _ = ∑ σ : Fin (N + 1), ∑ α' : Fin D, ∑ β' : Fin D,
          star (A σ p.1 α') * A σ p.2 β' * X β' α' := Finset.sum_comm
      _ = ∑ σ : Fin (N + 1), ∑ α' : Fin D, ∑ β' : Fin D,
          A σ p.2 β' * X β' α' * star (A σ p.1 α') := by
        congr 1
        funext σ
        congr 1
        funext α'
        congr 1
        funext β'
        ring
      _ = (∑ σ : Fin (N + 1),
          CStarMatrix.ofMatrix (A σ) * X *
            star (CStarMatrix.ofMatrix (A σ))) p.2 p.1 := by
        have hsum :
            (∑ σ : Fin (N + 1),
              CStarMatrix.ofMatrix (A σ) * X *
                star (CStarMatrix.ofMatrix (A σ))) p.2 p.1 =
              ∑ σ : Fin (N + 1),
                (CStarMatrix.ofMatrix (A σ) * X *
                  star (CStarMatrix.ofMatrix (A σ))) p.2 p.1 := by
          classical
          induction (Finset.univ : Finset (Fin (N + 1))) using Finset.induction_on with
          | empty => simp [CStarMatrix.zero_apply]
          | insert σ s hσ ih => simp [hσ, ih, CStarMatrix.add_apply]
        rw [hsum]
        simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply,
          CStarMatrix.ofMatrix_apply]
        simp_rw [Finset.sum_mul]
  have hconj :
      e.conjAlgEquiv ℂ (MPSTheorem75.Internal.finiteKrausMap A) =
        (mpsTransferMatrix A).mulVecLin := by
    apply LinearMap.ext
    intro v
    obtain ⟨X, rfl⟩ := e.surjective v
    simp only [LinearEquiv.conjAlgEquiv_apply, LinearMap.coe_comp,
      Function.comp_apply]
    simpa using (hintertwine X).symm
  have hspectrum :
      spectrum ℂ (MPSTheorem75.Internal.finiteKrausMap A) =
        spectrum ℂ (mpsTransferMatrix A) := by
    rw [← Matrix.spectrum_toLin']
    change spectrum ℂ (MPSTheorem75.Internal.finiteKrausMap A) =
      spectrum ℂ (mpsTransferMatrix A).mulVecLin
    rw [← hconj]
    exact (AlgEquiv.spectrum_eq
      (e.conjAlgEquiv ℂ) (MPSTheorem75.Internal.finiteKrausMap A)).symm
  have hunital :
      MPSTheorem75.Internal.finiteKrausMap A
        (1 : CStarMatrix (Fin D) (Fin D) ℂ) = 1 := by
    simpa [MPSTheorem75.Internal.finiteKrausMap] using hnorm.2
  have hfixed :
      ∀ X, MPSTheorem75.Internal.finiteKrausMap A X = X →
        ∃ c : ℂ, X = c • (1 : CStarMatrix (Fin D) (Fin D) ℂ) := by
    intro X hX
    let K := LinearMap.ker
      ((mpsTransferMatrix A).mulVecLin - (1 : ℂ) • LinearMap.id)
    have hKfin : finrank ℂ K = 1 := by
      simpa [K] using hprimitive.2.1
    have honeK : e (1 : CStarMatrix (Fin D) (Fin D) ℂ) ∈ K := by
      change e (1 : CStarMatrix (Fin D) (Fin D) ℂ) ∈ LinearMap.ker
        ((mpsTransferMatrix A).mulVecLin - (1 : ℂ) • LinearMap.id)
      rw [LinearMap.mem_ker]
      simp only [LinearMap.sub_apply, one_smul, LinearMap.id_coe, id_eq]
      change (mpsTransferMatrix A).mulVec (e 1) - e 1 = 0
      rw [hintertwine, hunital, sub_self]
    have honeNe : e (1 : CStarMatrix (Fin D) (Fin D) ℂ) ≠ 0 := by
      apply e.map_ne_zero_iff.mpr
      intro hzero
      have hentry := congrFun (congrFun hzero (0 : Fin D)) (0 : Fin D)
      norm_num [CStarMatrix.one_apply, CStarMatrix.zero_apply] at hentry
    have hspanle : ℂ ∙ e (1 : CStarMatrix (Fin D) (Fin D) ℂ) ≤ K :=
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr honeK)
    have hspanfin :
        finrank ℂ (ℂ ∙ e (1 : CStarMatrix (Fin D) (Fin D) ℂ)) = 1 :=
      finrank_span_singleton honeNe
    have hKeq : ℂ ∙ e (1 : CStarMatrix (Fin D) (Fin D) ℂ) = K :=
      Submodule.eq_of_le_of_finrank_le hspanle (by rw [hKfin, hspanfin])
    have heX : e X ∈ K := by
      change e X ∈ LinearMap.ker
        ((mpsTransferMatrix A).mulVecLin - (1 : ℂ) • LinearMap.id)
      rw [LinearMap.mem_ker]
      simp only [LinearMap.sub_apply, one_smul, LinearMap.id_coe, id_eq]
      change (mpsTransferMatrix A).mulVec (e X) - e X = 0
      rw [hintertwine, hX, sub_self]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hKeq.symm ▸ heX)
    exact ⟨c, e.injective (by simpa using hc.symm)⟩
  have hgap :
      ∀ μ ∈ spectrum ℂ (MPSTheorem75.Internal.finiteKrausMap A),
        μ ≠ 1 → ‖μ‖ < 1 := by
    intro μ hμ hμne
    exact hprimitive.2.2 μ (hspectrum ▸ hμ) (by simpa using hμne)
  exact MPSTheorem75.Internal.mps_spans_for_all_large_of_unit_faithful_spectral_gap
    A hnorm hfaith hfixed hgap

/-- Under normalization and a faithful dual eigenmatrix, eventual word spanning is equivalent to
the primitive transfer-spectrum condition.

This is the corrected form of the equivalence between conditions (ii) and (iii) in Tasaki
Theorem 7.5. The printed statement omits the faithful dual eigenmatrix condition supplied here
explicitly. -/
theorem mps_spans_for_all_large_iff_has_primitive_transfer_spectrum [NeZero D]
    (A : MPSMatrices D N) (lam : ℝ)
    (hnorm : IsMPSNormalized A lam)
    (hfaith : HasFaithfulDualEigenmatrix A lam) :
    MPSSpansForAllLarge A ↔ HasPrimitiveTransferSpectrum A lam := by
  have hnormUnit := unitNormalizedMPS_isNormalized A lam hnorm
  have hfaithUnit :=
    unitNormalizedMPS_hasFaithfulDualEigenmatrix A lam hnorm.1 hfaith
  constructor
  · intro hspan
    have hspanUnit :=
      (mpsSpansForAllLarge_unitNormalizedMPS_iff A lam hnorm.1).mpr hspan
    have hprimitiveUnit :=
      MPSTheorem75.Internal.has_primitive_transfer_spectrum_of_unit_faithful_spanning
        (unitNormalizedMPS A lam) hnormUnit hfaithUnit hspanUnit
    exact (hasPrimitiveTransferSpectrum_unitNormalizedMPS_iff A lam hnorm.1).mp
      hprimitiveUnit
  · intro hprimitive
    have hprimitiveUnit :=
      (hasPrimitiveTransferSpectrum_unitNormalizedMPS_iff A lam hnorm.1).mpr hprimitive
    have hspanUnit :=
      mpsSpansForAllLarge_of_unit_faithful_primitive
        (unitNormalizedMPS A lam) hnormUnit hfaithUnit hprimitiveUnit
    exact (mpsSpansForAllLarge_unitNormalizedMPS_iff A lam hnorm.1).mp hspanUnit

/-- **Corrected Tasaki Theorem 7.5 (injective matrix product states).**

For a normalized MPS family of positive bond dimension with a positive-definite dual
`lam`-eigenmatrix, conditions (i) fixed-length spanning, (ii) spanning at every sufficiently
large length, and (iii) a simple primitive transfer eigenvalue are equivalent. Tasaki's printed
statement omits the faithful dual/canonical condition; the formal theorem exposes it explicitly.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.2.2, Theorem 7.5, eqs. (7.2.41)–(7.2.42), pp. 202–203. -/
theorem mps_theorem_7_5
    (A : MPSMatrices D N) (lam : ℝ) (hD : 0 < D)
    (hnorm : IsMPSNormalized A lam)
    (hfaith : HasFaithfulDualEigenmatrix A lam) :
    (MPSSpansEventually A ↔ MPSSpansForAllLarge A) ∧
      (MPSSpansForAllLarge A ↔ HasPrimitiveTransferSpectrum A lam) := by
  letI : NeZero D := ⟨Nat.ne_of_gt hD⟩
  exact ⟨LatticeSystem.Quantum.mps_spans_eventually_iff_spans_for_all_large A lam hnorm,
    mps_spans_for_all_large_iff_has_primitive_transfer_spectrum A lam hnorm hfaith⟩

end LatticeSystem.Quantum
