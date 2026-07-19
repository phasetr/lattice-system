import LatticeSystem.Quantum.SpinS.MPSTheorem76Algebra
import LatticeSystem.Quantum.SpinS.MPSTheorem75Linear
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Unitary gauge data for Tasaki Theorem 7.6

This file turns the algebra transport of equal injective MPS representations into a unitary gauge.
It also proves equality of the normalization constants, scalarity of the positive inverse metric,
and uniqueness of the gauge up to phase.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.2.2, Theorem 7.6, eqs. (7.2.43)–(7.2.44), p. 203.
-/

namespace LatticeSystem.Quantum

open Matrix Module
open scoped CStarAlgebra ComplexOrder

variable {D N : ℕ}

/-- Finite square `CStarMatrix` spaces are finite-dimensional over `ℂ`. -/
private noncomputable local instance cstarMatrixFiniteDimensional :
    FiniteDimensional ℂ (CStarMatrix (Fin D) (Fin D) ℂ) :=
  CStarMatrix.ofMatrixₗ.finiteDimensional

/-- Every complex square-matrix algebra equivalence is conjugation by an invertible matrix. -/
private theorem exists_inner_matrix
    (e : Matrix (Fin D) (Fin D) ℂ ≃ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    ∃ P R : Matrix (Fin D) (Fin D) ℂ,
      P * R = 1 ∧ R * P = 1 ∧ ∀ X, e X = P * X * R := by
  let eEnd :
      ((Fin D → ℂ) →ₗ[ℂ] Fin D → ℂ) ≃ₐ[ℂ]
        ((Fin D → ℂ) →ₗ[ℂ] Fin D → ℂ) :=
    Matrix.toLinAlgEquiv'.symm.trans (e.trans Matrix.toLinAlgEquiv')
  obtain ⟨T, hT⟩ := eEnd.eq_linearEquivConjAlgEquiv
  let P := LinearMap.toMatrixAlgEquiv' T.toLinearMap
  let R := LinearMap.toMatrixAlgEquiv' T.symm.toLinearMap
  refine ⟨P, R, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrixAlgEquiv'_comp]
    simp
  · rw [← LinearMap.toMatrixAlgEquiv'_comp]
    simp
  · intro X
    have hx := DFunLike.congr_fun hT (Matrix.toLinAlgEquiv' X)
    have hx' := congrArg LinearMap.toMatrixAlgEquiv' hx
    simpa only [eEnd, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply,
      LinearEquiv.conjAlgEquiv_apply, LinearMap.toMatrixAlgEquiv'_comp,
      LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv', P, R, Matrix.mul_assoc] using hx'

/-- The completely positive transfer associated with an MPS matrix family. -/
private noncomputable def transfer (A : MPSMatrices D N)
    (X : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  ∑ σ, A σ * X * (A σ).conjTranspose

/-- An inverse implementer produces the positive candidate `(Pᴴ P)⁻¹`. -/
private noncomputable def inverseMetric
    (R : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  R * R.conjTranspose

/-- A two-sided inverse makes the inverse metric positive definite. -/
private theorem inverseMetric_posDef
    (P R : Matrix (Fin D) (Fin D) ℂ)
    (hPR : P * R = 1) (hRP : R * P = 1) :
    (inverseMetric R).PosDef := by
  have hunitR : IsUnit R := isUnit_iff_exists.mpr ⟨P, hRP, hPR⟩
  exact Matrix.PosDef.mul_conjTranspose_self R (Matrix.vecMul_injective_of_isUnit hunitR)

/-- Conjugation by an invertible matrix transports normalization to a positive transfer
eigenmatrix. -/
private theorem inverseMetric_eigen
    (A B : MPSMatrices D N) (lamB : ℝ)
    (P R : Matrix (Fin D) (Fin D) ℂ) (hRP : R * P = 1)
    (hgauge : ∀ σ, B σ = P * A σ * R) (hnormB : IsMPSNormalized B lamB) :
    transfer A (inverseMetric R) = (lamB : ℂ) • inverseMetric R := by
  have hPstarRstar : P.conjTranspose * R.conjTranspose = 1 := by
    simpa only [← Matrix.conjTranspose_mul, Matrix.conjTranspose_one] using
      congrArg Matrix.conjTranspose hRP
  have hterm (σ : Fin (N + 1)) :
      R * (B σ * (B σ).conjTranspose) * R.conjTranspose =
        A σ * inverseMetric R * (A σ).conjTranspose := by
    rw [hgauge, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [← Matrix.mul_assoc, hRP, Matrix.one_mul, inverseMetric]
    rw [Matrix.mul_assoc, hPstarRstar, Matrix.mul_one]
  calc
    transfer A (inverseMetric R) =
        ∑ σ, R * (B σ * (B σ).conjTranspose) * R.conjTranspose := by
      apply Finset.sum_congr rfl
      intro σ _
      exact (hterm σ).symm
    _ = R * (∑ σ, B σ * (B σ).conjTranspose) * R.conjTranspose := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = R * ((lamB : ℂ) • 1) * R.conjTranspose := by rw [hnormB.2]
    _ = (lamB : ℂ) • inverseMetric R := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, inverseMetric]

/-- A positive scalar inverse metric rescales the inner implementer to a unitary matrix. -/
private theorem unitary_rescale_of_inverseMetric_eq_smul_one
    (P R : Matrix (Fin D) (Fin D) ℂ) (hPR : P * R = 1)
    (c : ℝ) (hc : 0 < c) (hmetric : inverseMetric R = (c : ℂ) • 1) :
    ∃ W : Matrix (Fin D) (Fin D) ℂ,
      W ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
      ∀ X, P * X * R = W * X * W.conjTranspose := by
  let s : ℂ := (Real.sqrt c : ℝ)
  let W : Matrix (Fin D) (Fin D) ℂ := s • P
  have hss : s * s = (c : ℂ) := by
    dsimp only [s]
    have hr : Real.sqrt c * Real.sqrt c = c := by
      simpa only [pow_two] using Real.sq_sqrt hc.le
    exact_mod_cast hr
  have hRstarPstar : R.conjTranspose * P.conjTranspose = 1 := by
    simpa only [← Matrix.conjTranspose_mul, Matrix.conjTranspose_one] using
      congrArg Matrix.conjTranspose hPR
  have hPPstar : (c : ℂ) • (P * P.conjTranspose) = 1 := by
    have hconj : P * inverseMetric R * P.conjTranspose = 1 := by
      simp only [inverseMetric, ← Matrix.mul_assoc, hPR, Matrix.one_mul]
      exact hRstarPstar
    rw [hmetric] at hconj
    simpa only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] using hconj
  have hWunit : W ∈ Matrix.unitaryGroup (Fin D) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    simp only [W, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show star s = s by exact Complex.conj_ofReal _, hss, hPPstar]
  refine ⟨W, hWunit, ?_⟩
  intro X
  have hWR : W * R = s • (1 : Matrix (Fin D) (Fin D) ℂ) := by
    simp only [W, Matrix.smul_mul, hPR]
  have hR : R = s • W.conjTranspose := by
    have h := congrArg (fun Y => W.conjTranspose * Y) hWR
    have hstarW : W.conjTranspose * W = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp hWunit
    simpa only [← Matrix.mul_assoc, hstarW, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one] using h
  rw [hR]
  simp only [Matrix.mul_smul, W, Matrix.smul_mul, Matrix.mul_assoc]

/-- The inverse-square-root rescaling of an MPS family as a `CStarMatrix` Kraus family. -/
private noncomputable def scaledKraus (A : MPSMatrices D N) (lam : ℝ) :
    Fin (N + 1) → CStarMatrix (Fin D) (Fin D) ℂ :=
  fun σ => (((Real.sqrt lam : ℝ) : ℂ)⁻¹) • CStarMatrix.ofMatrix (A σ)

/-- The inverse square-root scaling coefficient has squared modulus `lam⁻¹`. -/
private theorem scaledKraus_scalar_sq {lam : ℝ} (hlam : 0 < lam) :
    (((Real.sqrt lam : ℝ) : ℂ)⁻¹) *
      star (((Real.sqrt lam : ℝ) : ℂ)⁻¹) = (lam : ℂ)⁻¹ := by
  change (((Real.sqrt lam : ℝ) : ℂ)⁻¹) *
    (starRingEnd ℂ) (((Real.sqrt lam : ℝ) : ℂ)⁻¹) = (lam : ℂ)⁻¹
  rw [map_inv₀, Complex.conj_ofReal]
  have hsqrt : ((Real.sqrt lam : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hlam).ne'
  field_simp
  exact_mod_cast (Real.sq_sqrt hlam.le).symm

/-- The reversed scalar product has the same inverse-normalization value. -/
private theorem scaledKraus_star_scalar_mul {lam : ℝ} (hlam : 0 < lam) :
    star (((Real.sqrt lam : ℝ) : ℂ)⁻¹) *
      (((Real.sqrt lam : ℝ) : ℂ)⁻¹) = (lam : ℂ)⁻¹ := by
  rw [mul_comm]
  exact scaledKraus_scalar_sq hlam

/-- The MPS normalization equation makes `scaledKraus` unital. -/
private theorem scaledKraus_unital
    (A : MPSMatrices D N) (lam : ℝ) (hnorm : IsMPSNormalized A lam) :
    MPSTheorem75.Internal.finiteKrausMap (scaledKraus A lam) 1 = 1 := by
  change (∑ σ, scaledKraus A lam σ * 1 * star (scaledKraus A lam σ)) = 1
  simp only [scaledKraus, mul_one, star_smul,
    CStarMatrix.smul_mul, CStarMatrix.mul_smul, smul_smul]
  rw [scaledKraus_star_scalar_mul hnorm.1, ← Finset.smul_sum]
  change (lam : ℂ)⁻¹ • (∑ σ, A σ * (A σ).conjTranspose) = 1
  rw [hnorm.2, smul_smul]
  simp [ne_of_gt hnorm.1]

/-- An unscaled positive-transfer eigenmatrix acquires eigenratio `mu / lam` after normalization. -/
private theorem scaledKraus_eigen
    (A : MPSMatrices D N) (lam mu : ℝ) (hnorm : IsMPSNormalized A lam)
    (Q : CStarMatrix (Fin D) (Fin D) ℂ)
    (hQ : (∑ σ, CStarMatrix.ofMatrix (A σ) * Q *
      star (CStarMatrix.ofMatrix (A σ))) = (mu : ℂ) • Q) :
    MPSTheorem75.Internal.finiteKrausMap (scaledKraus A lam) Q =
      ((mu / lam : ℝ) : ℂ) • Q := by
  change (∑ σ, scaledKraus A lam σ * Q * star (scaledKraus A lam σ)) =
    ((mu / lam : ℝ) : ℂ) • Q
  simp only [scaledKraus, star_smul, CStarMatrix.mul_smul,
    CStarMatrix.smul_mul, smul_smul]
  rw [scaledKraus_star_scalar_mul hnorm.1, ← Finset.smul_sum, hQ, smul_smul]
  congr 1
  push_cast
  field_simp

/-- Powers of a linear map act by scalar powers on an eigenvector. -/
private theorem linearMap_pow_apply_eigen
    {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (f : Module.End ℂ V) (X : V) (r : ℂ) (hX : f X = r • X) :
    ∀ n : ℕ, (f ^ n) X = r ^ n • X := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, hX, map_smul, ih, smul_smul]
      rw [pow_succ', mul_comm]

/-- The production power bound forces a positive real unital-Kraus eigenratio to be at most one. -/
private theorem eigenratio_le_one_of_unital_kraus
    [NeZero D]
    (K : Fin (N + 1) → CStarMatrix (Fin D) (Fin D) ℂ)
    (Q : CStarMatrix (Fin D) (Fin D) ℂ) (r : ℝ)
    (hunital : MPSTheorem75.Internal.finiteKrausMap K 1 = 1)
    (hQne : Q ≠ 0) (hr : 0 < r)
    (heig : MPSTheorem75.Internal.finiteKrausMap K Q = (r : ℂ) • Q) :
    r ≤ 1 := by
  by_contra hrle
  have hrone : 1 < r := lt_of_not_ge hrle
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (4 : ℝ) hrone
  have hbound := MPSTheorem75.Internal.norm_finiteKrausMap_pow_le K hunital n Q
  rw [linearMap_pow_apply_eigen _ Q (r : ℂ) heig n] at hbound
  have hQnorm : 0 < ‖Q‖ := norm_pos_iff.mpr hQne
  have hpowNorm : ‖((r : ℂ) ^ n)‖ = r ^ n := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  rw [norm_smul, hpowNorm] at hbound
  have hpowLe : r ^ n ≤ 4 := le_of_mul_le_mul_right hbound hQnorm
  exact (not_lt_of_ge hpowLe) hn

/-- Two normalized positive-transfer eigenratios force equality of the normalization constants. -/
private theorem normalization_eq_of_two_scaled_eigenmatrices
    (A B : MPSMatrices D N) (lamA lamB : ℝ)
    (QA QB : CStarMatrix (Fin D) (Fin D) ℂ)
    (hnormA : IsMPSNormalized A lamA) (hnormB : IsMPSNormalized B lamB)
    (hQAne : QA ≠ 0) (hQBne : QB ≠ 0)
    (hQAeig : (∑ σ, CStarMatrix.ofMatrix (A σ) * QA *
      star (CStarMatrix.ofMatrix (A σ))) = (lamB : ℂ) • QA)
    (hQBeig : (∑ σ, CStarMatrix.ofMatrix (B σ) * QB *
      star (CStarMatrix.ofMatrix (B σ))) = (lamA : ℂ) • QB) :
    lamA = lamB := by
  have hD : D ≠ 0 := by
    intro hzero
    subst D
    apply hQAne
    ext i
    exact Fin.elim0 i
  letI : NeZero D := ⟨hD⟩
  have hAB : lamB / lamA ≤ 1 :=
    eigenratio_le_one_of_unital_kraus (scaledKraus A lamA) QA (lamB / lamA)
      (scaledKraus_unital A lamA hnormA) hQAne (div_pos hnormB.1 hnormA.1)
      (scaledKraus_eigen A lamA lamB hnormA QA hQAeig)
  have hBA : lamA / lamB ≤ 1 :=
    eigenratio_le_one_of_unital_kraus (scaledKraus B lamB) QB (lamA / lamB)
      (scaledKraus_unital B lamB hnormB) hQBne (div_pos hnormA.1 hnormB.1)
      (scaledKraus_eigen B lamB lamA hnormB QB hQBeig)
  exact le_antisymm ((div_le_one hnormB.1).mp hBA) ((div_le_one hnormA.1).mp hAB)

/-- An index at which a Hermitian matrix has a largest eigenvalue. -/
private noncomputable def maxEigenIndex [NeZero D]
    {Q : Matrix (Fin D) (Fin D) ℂ} (hQ : Q.IsHermitian) : Fin D :=
  Classical.choose
    (Finset.exists_max_image (Finset.univ : Finset (Fin D)) hQ.eigenvalues
      Finset.univ_nonempty)

/-- The eigenvalue selected at `maxEigenIndex`. -/
private noncomputable def maxEigenvalue [NeZero D]
    {Q : Matrix (Fin D) (Fin D) ℂ} (hQ : Q.IsHermitian) : ℝ :=
  hQ.eigenvalues (maxEigenIndex hQ)

/-- Every eigenvalue is bounded above by the selected maximum eigenvalue. -/
private theorem eigenvalue_le_maxEigenvalue [NeZero D]
    {Q : Matrix (Fin D) (Fin D) ℂ} (hQ : Q.IsHermitian) (i : Fin D) :
    hQ.eigenvalues i ≤ maxEigenvalue hQ := by
  exact (Classical.choose_spec
    (Finset.exists_max_image (Finset.univ : Finset (Fin D)) hQ.eigenvalues
      Finset.univ_nonempty)).2 i (Finset.mem_univ i)

/-- The scalar identity minus `Q`, using the largest eigenvalue of `Q`. -/
private noncomputable def maxDefect [NeZero D]
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian) :
    Matrix (Fin D) (Fin D) ℂ :=
  (maxEigenvalue hQ : ℂ) • 1 - Q

/-- The maximum defect is positive semidefinite. -/
private theorem maxDefect_posSemidef [NeZero D]
    {Q : Matrix (Fin D) (Fin D) ℂ} (hQ : Q.PosDef) :
    (maxDefect Q hQ.1).PosSemidef := by
  let U : Matrix (Fin D) (Fin D) ℂ := hQ.1.eigenvectorUnitary
  let d : Fin D → ℂ := fun i => ((maxEigenvalue hQ.1 - hQ.1.eigenvalues i : ℝ) : ℂ)
  have hd : (Matrix.diagonal d).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ ((maxEigenvalue hQ.1 - hQ.1.eigenvalues i : ℝ) : ℂ)
    exact_mod_cast sub_nonneg.mpr (eigenvalue_le_maxEigenvalue hQ.1 i)
  have hconj := hd.mul_mul_conjTranspose_same U
  have hQspec :
      Q = U * Matrix.diagonal (fun i => (hQ.1.eigenvalues i : ℂ)) * star U := by
    simpa [U, Unitary.conjStarAlgAut_apply] using hQ.1.spectral_theorem
  have hscalar :
      (maxEigenvalue hQ.1 : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) =
        U * Matrix.diagonal (fun _ => (maxEigenvalue hQ.1 : ℂ)) * star U := by
    rw [← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.smul_mul]
    simp [U]
  have hdefect : maxDefect Q hQ.1 = U * Matrix.diagonal d * star U := by
    unfold maxDefect
    calc
      (maxEigenvalue hQ.1 : ℂ) • 1 - Q =
          (maxEigenvalue hQ.1 : ℂ) • 1 -
            (U * Matrix.diagonal (fun i => (hQ.1.eigenvalues i : ℂ)) * star U) :=
        congrArg (fun X => (maxEigenvalue hQ.1 : ℂ) • 1 - X) hQspec
      _ = U * Matrix.diagonal d * star U := by
        rw [hscalar, ← Matrix.sub_mul, ← Matrix.mul_sub]
        congr 2
        ext i j
        by_cases hij : i = j
        · subst j
          simp [d]
        · simp [Matrix.diagonal, hij, d]
  rw [hdefect]
  exact hconj

/-- A largest-eigenvalue eigenvector is nonzero. -/
private theorem maxEigenvector_ne_zero [NeZero D]
    {Q : Matrix (Fin D) (Fin D) ℂ} (hQ : Q.IsHermitian) :
    (⇑(hQ.eigenvectorBasis (maxEigenIndex hQ)) : Fin D → ℂ) ≠ 0 :=
  (WithLp.ofLp_eq_zero 2).ne.2
    (hQ.eigenvectorBasis.orthonormal.ne_zero (maxEigenIndex hQ))

/-- The maximum defect has a nonzero kernel vector. -/
private theorem maxDefect_exists_nonzero_kernel [NeZero D]
    {Q : Matrix (Fin D) (Fin D) ℂ} (hQ : Q.PosDef) :
    ∃ v : Fin D → ℂ, v ≠ 0 ∧ Matrix.mulVec (maxDefect Q hQ.1) v = 0 := by
  let v : Fin D → ℂ := ⇑(hQ.1.eigenvectorBasis (maxEigenIndex hQ.1))
  refine ⟨v, maxEigenvector_ne_zero hQ.1, ?_⟩
  rw [maxDefect, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    hQ.1.mulVec_eigenvectorBasis]
  change (maxEigenvalue hQ.1 : ℂ) • v -
    (hQ.1.eigenvalues (maxEigenIndex hQ.1) : ℂ) • v = 0
  simp [v, maxEigenvalue]

/-- Moving a Kraus matrix across a quadratic form applies its adjoint to the vector. -/
private theorem quadratic_conjugate
    (B H : Matrix (Fin D) (Fin D) ℂ) (x : Fin D → ℂ) :
    star x ⬝ᵥ Matrix.mulVec (B * H * B.conjTranspose) x =
      star (Matrix.mulVec B.conjTranspose x) ⬝ᵥ
        Matrix.mulVec H (Matrix.mulVec B.conjTranspose x) := by
  conv_lhs =>
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  conv_rhs =>
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.mulVec_mulVec]

/-- The kernel of the maximum defect is invariant under every adjoint Kraus generator. -/
private theorem maxDefect_star_generator_invariant
    [NeZero D]
    (A : MPSMatrices D N) (lam : ℝ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.PosDef)
    (hnorm : (∑ σ, A σ * (A σ).conjTranspose) = (lam : ℂ) • 1)
    (hfix : (∑ σ, A σ * Q * (A σ).conjTranspose) = (lam : ℂ) • Q)
    (x : Fin D → ℂ) (hx : Matrix.mulVec (maxDefect Q hQ.1) x = 0)
    (σ : Fin (N + 1)) :
    Matrix.mulVec (maxDefect Q hQ.1)
      (Matrix.mulVec (A σ).conjTranspose x) = 0 := by
  let H := maxDefect Q hQ.1
  have hH : H.PosSemidef := maxDefect_posSemidef hQ
  have hHfixed : (∑ τ, A τ * H * (A τ).conjTranspose) = (lam : ℂ) • H := by
    simp only [H, maxDefect, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one]
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum, hnorm, hfix, smul_smul]
    module
  let q : Fin (N + 1) → ℂ := fun τ =>
    star (Matrix.mulVec (A τ).conjTranspose x) ⬝ᵥ
      Matrix.mulVec H (Matrix.mulVec (A τ).conjTranspose x)
  have hq_nonneg : ∀ τ ∈ (Finset.univ : Finset (Fin (N + 1))), 0 ≤ q τ := by
    intro τ _
    exact hH.dotProduct_mulVec_nonneg _
  have hq_sum : ∑ τ, q τ = 0 := by
    calc
      ∑ τ, q τ =
          star x ⬝ᵥ Matrix.mulVec (∑ τ, A τ * H * (A τ).conjTranspose) x := by
        rw [Matrix.sum_mulVec, dotProduct_sum]
        apply Finset.sum_congr rfl
        intro τ _
        exact (quadratic_conjugate (A τ) H x).symm
      _ = star x ⬝ᵥ Matrix.mulVec ((lam : ℂ) • H) x := by rw [hHfixed]
      _ = 0 := by
        rw [Matrix.smul_mulVec, hx]
        simp
  have hq_zero := (Finset.sum_eq_zero_iff_of_nonneg hq_nonneg).mp hq_sum σ
    (Finset.mem_univ σ)
  exact (hH.dotProduct_mulVec_zero_iff _).mp hq_zero

/-- Adjoint ordered products preserve a kernel preserved by every adjoint generator. -/
private theorem orderedProd_star_invariant
    (A : MPSMatrices D N) (H : Matrix (Fin D) (Fin D) ℂ)
    (hgen : ∀ (σ : Fin (N + 1)) (v : Fin D → ℂ), Matrix.mulVec H v = 0 →
      Matrix.mulVec H (Matrix.mulVec (A σ).conjTranspose v) = 0) :
    ∀ (ss : List (Fin (N + 1))) (v : Fin D → ℂ), Matrix.mulVec H v = 0 →
      Matrix.mulVec H (Matrix.mulVec (star (orderedProd A ss)) v) = 0 := by
  intro ss
  induction ss with
  | nil =>
      intro v hv
      simpa [orderedProd] using hv
  | cons σ ss ih =>
      intro v hv
      rw [orderedProd, star_mul, Matrix.star_eq_conjTranspose, ← Matrix.mulVec_mulVec]
      exact ih _ (hgen σ v hv)

/-- Fixed-length spanning upgrades generator invariance to invariance under every matrix. -/
private theorem all_matrices_invariant
    (A : MPSMatrices D N) (H : Matrix (Fin D) (Fin D) ℂ) (ℓ : ℕ)
    (hspan : mpsProductsSpanAt A ℓ)
    (hgen : ∀ (σ : Fin (N + 1)) (v : Fin D → ℂ), Matrix.mulVec H v = 0 →
      Matrix.mulVec H (Matrix.mulVec (A σ).conjTranspose v) = 0) :
    ∀ (M : Matrix (Fin D) (Fin D) ℂ) (v : Fin D → ℂ), Matrix.mulVec H v = 0 →
      Matrix.mulVec H (Matrix.mulVec M v) = 0 := by
  intro M v hv
  have hstar_mem : star M ∈ Submodule.span ℂ
      {X : Matrix (Fin D) (Fin D) ℂ | ∃ ss : List (Fin (N + 1)),
        ss.length = ℓ ∧ X = orderedProd A ss} := by
    rw [hspan]
    exact Submodule.mem_top
  have hinvariant : ∀ X ∈ Submodule.span ℂ
      {Y : Matrix (Fin D) (Fin D) ℂ | ∃ ss : List (Fin (N + 1)),
        ss.length = ℓ ∧ Y = orderedProd A ss},
      Matrix.mulVec H (Matrix.mulVec (star X) v) = 0 := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem X hX =>
        obtain ⟨ss, _, rfl⟩ := hX
        exact orderedProd_star_invariant A H hgen ss v hv
    | zero => simp
    | add X Y _ _ hX hY =>
        rw [star_add, Matrix.add_mulVec, Matrix.mulVec_add, hX, hY]
        simp
    | smul c X _ hX =>
        rw [star_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, hX]
        simp
  simpa using hinvariant (star M) hstar_mem

/-- A nonzero vector can be sent to any prescribed vector by a square matrix. -/
private theorem exists_matrix_mulVec_eq
    [NeZero D] {v : Fin D → ℂ} (hv : v ≠ 0) (y : Fin D → ℂ) :
    ∃ R : Matrix (Fin D) (Fin D) ℂ, Matrix.mulVec R v = y := by
  obtain ⟨j, hvj⟩ := Function.ne_iff.mp hv
  have hvj' : v j ≠ 0 := by simpa using hvj
  let R : Matrix (Fin D) (Fin D) ℂ :=
    fun i k => if k = j then y i * (v j)⁻¹ else 0
  refine ⟨R, ?_⟩
  funext i
  simp only [Matrix.mulVec, dotProduct, R]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl, mul_assoc, inv_mul_cancel₀ hvj', mul_one]
  · intro k _ hkj
    simp [hkj]
  · simp

/-- A nontrivial invariant kernel and fixed-length spanning force the matrix to vanish. -/
private theorem eq_zero_of_nonzero_kernel_and_star_invariance
    [NeZero D]
    (A : MPSMatrices D N) (H : Matrix (Fin D) (Fin D) ℂ) (ℓ : ℕ)
    (hker : ∃ v : Fin D → ℂ, v ≠ 0 ∧ Matrix.mulVec H v = 0)
    (hgen : ∀ (σ : Fin (N + 1)) (v : Fin D → ℂ), Matrix.mulVec H v = 0 →
      Matrix.mulVec H (Matrix.mulVec (A σ).conjTranspose v) = 0)
    (hspan : mpsProductsSpanAt A ℓ) : H = 0 := by
  obtain ⟨v, hvne, hv⟩ := hker
  have hall := all_matrices_invariant A H ℓ hspan hgen
  apply Matrix.mulVec_injective
  funext y
  obtain ⟨R, hRy⟩ := exists_matrix_mulVec_eq hvne y
  rw [Matrix.zero_mulVec, ← hRy]
  exact hall R v hv

/-- Two unitary gauges implementing the same injective MPS differ by a scalar phase. -/
private theorem unitary_gauge_unique_up_to_phase
    (A B : MPSMatrices D N) (ℓ : ℕ) (hspan : mpsProductsSpanAt A ℓ)
    (U V : Matrix (Fin D) (Fin D) ℂ)
    (hUunit : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hVunit : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hU : ∀ σ, B σ = U.conjTranspose * A σ * U)
    (hV : ∀ σ, B σ = V.conjTranspose * A σ * V) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ V = z • U := by
  by_cases hD : D = 0
  · subst D
    exact ⟨1, norm_one, by simpa using (Subsingleton.elim V U)⟩
  letI : NeZero D := ⟨hD⟩
  let W := V * U.conjTranspose
  have hUUstar : U * U.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp hUunit
  have hUstarU : U.conjTranspose * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hUunit
  have hVVstar : V * V.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp hVunit
  have hgen (σ : Fin (N + 1)) : W * A σ = A σ * W := by
    have hgauge := (hU σ).symm.trans (hV σ)
    calc
      W * A σ = V * (U.conjTranspose * A σ * U) * U.conjTranspose := by
        rw [show V * (U.conjTranspose * A σ * U) * U.conjTranspose =
          (V * U.conjTranspose * A σ) * (U * U.conjTranspose) by noncomm_ring,
          hUUstar, Matrix.mul_one]
      _ = V * (V.conjTranspose * A σ * V) * U.conjTranspose := by rw [hgauge]
      _ = A σ * W := by
        rw [show V * (V.conjTranspose * A σ * V) * U.conjTranspose =
          (V * V.conjTranspose) * A σ * (V * U.conjTranspose) by noncomm_ring,
          hVVstar, Matrix.one_mul]
  have hword (ss : List (Fin (N + 1))) :
      W * orderedProd A ss = orderedProd A ss * W := by
    induction ss with
    | nil => simp [orderedProd]
    | cons σ ss ih =>
        rw [orderedProd]
        calc
          W * (A σ * orderedProd A ss) = (W * A σ) * orderedProd A ss := by
            noncomm_ring
          _ = (A σ * W) * orderedProd A ss := by rw [hgen]
          _ = A σ * (W * orderedProd A ss) := by noncomm_ring
          _ = A σ * (orderedProd A ss * W) := by rw [ih]
          _ = A σ * orderedProd A ss * W := by noncomm_ring
  have hcomm (X : Matrix (Fin D) (Fin D) ℂ) : W * X = X * W := by
    have hX : X ∈ Submodule.span ℂ {Y : Matrix (Fin D) (Fin D) ℂ |
        ∃ ss : List (Fin (N + 1)), ss.length = ℓ ∧ Y = orderedProd A ss} := by
      rw [hspan]
      exact Submodule.mem_top
    induction hX using Submodule.span_induction with
    | mem X hX =>
        obtain ⟨ss, _, rfl⟩ := hX
        exact hword ss
    | zero => simp
    | add X Y _ _ hX hY =>
        simpa only [Matrix.mul_add, Matrix.add_mul] using congrArg₂ (· + ·) hX hY
    | smul c X _ hX =>
        simpa only [Matrix.mul_smul, Matrix.smul_mul] using congrArg (c • ·) hX
  have hcenter : W ∈ Set.center (Matrix (Fin D) (Fin D) ℂ) := by
    rw [Semigroup.mem_center_iff]
    intro X
    exact (hcomm X).symm
  rw [Matrix.center_eq_range] at hcenter
  obtain ⟨z, hz⟩ := hcenter
  have hWscalar : W = z • (1 : Matrix (Fin D) (Fin D) ℂ) := by
    simpa [Matrix.scalar, Matrix.smul_one_eq_diagonal] using hz.symm
  have hVU : V = z • U := by
    calc
      V = W * U := by
        rw [show W * U = V * (U.conjTranspose * U) by
          simp only [W]
          noncomm_ring, hUstarU, Matrix.mul_one]
      _ = z • U := by rw [hWscalar, Matrix.smul_mul, Matrix.one_mul]
  have hWunit : W ∈ Matrix.unitaryGroup (Fin D) ℂ := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    change (V * U.conjTranspose) * star (V * U.conjTranspose) = 1
    rw [star_mul, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    change V * U.conjTranspose * (U * V.conjTranspose) = 1
    rw [show V * U.conjTranspose * (U * V.conjTranspose) =
      V * (U.conjTranspose * U) * V.conjTranspose by noncomm_ring,
      hUstarU, Matrix.mul_one, hVVstar]
  have hzstar : star z * z = 1 := by
    have hw := Matrix.mem_unitaryGroup_iff'.mp hWunit
    rw [hWscalar, star_smul, star_one, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, smul_smul] at hw
    let i : Fin D := Classical.choice inferInstance
    simpa using congrFun (congrFun hw i) i
  have hznorm : ‖z‖ = 1 := by
    have hzsq : ‖z‖ ^ 2 = 1 := by
      have hzmul : z * star z = 1 := by simpa [mul_comm] using hzstar
      change z * (starRingEnd ℂ) z = 1 at hzmul
      rw [Complex.mul_conj, ← Complex.sq_norm] at hzmul
      exact_mod_cast hzmul
    nlinarith [norm_nonneg z]
  exact ⟨z, hznorm, hVU⟩

namespace MPSTheorem76.Internal

/-- Equal injective MPS representations have a unitary gauge, unique up to phase.

This theorem-specific endpoint is consumed exactly by `mps_theorem_7_6` in
`AKLTMatrixProduct`. -/
theorem exists_unitary_gauge_data
    (A B : MPSMatrices D N) (lamA lamB : ℝ)
    (hA : IsInjectiveMPS A lamA) (hB : IsInjectiveMPS B lamB)
    (hsame : GeneratesSameMPS A B) :
    ∃ U : Matrix.unitaryGroup (Fin D) ℂ,
      (∀ σ, B σ = (U : Matrix (Fin D) (Fin D) ℂ).conjTranspose *
        A σ * (U : Matrix (Fin D) (Fin D) ℂ)) ∧
      ∀ V : Matrix (Fin D) (Fin D) ℂ,
        V ∈ Matrix.unitaryGroup (Fin D) ℂ →
        (∀ σ, B σ = V.conjTranspose * A σ * V) →
        ∃ z : ℂ, ‖z‖ = 1 ∧ V = z • (U : Matrix (Fin D) (Fin D) ℂ) := by
  by_cases hD : D = 0
  · subst D
    let U : Matrix.unitaryGroup (Fin 0) ℂ := ⟨1, by simp⟩
    refine ⟨U, ?_, ?_⟩
    · intro σ
      exact Subsingleton.elim _ _
    · intro V _ _
      exact ⟨1, norm_one, by simpa using
        (Subsingleton.elim V (U : Matrix (Fin 0) (Fin 0) ℂ))⟩
  letI : NeZero D := ⟨hD⟩
  obtain ⟨ℓA, hspanA_large⟩ := hA.2.2.1
  obtain ⟨ℓB, hspanB_large⟩ := hB.2.2.1
  let ℓ := max (max ℓA ℓB) 1
  have hℓ : 1 ≤ ℓ := le_max_right _ _
  have hspanA := hspanA_large ℓ (le_trans (le_max_left _ _) (le_max_left _ _))
  have hspanB := hspanB_large ℓ (le_trans (le_max_right _ _) (le_max_left _ _))
  obtain ⟨e, _, _, he⟩ :=
    exists_word_transport_algEquiv A B ℓ hℓ hsame hspanA hspanB
  obtain ⟨P, R, hPR, hRP, hinner⟩ := exists_inner_matrix e
  have hgauge (σ : Fin (N + 1)) : B σ = P * A σ * R := by
    rw [← he]
    exact hinner _
  have hQ := inverseMetric_posDef P R hPR hRP
  have hQeig := inverseMetric_eigen A B lamB P R hRP hgauge hB.1
  have heSymm (σ : Fin (N + 1)) : e.symm (B σ) = A σ := by
    rw [← he σ, e.symm_apply_apply]
  obtain ⟨PB, RB, hPBRB, hRBPB, hinnerB⟩ := exists_inner_matrix e.symm
  have hgaugeB (σ : Fin (N + 1)) : A σ = PB * B σ * RB := by
    rw [← heSymm]
    exact hinnerB _
  have hQB := inverseMetric_posDef PB RB hPBRB hRBPB
  have hQBeig := inverseMetric_eigen B A lamA PB RB hRBPB hgaugeB hA.1
  let QA := CStarMatrix.ofMatrix (inverseMetric R)
  let QB := CStarMatrix.ofMatrix (inverseMetric RB)
  have hQAne : QA ≠ 0 := by
    intro hzero
    apply hQ.isUnit.ne_zero
    apply CStarMatrix.ofMatrix.injective
    simpa [QA] using hzero
  have hQBne : QB ≠ 0 := by
    intro hzero
    apply hQB.isUnit.ne_zero
    apply CStarMatrix.ofMatrix.injective
    simpa [QB] using hzero
  have hQAeig :
      (∑ σ, CStarMatrix.ofMatrix (A σ) * QA *
        star (CStarMatrix.ofMatrix (A σ))) = (lamB : ℂ) • QA := by
    simpa [QA, map_sum] using congrArg CStarMatrix.ofMatrix hQeig
  have hQBeig' :
      (∑ σ, CStarMatrix.ofMatrix (B σ) * QB *
        star (CStarMatrix.ofMatrix (B σ))) = (lamA : ℂ) • QB := by
    simpa [QB, map_sum] using congrArg CStarMatrix.ofMatrix hQBeig
  have hlam := normalization_eq_of_two_scaled_eigenmatrices
    A B lamA lamB QA QB hA.1 hB.1 hQAne hQBne hQAeig hQBeig'
  let Q := inverseMetric R
  change Q.PosDef at hQ
  let H := maxDefect Q hQ.1
  have hQeigA : transfer A Q = (lamA : ℂ) • Q := by
    simpa [Q, hlam] using hQeig
  have hH := maxDefect_posSemidef hQ
  have hker := maxDefect_exists_nonzero_kernel hQ
  have hgen : ∀ (σ : Fin (N + 1)) (v : Fin D → ℂ), Matrix.mulVec H v = 0 →
      Matrix.mulVec H (Matrix.mulVec (A σ).conjTranspose v) = 0 := by
    intro σ v hv
    exact maxDefect_star_generator_invariant
      A lamA Q hQ hA.1.2 hQeigA v hv σ
  have hHzero := eq_zero_of_nonzero_kernel_and_star_invariance
    A H ℓ hker hgen hspanA
  have hQscalar : Q = (maxEigenvalue hQ.1 : ℂ) • 1 := by
    change maxDefect Q hQ.1 = 0 at hHzero
    rw [maxDefect] at hHzero
    exact (sub_eq_zero.mp hHzero).symm
  let i : Fin D := Classical.choice inferInstance
  let v : Fin D → ℂ := Pi.single i 1
  have hv : v ≠ 0 := by
    intro hv
    have := congrFun hv i
    simp [v] at this
  have hpositive := hQ.dotProduct_mulVec_pos hv
  rw [hQscalar, Matrix.smul_mulVec, Matrix.one_mulVec] at hpositive
  have hvnorm : star v ⬝ᵥ v = 1 := by
    simp only [dotProduct, v]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  rw [dotProduct_smul, hvnorm] at hpositive
  have hc : 0 < maxEigenvalue hQ.1 := by
    have : (0 : ℂ) < (maxEigenvalue hQ.1 : ℂ) := by
      simpa only [smul_eq_mul, mul_one] using hpositive
    exact_mod_cast this
  obtain ⟨W, hWunit, hconj⟩ :=
    unitary_rescale_of_inverseMetric_eq_smul_one P R hPR _ hc hQscalar
  have hUunit : W.conjTranspose ∈ Matrix.unitaryGroup (Fin D) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hWunit
  let U : Matrix.unitaryGroup (Fin D) ℂ := ⟨W.conjTranspose, hUunit⟩
  have hU (σ : Fin (N + 1)) :
      B σ = (U : Matrix (Fin D) (Fin D) ℂ).conjTranspose *
        A σ * (U : Matrix (Fin D) (Fin D) ℂ) := by
    rw [hgauge, hconj]
    simp only [U, Matrix.conjTranspose_conjTranspose]
  refine ⟨U, hU, ?_⟩
  intro V hVunit hV
  exact unitary_gauge_unique_up_to_phase
    A B ℓ hspanA U V U.property hVunit hU hV

end MPSTheorem76.Internal

end LatticeSystem.Quantum
