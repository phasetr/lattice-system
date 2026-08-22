import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Degenerate perturbation theory: the second-order effective Hamiltonian (Tasaki Lemma 10.1)

This file formalizes **Tasaki Lemma 10.1** (Hal Tasaki, *Physics and
Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020, §10.1,
eq. (10.1.20), p. 346): the degenerate-perturbation-theory statement that
underlies the proof of Lieb's theorem for the repulsive Hubbard model
(§10.2.2).

For a Hamiltonian family `Ĥ(λ) = Ĥ₀ + λ V̂` with `Ĥ₀ ≥ 0` Hermitian and
ground space `H₀ = ker Ĥ₀`, the second-order effective Hamiltonian on `H₀`
is

  `Ĥeff = − P̂₀ V̂ Ĥ₀⁻¹ V̂ P̂₀`,   (eq. (10.1.20))

where `P̂₀` is the orthogonal projection onto `H₀` and `Ĥ₀⁻¹` is the reduced
(Moore–Penrose) inverse, supported on `H₀ᗮ`. The second-order formula
applies when the first-order term vanishes on the degenerate subspace,
`P̂₀ V̂ P̂₀ = 0` (so that Tasaki's `Ĥspin = λ² Ĥeff`, eq. (10.1.6), has no
`λ¹` contribution). Lemma 10.1 states: if `Ĥeff` (restricted to `H₀`) has
a unique ground state `|Φeff-GS⟩`, then `Ĥ(λ)` has a unique ground state for
all sufficiently small `λ > 0`, and a phase choice of normalized ground
states converges to `|Φeff-GS⟩` as `λ → 0⁺`.

Alongside the definitions the file carries the spectral-gap layer of the setup
(10.1.13)–(10.1.14): coercivity of `Ĥ₀` on `(ker Ĥ₀)ᗮ`, the strictly positive gap above a
unique ground state on an invariant subspace, and the resulting operator-norm bound
`‖Ĥ₀⁻¹ u‖ ≤ ‖u‖ / E_gap` on the reduced inverse.

## Role

This is the definitional base of the Lemma 10.1 layer cake: the kernel projection `P̂₀`, the
reduced-inverse contract `IsReducedInverse`, the effective and perturbed Hamiltonians, and the
ground-state predicates `IsGroundEigenvalueOn` / `IsUniqueGroundStateOn`, together with the
spectral-gap facts (10.1.13)–(10.1.14) that all later layers consume. The quantitative layers
built on it are `DegeneratePerturbationReducedResolvent.lean` (the resolvent `R(λ,E)`),
`DegeneratePerturbationFeshbach.lean` (the exact elimination of `|Γ⟩`),
`DegeneratePerturbationGroundEnergy.lean` (the bounds on the ground energy `E(λ)`),
`DegeneratePerturbationUniqueness.lean` (one-dimensionality of the ground state), and
`DegeneratePerturbationConvergence.lean`, which carries Lemma 10.1 itself.
-/

namespace LatticeSystem.Math

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `Matrix.toEuclideanLin` sends matrix multiplication to composition of the associated linear
maps, read off pointwise. -/
theorem toEuclideanLin_mul_apply (A B : Matrix n n ℂ) (v : EuclideanSpace ℂ n) :
    Matrix.toEuclideanLin (A * B) v
      = Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) := by
  apply WithLp.ofLp_injective 2
  simp [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Matrix.mulVec_mulVec]

/-- The linear map of the complementary matrix `1 - A` is `v ↦ v - A v`. -/
theorem toEuclideanLin_one_sub_apply (A : Matrix n n ℂ) (v : EuclideanSpace ℂ n) :
    Matrix.toEuclideanLin (1 - A) v = v - Matrix.toEuclideanLin A v := by
  apply WithLp.ofLp_injective 2
  simp [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]

/-- The kernel of a finite matrix, as a subspace of `EuclideanSpace ℂ n`
via `Matrix.toEuclideanLin`. -/
noncomputable def matrixKernel (H : Matrix n n ℂ) :
    Submodule ℂ (EuclideanSpace ℂ n) :=
  LinearMap.ker (Matrix.toEuclideanLin H)

/-- The orthogonal projection matrix `P̂₀` onto `ker H`, expressed in the
standard orthonormal basis of `EuclideanSpace ℂ n`. -/
noncomputable def kernelProjectionMatrix (H : Matrix n n ℂ) : Matrix n n ℂ :=
  LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun n ℂ)
    (matrixKernel H).starProjection.toLinearMap

/-- The matrix element of `P̂₀` is the inner product
`(P̂₀)_{xy} = ⟪e_x, P̂₀ e_y⟫`. -/
theorem kernelProjectionMatrix_apply (H : Matrix n n ℂ) (x y : n) :
    kernelProjectionMatrix H x y
      = inner ℂ (EuclideanSpace.basisFun n ℂ x)
        ((matrixKernel H).starProjection (EuclideanSpace.basisFun n ℂ y)) := by
  rw [kernelProjectionMatrix, LinearMap.toMatrixOrthonormal_apply_apply]
  rfl

/-- **`P̂₀` is Hermitian** (the orthonormal-basis matrix of a self-adjoint
projection). -/
theorem kernelProjectionMatrix_isHermitian (H : Matrix n n ℂ) :
    (kernelProjectionMatrix H).IsHermitian := by
  ext x y
  rw [Matrix.conjTranspose_apply, kernelProjectionMatrix_apply,
    kernelProjectionMatrix_apply, ← starRingEnd_apply, inner_conj_symm]
  exact Submodule.inner_starProjection_left_eq_right (matrixKernel H) _ _

/-- **`P̂₀` is idempotent**: `P̂₀ · P̂₀ = P̂₀`. -/
theorem kernelProjectionMatrix_isIdempotent (H : Matrix n n ℂ) :
    kernelProjectionMatrix H * kernelProjectionMatrix H = kernelProjectionMatrix H := by
  have h := (matrixKernel H).isIdempotentElem_starProjection
  unfold kernelProjectionMatrix
  rw [← map_mul (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun n ℂ))]
  congr 1
  rw [← ContinuousLinearMap.coe_mul, h]

/-- **The projection matrix represents the orthogonal projection.** The linear map attached to
`kernelProjectionMatrix H` is the star projection onto `ker H`; this is the bridge that turns
matrix identities involving `P̂₀` into Hilbert-space projection facts. -/
theorem toEuclideanLin_kernelProjectionMatrix (H : Matrix n n ℂ) :
    Matrix.toEuclideanLin (kernelProjectionMatrix H)
      = (matrixKernel H).starProjection.toLinearMap := by
  have hrepr : kernelProjectionMatrix H
      = LinearMap.toMatrix (EuclideanSpace.basisFun n ℂ).toBasis
          (EuclideanSpace.basisFun n ℂ).toBasis
          (matrixKernel H).starProjection.toLinearMap := rfl
  rw [hrepr, Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.toLin_toMatrix]

/-- **The range of a Hermitian matrix is orthogonal to its kernel.** In particular `(ker H)ᗮ` is
invariant under `H`, which is what the spectral-gap extractions below need. -/
theorem toEuclideanLin_mem_matrixKernel_orthogonal {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (v : EuclideanSpace ℂ n) : Matrix.toEuclideanLin H v ∈ (matrixKernel H)ᗮ := by
  have hsym : (Matrix.toEuclideanLin H).IsSymmetric := Matrix.isHermitian_iff_isSymmetric.mp hH
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [← hsym u v, LinearMap.mem_ker.mp hu, inner_zero_left]

/-- **A matrix annihilates the projection onto its own kernel**: `H · P̂₀ = 0`. -/
theorem mul_kernelProjectionMatrix_eq_zero (H : Matrix n n ℂ) :
    H * kernelProjectionMatrix H = 0 := by
  refine Matrix.toEuclideanLin.injective (LinearMap.ext fun x => ?_)
  have hmem : (matrixKernel H).starProjection x ∈ matrixKernel H :=
    Submodule.starProjection_apply_mem _ x
  rw [toEuclideanLin_mul_apply, toEuclideanLin_kernelProjectionMatrix, map_zero,
    LinearMap.zero_apply]
  exact LinearMap.mem_ker.mp hmem

/-- **A Hermitian matrix is annihilated by the projection onto its kernel**: `P̂₀ · H = 0`. The
adjoint of `H · P̂₀ = 0`, using that both factors are Hermitian. -/
theorem kernelProjectionMatrix_mul_eq_zero {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    kernelProjectionMatrix H * H = 0 := by
  have h := congrArg Matrix.conjTranspose (mul_kernelProjectionMatrix_eq_zero H)
  rwa [Matrix.conjTranspose_mul, (kernelProjectionMatrix_isHermitian H).eq, hH.eq,
    Matrix.conjTranspose_zero] at h

/-- `H0inv` is the **reduced (Moore–Penrose) inverse** of `H0`: it inverts
`H0` on `(ker H0)ᗮ` and vanishes on `ker H0`. We axiomatize this property
(mathlib has no general pseudo-inverse construction) and pass `H0inv` as
data to the effective-Hamiltonian definition. -/
structure IsReducedInverse (H0 H0inv : Matrix n n ℂ) : Prop where
  /-- `H0 · H0inv = 1 − P̂₀` (inverts `H0` on the orthogonal complement of `ker H0`). -/
  left_inv_on_compl : H0 * H0inv = 1 - kernelProjectionMatrix H0
  /-- `H0inv · H0 = 1 − P̂₀`. -/
  right_inv_on_compl : H0inv * H0 = 1 - kernelProjectionMatrix H0
  /-- `H0inv` annihilates `ker H0` from the left. -/
  kills_kernel_left : kernelProjectionMatrix H0 * H0inv = 0
  /-- `H0inv` annihilates `ker H0` from the right. -/
  kills_kernel_right : H0inv * kernelProjectionMatrix H0 = 0
  /-- `H0inv` is Hermitian. -/
  hermitian : H0inv.IsHermitian

/-- The **second-order effective Hamiltonian** `Ĥeff = − P̂₀ V̂ Ĥ₀⁻¹ V̂ P̂₀`
(Tasaki eq. (10.1.20)). -/
noncomputable def secondOrderEffectiveHamiltonian (H0 V H0inv : Matrix n n ℂ) :
    Matrix n n ℂ :=
  -(kernelProjectionMatrix H0 * V * H0inv * V * kernelProjectionMatrix H0)

/-- The **perturbed Hamiltonian** `Ĥ(λ) = Ĥ₀ + λ V̂`. -/
noncomputable def perturbedHamiltonian (H0 V : Matrix n n ℂ) (lam : ℝ) :
    Matrix n n ℂ :=
  H0 + (lam : ℂ) • V

/-- `E` is the **ground (lowest) eigenvalue** of `H`, restricted to a
subspace `K`: some nonzero `φ ∈ K` is an `E`-eigenvector, and every
eigenvalue with an eigenvector in `K` is `≥ E`. -/
def IsGroundEigenvalueOn (K : Submodule ℂ (EuclideanSpace ℂ n))
    (H : Matrix n n ℂ) (E : ℝ) : Prop :=
  (∃ φ : EuclideanSpace ℂ n,
      φ ∈ K ∧ φ ≠ 0 ∧ Matrix.toEuclideanLin H φ = (E : ℂ) • φ) ∧
    ∀ μ : ℝ, (∃ ψ : EuclideanSpace ℂ n,
        ψ ∈ K ∧ ψ ≠ 0 ∧ Matrix.toEuclideanLin H ψ = (μ : ℂ) • ψ) → E ≤ μ

/-- `φ` is the **unique normalized ground state** of `H` on `K`: it is a
normalized `E`-eigenvector in `K`, `E` is the ground eigenvalue on `K`, and
every `E`-eigenvector in `K` is a scalar multiple of `φ`. -/
def IsUniqueGroundStateOn (K : Submodule ℂ (EuclideanSpace ℂ n))
    (H : Matrix n n ℂ) (E : ℝ) (φ : EuclideanSpace ℂ n) : Prop :=
  φ ∈ K ∧ ‖φ‖ = 1 ∧ Matrix.toEuclideanLin H φ = (E : ℂ) • φ ∧
    IsGroundEigenvalueOn K H E ∧
    ∀ ψ : EuclideanSpace ℂ n, ψ ∈ K →
      Matrix.toEuclideanLin H ψ = (E : ℂ) • ψ → ∃ c : ℂ, ψ = c • φ

/-- **The unique ground state is only determined up to a phase.** Rescaling by a unit-modulus
`c : ℂ` preserves `IsUniqueGroundStateOn`, so any statement that pins down a normalized ground
state may choose the phase freely. -/
theorem IsUniqueGroundStateOn.smul_of_norm_one {K : Submodule ℂ (EuclideanSpace ℂ n)}
    {H : Matrix n n ℂ} {E : ℝ} {φ : EuclideanSpace ℂ n} {c : ℂ} (hc : ‖c‖ = 1)
    (hGS : IsUniqueGroundStateOn K H E φ) : IsUniqueGroundStateOn K H E (c • φ) := by
  obtain ⟨hmem, hnorm, heig, hground, huniq⟩ := hGS
  have hcne : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc
    exact zero_ne_one hc
  refine ⟨K.smul_mem c hmem, by rw [norm_smul, hc, hnorm, mul_one], ?_, hground, ?_⟩
  · rw [map_smul, heig, smul_comm]
  · intro ψ hψ hψeig
    obtain ⟨d, hd⟩ := huniq ψ hψ hψeig
    exact ⟨d * c⁻¹, by rw [hd, smul_smul, mul_assoc, inv_mul_cancel₀ hcne, mul_one]⟩

open Metric in
/-- **Lowest energy on an invariant subspace, attained at a unit eigenvector.**
If a Hermitian matrix `H` preserves a nonzero subspace `q` of `EuclideanSpace ℂ n`, then the
energy quadratic form `w ↦ re ⟪w, H w⟫` admits a sharp lower bound `m ‖w‖²` on `q`, the optimal
constant `m` being attained at a unit eigenvector of `H` lying in `q`. The minimum of the
continuous energy on the compact unit sphere of `q` is a local extremum of the Rayleigh quotient,
hence an eigenvector, and homogeneity of the quadratic form propagates the sphere minimum to all
of `q`. The two spectral-gap statements below obtain their minimising eigenvector from this
extraction. -/
theorem exists_unit_eigenvector_min_energy_on_invariant {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {q : Submodule ℂ (EuclideanSpace ℂ n)}
    (hInv : ∀ v ∈ q, Matrix.toEuclideanLin H v ∈ q) (hq : q ≠ ⊥) :
    ∃ m : ℝ, ∃ x : EuclideanSpace ℂ n, x ∈ q ∧ ‖x‖ = 1 ∧
      Matrix.toEuclideanLin H x = (m : ℂ) • x ∧
      ∀ w ∈ q, m * ‖w‖ ^ 2 ≤ RCLike.re (inner ℂ w (Matrix.toEuclideanLin H w)) := by
  classical
  haveI : ProperSpace (EuclideanSpace ℂ n) :=
    FiniteDimensional.proper_rclike ℂ (EuclideanSpace ℂ n)
  have hsym : (Matrix.toEuclideanLin H).IsSymmetric := Matrix.isHermitian_iff_isSymmetric.mp hH
  have hres := hsym.restrict_invariant hInv
  -- The adjoint/star structure on `↥q →L[ℂ] ↥q` needs completeness at the `NormedAddCommGroup`
  -- instance path, which is only definitionally (not syntactically) the one instance search finds.
  haveI : @CompleteSpace (↥q)
      (@PseudoMetricSpace.toUniformSpace (↥q)
        (@SeminormedAddCommGroup.toPseudoMetricSpace (↥q)
          (@NormedAddCommGroup.toSeminormedAddCommGroup (↥q)
            (Submodule.normedAddCommGroup q)))) := inferInstanceAs (CompleteSpace q)
  haveI : Nontrivial (↥q) := Submodule.nontrivial_iff_ne_bot.mpr hq
  set T := hres.toSelfAdjoint
  obtain ⟨y, hy⟩ : ∃ y : ↥q, y ≠ 0 := exists_ne 0
  have hcompact : IsCompact (sphere (0 : ↥q) 1) := isCompact_sphere _ _
  have hne : (sphere (0 : ↥q) 1).Nonempty :=
    ⟨(‖y‖⁻¹ : ℂ) • y, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hy)⟩
  obtain ⟨x₀, hx₀mem, hmin⟩ :=
    hcompact.exists_isMinOn hne (T.val.reApplyInnerSelf_continuous).continuousOn
  have hx₀norm : ‖x₀‖ = 1 := mem_sphere_zero_iff_norm.mp hx₀mem
  have hx₀ne : x₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx₀norm
    exact zero_ne_one hx₀norm
  have hextr : IsMinOn T.val.reApplyInnerSelf (sphere (0 : ↥q) ‖x₀‖) x₀ := by
    rw [hx₀norm]; exact hmin
  have hev := T.prop.hasEigenvector_of_isLocalExtrOn hx₀ne (Or.inl hextr.localize)
  have hray : T.val.rayleighQuotient x₀ = T.val.reApplyInnerSelf x₀ := by
    rw [ContinuousLinearMap.rayleighQuotient, hx₀norm, one_pow, div_one]
  refine ⟨T.val.reApplyInnerSelf x₀, (x₀ : EuclideanSpace ℂ n), x₀.2, hx₀norm, ?_, ?_⟩
  · have heig : (T.val x₀ : ↥q) = ((T.val.rayleighQuotient x₀ : ℝ) : ℂ) • x₀ :=
      Module.End.mem_eigenspace_iff.mp hev.1
    have hcoe : ((T.val x₀ : ↥q) : EuclideanSpace ℂ n)
        = Matrix.toEuclideanLin H (x₀ : EuclideanSpace ℂ n) := rfl
    have hlift := congrArg (fun z : ↥q => (z : EuclideanSpace ℂ n)) heig
    simpa [hcoe, hray] using hlift
  · intro w hw
    rcases eq_or_ne w 0 with rfl | hw0
    · simp
    · set W : ↥q := ⟨w, hw⟩
      have hWne : W ≠ 0 := by
        intro h
        exact hw0 (congrArg Subtype.val h)
      have hWpos : 0 < ‖W‖ := norm_pos_iff.mpr hWne
      have hmem : ((‖W‖⁻¹ : ℂ) • W) ∈ sphere (0 : ↥q) 1 :=
        mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hWne)
      have hle : T.val.reApplyInnerSelf x₀
          ≤ T.val.reApplyInnerSelf ((‖W‖⁻¹ : ℂ) • W) := hmin hmem
      rw [ContinuousLinearMap.reApplyInnerSelf_smul] at hle
      have hnormc : ‖((‖W‖ : ℝ) : ℂ)‖ = ‖W‖ := by simp
      have hnorm : ‖(‖W‖⁻¹ : ℂ)‖ ^ 2 = (‖W‖ ^ 2)⁻¹ := by
        rw [norm_inv, hnormc, inv_pow]
      rw [hnorm] at hle
      have hsq : (0 : ℝ) < ‖W‖ ^ 2 := by positivity
      have hmul := mul_le_mul_of_nonneg_right hle hsq.le
      rw [inv_mul_eq_div, div_mul_cancel₀ _ hsq.ne', mul_comm] at hmul
      have hcoe : T.val.reApplyInnerSelf W
          = RCLike.re (inner ℂ w (Matrix.toEuclideanLin H w)) := by
        rw [ContinuousLinearMap.reApplyInnerSelf_apply, Submodule.coe_inner]
        have h1 : ((T.val W : ↥q) : EuclideanSpace ℂ n) = Matrix.toEuclideanLin H w := rfl
        rw [h1]
        exact congrArg RCLike.re (hsym w w)
      have hWnorm : ‖W‖ = ‖w‖ := rfl
      rw [hcoe, hWnorm] at hmul
      linarith [hmul]

/-- **Spectral gap of `Ĥ₀` on `(ker Ĥ₀)ᗮ`** (Tasaki §10.1, the gap `E_gap > 0` of the setup
(10.1.13)–(10.1.14)). For a positive semidefinite `Ĥ₀` there is a strictly positive `g` with
`g ‖u‖² ≤ re ⟪u, Ĥ₀ u⟫` for every `u` orthogonal to the degenerate ground space `ker Ĥ₀`. In finite
dimensions no gap hypothesis is needed: the lowest energy on the invariant subspace `(ker Ĥ₀)ᗮ` is
attained at an eigenvector, which is not annihilated by `Ĥ₀`, so its eigenvalue is strictly
positive. When `ker Ĥ₀ = ⊤` the bound is vacuous and any `g` works. -/
theorem matrixKernel_orthogonal_gap {H0 : Matrix n n ℂ} (hH0pos : H0.PosSemidef) :
    ∃ g : ℝ, 0 < g ∧ ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)) := by
  classical
  by_cases hbot : (matrixKernel H0)ᗮ = ⊥
  · refine ⟨1, one_pos, fun u hu => ?_⟩
    rw [hbot, Submodule.mem_bot] at hu
    simp [hu]
  · have hInv : ∀ v ∈ (matrixKernel H0)ᗮ, Matrix.toEuclideanLin H0 v ∈ (matrixKernel H0)ᗮ :=
      fun v _ => toEuclideanLin_mem_matrixKernel_orthogonal hH0pos.1 v
    obtain ⟨m, x, hxq, hxnorm, hxeig, hbound⟩ :=
      exists_unit_eigenvector_min_energy_on_invariant hH0pos.1 hInv hbot
    refine ⟨m, ?_, hbound⟩
    have hxx : (inner ℂ x x : ℂ) = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hxnorm]
      norm_num
    have hmre : RCLike.re (inner ℂ x (Matrix.toEuclideanLin H0 x)) = m := by
      rw [hxeig, inner_smul_right, hxx, mul_one]
      simp
    have hnonneg : 0 ≤ m := by
      have := (Matrix.isPositive_toEuclideanLin_iff.mpr hH0pos).re_inner_nonneg_right x
      rwa [hmre] at this
    refine hnonneg.lt_of_ne' ?_
    intro hm
    have hker : x ∈ matrixKernel H0 := by
      rw [matrixKernel, LinearMap.mem_ker, hxeig, hm]
      simp
    have hzero : x = 0 := by
      have : x ∈ matrixKernel H0 ⊓ (matrixKernel H0)ᗮ := ⟨hker, hxq⟩
      rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at this
    rw [hzero, norm_zero] at hxnorm
    exact zero_ne_one hxnorm

/-- **Gap above a unique ground state** (Tasaki §10.1: the effective Hamiltonian `Ĥeff` separates
its unique ground state `Φeff` from the rest of the degenerate space by a strictly positive `δ`).
If `H` is Hermitian, preserves `K`, and has `φ` as its unique normalized ground state on `K` with
ground energy `E`, then `(E + δ) ‖w‖² ≤ re ⟪w, H w⟫` for every `w ∈ K` orthogonal to `φ`. The
minimiser of the energy on `K ⊓ (ℂ ∙ φ)ᗮ` is an eigenvector of `H` inside `K`, so its eigenvalue is
`≥ E`, and it cannot equal `E` since uniqueness would make it a multiple of `φ`. When `K` is
spanned by `φ` the bound is vacuous and any `δ` works. -/
theorem IsUniqueGroundStateOn.orthogonal_gap {K : Submodule ℂ (EuclideanSpace ℂ n)}
    {H : Matrix n n ℂ} {E : ℝ} {φ : EuclideanSpace ℂ n} (hH : H.IsHermitian)
    (hKinv : ∀ v ∈ K, Matrix.toEuclideanLin H v ∈ K) (hGS : IsUniqueGroundStateOn K H E φ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : EuclideanSpace ℂ n, w ∈ K ⊓ (Submodule.span ℂ {φ})ᗮ →
      (E + δ) * ‖w‖ ^ 2 ≤ RCLike.re (inner ℂ w (Matrix.toEuclideanLin H w)) := by
  classical
  obtain ⟨-, hφnorm, hφeig, hground, huniq⟩ := hGS
  by_cases hbot : K ⊓ (Submodule.span ℂ {φ})ᗮ = ⊥
  · refine ⟨1, one_pos, fun w hw => ?_⟩
    rw [hbot, Submodule.mem_bot] at hw
    simp [hw]
  · have hsym : (Matrix.toEuclideanLin H).IsSymmetric := Matrix.isHermitian_iff_isSymmetric.mp hH
    have hInv : ∀ v ∈ K ⊓ (Submodule.span ℂ {φ})ᗮ,
        Matrix.toEuclideanLin H v ∈ K ⊓ (Submodule.span ℂ {φ})ᗮ := by
      intro v hv
      obtain ⟨hvK, hvφ⟩ := Submodule.mem_inf.mp hv
      refine Submodule.mem_inf.mpr ⟨hKinv v hvK, ?_⟩
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hvφ ⊢
      rw [← hsym φ v, hφeig, inner_smul_left, hvφ, mul_zero]
    obtain ⟨m, x, hxq, hxnorm, hxeig, hbound⟩ :=
      exists_unit_eigenvector_min_energy_on_invariant hH hInv hbot
    have hxne : x ≠ 0 := by
      intro h
      rw [h, norm_zero] at hxnorm
      exact zero_ne_one hxnorm
    obtain ⟨hxK, hxφ⟩ := Submodule.mem_inf.mp hxq
    have hEle : E ≤ m := hground.2 m ⟨x, hxK, hxne, hxeig⟩
    have hφφ : (inner ℂ φ φ : ℂ) = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hφnorm]
      norm_num
    have hEne : E ≠ m := by
      intro hEm
      obtain ⟨c, hc⟩ := huniq x hxK (by rw [hxeig, hEm])
      have hinner : inner ℂ φ x = 0 :=
        Submodule.mem_orthogonal_singleton_iff_inner_right.mp hxφ
      rw [hc, inner_smul_right, hφφ, mul_one] at hinner
      rw [hinner, zero_smul] at hc
      exact hxne hc
    refine ⟨m - E, sub_pos.mpr (lt_of_le_of_ne hEle hEne), fun w hw => ?_⟩
    have hEm : E + (m - E) = m := by ring
    rw [hEm]
    exact hbound w hw

/-- **Operator-norm bound for the reduced inverse.** If `H0inv` is the reduced inverse of `Ĥ₀` and
`g` is a spectral gap of `Ĥ₀` on `(ker Ĥ₀)ᗮ`, then `‖Ĥ₀⁻¹ u‖ ≤ ‖u‖ / g` for every `u`. The reduced
inverse lands in `(ker Ĥ₀)ᗮ`, where the gap form applies, and `Ĥ₀ Ĥ₀⁻¹ u = u − P̂₀ u` pairs against
`Ĥ₀⁻¹ u` to give `g ‖Ĥ₀⁻¹ u‖² ≤ ‖Ĥ₀⁻¹ u‖ ‖u‖`. -/
theorem IsReducedInverse.norm_toEuclideanLin_le {H0 H0inv : Matrix n n ℂ}
    (hInv : IsReducedInverse H0 H0inv) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (u : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin H0inv u‖ ≤ ‖u‖ / g := by
  classical
  have hPsym : (Matrix.toEuclideanLin (kernelProjectionMatrix H0)).IsSymmetric :=
    Matrix.isHermitian_iff_isSymmetric.mp (kernelProjectionMatrix_isHermitian H0)
  set y : EuclideanSpace ℂ n := Matrix.toEuclideanLin H0inv u with hydef
  have hPy : Matrix.toEuclideanLin (kernelProjectionMatrix H0) y = 0 := by
    rw [hydef, ← toEuclideanLin_mul_apply, hInv.kills_kernel_left]
    simp
  have hyperp : y ∈ (matrixKernel H0)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    have hPv : Matrix.toEuclideanLin (kernelProjectionMatrix H0) v = v := by
      have hv' := toEuclideanLin_mul_apply H0inv H0 v
      rw [hInv.right_inv_on_compl, LinearMap.mem_ker.mp hv, map_zero,
        toEuclideanLin_one_sub_apply, sub_eq_zero] at hv'
      exact hv'.symm
    rw [← hPv, hPsym v y, hPy, inner_zero_right]
  have hH0y : Matrix.toEuclideanLin H0 y
      = u - Matrix.toEuclideanLin (kernelProjectionMatrix H0) u := by
    rw [hydef, ← toEuclideanLin_mul_apply, hInv.left_inv_on_compl,
      toEuclideanLin_one_sub_apply]
  have hpair : RCLike.re (inner ℂ y (Matrix.toEuclideanLin H0 y)) = RCLike.re (inner ℂ y u) := by
    rw [hH0y, inner_sub_right, ← hPsym y u, hPy, inner_zero_left, sub_zero]
  have hkey : g * ‖y‖ ^ 2 ≤ ‖y‖ * ‖u‖ := by
    have h1 := hgap y hyperp
    rw [hpair] at h1
    exact h1.trans (re_inner_le_norm y u)
  rcases eq_or_lt_of_le (norm_nonneg y) with h0 | h0
  · rw [← h0]
    positivity
  · rw [le_div_iff₀ hg]
    nlinarith [hkey, h0]

end LatticeSystem.Math
