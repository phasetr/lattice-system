import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbation

/-!
# The reduced resolvent `R(λ,E)` of degenerate perturbation theory (Tasaki §10.1)

Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020,
§10.1, pp. 346–347. Between eq. (10.1.17) `λV̂|Φ⟩ = {−Ĥ₀ + E + λ(P̂₀−1̂)V̂}|Γ⟩` and its inversion
(10.1.21) the text asserts, without proof, that `−Ĥ₀ + E_j(λ) + λ(P̂₀−1̂)V̂` *is invertible in
`H⊥` when `λ` is sufficiently small*; the approximate solution (10.1.18) `|Γ⟩ ≃ −λĤ₀⁻¹V̂|Φ⟩`
is the `λ, E → 0` limit of that inverse. This file makes both statements quantitative.

The sign convention here is the negative of the book's braced operator: we work with the
symmetric compression

  `A(λ,E) := (1̂ − P̂₀)(Ĥ(λ) − E)(1̂ − P̂₀)`,

so that `A(0,0) = Ĥ₀` and the effective operator of (10.1.21) is `K(λ,E) = −P̂₀V̂ R(λ,E) V̂P̂₀`,
matching (10.1.20) `Ĥeff = −P̂₀V̂Ĥ₀⁻¹V̂P̂₀` at `λ = E = 0` — the match uses that a reduced inverse
is unique, so that `R(0,0)` *is* `Ĥ₀⁻¹`. Tasaki compresses on the left only;
the two operators agree on `H⊥`, and the symmetric compression is used because it is Hermitian
as a matrix and annihilates `ker Ĥ₀` on both sides, which is exactly what the five-field contract
`IsReducedInverse` requires.

The results are:

* a reduced inverse is unique, so `Ĥ₀⁻¹` and `R(λ,E)` denote well-defined matrices;
* every Hermitian matrix has a reduced inverse (the existence engine, applied both to `Ĥ₀` and to
  `A(λ,E)`);
* under the smallness hypothesis `|λ| v + |E| < g` — with `g` a spectral gap of `Ĥ₀` on `(ker Ĥ₀)ᗮ`
  and `v` an operator bound for `V̂` — the compression `A(λ,E)` inherits the gap `g − |λ|v − |E|`
  and has *the same kernel* as `Ĥ₀`;
* hence the reduced resolvent `R(λ,E)` exists with `‖R(λ,E) u‖ ≤ ‖u‖ / (g − |λ|v − |E|)`, and it
  converges to `Ĥ₀⁻¹` at the rate `‖(R(λ,E) − Ĥ₀⁻¹) u‖ ≤ (|λ|v + |E|) ‖u‖ / (g (g − |λ|v − |E|))`.

The gap `g` and the operator bound `v` are passed as plain hypotheses, as in
`DegeneratePerturbation.lean`, so no operator-norm instance on matrices is needed.
-/

namespace LatticeSystem.Math

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The reduced inverse is unique.** If `R` and `R'` both invert `A` on `(ker A)ᗮ` and annihilate
`ker A`, then `R' = R' (A R) = (R' A) R = (1̂ − P̂₀) R = R`. This well-definedness is what licenses
the notation `Ĥ₀⁻¹` for *the* reduced inverse, and hence the reading of `K(λ,E)` at `λ = E = 0` as
Tasaki's `Ĥeff` of eq. (10.1.20): `A(0,0) = Ĥ₀` pins `R(0,0)` to `Ĥ₀⁻¹` only because no other
reduced inverse of `Ĥ₀` exists. -/
theorem IsReducedInverse.unique {A R R' : Matrix n n ℂ}
    (hR : IsReducedInverse A R) (hR' : IsReducedInverse A R') : R = R' :=
  calc R = R' * A * R := by
        rw [hR'.right_inv_on_compl, sub_mul, one_mul, hR.kills_kernel_left, sub_zero]
    _ = R' * (A * R) := mul_assoc _ _ _
    _ = R' := by rw [hR.left_inv_on_compl, mul_sub, mul_one, hR'.kills_kernel_right, sub_zero]

/-- **Every Hermitian matrix has a reduced inverse.** On `(ker A)ᗮ` the operator `A` is injective,
hence (finite dimension) bijective, so inverting it there and extending by `0` on `ker A` produces
a matrix satisfying the five-field contract `IsReducedInverse`. The pointwise sibling of this
statement, `hermitian_posSemidef_exists_orthogonal_potential`
(`Math/MatrixAnalysis/HermitianPseudoinverse.lean`), produces a single preimage rather than the
bundled inverse matrix. -/
theorem exists_isReducedInverse_of_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ∃ R : Matrix n n ℂ, IsReducedInverse A R := by
  classical
  have hsym : (Matrix.toEuclideanLin A).IsSymmetric := Matrix.isHermitian_iff_isSymmetric.mp hA
  have hmaps : ∀ w ∈ (matrixKernel A)ᗮ,
      Matrix.toEuclideanLin A w ∈ (matrixKernel A)ᗮ :=
    fun w _ => toEuclideanLin_mem_matrixKernel_orthogonal hA w
  set F : (matrixKernel A)ᗮ →ₗ[ℂ] (matrixKernel A)ᗮ :=
    (Matrix.toEuclideanLin A).restrict hmaps
  have hFcoe : ∀ w : (matrixKernel A)ᗮ,
      (F w : EuclideanSpace ℂ n) = Matrix.toEuclideanLin A (w : EuclideanSpace ℂ n) :=
    fun _ => rfl
  have hFinj : Function.Injective F := by
    intro w₁ w₂ hw
    have h0 : Matrix.toEuclideanLin A ((w₁ : EuclideanSpace ℂ n) - w₂) = 0 := by
      rw [map_sub, ← hFcoe, ← hFcoe, hw, sub_self]
    have hmem : ((w₁ : EuclideanSpace ℂ n) - w₂) ∈ matrixKernel A ⊓ (matrixKernel A)ᗮ :=
      ⟨LinearMap.mem_ker.mpr h0, Submodule.sub_mem _ w₁.2 w₂.2⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot, sub_eq_zero] at hmem
    exact Subtype.ext hmem
  set e : (matrixKernel A)ᗮ ≃ₗ[ℂ] (matrixKernel A)ᗮ :=
    LinearEquiv.ofBijective F ⟨hFinj, LinearMap.injective_iff_surjective.mp hFinj⟩
  set Rlin : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n :=
    (matrixKernel A)ᗮ.subtype ∘ₗ (e.symm : (matrixKernel A)ᗮ →ₗ[ℂ] (matrixKernel A)ᗮ) ∘ₗ
      (matrixKernel A)ᗮ.orthogonalProjection.toLinearMap
  have hRapply : ∀ x : EuclideanSpace ℂ n,
      Rlin x = ((e.symm ((matrixKernel A)ᗮ.orthogonalProjection x) : (matrixKernel A)ᗮ) :
        EuclideanSpace ℂ n) := fun _ => rfl
  have hAe : ∀ w : (matrixKernel A)ᗮ,
      Matrix.toEuclideanLin A ((e.symm w : (matrixKernel A)ᗮ) : EuclideanSpace ℂ n)
        = (w : EuclideanSpace ℂ n) := by
    intro w
    rw [← hFcoe]
    exact congrArg _ (e.apply_symm_apply w)
  have hR : Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm Rlin) = Rlin :=
    Matrix.toEuclideanLin.apply_symm_apply Rlin
  refine ⟨Matrix.toEuclideanLin.symm Rlin, ?_, ?_, ?_, ?_, ?_⟩
  · refine Matrix.toEuclideanLin.injective (LinearMap.ext fun x => ?_)
    rw [toEuclideanLin_mul_apply, hR, hRapply, hAe, toEuclideanLin_one_sub_apply,
      toEuclideanLin_kernelProjectionMatrix]
    change ((matrixKernel A)ᗮ.orthogonalProjection x : EuclideanSpace ℂ n)
      = x - (matrixKernel A).starProjection x
    rw [← Submodule.starProjection_apply, Submodule.starProjection_orthogonal']
    simp
  · refine Matrix.toEuclideanLin.injective (LinearMap.ext fun x => ?_)
    have hw : x - (matrixKernel A).starProjection x ∈ (matrixKernel A)ᗮ :=
      Submodule.sub_starProjection_mem_orthogonal x
    have hAx : Matrix.toEuclideanLin A x = (F ⟨_, hw⟩ : EuclideanSpace ℂ n) := by
      rw [hFcoe]
      have hk : Matrix.toEuclideanLin A ((matrixKernel A).starProjection x) = 0 :=
        LinearMap.mem_ker.mp (Submodule.starProjection_apply_mem _ x)
      simp [map_sub, hk]
    rw [toEuclideanLin_mul_apply, hR, hRapply, hAx,
      Submodule.orthogonalProjection_mem_subspace_eq_self, toEuclideanLin_one_sub_apply,
      toEuclideanLin_kernelProjectionMatrix]
    exact congrArg _ (e.symm_apply_apply ⟨_, hw⟩)
  · refine Matrix.toEuclideanLin.injective (LinearMap.ext fun x => ?_)
    rw [toEuclideanLin_mul_apply, toEuclideanLin_kernelProjectionMatrix, hR, hRapply, map_zero,
      LinearMap.zero_apply]
    change (matrixKernel A).starProjection _ = 0
    rw [Submodule.starProjection_apply,
      Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero
        (Subtype.coe_prop _)]
    simp
  · refine Matrix.toEuclideanLin.injective (LinearMap.ext fun x => ?_)
    rw [toEuclideanLin_mul_apply, toEuclideanLin_kernelProjectionMatrix, hR, hRapply, map_zero,
      LinearMap.zero_apply]
    change ((e.symm ((matrixKernel A)ᗮ.orthogonalProjection
      ((matrixKernel A).starProjection x)) : (matrixKernel A)ᗮ) : EuclideanSpace ℂ n) = 0
    rw [Submodule.orthogonalProjection_orthogonal_apply_eq_zero
      (Submodule.starProjection_apply_mem _ x), map_zero]
    simp
  · have hRsym : Rlin.IsSymmetric := by
      intro x y
      have hleft : ∀ (a : (matrixKernel A)ᗮ) (z : EuclideanSpace ℂ n),
          inner ℂ (a : EuclideanSpace ℂ n) z
            = inner ℂ (a : EuclideanSpace ℂ n) ((matrixKernel A)ᗮ.starProjection z) := by
        intro a z
        conv_lhs => rw [← Submodule.starProjection_eq_self_iff.mpr a.2]
        exact Submodule.inner_starProjection_left_eq_right _ _ _
      have hright : ∀ (b : (matrixKernel A)ᗮ) (z : EuclideanSpace ℂ n),
          inner ℂ z (b : EuclideanSpace ℂ n)
            = inner ℂ ((matrixKernel A)ᗮ.starProjection z) (b : EuclideanSpace ℂ n) := by
        intro b z
        conv_lhs => rw [← Submodule.starProjection_eq_self_iff.mpr b.2]
        exact (Submodule.inner_starProjection_left_eq_right _ _ _).symm
      rw [hRapply, hRapply, hleft _ y, hright _ x, Submodule.starProjection_apply,
        Submodule.starProjection_apply, ← hAe ((matrixKernel A)ᗮ.orthogonalProjection y),
        ← hAe ((matrixKernel A)ᗮ.orthogonalProjection x)]
      exact (hsym _ _).symm
    change Matrix.conjTranspose (Matrix.toEuclideanLin.symm Rlin) = Matrix.toEuclideanLin.symm Rlin
    refine Matrix.toEuclideanLin.injective ?_
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hR, hRsym.adjoint_eq]

/-- The **compressed perturbed Hamiltonian** `A(λ,E) = (1̂ − P̂₀)(Ĥ(λ) − E)(1̂ − P̂₀)`, the operator
that Tasaki inverts on `H⊥` in eq. (10.1.21) (up to the overall sign fixed in the module doc). -/
noncomputable def reducedPerturbedHamiltonian (H0 V : Matrix n n ℂ) (lam E : ℝ) :
    Matrix n n ℂ :=
  (1 - kernelProjectionMatrix H0) * (perturbedHamiltonian H0 V lam - (E : ℂ) • 1)
    * (1 - kernelProjectionMatrix H0)

/-- The compression `A(λ,E)` of a Hermitian family is Hermitian. -/
theorem reducedPerturbedHamiltonian_isHermitian {H0 V : Matrix n n ℂ}
    (hH0 : H0.IsHermitian) (hV : V.IsHermitian) (lam E : ℝ) :
    (reducedPerturbedHamiltonian H0 V lam E).IsHermitian := by
  have hQ : (1 - kernelProjectionMatrix H0).IsHermitian :=
    Matrix.isHermitian_one.sub (kernelProjectionMatrix_isHermitian H0)
  have hmid : (perturbedHamiltonian H0 V lam - (E : ℂ) • 1).IsHermitian :=
    (hH0.add (hV.smul (isSelfAdjoint_iff.mpr (by simp)))).sub
      (Matrix.isHermitian_one.smul (isSelfAdjoint_iff.mpr (by simp)))
  have hconj := Matrix.isHermitian_conjTranspose_mul_mul (1 - kernelProjectionMatrix H0) hmid
  rwa [hQ.eq] at hconj

/-- **Expansion of the compression**: `A(λ,E) = Ĥ₀ + λ (1̂−P̂₀)V̂(1̂−P̂₀) − E (1̂−P̂₀)`. The
`Ĥ₀`-term survives uncompressed because `Ĥ₀ P̂₀ = P̂₀ Ĥ₀ = 0`, and `1̂−P̂₀` is idempotent. -/
theorem reducedPerturbedHamiltonian_eq {H0 V : Matrix n n ℂ} (hH0 : H0.IsHermitian) (lam E : ℝ) :
    reducedPerturbedHamiltonian H0 V lam E
      = H0 + (lam : ℂ) •
          ((1 - kernelProjectionMatrix H0) * V * (1 - kernelProjectionMatrix H0))
        - (E : ℂ) • (1 - kernelProjectionMatrix H0) := by
  have hidem := kernelProjectionMatrix_isIdempotent H0
  have hHP := mul_kernelProjectionMatrix_eq_zero H0
  have hPH := kernelProjectionMatrix_mul_eq_zero hH0
  have hQ2 : (1 - kernelProjectionMatrix H0) * (1 - kernelProjectionMatrix H0)
      = 1 - kernelProjectionMatrix H0 := by
    rw [mul_sub, mul_one, sub_mul, one_mul, hidem, sub_self, sub_zero]
  have hQH : (1 - kernelProjectionMatrix H0) * H0 * (1 - kernelProjectionMatrix H0) = H0 := by
    rw [sub_mul, one_mul, hPH, sub_zero, mul_sub, mul_one, hHP, sub_zero]
  have hleft : (1 - kernelProjectionMatrix H0) * (H0 + (lam : ℂ) • V - (E : ℂ) • 1)
      = (1 - kernelProjectionMatrix H0) * H0
        + (lam : ℂ) • ((1 - kernelProjectionMatrix H0) * V)
        - (E : ℂ) • (1 - kernelProjectionMatrix H0) := by
    rw [mul_sub, mul_add, mul_smul_comm, mul_smul_comm, mul_one]
  have hright : ((1 - kernelProjectionMatrix H0) * H0
        + (lam : ℂ) • ((1 - kernelProjectionMatrix H0) * V)
        - (E : ℂ) • (1 - kernelProjectionMatrix H0)) * (1 - kernelProjectionMatrix H0)
      = (1 - kernelProjectionMatrix H0) * H0 * (1 - kernelProjectionMatrix H0)
        + (lam : ℂ) • ((1 - kernelProjectionMatrix H0) * V * (1 - kernelProjectionMatrix H0))
        - (E : ℂ) • ((1 - kernelProjectionMatrix H0) * (1 - kernelProjectionMatrix H0)) := by
    rw [sub_mul, add_mul, smul_mul_assoc, smul_mul_assoc]
  rw [reducedPerturbedHamiltonian, perturbedHamiltonian, hleft, hright, hQ2, hQH]

/-- **The compression inherits the gap.** If `g` is a spectral gap of `Ĥ₀` on `(ker Ĥ₀)ᗮ` and `v`
bounds `V̂`, then `A(λ,E)` is bounded below by `g − |λ|v − |E|` on the same subspace: this is the
quantitative form of Tasaki's "sufficiently small `λ`" (§10.1, p. 347). -/
theorem reducedPerturbedHamiltonian_gap {H0 V : Matrix n n ℂ} {lam E g v : ℝ}
    (hH0 : H0.IsHermitian)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (u : EuclideanSpace ℂ n) (hu : u ∈ (matrixKernel H0)ᗮ) :
    (g - |lam| * v - |E|) * ‖u‖ ^ 2
      ≤ RCLike.re (inner ℂ u
          (Matrix.toEuclideanLin (reducedPerturbedHamiltonian H0 V lam E) u)) := by
  have hPu : (matrixKernel H0).starProjection u = 0 := by
    rw [Submodule.starProjection_apply,
      Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hu]
    simp
  have hQu : Matrix.toEuclideanLin (1 - kernelProjectionMatrix H0) u = u := by
    rw [toEuclideanLin_one_sub_apply, toEuclideanLin_kernelProjectionMatrix]
    change u - (matrixKernel H0).starProjection u = u
    rw [hPu, sub_zero]
  have hQsym : (Matrix.toEuclideanLin (1 - kernelProjectionMatrix H0)).IsSymmetric :=
    Matrix.isHermitian_iff_isSymmetric.mp
      (Matrix.isHermitian_one.sub (kernelProjectionMatrix_isHermitian H0))
  have hAu : Matrix.toEuclideanLin (reducedPerturbedHamiltonian H0 V lam E) u
      = Matrix.toEuclideanLin H0 u
        + (lam : ℂ) • Matrix.toEuclideanLin (1 - kernelProjectionMatrix H0)
            (Matrix.toEuclideanLin V u)
        - (E : ℂ) • u := by
    rw [reducedPerturbedHamiltonian_eq hH0, map_sub, LinearMap.sub_apply, map_add,
      LinearMap.add_apply, map_smul, LinearMap.smul_apply, map_smul, LinearMap.smul_apply, hQu,
      toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, hQu]
  have hVinner : inner ℂ u (Matrix.toEuclideanLin (1 - kernelProjectionMatrix H0)
      (Matrix.toEuclideanLin V u)) = inner ℂ u (Matrix.toEuclideanLin V u) := by
    rw [← hQsym u (Matrix.toEuclideanLin V u), hQu]
  have hinner : RCLike.re (inner ℂ u
        (Matrix.toEuclideanLin (reducedPerturbedHamiltonian H0 V lam E) u))
      = RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u))
        + lam * RCLike.re (inner ℂ u (Matrix.toEuclideanLin V u))
        - E * ‖u‖ ^ 2 := by
    rw [hAu, inner_sub_right, inner_add_right, inner_smul_right, inner_smul_right, hVinner,
      inner_self_eq_norm_sq_to_K]
    have hnorm2 : ((‖u‖ : ℂ) ^ 2).re = ‖u‖ ^ 2 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    simp [hnorm2]
  have hVbound : |RCLike.re (inner ℂ u (Matrix.toEuclideanLin V u))| ≤ v * ‖u‖ ^ 2 :=
    calc |RCLike.re (inner ℂ u (Matrix.toEuclideanLin V u))|
        ≤ ‖inner ℂ u (Matrix.toEuclideanLin V u)‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖u‖ * ‖Matrix.toEuclideanLin V u‖ := norm_inner_le_norm _ _
      _ ≤ ‖u‖ * (v * ‖u‖) := mul_le_mul_of_nonneg_left (hv u) (norm_nonneg u)
      _ = v * ‖u‖ ^ 2 := by ring
  have hlam : -(|lam| * (v * ‖u‖ ^ 2))
      ≤ lam * RCLike.re (inner ℂ u (Matrix.toEuclideanLin V u)) := by
    have h := mul_le_mul_of_nonneg_left hVbound (abs_nonneg lam)
    have h' := neg_abs_le (lam * RCLike.re (inner ℂ u (Matrix.toEuclideanLin V u)))
    rw [abs_mul] at h'
    linarith
  have hE : -(|E| * ‖u‖ ^ 2) ≤ -(E * ‖u‖ ^ 2) :=
    neg_le_neg (mul_le_mul_of_nonneg_right (le_abs_self E) (sq_nonneg ‖u‖))
  rw [hinner]
  linarith [hgap u hu]

/-- **The compression has the same kernel as `Ĥ₀`.** Under the smallness hypothesis
`|λ|v + |E| < g`, the operator `A(λ,E)` acquires no new kernel vectors: it kills `ker Ĥ₀` because
`1̂−P̂₀` does, and the inherited gap forbids kernel vectors in `(ker Ĥ₀)ᗮ`. -/
theorem matrixKernel_reducedPerturbedHamiltonian {H0 V : Matrix n n ℂ} {lam E g v : ℝ}
    (hH0 : H0.IsHermitian)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hsmall : |lam| * v + |E| < g) :
    matrixKernel (reducedPerturbedHamiltonian H0 V lam E) = matrixKernel H0 := by
  have hg' : 0 < g - |lam| * v - |E| := by linarith
  have hkills : ∀ x ∈ matrixKernel H0,
      Matrix.toEuclideanLin (reducedPerturbedHamiltonian H0 V lam E) x = 0 := by
    intro x hx
    have hQx : Matrix.toEuclideanLin (1 - kernelProjectionMatrix H0) x = 0 := by
      rw [toEuclideanLin_one_sub_apply, toEuclideanLin_kernelProjectionMatrix]
      change x - (matrixKernel H0).starProjection x = 0
      rw [Submodule.starProjection_eq_self_iff.mpr hx, sub_self]
    rw [reducedPerturbedHamiltonian_eq hH0, map_sub, LinearMap.sub_apply, map_add,
      LinearMap.add_apply, map_smul, LinearMap.smul_apply, map_smul, LinearMap.smul_apply, hQx,
      toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, hQx, map_zero, map_zero,
      LinearMap.mem_ker.mp hx]
    simp
  refine le_antisymm (fun x hx => ?_) (fun x hx => hkills x hx)
  have hw : x - (matrixKernel H0).starProjection x ∈ (matrixKernel H0)ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal x
  have hAw : Matrix.toEuclideanLin (reducedPerturbedHamiltonian H0 V lam E)
      (x - (matrixKernel H0).starProjection x) = 0 := by
    rw [map_sub, LinearMap.mem_ker.mp hx,
      hkills _ (Submodule.starProjection_apply_mem _ x), sub_zero]
  have hbound := reducedPerturbedHamiltonian_gap (V := V) (lam := lam) (E := E) hH0 hgap hv
    (x - (matrixKernel H0).starProjection x) hw
  rw [hAw, inner_zero_right, map_zero] at hbound
  have hsq : ‖x - (matrixKernel H0).starProjection x‖ ^ 2 ≤ 0 :=
    le_of_mul_le_mul_left (by linarith) hg'
  have hzero : ‖x - (matrixKernel H0).starProjection x‖ = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm hsq (sq_nonneg _))
  have hxeq : x = (matrixKernel H0).starProjection x :=
    sub_eq_zero.mp (norm_eq_zero.mp hzero)
  have hmem : (matrixKernel H0).starProjection x ∈ matrixKernel H0 :=
    Submodule.starProjection_apply_mem _ x
  rwa [← hxeq] at hmem

/-- The projection onto `ker A(λ,E)` is the projection onto `ker Ĥ₀`, a restatement of
`matrixKernel_reducedPerturbedHamiltonian` at the level of the projection matrices. -/
theorem kernelProjectionMatrix_reducedPerturbedHamiltonian {H0 V : Matrix n n ℂ} {lam E g v : ℝ}
    (hH0 : H0.IsHermitian)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hsmall : |lam| * v + |E| < g) :
    kernelProjectionMatrix (reducedPerturbedHamiltonian H0 V lam E)
      = kernelProjectionMatrix H0 := by
  simp only [kernelProjectionMatrix, matrixKernel_reducedPerturbedHamiltonian hH0 hgap hv hsmall]

/-- **The reduced resolvent `R(λ,E)`** (Tasaki §10.1, the inverse used in eq. (10.1.21)): under
`|λ|v + |E| < g` the compression `A(λ,E)` has a reduced inverse, and that inverse obeys the
uniform bound `‖R(λ,E) u‖ ≤ ‖u‖ / (g − |λ|v − |E|)`. -/
theorem exists_isReducedInverse_reducedPerturbedHamiltonian {H0 V : Matrix n n ℂ} {lam E g v : ℝ}
    (hH0 : H0.IsHermitian) (hV : V.IsHermitian)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hsmall : |lam| * v + |E| < g) :
    ∃ R, IsReducedInverse (reducedPerturbedHamiltonian H0 V lam E) R ∧
      ∀ u : EuclideanSpace ℂ n,
        ‖Matrix.toEuclideanLin R u‖ ≤ ‖u‖ / (g - |lam| * v - |E|) := by
  obtain ⟨R, hR⟩ :=
    exists_isReducedInverse_of_isHermitian (reducedPerturbedHamiltonian_isHermitian hH0 hV lam E)
  refine ⟨R, hR, fun u => hR.norm_toEuclideanLin_le (by linarith) (fun w hw => ?_) u⟩
  rw [matrixKernel_reducedPerturbedHamiltonian hH0 hgap hv hsmall] at hw
  exact reducedPerturbedHamiltonian_gap hH0 hgap hv w hw

/-- **The resolvent converges to `Ĥ₀⁻¹`** at the rate
`‖(R(λ,E) − Ĥ₀⁻¹) u‖ ≤ (|λ|v + |E|) ‖u‖ / (g (g − |λ|v − |E|))`, the quantitative form of Tasaki's
approximation `|Γ⟩ ≃ −λĤ₀⁻¹V̂|Φ⟩` (eq. (10.1.18)). The proof is the exact resolvent identity
`R − Ĥ₀⁻¹ = R (Ĥ₀ − A(λ,E)) Ĥ₀⁻¹` together with `Ĥ₀ − A(λ,E) = E(1̂−P̂₀) − λ(1̂−P̂₀)V̂(1̂−P̂₀)`. -/
theorem norm_sub_reducedInverse_le {H0 V H0inv R : Matrix n n ℂ} {lam E g v : ℝ}
    (hH0 : H0.IsHermitian) (hInv0 : IsReducedInverse H0 H0inv)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hsmall : |lam| * v + |E| < g)
    (hR : IsReducedInverse (reducedPerturbedHamiltonian H0 V lam E) R)
    (u : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin R u - Matrix.toEuclideanLin H0inv u‖
      ≤ (|lam| * v + |E|) * ‖u‖ / (g * (g - |lam| * v - |E|)) := by
  have hg' : 0 < g - |lam| * v - |E| := by linarith
  have hPA := kernelProjectionMatrix_reducedPerturbedHamiltonian hH0 hgap hv hsmall (V := V)
  rcases eq_or_lt_of_le (norm_nonneg u) with hu0 | hu0
  · have hu : u = 0 := norm_eq_zero.mp hu0.symm
    simp [hu]
  have hvnn : 0 ≤ v := by
    have h : 0 ≤ v * ‖u‖ := (norm_nonneg (Matrix.toEuclideanLin V u)).trans (hv u)
    refine le_of_mul_le_mul_right ?_ hu0
    simpa using h
  have hcnn : 0 ≤ |lam| * v + |E| :=
    add_nonneg (mul_nonneg (abs_nonneg lam) hvnn) (abs_nonneg E)
  have hg : 0 < g := lt_of_le_of_lt hcnn hsmall
  -- the exact resolvent identity
  have h1 : R * (H0 * H0inv) = R := by
    rw [hInv0.left_inv_on_compl, mul_sub, mul_one, ← hPA, hR.kills_kernel_right, sub_zero]
  have h2 : R * reducedPerturbedHamiltonian H0 V lam E * H0inv = H0inv := by
    rw [hR.right_inv_on_compl, hPA, sub_mul, one_mul, hInv0.kills_kernel_left, sub_zero]
  have key : R - H0inv = R * (H0 - reducedPerturbedHamiltonian H0 V lam E) * H0inv := by
    rw [mul_sub, sub_mul, mul_assoc R H0 H0inv, h1, h2]
  -- the difference operator, evaluated at `x = Ĥ₀⁻¹ u`
  have hQH0inv : (1 - kernelProjectionMatrix H0) * H0inv = H0inv := by
    rw [sub_mul, one_mul, hInv0.kills_kernel_left, sub_zero]
  have hQx : Matrix.toEuclideanLin (1 - kernelProjectionMatrix H0)
      (Matrix.toEuclideanLin H0inv u) = Matrix.toEuclideanLin H0inv u := by
    rw [← toEuclideanLin_mul_apply, hQH0inv]
  have hdiff : Matrix.toEuclideanLin (H0 - reducedPerturbedHamiltonian H0 V lam E)
      (Matrix.toEuclideanLin H0inv u)
      = (E : ℂ) • Matrix.toEuclideanLin H0inv u
        - (lam : ℂ) • Matrix.toEuclideanLin (1 - kernelProjectionMatrix H0)
            (Matrix.toEuclideanLin V (Matrix.toEuclideanLin H0inv u)) := by
    rw [map_sub, LinearMap.sub_apply, reducedPerturbedHamiltonian_eq hH0, map_sub,
      LinearMap.sub_apply, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      map_smul, LinearMap.smul_apply, hQx, toEuclideanLin_mul_apply, toEuclideanLin_mul_apply,
      hQx]
    abel
  have hQnorm : ∀ y : EuclideanSpace ℂ n,
      ‖Matrix.toEuclideanLin (1 - kernelProjectionMatrix H0) y‖ ≤ ‖y‖ := by
    intro y
    rw [toEuclideanLin_one_sub_apply, toEuclideanLin_kernelProjectionMatrix]
    change ‖y - (matrixKernel H0).starProjection y‖ ≤ ‖y‖
    have hy : y - (matrixKernel H0).starProjection y = (matrixKernel H0)ᗮ.starProjection y := by
      rw [Submodule.starProjection_orthogonal']
      simp
    rw [hy]
    exact Submodule.norm_starProjection_apply_le _ y
  -- assembling the bounds
  have hx : ‖Matrix.toEuclideanLin H0inv u‖ ≤ ‖u‖ / g :=
    hInv0.norm_toEuclideanLin_le hg hgap u
  have hdiffnorm : ‖Matrix.toEuclideanLin (H0 - reducedPerturbedHamiltonian H0 V lam E)
      (Matrix.toEuclideanLin H0inv u)‖
      ≤ (|lam| * v + |E|) * ‖Matrix.toEuclideanLin H0inv u‖ := by
    rw [hdiff]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    have hVx := hv (Matrix.toEuclideanLin H0inv u)
    have hQV := hQnorm (Matrix.toEuclideanLin V (Matrix.toEuclideanLin H0inv u))
    have := mul_le_mul_of_nonneg_left (hQV.trans hVx) (abs_nonneg lam)
    linarith
  have hRnorm : ∀ y : EuclideanSpace ℂ n,
      ‖Matrix.toEuclideanLin R y‖ ≤ ‖y‖ / (g - |lam| * v - |E|) := by
    refine hR.norm_toEuclideanLin_le hg' (fun w hw => ?_)
    rw [matrixKernel_reducedPerturbedHamiltonian hH0 hgap hv hsmall] at hw
    exact reducedPerturbedHamiltonian_gap hH0 hgap hv w hw
  have hsplit : Matrix.toEuclideanLin R u - Matrix.toEuclideanLin H0inv u
      = Matrix.toEuclideanLin R
        (Matrix.toEuclideanLin (H0 - reducedPerturbedHamiltonian H0 V lam E)
          (Matrix.toEuclideanLin H0inv u)) := by
    rw [← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, ← key, map_sub,
      LinearMap.sub_apply]
  rw [hsplit]
  set z : EuclideanSpace ℂ n := Matrix.toEuclideanLin
    (H0 - reducedPerturbedHamiltonian H0 V lam E) (Matrix.toEuclideanLin H0inv u)
  have hchain : ‖z‖ ≤ (|lam| * v + |E|) * (‖u‖ / g) :=
    hdiffnorm.trans (mul_le_mul_of_nonneg_left hx hcnn)
  refine (hRnorm z).trans ?_
  rw [div_le_div_iff₀ hg' (mul_pos hg hg')]
  have hmul := mul_le_mul_of_nonneg_right hchain (mul_pos hg hg').le
  have heq : (|lam| * v + |E|) * (‖u‖ / g) * (g * (g - |lam| * v - |E|))
      = (|lam| * v + |E|) * ‖u‖ * (g - |lam| * v - |E|) := by
    field_simp
  rw [heq] at hmul
  linarith

end LatticeSystem.Math
