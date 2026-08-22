import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbationReducedResolvent

/-!
# The exact Feshbach reduction of degenerate perturbation theory (Tasaki §10.1)

Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020,
§10.1, pp. 346–347. Tasaki splits an eigenvector `|Ξ⟩ = |Φ⟩ + |Γ⟩` of `Ĥ(λ) = Ĥ₀ + λV̂` along
the degenerate space `H₀ = ker Ĥ₀` and its orthogonal complement `H⊥`, obtaining the two
component equations (10.1.15) `λP̂₀V̂|Γ⟩ = E|Φ⟩` and (10.1.16)/(10.1.17)
`λV̂|Φ⟩ = {−Ĥ₀ + E + λ(P̂₀−1̂)V̂}|Γ⟩`, and then eliminates `|Γ⟩` to reach (10.1.21).

This file performs that elimination *exactly*. With the reduced resolvent `R(λ,E)` of
`DegeneratePerturbationReducedResolvent.lean`, being an `E`-eigenvector `|Φ⟩ + |Γ⟩` of `Ĥ(λ)`
is equivalent to the pair of conditions

  `|Γ⟩ = −λ R(λ,E) V̂|Φ⟩`,   `λ² K(λ,E)|Φ⟩ = E|Φ⟩`,

the second being (10.1.21) with the book's `≃` replaced by `=` and with the quotient `E/λ²`
cleared, so that no `λ ≠ 0` hypothesis is needed. Here

  `K(λ,E) = secondOrderEffectiveHamiltonian H0 V R(λ,E)`,
  `Ĥeff = secondOrderEffectiveHamiltonian H0 V Ĥ₀⁻¹`  (eq. (10.1.20)),

that is, (10.1.20) and (10.1.21) are *the same expression* evaluated at two different middle
factors; uniqueness of the reduced inverse identifies `K(0,0)` with `Ĥeff`.

The book's next step — "the left-hand side of (10.1.21) clearly converges to `Ĥeff|Ξ⟩` as
`λ → 0`" — is made quantitative here as `‖K(λ,E)u − Ĥeff u‖ ≤ (4v³/g²)|λ| ‖u‖`, valid once
`0 < g`, `|E| ≤ |λ|v` and `4|λ|v ≤ g`, with `g` a spectral gap of `Ĥ₀` on `H⊥` and `v` an
operator bound for `V̂`.

The equivalence itself is purely algebraic: besides Hermiticity of `Ĥ₀` it uses only the
vanishing first-order term `P̂₀V̂P̂₀ = 0`, the reduced-inverse contract for `R`, and the equality
of the kernel projections of `A(λ,E)` and `Ĥ₀`. The gap, the operator bound and the smallness
hypothesis enter only in the norm estimates.
-/

namespace LatticeSystem.Math

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Pointwise form of the second-order effective Hamiltonian**: `−P̂₀V̂MV̂P̂₀` acts on a vector
by applying the five factors in turn. This is the bridge from the matrix product to the
Hilbert-space estimates, used for both `Ĥeff` (`M = Ĥ₀⁻¹`, eq. (10.1.20)) and `K(λ,E)`
(`M = R(λ,E)`, eq. (10.1.21)). -/
theorem toEuclideanLin_secondOrderEffectiveHamiltonian_apply (H0 V M : Matrix n n ℂ)
    (y : EuclideanSpace ℂ n) :
    Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V M) y
      = -Matrix.toEuclideanLin (kernelProjectionMatrix H0)
          (Matrix.toEuclideanLin V (Matrix.toEuclideanLin M
            (Matrix.toEuclideanLin V
              (Matrix.toEuclideanLin (kernelProjectionMatrix H0) y)))) := by
  rw [secondOrderEffectiveHamiltonian, map_neg, LinearMap.neg_apply, toEuclideanLin_mul_apply,
    toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, toEuclideanLin_mul_apply]

/-- **The second-order effective Hamiltonian is Hermitian** as soon as `V̂` and the middle factor
`M` are: conjugating reverses the palindromic product `P̂₀V̂MV̂P̂₀`. Applies verbatim to `Ĥeff`
(eq. (10.1.20)) and to `K(λ,E)` (eq. (10.1.21)). -/
theorem secondOrderEffectiveHamiltonian_isHermitian {H0 V M : Matrix n n ℂ}
    (hV : V.IsHermitian) (hM : M.IsHermitian) :
    (secondOrderEffectiveHamiltonian H0 V M).IsHermitian := by
  have hP := kernelProjectionMatrix_isHermitian H0
  have hprod :
      (kernelProjectionMatrix H0 * V * M * V * kernelProjectionMatrix H0).IsHermitian := by
    change Matrix.conjTranspose _ = _
    simp only [Matrix.conjTranspose_mul, hP.eq, hV.eq, hM.eq, mul_assoc]
  rw [secondOrderEffectiveHamiltonian]
  exact hprod.neg

/-- **The second-order effective Hamiltonian preserves the degenerate space**: its range lies in
`ker Ĥ₀`, because the leftmost factor is the projection `P̂₀`. Together with Hermiticity this is
what makes `ker Ĥ₀` an invariant subspace for `Ĥeff` and for `K(λ,E)`. -/
theorem toEuclideanLin_secondOrderEffectiveHamiltonian_mem_matrixKernel {H0 V M : Matrix n n ℂ}
    (x : EuclideanSpace ℂ n) :
    Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V M) x ∈ matrixKernel H0 := by
  rw [toEuclideanLin_secondOrderEffectiveHamiltonian_apply, toEuclideanLin_kernelProjectionMatrix]
  exact Submodule.neg_mem _ (Submodule.starProjection_apply_mem _ _)

/-- **The exact Feshbach equivalence** (Tasaki §10.1, eqs. (10.1.15), (10.1.17), (10.1.21),
pp. 346–347). Let `Ĥ₀` be Hermitian with vanishing first-order term `P̂₀V̂P̂₀ = 0`, let `R` be a
reduced inverse of the compression `A(λ,E)`, and assume `A(λ,E)` has the same kernel projection
as `Ĥ₀`. Then for `Φ ∈ ker Ĥ₀` and `Γ ∈ (ker Ĥ₀)ᗮ` the vector `Φ + Γ` is an `E`-eigenvector of
`Ĥ(λ) = Ĥ₀ + λV̂` if and only if `Γ` is the resolvent reconstruction `−λRV̂Φ` of `Φ` (the exact
form of the book's approximation (10.1.18)) and `Φ` solves the effective eigenvalue equation
`λ²K(λ,E)Φ = EΦ`, which is (10.1.21) with `≃` replaced by `=` and the quotient `E/λ²` cleared.

Both directions rest on the two orthogonal components of the eigenvalue equation: the `P̂₀`
component is (10.1.15) and the `1̂−P̂₀` component is (10.1.16)/(10.1.17). -/
theorem perturbedHamiltonian_eigenvector_iff {H0 V R : Matrix n n ℂ} {lam E : ℝ}
    (hH0 : H0.IsHermitian)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hR : IsReducedInverse (reducedPerturbedHamiltonian H0 V lam E) R)
    (hPA : kernelProjectionMatrix (reducedPerturbedHamiltonian H0 V lam E)
      = kernelProjectionMatrix H0)
    {Φ Γ : EuclideanSpace ℂ n} (hΦ : Φ ∈ matrixKernel H0) (hΓ : Γ ∈ (matrixKernel H0)ᗮ) :
    Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (Φ + Γ) = (E : ℂ) • (Φ + Γ)
      ↔ Γ = -(lam : ℂ) • Matrix.toEuclideanLin R (Matrix.toEuclideanLin V Φ)
        ∧ ((lam : ℂ) ^ 2) • Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V R) Φ
          = (E : ℂ) • Φ := by
  have hΦ0 : Matrix.toEuclideanLin H0 Φ = 0 := LinearMap.mem_ker.mp hΦ
  have hPΦ : Matrix.toEuclideanLin (kernelProjectionMatrix H0) Φ = Φ := by
    rw [toEuclideanLin_kernelProjectionMatrix]
    change (matrixKernel H0).starProjection Φ = Φ
    exact Submodule.starProjection_eq_self_iff.mpr hΦ
  have hPΓ : Matrix.toEuclideanLin (kernelProjectionMatrix H0) Γ = 0 := by
    rw [toEuclideanLin_kernelProjectionMatrix]
    change (matrixKernel H0).starProjection Γ = 0
    rw [Submodule.starProjection_apply,
      Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hΓ]
    simp
  have hQΓ : Matrix.toEuclideanLin (1 - kernelProjectionMatrix H0) Γ = Γ := by
    rw [toEuclideanLin_one_sub_apply, hPΓ, sub_zero]
  have hPH0Γ : Matrix.toEuclideanLin (kernelProjectionMatrix H0)
      (Matrix.toEuclideanLin H0 Γ) = 0 := by
    rw [← toEuclideanLin_mul_apply, kernelProjectionMatrix_mul_eq_zero hH0]
    simp
  have hPVΦ : Matrix.toEuclideanLin (kernelProjectionMatrix H0)
      (Matrix.toEuclideanLin V Φ) = 0 := by
    have h : Matrix.toEuclideanLin
        (kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0) Φ = 0 := by
      rw [hFirstOrder]
      simp
    rwa [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, hPΦ] at h
  have hKΦ : Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V R) Φ
      = -Matrix.toEuclideanLin (kernelProjectionMatrix H0)
          (Matrix.toEuclideanLin V (Matrix.toEuclideanLin R (Matrix.toEuclideanLin V Φ))) := by
    rw [toEuclideanLin_secondOrderEffectiveHamiltonian_apply, hPΦ]
  have hHsplit : ∀ y : EuclideanSpace ℂ n,
      Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) y
        = Matrix.toEuclideanLin H0 y + (lam : ℂ) • Matrix.toEuclideanLin V y := by
    intro y
    rw [perturbedHamiltonian, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply]
  have hHapply : Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (Φ + Γ)
      = Matrix.toEuclideanLin H0 Γ + (lam : ℂ) • Matrix.toEuclideanLin V Φ
        + (lam : ℂ) • Matrix.toEuclideanLin V Γ := by
    rw [hHsplit, map_add, map_add, hΦ0, zero_add, smul_add]
    abel
  have hAΓ : Matrix.toEuclideanLin (reducedPerturbedHamiltonian H0 V lam E) Γ
      = Matrix.toEuclideanLin H0 Γ
        + (lam : ℂ) • (Matrix.toEuclideanLin V Γ
          - Matrix.toEuclideanLin (kernelProjectionMatrix H0) (Matrix.toEuclideanLin V Γ))
        - (E : ℂ) • Γ := by
    rw [reducedPerturbedHamiltonian_eq hH0, map_sub, LinearMap.sub_apply, map_add,
      LinearMap.add_apply, map_smul, LinearMap.smul_apply, map_smul, LinearMap.smul_apply, hQΓ,
      toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, hQΓ, toEuclideanLin_one_sub_apply]
  -- The `P̂₀` component of the eigenvalue equation, i.e. eq. (10.1.15).
  have hPcomp : Matrix.toEuclideanLin (kernelProjectionMatrix H0)
      (Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (Φ + Γ) - (E : ℂ) • (Φ + Γ))
      = (lam : ℂ) • Matrix.toEuclideanLin (kernelProjectionMatrix H0)
          (Matrix.toEuclideanLin V Γ) - (E : ℂ) • Φ := by
    rw [hHapply]
    simp only [map_sub, map_add, map_smul, hPH0Γ, hPVΦ, hPΦ, hPΓ, smul_zero, zero_add, add_zero,
      smul_add]
  -- The `1̂−P̂₀` component of the eigenvalue equation, i.e. eqs. (10.1.16)/(10.1.17).
  have hQcomp :
      Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (Φ + Γ) - (E : ℂ) • (Φ + Γ)
        - Matrix.toEuclideanLin (kernelProjectionMatrix H0)
          (Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (Φ + Γ) - (E : ℂ) • (Φ + Γ))
        = Matrix.toEuclideanLin (reducedPerturbedHamiltonian H0 V lam E) Γ
          + (lam : ℂ) • Matrix.toEuclideanLin V Φ := by
    rw [hPcomp, hAΓ, hHapply, smul_add, smul_sub]
    abel
  constructor
  · intro heq
    have hX : Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (Φ + Γ)
        - (E : ℂ) • (Φ + Γ) = 0 := sub_eq_zero_of_eq heq
    have hP0 : (lam : ℂ) • Matrix.toEuclideanLin (kernelProjectionMatrix H0)
        (Matrix.toEuclideanLin V Γ) - (E : ℂ) • Φ = 0 := by
      rw [← hPcomp, hX, map_zero]
    have hQ0 : Matrix.toEuclideanLin (reducedPerturbedHamiltonian H0 V lam E) Γ
        + (lam : ℂ) • Matrix.toEuclideanLin V Φ = 0 := by
      rw [← hQcomp, hX, map_zero, sub_zero]
    have hΓeq : Γ = -(lam : ℂ) • Matrix.toEuclideanLin R (Matrix.toEuclideanLin V Φ) := by
      have hRA : Matrix.toEuclideanLin R
          (Matrix.toEuclideanLin (reducedPerturbedHamiltonian H0 V lam E) Γ) = Γ := by
        rw [← toEuclideanLin_mul_apply, hR.right_inv_on_compl, hPA,
          toEuclideanLin_one_sub_apply, hPΓ, sub_zero]
      have hAeq : Matrix.toEuclideanLin (reducedPerturbedHamiltonian H0 V lam E) Γ
          = -((lam : ℂ) • Matrix.toEuclideanLin V Φ) := eq_neg_of_add_eq_zero_left hQ0
      rw [← hRA, hAeq, map_neg, map_smul, neg_smul]
    refine ⟨hΓeq, ?_⟩
    have hPVΓ : Matrix.toEuclideanLin (kernelProjectionMatrix H0) (Matrix.toEuclideanLin V Γ)
        = -((lam : ℂ) • Matrix.toEuclideanLin (kernelProjectionMatrix H0)
            (Matrix.toEuclideanLin V (Matrix.toEuclideanLin R (Matrix.toEuclideanLin V Φ)))) := by
      rw [hΓeq]
      simp only [neg_smul, map_neg, map_smul]
    have hEΦ : (lam : ℂ) • Matrix.toEuclideanLin (kernelProjectionMatrix H0)
        (Matrix.toEuclideanLin V Γ) = (E : ℂ) • Φ := sub_eq_zero.mp hP0
    rw [hPVΓ] at hEΦ
    rw [hKΦ, ← hEΦ]
    simp only [smul_neg, smul_smul, pow_two]
  · rintro ⟨hΓeq, hKeq⟩
    have hAR : Matrix.toEuclideanLin (reducedPerturbedHamiltonian H0 V lam E)
        (Matrix.toEuclideanLin R (Matrix.toEuclideanLin V Φ)) = Matrix.toEuclideanLin V Φ := by
      rw [← toEuclideanLin_mul_apply, hR.left_inv_on_compl, hPA, toEuclideanLin_one_sub_apply,
        hPVΦ, sub_zero]
    have hQ0 : Matrix.toEuclideanLin (reducedPerturbedHamiltonian H0 V lam E) Γ
        + (lam : ℂ) • Matrix.toEuclideanLin V Φ = 0 := by
      rw [hΓeq]
      simp only [neg_smul, map_neg, map_smul, hAR]
      simp
    have hPVΓ : Matrix.toEuclideanLin (kernelProjectionMatrix H0) (Matrix.toEuclideanLin V Γ)
        = -((lam : ℂ) • Matrix.toEuclideanLin (kernelProjectionMatrix H0)
            (Matrix.toEuclideanLin V (Matrix.toEuclideanLin R (Matrix.toEuclideanLin V Φ)))) := by
      rw [hΓeq]
      simp only [neg_smul, map_neg, map_smul]
    have hP0 : (lam : ℂ) • Matrix.toEuclideanLin (kernelProjectionMatrix H0)
        (Matrix.toEuclideanLin V Γ) - (E : ℂ) • Φ = 0 := by
      rw [hPVΓ, ← hKeq, hKΦ]
      simp only [smul_neg, smul_smul, pow_two]
      abel
    have h1 : Matrix.toEuclideanLin (kernelProjectionMatrix H0)
        (Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (Φ + Γ) - (E : ℂ) • (Φ + Γ))
        = 0 := by
      rw [hPcomp]
      exact hP0
    have h2 : Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (Φ + Γ) - (E : ℂ) • (Φ + Γ)
        - Matrix.toEuclideanLin (kernelProjectionMatrix H0)
          (Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (Φ + Γ) - (E : ℂ) • (Φ + Γ))
        = 0 := by
      rw [hQcomp]
      exact hQ0
    have hX : Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (Φ + Γ)
        - (E : ℂ) • (Φ + Γ) = 0 := by
      rw [sub_eq_zero.mp h2]
      exact h1
    exact sub_eq_zero.mp hX

/-- **An eigenvector of `Ĥ(λ)` with vanishing `P̂₀` component is zero.** This is the injectivity
of `Ξ ↦ P̂₀Ξ` on the `E`-eigenspace of `Ĥ(λ)` (Tasaki §10.1, p. 347: the low-lying eigenstates
are labelled by their components in the degenerate space), obtained from the exact Feshbach
equivalence by taking `Φ = P̂₀Ξ = 0`, which forces `Γ = −λRV̂Φ = 0`. -/
theorem perturbedHamiltonian_eigenvector_eq_zero_of_starProjection_eq_zero
    {H0 V R : Matrix n n ℂ} {lam E : ℝ} (hH0 : H0.IsHermitian)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hR : IsReducedInverse (reducedPerturbedHamiltonian H0 V lam E) R)
    (hPA : kernelProjectionMatrix (reducedPerturbedHamiltonian H0 V lam E)
      = kernelProjectionMatrix H0)
    {Ξ : EuclideanSpace ℂ n}
    (hΞ : Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) Ξ = (E : ℂ) • Ξ)
    (hP : (matrixKernel H0).starProjection Ξ = 0) :
    Ξ = 0 := by
  have hΓmem : Ξ ∈ (matrixKernel H0)ᗮ := by
    have h : Ξ - (matrixKernel H0).starProjection Ξ ∈ (matrixKernel H0)ᗮ :=
      Submodule.sub_starProjection_mem_orthogonal Ξ
    rwa [hP, sub_zero] at h
  have heq : Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (0 + Ξ)
      = (E : ℂ) • (0 + Ξ) := by
    rwa [zero_add]
  obtain ⟨hΓ, -⟩ :=
    (perturbedHamiltonian_eigenvector_iff hH0 hFirstOrder hR hPA (Submodule.zero_mem _)
      hΓmem).mp heq
  simpa using hΓ

/-- **The exact effective Hamiltonian is close to the second-order one** (Tasaki §10.1, p. 347:
the left-hand side of (10.1.21) converges to `Ĥeff|Ξ⟩` as `λ → 0`). The difference
`K(λ,E) − Ĥeff = −P̂₀V̂(R(λ,E) − Ĥ₀⁻¹)V̂P̂₀` is estimated by the convergence rate of the reduced
resolvent, one factor `v` for each `V̂` and a norm-nonincreasing `P̂₀`. -/
theorem norm_sub_secondOrderEffectiveHamiltonian_le {H0 V H0inv R : Matrix n n ℂ}
    {lam E g v : ℝ} (hH0 : H0.IsHermitian) (hInv0 : IsReducedInverse H0 H0inv)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hsmall : |lam| * v + |E| < g)
    (hR : IsReducedInverse (reducedPerturbedHamiltonian H0 V lam E) R)
    (u : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V R) u
        - Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) u‖
      ≤ v ^ 2 * (|lam| * v + |E|) * ‖u‖ / (g * (g - |lam| * v - |E|)) := by
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
  have hg' : 0 < g - |lam| * v - |E| := by linarith
  have hD : 0 < g * (g - |lam| * v - |E|) := mul_pos hg hg'
  have hPnorm : ∀ y : EuclideanSpace ℂ n,
      ‖Matrix.toEuclideanLin (kernelProjectionMatrix H0) y‖ ≤ ‖y‖ := by
    intro y
    rw [toEuclideanLin_kernelProjectionMatrix]
    exact Submodule.norm_starProjection_apply_le _ y
  obtain ⟨z, hzdef⟩ : ∃ z : EuclideanSpace ℂ n,
      z = Matrix.toEuclideanLin V (Matrix.toEuclideanLin (kernelProjectionMatrix H0) u) :=
    ⟨_, rfl⟩
  have hdiff : Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V R) u
      - Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) u
      = -Matrix.toEuclideanLin (kernelProjectionMatrix H0)
          (Matrix.toEuclideanLin V
            (Matrix.toEuclideanLin R z - Matrix.toEuclideanLin H0inv z)) := by
    rw [toEuclideanLin_secondOrderEffectiveHamiltonian_apply,
      toEuclideanLin_secondOrderEffectiveHamiltonian_apply, hzdef, map_sub, map_sub]
    abel
  have hznorm : ‖z‖ ≤ v * ‖u‖ := by
    rw [hzdef]
    exact (hv _).trans (mul_le_mul_of_nonneg_left (hPnorm u) hvnn)
  have hstep : ‖Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V R) u
      - Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) u‖
      ≤ v * ‖Matrix.toEuclideanLin R z - Matrix.toEuclideanLin H0inv z‖ := by
    rw [hdiff, norm_neg]
    exact (hPnorm _).trans (hv _)
  have hd := norm_sub_reducedInverse_le hH0 hInv0 hgap hv hsmall hR z
  rw [le_div_iff₀ hD]
  have e1 := mul_le_mul_of_nonneg_right hstep hD.le
  have e2 := mul_le_mul_of_nonneg_left ((le_div_iff₀ hD).mp hd) hvnn
  have e3 := mul_le_mul_of_nonneg_left hznorm (mul_nonneg hvnn hcnn)
  linarith

/-- **The explicit `O(λ)` bound on `K(λ,E) − Ĥeff`** (Tasaki §10.1, p. 347). For a strictly
positive gap (`0 < g`; `4|λ|v ≤ g` alone still admits the degenerate `g = 0`, where the constant
`4v³/g²` is meaningless), once the energy is of the order of the perturbation (`|E| ≤ |λ|v`) and
the perturbation is small compared with the gap (`4|λ|v ≤ g`), the compression keeps at least
half of the gap, and the sharp bound collapses to
`‖K(λ,E)u − Ĥeff u‖ ≤ (4v³/g²)|λ| ‖u‖`. -/
theorem norm_sub_secondOrderEffectiveHamiltonian_le_abs_mul {H0 V H0inv R : Matrix n n ℂ}
    {lam E g v : ℝ} (hH0 : H0.IsHermitian) (hInv0 : IsReducedInverse H0 H0inv)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hgpos : 0 < g) (hEle : |E| ≤ |lam| * v) (hsmall4 : 4 * (|lam| * v) ≤ g)
    (hR : IsReducedInverse (reducedPerturbedHamiltonian H0 V lam E) R)
    (u : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V R) u
        - Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) u‖
      ≤ (4 * v ^ 3 / g ^ 2) * |lam| * ‖u‖ := by
  rcases eq_or_lt_of_le (norm_nonneg u) with hu0 | hu0
  · have hu : u = 0 := norm_eq_zero.mp hu0.symm
    simp [hu]
  have hvnn : 0 ≤ v := by
    have h : 0 ≤ v * ‖u‖ := (norm_nonneg (Matrix.toEuclideanLin V u)).trans (hv u)
    refine le_of_mul_le_mul_right ?_ hu0
    simpa using h
  have habs : 0 ≤ |lam| * v := mul_nonneg (abs_nonneg lam) hvnn
  have hsmall : |lam| * v + |E| < g := by linarith
  have hg' : 0 < g - |lam| * v - |E| := by linarith
  have hD : 0 < g * (g - |lam| * v - |E|) := mul_pos hgpos hg'
  refine (norm_sub_secondOrderEffectiveHamiltonian_le hH0 hInv0 hgap hv hsmall hR u).trans ?_
  have hrhs : 4 * v ^ 3 / g ^ 2 * |lam| * ‖u‖ = 4 * v ^ 3 * |lam| * ‖u‖ / g ^ 2 := by ring
  rw [hrhs, div_le_div_iff₀ hD (by positivity : (0 : ℝ) < g ^ 2)]
  have hfac1 : (0 : ℝ) ≤ v ^ 2 * ‖u‖ * g ^ 2 := by positivity
  have hfac2 : (0 : ℝ) ≤ 4 * v ^ 3 * |lam| * ‖u‖ * g :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hvnn 3))
      (abs_nonneg lam)) (norm_nonneg u)) hgpos.le
  have h1 := mul_le_mul_of_nonneg_left
    (show |lam| * v + |E| ≤ 2 * (|lam| * v) by linarith) hfac1
  have h2 := mul_le_mul_of_nonneg_left
    (show g / 2 ≤ g - |lam| * v - |E| by linarith) hfac2
  linarith

end LatticeSystem.Math
