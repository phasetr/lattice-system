import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbation

/-!
# Test coverage for the Lemma 10.1 gap quadratic forms (Tasaki §10.1)

Pins the API contract of the three spectral-gap declarations that the Lemma 10.1 development
builds on top of the `DegeneratePerturbation.lean` definitions (`matrixKernel`,
`kernelProjectionMatrix`, `IsReducedInverse`, `secondOrderEffectiveHamiltonian`,
`IsUniqueGroundStateOn`):

1. `matrixKernel_orthogonal_gap` — the spectral-gap quadratic form for `H0` on
   `(ker H0)ᗮ`: `∃ g > 0, ∀ u ∈ (ker H0)ᗮ, g‖u‖² ≤ re⟪u, H0 u⟫`.
2. `IsUniqueGroundStateOn.orthogonal_gap` — the analogous gap for a Hermitian `H` with a
   unique ground state `φ` on an `H`-invariant `K`, restricted to `K ⊓ (ℂ∙φ)ᗮ`:
   `∃ δ > 0, ∀ w ∈ K ⊓ (ℂ∙φ)ᗮ, (E+δ)‖w‖² ≤ re⟪w, Hw⟫`.
3. `IsReducedInverse.norm_toEuclideanLin_le` — the corollary bounding the reduced inverse's
   operator norm by the reciprocal gap: `‖H0inv u‖ ≤ ‖u‖ / g`.

The `H`-invariance hypothesis of (2) is additionally pinned as load-bearing by an explicit
`Fin 3` counterexample refuting the hypothesis-free variant.

The quadratic-form shape (`c * ‖x‖ ^ 2 ≤ RCLike.re (inner ℂ x (Matrix.toEuclideanLin H x))`)
follows the `isSymmetric_block_lower` precedent in
`LatticeSystem/Math/MatrixAnalysis/CourantFischer.lean`.
-/

namespace LatticeSystem.Tests.DegeneratePerturbationSpectralGapForm

open LatticeSystem.Math Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Pins the gap quadratic form for `H0` restricted to `(ker H0)ᗮ`: a *strictly positive*,
hypothesis-free gap `g` (no side condition, so the degenerate corners `ker H0 = ⊤` and
`dim ker H0 = 1` are covered by the same statement, the `∀ u ∈ (ker H0)ᗮ` clause being vacuous
when `(ker H0)ᗮ = ⊥`). -/
example {H0 : Matrix n n ℂ} (hH0pos : H0.PosSemidef) :
    ∃ g : ℝ, 0 < g ∧ ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)) :=
  matrixKernel_orthogonal_gap hH0pos

/-- Pins the gap quadratic form for a Hermitian `H` with a unique ground state `φ` on `K`,
restricted to the orthogonal complement of `φ` inside `K`. The degenerate corner
`dim ker H0 = 1` (hence `K` one-dimensional) makes the `∀ w ∈ K ⊓ (span {φ})ᗮ` clause vacuous,
so `δ > 0` must still be produced unconditionally, exactly as for `matrixKernel_orthogonal_gap`.

`H`-invariance of `K` is not decorative: without it the energy minimiser on `K` need not be an
eigenvector of `H`, and the bound is false. Witness: `H = diag(0, 10, -10)`,
`K = span {e₀, e₁ + e₂}`, `φ = e₀`, `E = 0` — the only eigenvectors of `H` inside `K` are the
multiples of `e₀`, so `φ` is the unique ground state on `K`, yet
`re⟪e₁ + e₂, H (e₁ + e₂)⟫ = 0` while `‖e₁ + e₂‖² = 2`, forcing `δ ≤ 0`. -/
example {K : Submodule ℂ (EuclideanSpace ℂ n)} {H : Matrix n n ℂ} {E : ℝ}
    {φ : EuclideanSpace ℂ n} (hH : H.IsHermitian)
    (hKinv : ∀ v ∈ K, Matrix.toEuclideanLin H v ∈ K)
    (hGS : IsUniqueGroundStateOn K H E φ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : EuclideanSpace ℂ n, w ∈ K ⊓ (Submodule.span ℂ {φ})ᗮ →
      (E + δ) * ‖w‖ ^ 2 ≤ RCLike.re (inner ℂ w (Matrix.toEuclideanLin H w)) :=
  IsUniqueGroundStateOn.orthogonal_gap hH hKinv hGS

/-- Machine-checks the counterexample described just above: dropping the `H`-invariance hypothesis
`hKinv` from `IsUniqueGroundStateOn.orthogonal_gap` turns it into a **false** statement, already at
`n = Fin 3`. With `H = diag(0, 10, -10)`, `K = span {e₀, e₁ + e₂}` and `φ = e₀`, an eigenvector
`a e₀ + b (e₁ + e₂) ∈ K` of `H` forces `10 b = μ b = -10 b`, hence `b = 0`, so the eigenvectors of
`H` inside `K` are exactly the multiples of `e₀` and `φ` is the unique normalized ground state on
`K` at energy `E = 0`. Yet `w = e₁ + e₂ ∈ K ⊓ (ℂ ∙ φ)ᗮ` has `re ⟪w, H w⟫ = 0` and `‖w‖² = 2`, so
the conclusion would give `(0 + δ) * 2 ≤ 0`, contradicting `δ > 0`. The hypothesis fails here
because `H w = 10 e₁ - 10 e₂ ∉ K`. -/
example : ¬ ∀ (K : Submodule ℂ (EuclideanSpace ℂ (Fin 3))) (H : Matrix (Fin 3) (Fin 3) ℂ)
    (E : ℝ) (φ : EuclideanSpace ℂ (Fin 3)), H.IsHermitian →
    IsUniqueGroundStateOn K H E φ →
      ∃ δ : ℝ, 0 < δ ∧ ∀ w : EuclideanSpace ℂ (Fin 3), w ∈ K ⊓ (Submodule.span ℂ {φ})ᗮ →
        (E + δ) * ‖w‖ ^ 2 ≤ RCLike.re (inner ℂ w (Matrix.toEuclideanLin H w)) := by
  intro hgap
  set Hc : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![0, 10, -10] with hHc
  set φc : EuclideanSpace ℂ (Fin 3) := !₂[1, 0, 0] with hφc
  set wc : EuclideanSpace ℂ (Fin 3) := !₂[0, 1, 1] with hwc
  set Kc : Submodule ℂ (EuclideanSpace ℂ (Fin 3)) := Submodule.span ℂ {φc, wc} with hKc
  have hHv : ∀ v : EuclideanSpace ℂ (Fin 3),
      Matrix.toEuclideanLin Hc v = !₂[0, 10 * v 1, -(10 * v 2)] := by
    intro v
    apply WithLp.ofLp_injective 2
    funext i
    fin_cases i <;>
      simp [hHc, Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  have hcoord : ∀ (a b : ℂ) (i : Fin 3), (a • φc + b • wc) i = ![a, b, b] i := by
    intro a b i
    fin_cases i <;> simp [hφc, hwc]
  have hHerm : Hc.IsHermitian := by
    refine Matrix.isHermitian_diagonal_iff.mpr fun i => ?_
    fin_cases i <;> simp [isSelfAdjoint_iff]
  have hφmem : φc ∈ Kc := Submodule.subset_span (by simp)
  have hwmem : wc ∈ Kc := Submodule.subset_span (by simp)
  have hφnorm : ‖φc‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [hφc, Fin.sum_univ_three]
  have hHφ : Matrix.toEuclideanLin Hc φc = ((0 : ℝ) : ℂ) • φc := by
    rw [hHv]
    apply WithLp.ofLp_injective 2
    funext i
    fin_cases i <;> simp [hφc]
  have hφne : φc ≠ 0 := by
    intro h
    rw [h, norm_zero] at hφnorm
    exact zero_ne_one hφnorm
  have heig : ∀ (v : EuclideanSpace ℂ (Fin 3)) (μ : ℂ), v ∈ Kc → v ≠ 0 →
      Matrix.toEuclideanLin Hc v = μ • v → μ = 0 ∧ ∃ c : ℂ, v = c • φc := by
    intro v μ hv hvne heq
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
    have h0 := congrArg (fun z : EuclideanSpace ℂ (Fin 3) => z 0) heq
    have h1 := congrArg (fun z : EuclideanSpace ℂ (Fin 3) => z 1) heq
    have h2 := congrArg (fun z : EuclideanSpace ℂ (Fin 3) => z 2) heq
    simp only [hHv, hcoord, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2
    have hb : b = 0 := by
      have : (20 : ℂ) * b = 0 := by linear_combination h1 - h2
      simpa using this
    subst hb
    have hane : a ≠ 0 := by
      intro ha
      apply hvne
      subst ha
      simp
    have hμ : μ = 0 := by
      rcases mul_eq_zero.mp h0.symm with h | h
      · exact h
      · exact absurd h hane
    exact ⟨hμ, a, by simp⟩
  have hGS : IsUniqueGroundStateOn Kc Hc 0 φc := by
    refine ⟨hφmem, hφnorm, hHφ, ⟨⟨φc, hφmem, hφne, hHφ⟩, ?_⟩, ?_⟩
    · rintro μ ⟨ψ, hψK, hψne, hψeq⟩
      obtain ⟨hμ, -⟩ := heig ψ ((μ : ℝ) : ℂ) hψK hψne hψeq
      rw [Complex.ofReal_eq_zero] at hμ
      exact hμ.ge
    · intro ψ hψK hψeq
      rcases eq_or_ne ψ 0 with rfl | hψne
      · exact ⟨0, by simp⟩
      · exact (heig ψ (((0 : ℝ) : ℂ)) hψK hψne hψeq).2
  have hwperp : wc ∈ Kc ⊓ (Submodule.span ℂ {φc})ᗮ := by
    refine Submodule.mem_inf.mpr ⟨hwmem, ?_⟩
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    simp [hφc, hwc, PiLp.inner_apply, Fin.sum_univ_three]
  have hwinner : RCLike.re (inner ℂ wc (Matrix.toEuclideanLin Hc wc)) = 0 := by
    rw [hHv]
    simp [hwc, PiLp.inner_apply, Fin.sum_univ_three]
  have hwnorm : ‖wc‖ ^ 2 = 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    norm_num [hwc, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]
  obtain ⟨δ, hδpos, hδ⟩ := hgap Kc Hc 0 φc hHerm hGS
  have hle := hδ wc hwperp
  rw [hwinner, hwnorm] at hle
  linarith

/-- Pins the corollary `‖H0inv u‖ ≤ ‖u‖/g`, derived from `P₀ H0inv = 0` (so the reduced inverse
lands in `(ker H0)ᗮ`) composed with the coercivity bound there. -/
example {H0 H0inv : Matrix n n ℂ} (hInv : IsReducedInverse H0 H0inv) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (u : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin H0inv u‖ ≤ ‖u‖ / g :=
  hInv.norm_toEuclideanLin_le hg hgap u

end LatticeSystem.Tests.DegeneratePerturbationSpectralGapForm
