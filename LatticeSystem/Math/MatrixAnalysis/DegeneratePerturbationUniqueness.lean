import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbationFeshbach
import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbationGroundEnergy
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Ground-state one-dimensionality in degenerate perturbation theory (Tasaki §10.1)

Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020,
§10.1, p. 347, eqs. (10.1.21)–(10.1.22): the closing paragraph of the proof of Lemma 10.1,
which concludes that `Ĥ(λ) = Ĥ₀ + λV̂` has a *unique* ground state for all sufficiently small
`λ > 0` once the second-order effective Hamiltonian `Ĥeff = −P̂₀V̂Ĥ₀⁻¹V̂P̂₀` (eq. (10.1.20)) has a
unique ground state inside the degenerate space `H₀ = ker Ĥ₀`.

## Provenance: this is *not* Tasaki's argument

Tasaki reaches that conclusion by counting: *"Because the states `|Ξ_j(0)⟩` with `j = 1, …, D₀`
are linearly independent, one of them must coincide with `|Φeff-GS⟩` … Recalling that
`ε_j > ε₁` for any `j = 2, …, D₀` by assumption, and `ε_j = lim_{λ→0} E_j(λ)/λ²`, we find that
`|Ξ₁(λ)⟩` is the unique ground state of `Ĥ(λ)` for sufficiently small λ."* That paragraph rests
on the proof's opening analytic input — *"By continuity there are exactly `D₀` independent
eigenstates … each of these `D₀` eigenstates depends continuously on λ"* (Rellich–Kato,
asserted without proof) — together with a count over the `D₀` continuous branches and the limit
`ε_j = lim E_j(λ)/λ²`.

**None of that is used here.** This file uses no continuity, no branch counting, no `λ → 0`
limit and no `D₀`. It replaces them by an independent elementary route: a quadratic-form
comparison at a *single* `λ` (`abs_inner_secondOrderEffectiveHamiltonian_sub_mul_norm_sq_le`,
built on the exact Feshbach equivalence), the `Ĥeff`-gap `δ` inside `ker Ĥ₀`, and the
variational bound `E ≤ λ²Eeff + c₃λ³`, matched against each other; uniqueness then follows from
an antisymmetric linear combination of two eigenvectors, which is not in the book. The
conclusion reached is exactly the book's; the route is not, and reading this file as "Tasaki's
proof, formalized" would be a false attribution.

## Contents

* `exists_norm_toEuclideanLin_le` — every matrix is a bounded operator on `EuclideanSpace ℂ n`,
  supplying the operator bound `v` that the arc passes around as a plain hypothesis.
* `abs_inner_secondOrderEffectiveHamiltonian_sub_mul_norm_sq_le` — the quadratic-form engine: an
  exact `(Φ,Γ)`-split `E`-eigenvector of `Ĥ(λ)` satisfies
  `|λ² re⟪Φ, ĤeffΦ⟫ − E‖Φ‖²| ≤ (4v³/g²) λ³ ‖Φ‖²`.
* `perturbedHamiltonian_eigenvector_eq_zero_of_inner_starProjection_eq_zero` — kernel
  triviality: at the ground energy, an eigenvector whose `P̂₀`-component is orthogonal to `Φeff`
  vanishes.
* `exists_isUniqueGroundStateOn_perturbedHamiltonian` — uniqueness at a fixed small `λ`.
* `exists_lam0_isUniqueGroundStateOn_perturbedHamiltonian` — the packaged statement
  `∃ λ₀ > 0, ∀ λ ∈ (0, λ₀), Ĥ(λ)` has a unique ground state on the whole space, under exactly
  the hypotheses of `tasaki_lemma_10_1_degenerate_perturbation`.

The smallness threshold is explicit: `λ₀ = min 1 (min (g/(4v+1)) (δ/(c₃+C+1)))` with
`C = 4v³/g²`, the `+1`s keeping the quotients well-formed at `v = 0` and at `c₃ = C = 0`.
-/

namespace LatticeSystem.Math

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Every matrix is a bounded operator on `EuclideanSpace ℂ n`.** The arc passes an operator
bound `v` for `V̂` around as a plain hypothesis `‖V̂u‖ ≤ v‖u‖`, so as to avoid committing to a
norm instance on `Matrix n n ℂ`; this lemma discharges that hypothesis once and for all from the
bundled continuous linear map `Matrix.toEuclideanCLM`, whose operator norm is the optimal `v`. -/
theorem exists_norm_toEuclideanLin_le (V : Matrix n n ℂ) :
    ∃ v : ℝ, 0 ≤ v ∧ ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖ :=
  ⟨‖Matrix.toEuclideanCLM (𝕜 := ℂ) V‖, norm_nonneg _,
    fun u => (Matrix.toEuclideanCLM (𝕜 := ℂ) V).le_opNorm u⟩

/-- **The quadratic-form engine of the uniqueness proof** (Tasaki §10.1, eq. (10.1.21), p. 347,
in the exact form supplied by `perturbedHamiltonian_eigenvector_iff`). Let `Φ + Γ` be an
`E`-eigenvector of `Ĥ(λ) = Ĥ₀ + λV̂` split along `ker Ĥ₀` and its orthogonal complement, with the
energy of the order of the perturbation (`|E| ≤ λv`) and the perturbation small compared with
the gap (`4λv ≤ g`, `0 < g`). Then

  `|λ² re⟪Φ, ĤeffΦ⟫ − E‖Φ‖²| ≤ (4v³/g²) λ³ ‖Φ‖²`.

Pairing the *exact* effective eigenvalue equation `λ²K(λ,E)Φ = EΦ` with `Φ` gives the identity
`λ² re⟪Φ, K(λ,E)Φ⟫ = E‖Φ‖²` with no division by `λ²`; the `O(λ)` bound on `K(λ,E) − Ĥeff` then
transfers it to `Ĥeff` at the cost of one extra power of `λ`. This is the only analytic step of
the uniqueness argument, and it is *not* Tasaki's `λ → 0` limit: it holds at each fixed `λ`. -/
theorem abs_inner_secondOrderEffectiveHamiltonian_sub_mul_norm_sq_le
    {H0 V H0inv : Matrix n n ℂ} {g v lam E : ℝ} {Φ Γ : EuclideanSpace ℂ n}
    (hH0 : H0.IsHermitian) (hV : V.IsHermitian) (hInv : IsReducedInverse H0 H0inv)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hgpos : 0 < g) (hlam : 0 < lam) (hEabs : |E| ≤ lam * v) (hsmall4 : 4 * (lam * v) ≤ g)
    (hΦ : Φ ∈ matrixKernel H0) (hΓ : Γ ∈ (matrixKernel H0)ᗮ)
    (heig : Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (Φ + Γ) = (E : ℂ) • (Φ + Γ)) :
    |lam ^ 2 * RCLike.re (inner ℂ Φ
          (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φ))
        - E * ‖Φ‖ ^ 2|
      ≤ (4 * v ^ 3 / g ^ 2) * lam ^ 3 * ‖Φ‖ ^ 2 := by
  have habs : |lam| = lam := abs_of_pos hlam
  have hsmall : |lam| * v + |E| < g := by
    rw [habs]
    linarith
  obtain ⟨R, hR, -⟩ := exists_isReducedInverse_reducedPerturbedHamiltonian hH0 hV hgap hv hsmall
  have hPA := kernelProjectionMatrix_reducedPerturbedHamiltonian hH0 hgap hv hsmall
  obtain ⟨-, hKeq⟩ := (perturbedHamiltonian_eigenvector_iff hH0 hFirstOrder hR hPA hΦ hΓ).mp heig
  -- The exact identity `λ² re⟪Φ, K(λ,E)Φ⟫ = E‖Φ‖²`, obtained without dividing by `λ²`.
  have hEid : lam ^ 2 * RCLike.re (inner ℂ Φ
        (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V R) Φ))
      = E * ‖Φ‖ ^ 2 := by
    have hinner := congrArg (fun y : EuclideanSpace ℂ n => (inner ℂ Φ y : ℂ)) hKeq
    simp only [inner_smul_right] at hinner
    have hcast : ((lam : ℂ)) ^ 2 = (((lam ^ 2 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [hcast] at hinner
    have hre := congrArg Complex.re hinner
    rwa [Complex.re_ofReal_mul, Complex.re_ofReal_mul, ← RCLike.re_to_complex,
      ← RCLike.re_to_complex, inner_self_eq_norm_sq] at hre
  -- The `O(λ)` comparison of the two quadratic forms.
  have hdiff : |RCLike.re (inner ℂ Φ
        (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φ))
      - RCLike.re (inner ℂ Φ
        (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V R) Φ))|
      ≤ (4 * v ^ 3 / g ^ 2) * lam * ‖Φ‖ ^ 2 := by
    have hC6 := norm_sub_secondOrderEffectiveHamiltonian_le_abs_mul hH0 hInv hgap hv hgpos
      (by rwa [habs]) (by rwa [habs]) hR Φ
    rw [habs] at hC6
    have hsplit : RCLike.re (inner ℂ Φ
          (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φ))
        - RCLike.re (inner ℂ Φ
          (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V R) Φ))
        = -RCLike.re (inner ℂ Φ
          (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V R) Φ
            - Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φ)) := by
      rw [inner_sub_right, map_sub]
      ring
    rw [hsplit, abs_neg]
    refine (RCLike.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    calc ‖Φ‖ * ‖Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V R) Φ
            - Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φ‖
        ≤ ‖Φ‖ * ((4 * v ^ 3 / g ^ 2) * lam * ‖Φ‖) :=
          mul_le_mul_of_nonneg_left hC6 (norm_nonneg Φ)
      _ = (4 * v ^ 3 / g ^ 2) * lam * ‖Φ‖ ^ 2 := by ring
  have hrewrite : |lam ^ 2 * RCLike.re (inner ℂ Φ
        (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φ))
      - E * ‖Φ‖ ^ 2|
      = lam ^ 2 * |RCLike.re (inner ℂ Φ
        (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φ))
      - RCLike.re (inner ℂ Φ
        (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V R) Φ))| := by
    rw [← hEid, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg lam)]
  rw [hrewrite]
  calc lam ^ 2 * |RCLike.re (inner ℂ Φ
          (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φ))
        - RCLike.re (inner ℂ Φ
          (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V R) Φ))|
      ≤ lam ^ 2 * ((4 * v ^ 3 / g ^ 2) * lam * ‖Φ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hdiff (sq_nonneg lam)
    _ = (4 * v ^ 3 / g ^ 2) * lam ^ 3 * ‖Φ‖ ^ 2 := by ring

/-- **An eigenvector whose degenerate component is orthogonal to `Φeff` vanishes.** At the
ground energy `E` of `Ĥ(λ)` — so that the variational bound `E ≤ λ²Eeff + c₃λ³` is available —
and for `λ` small enough that `(c₃ + 4v³/g²)λ < δ`, where `δ` is the gap of `Ĥeff` above `Φeff`
inside `ker Ĥ₀`, any `E`-eigenvector `Ξ` of `Ĥ(λ)` with `⟪Φeff, P̂₀Ξ⟫ = 0` is zero.

If `Φ = P̂₀Ξ` were nonzero it would lie in `ker Ĥ₀ ⊓ (ℂ∙Φeff)ᗮ`, where the `δ`-gap forces
`λ²(Eeff+δ)‖Φ‖² ≤ λ² re⟪Φ, ĤeffΦ⟫`, while the quadratic-form engine plus the variational bound
force `λ² re⟪Φ, ĤeffΦ⟫ ≤ (λ²Eeff + (c₃ + 4v³/g²)λ³)‖Φ‖²`; together they give
`δ ≤ (c₃ + 4v³/g²)λ`, a contradiction. Hence `P̂₀Ξ = 0`, and the Feshbach reconstruction
`Γ = −λR(λ,E)V̂Φ` then kills `Ξ` itself. This replaces Tasaki's labelling of the low-lying
eigenstates by their components in the degenerate space (p. 347). -/
theorem perturbedHamiltonian_eigenvector_eq_zero_of_inner_starProjection_eq_zero
    {H0 V H0inv : Matrix n n ℂ} {g v lam E Eeff δ c₃ : ℝ} {Φeff Ξ : EuclideanSpace ℂ n}
    (hH0 : H0.IsHermitian) (hV : V.IsHermitian) (hInv : IsReducedInverse H0 H0inv)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hgpos : 0 < g) (hlam : 0 < lam) (hEabs : |E| ≤ lam * v) (hsmall4 : 4 * (lam * v) ≤ g)
    (hδgap : ∀ w ∈ matrixKernel H0 ⊓ (Submodule.span ℂ {Φeff})ᗮ,
      (Eeff + δ) * ‖w‖ ^ 2
        ≤ RCLike.re (inner ℂ w (Matrix.toEuclideanLin
            (secondOrderEffectiveHamiltonian H0 V H0inv) w)))
    (hEup : E ≤ lam ^ 2 * Eeff + c₃ * lam ^ 3)
    (hsmallδ : (c₃ + 4 * v ^ 3 / g ^ 2) * lam < δ)
    (hΞ : Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) Ξ = (E : ℂ) • Ξ)
    (hperp : (inner ℂ Φeff ((matrixKernel H0).starProjection Ξ) : ℂ) = 0) :
    Ξ = 0 := by
  have habs : |lam| = lam := abs_of_pos hlam
  have hsmall : |lam| * v + |E| < g := by
    rw [habs]
    linarith
  obtain ⟨R, hR, -⟩ := exists_isReducedInverse_reducedPerturbedHamiltonian hH0 hV hgap hv hsmall
  have hPA := kernelProjectionMatrix_reducedPerturbedHamiltonian hH0 hgap hv hsmall
  by_cases hzero : (matrixKernel H0).starProjection Ξ = 0
  · exact perturbedHamiltonian_eigenvector_eq_zero_of_starProjection_eq_zero hH0 hFirstOrder hR
      hPA hΞ hzero
  exfalso
  set Φ : EuclideanSpace ℂ n := (matrixKernel H0).starProjection Ξ with hΦdef
  have hΦmem : Φ ∈ matrixKernel H0 := Submodule.starProjection_apply_mem _ Ξ
  have hΓmem : Ξ - Φ ∈ (matrixKernel H0)ᗮ := Submodule.sub_starProjection_mem_orthogonal Ξ
  have heig : Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (Φ + (Ξ - Φ))
      = (E : ℂ) • (Φ + (Ξ - Φ)) := by
    rw [add_sub_cancel]
    exact hΞ
  have hU0 := abs_inner_secondOrderEffectiveHamiltonian_sub_mul_norm_sq_le hH0 hV hInv
    hFirstOrder hgap hv hgpos hlam hEabs hsmall4 hΦmem hΓmem heig
  have hΦgap := hδgap Φ (Submodule.mem_inf.mpr
    ⟨hΦmem, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hperp⟩)
  have hΦpos : (0 : ℝ) < ‖Φ‖ ^ 2 := by
    have hpos : 0 < ‖Φ‖ := norm_pos_iff.mpr hzero
    positivity
  have hupper := (abs_le.mp hU0).2
  have h1 : lam ^ 2 * ((Eeff + δ) * ‖Φ‖ ^ 2)
      ≤ lam ^ 2 * RCLike.re (inner ℂ Φ
        (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φ)) :=
    mul_le_mul_of_nonneg_left hΦgap (sq_nonneg lam)
  have h2 : E * ‖Φ‖ ^ 2 ≤ (lam ^ 2 * Eeff + c₃ * lam ^ 3) * ‖Φ‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hEup hΦpos.le
  have h3 : (0 : ℝ) < lam ^ 2 * ‖Φ‖ ^ 2 := by positivity
  have h4 := mul_lt_mul_of_pos_right hsmallδ h3
  nlinarith [h1, h2, hupper, h4]

/-- **Uniqueness of the ground state at a fixed small `λ`** (Tasaki §10.1, p. 347, final
paragraph, by a different route). Under the arc's smallness hypotheses — a strictly positive gap
`g` of `Ĥ₀` on `(ker Ĥ₀)ᗮ`, an operator bound `v` for `V̂`, the `δ`-gap of `Ĥeff` above a
normalized `Φeff ∈ ker Ĥ₀`, the variational bound `hc₃` at this `λ`, and
`0 < λ`, `4λv ≤ g`, `(c₃ + 4v³/g²)λ < δ` — the perturbed Hamiltonian `Ĥ(λ) = Ĥ₀ + λV̂` has a
unique normalized ground state on the whole space.

The ground eigenvalue `E` exists by compactness, and `|E| ≤ λv` together with
`E ≤ λ²Eeff + c₃λ³` makes the kernel-triviality lemma applicable at that `E`. Writing
`a(ψ) = ⟪Φeff, P̂₀ψ⟫` — ℂ-linear in `ψ`, since `P̂₀` is a continuous linear map and the inner
product is linear in its second slot — kernel triviality says `a(ψ) ≠ 0` for every nonzero
`E`-eigenvector. For a normalized ground eigenvector `φ` and any `E`-eigenvector `ψ`, the
antisymmetric combination `a(φ)•ψ − a(ψ)•φ` is again an `E`-eigenvector and has `a = 0`, hence
vanishes: `ψ` is a multiple of `φ`. **This combination is not Tasaki's argument**; it replaces
his count over the `D₀` continuous branches. -/
theorem exists_isUniqueGroundStateOn_perturbedHamiltonian
    {H0 V H0inv : Matrix n n ℂ} {g v lam Eeff δ c₃ : ℝ} {Φeff : EuclideanSpace ℂ n}
    (hH0pos : H0.PosSemidef) (hV : V.IsHermitian) (hInv : IsReducedInverse H0 H0inv)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hgpos : 0 < g)
    (hδgap : ∀ w ∈ matrixKernel H0 ⊓ (Submodule.span ℂ {Φeff})ᗮ,
      (Eeff + δ) * ‖w‖ ^ 2
        ≤ RCLike.re (inner ℂ w (Matrix.toEuclideanLin
            (secondOrderEffectiveHamiltonian H0 V H0inv) w)))
    (hΦeff : Φeff ∈ matrixKernel H0) (hnorm : ‖Φeff‖ = 1)
    (hlam : 0 < lam) (hsmall4 : 4 * (lam * v) ≤ g)
    (hsmallδ : (c₃ + 4 * v ^ 3 / g ^ 2) * lam < δ)
    (hc₃ : ∀ E : ℝ, IsGroundEigenvalueOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n))
      (perturbedHamiltonian H0 V lam) E → E ≤ lam ^ 2 * Eeff + c₃ * lam ^ 3) :
    ∃ E φ, IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n))
      (perturbedHamiltonian H0 V lam) E φ := by
  have hHerm : (perturbedHamiltonian H0 V lam).IsHermitian :=
    perturbedHamiltonian_isHermitian hH0pos.1 hV
  have hTopinv : ∀ w ∈ (⊤ : Submodule ℂ (EuclideanSpace ℂ n)),
      Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) w
        ∈ (⊤ : Submodule ℂ (EuclideanSpace ℂ n)) := fun _ _ => Submodule.mem_top
  have hΦeffne : Φeff ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hTopne : (⊤ : Submodule ℂ (EuclideanSpace ℂ n)) ≠ ⊥ := by
    intro h
    exact hΦeffne (Submodule.mem_bot ℂ |>.mp (h ▸ Submodule.mem_top))
  obtain ⟨E, hE⟩ := exists_isGroundEigenvalueOn hHerm hTopinv hTopne
  have hEabs : |E| ≤ lam * v :=
    abs_isGroundEigenvalue_perturbedHamiltonian_le hH0pos hV hv hFirstOrder hΦeff hnorm hlam hE
  have hEup : E ≤ lam ^ 2 * Eeff + c₃ * lam ^ 3 := hc₃ E hE
  obtain ⟨φ₀, -, hφ₀ne, hφ₀eig⟩ := hE.1
  obtain ⟨φ, hφnorm, hφeig⟩ : ∃ φ : EuclideanSpace ℂ n, ‖φ‖ = 1 ∧
      Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) φ = (E : ℂ) • φ :=
    ⟨(‖φ₀‖⁻¹ : ℂ) • φ₀, norm_smul_inv_norm hφ₀ne, by
      rw [map_smul, hφ₀eig]
      exact smul_comm _ _ _⟩
  have haφ : (inner ℂ Φeff ((matrixKernel H0).starProjection φ) : ℂ) ≠ 0 := by
    intro h0
    have hφ0 := perturbedHamiltonian_eigenvector_eq_zero_of_inner_starProjection_eq_zero
      hH0pos.1 hV hInv hFirstOrder hgap hv hgpos hlam hEabs hsmall4 hδgap hEup hsmallδ hφeig h0
    rw [hφ0, norm_zero] at hφnorm
    exact zero_ne_one hφnorm
  refine ⟨E, φ, Submodule.mem_top, hφnorm, hφeig, hE, ?_⟩
  rintro ψ - hψeig
  set aφ : ℂ := inner ℂ Φeff ((matrixKernel H0).starProjection φ) with haφdef
  set aψ : ℂ := inner ℂ Φeff ((matrixKernel H0).starProjection ψ) with haψdef
  have hΞeig : Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (aφ • ψ - aψ • φ)
      = (E : ℂ) • (aφ • ψ - aψ • φ) := by
    rw [map_sub, map_smul, map_smul, hψeig, hφeig, smul_comm aφ (E : ℂ) ψ,
      smul_comm aψ (E : ℂ) φ, ← smul_sub]
  have hΞperp :
      (inner ℂ Φeff ((matrixKernel H0).starProjection (aφ • ψ - aψ • φ)) : ℂ) = 0 := by
    rw [map_sub, map_smul, map_smul, inner_sub_right, inner_smul_right, inner_smul_right,
      ← haφdef, ← haψdef]
    ring
  have hΞ0 := perturbedHamiltonian_eigenvector_eq_zero_of_inner_starProjection_eq_zero
    hH0pos.1 hV hInv hFirstOrder hgap hv hgpos hlam hEabs hsmall4 hδgap hEup hsmallδ hΞeig hΞperp
  refine ⟨aφ⁻¹ * aψ, ?_⟩
  rw [← smul_smul, ← sub_eq_zero.mp hΞ0, smul_smul, inv_mul_cancel₀ haφ, one_smul]

/-- **Ground-state one-dimensionality for small `λ`** (Tasaki Lemma 10.1, §10.1, p. 347,
eqs. (10.1.21)–(10.1.22); first conjunct of the conclusion). For `Ĥ(λ) = Ĥ₀ + λV̂` with
`Ĥ₀ ≥ 0`, `V̂` Hermitian, `Ĥ₀⁻¹` a reduced inverse of `Ĥ₀` and vanishing first-order term
`P̂₀V̂P̂₀ = 0`: if the second-order effective Hamiltonian `Ĥeff = −P̂₀V̂Ĥ₀⁻¹V̂P̂₀` (eq. (10.1.20))
has a unique ground state on `ker Ĥ₀`, then there is `λ₀ > 0` such that `Ĥ(λ)` has a unique
ground state on the whole space for every `λ ∈ (0, λ₀)`.

All four constants are produced internally: the gap `g > 0` of `Ĥ₀` on `(ker Ĥ₀)ᗮ`, the operator
bound `v` for `V̂`, the gap `δ > 0` of `Ĥeff` above `Φeff` inside `ker Ĥ₀`, and the variational
constant `c₃ ≥ 0`. With `C = 4v³/g²` the threshold is the explicit
`λ₀ = min 1 (min (g/(4v+1)) (δ/(c₃+C+1)))`, the `+1`s keeping it well-formed at `v = 0` and at
`c₃ = C = 0`.

**Provenance.** Tasaki's own proof of this conclusion counts continuous eigenvalue branches
(Rellich–Kato) and takes `λ → 0` limits; the route taken here does neither. See the module
documentation. -/
theorem exists_lam0_isUniqueGroundStateOn_perturbedHamiltonian {H0 V H0inv : Matrix n n ℂ}
    {Eeff : ℝ} {Φeff : EuclideanSpace ℂ n}
    (hH0pos : H0.PosSemidef) (hV : V.IsHermitian) (hInv : IsReducedInverse H0 H0inv)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hEffGS : IsUniqueGroundStateOn (matrixKernel H0)
      (secondOrderEffectiveHamiltonian H0 V H0inv) Eeff Φeff) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam < lam0 →
      ∃ E φ, IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n))
        (perturbedHamiltonian H0 V lam) E φ := by
  obtain ⟨g, hgpos, hgap⟩ := matrixKernel_orthogonal_gap hH0pos
  obtain ⟨v, hvnn, hv⟩ := exists_norm_toEuclideanLin_le V
  obtain ⟨δ, hδpos, hδgap⟩ := hEffGS.orthogonal_gap
    (secondOrderEffectiveHamiltonian_isHermitian hV hInv.hermitian)
    (fun w _ => toEuclideanLin_secondOrderEffectiveHamiltonian_mem_matrixKernel w)
  obtain ⟨hΦeff, hnorm, hEeff, -, -⟩ := hEffGS
  obtain ⟨c₃, hc₃nn, hc₃⟩ := exists_const_isGroundEigenvalue_perturbedHamiltonian_le hH0pos.1 hV
    hInv hFirstOrder hΦeff hnorm hEeff
  have hCnn : (0 : ℝ) ≤ 4 * v ^ 3 / g ^ 2 := by positivity
  refine ⟨min 1 (min (g / (4 * v + 1)) (δ / (c₃ + 4 * v ^ 3 / g ^ 2 + 1))),
    lt_min one_pos (lt_min (div_pos hgpos (by linarith)) (div_pos hδpos (by linarith))),
    fun lam hlam hlt => ?_⟩
  have hlam1 : lam ≤ 1 := (lt_of_lt_of_le hlt (min_le_left _ _)).le
  have hsmall4 : 4 * (lam * v) ≤ g := by
    have hdiv := (lt_div_iff₀ (by linarith : (0 : ℝ) < 4 * v + 1)).mp
      (lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_left _ _)))
    nlinarith
  have hsmallδ : (c₃ + 4 * v ^ 3 / g ^ 2) * lam < δ := by
    have hdiv := (lt_div_iff₀ (by linarith : (0 : ℝ) < c₃ + 4 * v ^ 3 / g ^ 2 + 1)).mp
      (lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith
  exact exists_isUniqueGroundStateOn_perturbedHamiltonian hH0pos hV hInv hFirstOrder hgap hv
    hgpos hδgap hΦeff hnorm hlam hsmall4 hsmallδ fun E hE => hc₃ lam E hlam hlam1 hE

end LatticeSystem.Math
