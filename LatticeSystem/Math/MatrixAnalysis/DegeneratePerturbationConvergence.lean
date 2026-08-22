import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbationUniqueness

/-!
# Convergence of the perturbed ground state (Tasaki Lemma 10.1)

Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020,
§10.1, Lemma 10.1 and eqs. (10.1.20)–(10.1.22), pp. 346–347. This module carries the statement of
Lemma 10.1 itself: for `Ĥ(λ) = Ĥ₀ + λV̂` with `Ĥ₀ ≥ 0`, `V̂` Hermitian, `Ĥ₀⁻¹` a reduced inverse
and vanishing first-order term `P̂₀V̂P̂₀ = 0`, if the second-order effective Hamiltonian
`Ĥeff = −P̂₀V̂Ĥ₀⁻¹V̂P̂₀` has a unique ground state `Φeff` inside `ker Ĥ₀`, then `Ĥ(λ)` has a unique
ground state for every sufficiently small `λ > 0`, and a phase choice of those normalized ground
states converges to `Φeff` as `λ → 0⁺`.

## Provenance: the book supplies no argument for the convergence conjunct

Tasaki's printed proof (pp. 346–347) ends at uniqueness — *"we find that `|Ξ₁(λ)⟩` is the unique
ground state of `Ĥ(λ)` for sufficiently small λ."* Convergence is left implicit in the proof's
opening analytic input, *"We can also assume that each of these `D₀` eigenstates depends
continuously on λ"* (Rellich–Kato, asserted without proof), combined with the identification
`|Ξ₁(0)⟩ = (const.)|Φeff-GS⟩` read off (10.1.21)–(10.1.22). No rate is claimed.

What is proved here is an independent, fully quantitative substitute: for `Φ = P̂₀φ`, `Γ = φ − Φ`,
`a = ⟪Φeff, Φ⟫` and `w = Φ − aΦeff`, a single-`λ` estimate gives `‖Γ‖ = O(λ)` and `‖w‖² = O(λ)`,
whence `‖cφ − Φeff‖² = 2 − 2|a| ≤ 2(‖w‖² + ‖Γ‖²) ≤ Kλ` with the explicit

  `K = 2((c₃ + 4v³/g²)/δ + 4v²/g²)`,

`g` the gap of `Ĥ₀` on `(ker Ĥ₀)ᗮ`, `v` an operator bound for `V̂`, `δ` the `Ĥeff`-gap above `Φeff`
inside `ker Ĥ₀`, and `c₃` the variational constant. No continuity, no eigenvalue branches, no `D₀`
and no `λ → 0` limit enter the estimate; the only topology in the whole argument is the final
`Tendsto`, discharged by squeezing against `√(Kλ)`. The resulting rate `O(√λ)` is not optimal (the
true rate is `O(λ)`) and is not claimed to be.

## Two points of fidelity

* The book writes "converges to `|Φeff-GS⟩`" with no phase caveat, while an eigenvector is only
  determined up to a phase; the existential `Philam` supplies the phase choice, legitimised by
  `IsUniqueGroundStateOn.smul_of_norm_one`.
* The book's `λ → 0` is two-sided while the statement below uses `𝓝[>] 0`, i.e. is weaker.

## Contents

* `norm_sub_starProjection_perturbedHamiltonian_le` — `‖Γ‖ ≤ (2v/g) λ ‖Φ‖`.
* `mul_norm_sub_smul_sq_le` — `δ‖w‖² ≤ (c₃ + 4v³/g²) λ ‖Φ‖²`.
* `exists_norm_smul_sub_sq_le_of_isUniqueGroundStateOn` — the rate `‖cφ − Φeff‖² ≤ Kλ`.
* `exists_lam0_isUniqueGroundStateOn_norm_sub_sq_le` — uniqueness and the rate, packaged over a
  threshold `λ₀`.
* `tasaki_lemma_10_1_degenerate_perturbation` — Lemma 10.1.
-/

namespace LatticeSystem.Math

open Matrix Filter Topology
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The orthogonal component of an eigenvector is `O(λ)`** (Tasaki §10.1, the exact form of the
approximation (10.1.18), p. 346). Let `Φ + Γ` be an `E`-eigenvector of `Ĥ(λ) = Ĥ₀ + λV̂` split
along `ker Ĥ₀` and its orthogonal complement, with `|E| ≤ λv` and `4λv ≤ g`. The Feshbach
reconstruction `Γ = −λR(λ,E)V̂Φ` and the resolvent bound `‖R u‖ ≤ ‖u‖/(g − λv − |E|)` combine with
`g − λv − |E| ≥ g/2` to give

  `‖Γ‖ ≤ (2v/g) λ ‖Φ‖`. -/
theorem norm_sub_starProjection_perturbedHamiltonian_le {H0 V : Matrix n n ℂ} {g v lam E : ℝ}
    {Φ Γ : EuclideanSpace ℂ n} (hH0 : H0.IsHermitian) (hV : V.IsHermitian)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hgpos : 0 < g) (hlam : 0 < lam) (hEabs : |E| ≤ lam * v) (hsmall4 : 4 * (lam * v) ≤ g)
    (hΦ : Φ ∈ matrixKernel H0) (hΓ : Γ ∈ (matrixKernel H0)ᗮ)
    (heig : Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (Φ + Γ) = (E : ℂ) • (Φ + Γ)) :
    ‖Γ‖ ≤ 2 * v / g * lam * ‖Φ‖ := by
  have habs : |lam| = lam := abs_of_pos hlam
  have hsmall : |lam| * v + |E| < g := by
    rw [habs]
    linarith
  obtain ⟨R, hR, hRnorm⟩ :=
    exists_isReducedInverse_reducedPerturbedHamiltonian hH0 hV hgap hv hsmall
  have hPA := kernelProjectionMatrix_reducedPerturbedHamiltonian hH0 hgap hv hsmall
  obtain ⟨hΓeq, -⟩ := (perturbedHamiltonian_eigenvector_iff hH0 hFirstOrder hR hPA hΦ hΓ).mp heig
  have hΓnorm : ‖Γ‖ = lam * ‖Matrix.toEuclideanLin R (Matrix.toEuclideanLin V Φ)‖ := by
    rw [hΓeq, norm_smul, norm_neg]
    simp [habs]
  have hden : g / 2 ≤ g - |lam| * v - |E| := by
    rw [habs]
    linarith
  have hdenpos : (0 : ℝ) < g - |lam| * v - |E| := by linarith
  have hRb := hRnorm (Matrix.toEuclideanLin V Φ)
  rw [le_div_iff₀ hdenpos] at hRb
  have hRle : ‖Matrix.toEuclideanLin R (Matrix.toEuclideanLin V Φ)‖ * (g / 2) ≤ v * ‖Φ‖ := by
    nlinarith [norm_nonneg (Matrix.toEuclideanLin R (Matrix.toEuclideanLin V Φ)), hv Φ, hden, hRb]
  rw [hΓnorm, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hgpos]
  nlinarith [hRle, hlam]

/-- **The degenerate component of an eigenvector is close to the `Φeff`-axis** (Tasaki §10.1,
eqs. (10.1.21)–(10.1.22), p. 347, by an independent route). Write `a = ⟪Φeff, Φ⟫` and
`w = Φ − aΦeff` for the component of `Φ = P̂₀Ξ` transverse to the effective ground state. Then

  `δ ‖w‖² ≤ (c₃ + 4v³/g²) λ ‖Φ‖²`,

where `δ` is the `Ĥeff`-gap above `Φeff` inside `ker Ĥ₀` and `c₃` the variational constant of the
bound `E ≤ λ²Eeff + c₃λ³`.

The proof is an exact cancellation. Splitting `Φ = aΦeff + w` orthogonally, symmetry of `Ĥeff` and
`ĤeffΦeff = EeffΦeff` give `re⟪Φ, ĤeffΦ⟫ = |a|²Eeff + re⟪w, Ĥeff w⟫`, which the `δ`-gap bounds
below by `|a|²Eeff + (Eeff+δ)‖w‖²`; the quadratic-form engine plus the variational bound bound
`λ² re⟪Φ, ĤeffΦ⟫` above by `(λ²Eeff + (c₃+4v³/g²)λ³)‖Φ‖²`. Pythagoras `‖Φ‖² = |a|² + ‖w‖²` makes
the whole `Eeff` contribution cancel, with no sign hypothesis on `Eeff`. -/
theorem mul_norm_sub_smul_sq_le {H0 V H0inv : Matrix n n ℂ} {g v lam E Eeff δ c₃ : ℝ}
    {Φeff Φ Γ : EuclideanSpace ℂ n} (hH0 : H0.IsHermitian) (hV : V.IsHermitian)
    (hInv : IsReducedInverse H0 H0inv)
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
    (hΦeff : Φeff ∈ matrixKernel H0) (hnorm : ‖Φeff‖ = 1)
    (hEeff : Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φeff
      = (Eeff : ℂ) • Φeff)
    (hΦ : Φ ∈ matrixKernel H0) (hΓ : Γ ∈ (matrixKernel H0)ᗮ)
    (heig : Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (Φ + Γ) = (E : ℂ) • (Φ + Γ)) :
    δ * ‖Φ - (inner ℂ Φeff Φ : ℂ) • Φeff‖ ^ 2
      ≤ (c₃ + 4 * v ^ 3 / g ^ 2) * lam * ‖Φ‖ ^ 2 := by
  have hU0 := abs_inner_secondOrderEffectiveHamiltonian_sub_mul_norm_sq_le hH0 hV hInv hFirstOrder
    hgap hv hgpos hlam hEabs hsmall4 hΦ hΓ heig
  have hsym : (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv)).IsSymmetric :=
    Matrix.isHermitian_iff_isSymmetric.mp
      (secondOrderEffectiveHamiltonian_isHermitian hV hInv.hermitian)
  obtain ⟨a, hadef⟩ : ∃ a : ℂ, a = (inner ℂ Φeff Φ : ℂ) := ⟨_, rfl⟩
  obtain ⟨w, hwdef⟩ : ∃ w : EuclideanSpace ℂ n, w = Φ - a • Φeff := ⟨_, rfl⟩
  rw [← hadef, ← hwdef]
  have hΦeffΦeff : (inner ℂ Φeff Φeff : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    norm_num
  have hwperp : (inner ℂ Φeff w : ℂ) = 0 := by
    rw [hwdef, inner_sub_right, inner_smul_right, hΦeffΦeff, mul_one, ← hadef, sub_self]
  have hwperp' : (inner ℂ w Φeff : ℂ) = 0 := by
    rw [← inner_conj_symm, hwperp, map_zero]
  have hdecomp : a • Φeff + w = Φ := by
    rw [hwdef]
    abel
  have hwker : w ∈ matrixKernel H0 := by
    rw [hwdef]
    exact Submodule.sub_mem _ hΦ (Submodule.smul_mem _ _ hΦeff)
  have hwmem : w ∈ matrixKernel H0 ⊓ (Submodule.span ℂ {Φeff})ᗮ :=
    Submodule.mem_inf.mpr ⟨hwker,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hwperp⟩
  have hpyth : ‖Φ‖ ^ 2 = ‖a‖ ^ 2 + ‖w‖ ^ 2 := by
    have hin : (inner ℂ (a • Φeff) w : ℂ) = 0 := by rw [inner_smul_left, hwperp, mul_zero]
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) (a • Φeff) w hin
    rw [hdecomp, norm_smul, hnorm, mul_one] at h
    linarith
  -- The quadratic form of `Ĥeff` splits along `Φ = aΦeff + w`.
  have hTΦ : Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φ
      = (a * (Eeff : ℂ)) • Φeff
        + Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) w := by
    rw [← hdecomp, map_add, map_smul, hEeff, smul_smul]
  have hTw : (inner ℂ Φeff
      (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) w) : ℂ) = 0 := by
    rw [← hsym Φeff w, hEeff, inner_smul_left, hwperp, mul_zero]
  have hexp : (inner ℂ Φ
        (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φ) : ℂ)
      = ((‖a‖ ^ 2 : ℝ) : ℂ) * (Eeff : ℂ)
        + (inner ℂ w
            (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) w) : ℂ) := by
    have hconj : (starRingEnd ℂ) a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
      simpa using RCLike.conj_mul a
    rw [hTΦ, ← hdecomp, inner_add_left, inner_add_right, inner_add_right, inner_smul_left,
      inner_smul_left, inner_smul_right, inner_smul_right, hΦeffΦeff, hTw, hwperp']
    linear_combination (Eeff : ℂ) * hconj
  have hquad : RCLike.re (inner ℂ Φ
        (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φ))
      = ‖a‖ ^ 2 * Eeff
        + RCLike.re (inner ℂ w
            (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) w)) := by
    have hre := congrArg Complex.re hexp
    rwa [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re, ← RCLike.re_to_complex,
      ← RCLike.re_to_complex] at hre
  have hlam2 : (0 : ℝ) < lam ^ 2 := by positivity
  have e1 : lam ^ 2 * RCLike.re (inner ℂ Φ
        (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φ))
      = lam ^ 2 * (‖a‖ ^ 2 * Eeff)
        + lam ^ 2 * RCLike.re (inner ℂ w
            (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) w)) := by
    rw [hquad]
    ring
  have e2 : lam ^ 2 * ((Eeff + δ) * ‖w‖ ^ 2)
      ≤ lam ^ 2 * RCLike.re (inner ℂ w
          (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) w)) :=
    mul_le_mul_of_nonneg_left (hδgap w hwmem) hlam2.le
  have e3 : E * ‖Φ‖ ^ 2 ≤ (lam ^ 2 * Eeff + c₃ * lam ^ 3) * ‖Φ‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hEup (sq_nonneg _)
  have e4 : lam ^ 2 * Eeff * ‖Φ‖ ^ 2
      = lam ^ 2 * Eeff * ‖a‖ ^ 2 + lam ^ 2 * Eeff * ‖w‖ ^ 2 := by
    rw [hpyth]
    ring
  have hkey : lam ^ 2 * (δ * ‖w‖ ^ 2)
      ≤ lam ^ 2 * ((c₃ + 4 * v ^ 3 / g ^ 2) * lam * ‖Φ‖ ^ 2) := by
    linarith [(abs_le.mp hU0).2, e1, e2, e3, e4]
  exact le_of_mul_le_mul_left hkey hlam2

/-- **The quantitative form of Lemma 10.1's convergence conjunct at a fixed `λ`.** Under the arc's
smallness hypotheses, if `φ` is *the* normalized ground state of `Ĥ(λ) = Ĥ₀ + λV̂` on the whole
space, then a phase `c` of modulus one brings it within `O(√λ)` of the effective ground state:

  `‖cφ − Φeff‖² ≤ 2((c₃ + 4v³/g²)/δ + 4v²/g²) λ`.

Writing `Φ = P̂₀φ`, `Γ = φ − Φ`, `a = ⟪Φeff, Φ⟫` and `w = Φ − aΦeff`, the two Pythagoras identities
`1 = ‖Φ‖² + ‖Γ‖²` and `‖Φ‖² = |a|² + ‖w‖²` give `1 − |a|² = ‖w‖² + ‖Γ‖²`. Kernel triviality makes
`a ≠ 0`, so `c = |a|/a` is well defined, `⟪Φeff, cφ⟫ = |a|` and `‖cφ − Φeff‖² = 2 − 2|a|`, which
`|a| ≤ 1` bounds by `2(1 − |a|²)`. The two estimates of `‖w‖` and `‖Γ‖` finish the count.

**This is not Tasaki's argument**; the book asserts convergence as a consequence of an unproved
continuity assumption and claims no rate. See the module documentation. -/
theorem exists_norm_smul_sub_sq_le_of_isUniqueGroundStateOn {H0 V H0inv : Matrix n n ℂ}
    {g v lam E Eeff δ c₃ : ℝ} {Φeff φ : EuclideanSpace ℂ n}
    (hH0pos : H0.PosSemidef) (hV : V.IsHermitian) (hInv : IsReducedInverse H0 H0inv)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hgpos : 0 < g) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hsmall4 : 4 * (lam * v) ≤ g)
    (hδgap : ∀ w ∈ matrixKernel H0 ⊓ (Submodule.span ℂ {Φeff})ᗮ,
      (Eeff + δ) * ‖w‖ ^ 2
        ≤ RCLike.re (inner ℂ w (Matrix.toEuclideanLin
            (secondOrderEffectiveHamiltonian H0 V H0inv) w)))
    (hδpos : 0 < δ) (hΦeff : Φeff ∈ matrixKernel H0) (hnorm : ‖Φeff‖ = 1)
    (hEeff : Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φeff
      = (Eeff : ℂ) • Φeff)
    (hEup : E ≤ lam ^ 2 * Eeff + c₃ * lam ^ 3)
    (hsmallδ : (c₃ + 4 * v ^ 3 / g ^ 2) * lam < δ)
    (hGS : IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n))
      (perturbedHamiltonian H0 V lam) E φ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      ‖c • φ - Φeff‖ ^ 2
        ≤ 2 * ((c₃ + 4 * v ^ 3 / g ^ 2) / δ + 4 * v ^ 2 / g ^ 2) * lam := by
  obtain ⟨-, hφnorm, hφeig, hground, -⟩ := hGS
  have hEabs : |E| ≤ lam * v :=
    abs_isGroundEigenvalue_perturbedHamiltonian_le hH0pos hV hv hFirstOrder hΦeff hnorm hlam hground
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : EuclideanSpace ℂ n, Φ = (matrixKernel H0).starProjection φ :=
    ⟨_, rfl⟩
  obtain ⟨Γ, hΓdef⟩ : ∃ Γ : EuclideanSpace ℂ n, Γ = φ - Φ := ⟨_, rfl⟩
  have hΦmem : Φ ∈ matrixKernel H0 := by
    rw [hΦdef]
    exact Submodule.starProjection_apply_mem _ φ
  have hΓmem : Γ ∈ (matrixKernel H0)ᗮ := by
    rw [hΓdef, hΦdef]
    exact Submodule.sub_starProjection_mem_orthogonal φ
  have hsum : Φ + Γ = φ := by
    rw [hΓdef]
    abel
  have heig : Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (Φ + Γ)
      = (E : ℂ) • (Φ + Γ) := by
    rw [hsum]
    exact hφeig
  have hpyth1 : ‖Φ‖ ^ 2 + ‖Γ‖ ^ 2 = 1 := by
    have hΦΓ : (inner ℂ Φ Γ : ℂ) = 0 := (Submodule.mem_orthogonal _ Γ).mp hΓmem Φ hΦmem
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) Φ Γ hΦΓ
    rw [hsum, hφnorm] at h
    linarith only [h]
  have hane : (inner ℂ Φeff Φ : ℂ) ≠ 0 := by
    intro h0
    rw [hΦdef] at h0
    have hzero := perturbedHamiltonian_eigenvector_eq_zero_of_inner_starProjection_eq_zero
      hH0pos.1 hV hInv hFirstOrder hgap hv hgpos hlam hEabs hsmall4 hδgap hEup hsmallδ hφeig h0
    rw [hzero, norm_zero] at hφnorm
    exact zero_ne_one hφnorm
  have hG1 := norm_sub_starProjection_perturbedHamiltonian_le hH0pos.1 hV hFirstOrder hgap hv
    hgpos hlam hEabs hsmall4 hΦmem hΓmem heig
  have hG2 := mul_norm_sub_smul_sq_le hH0pos.1 hV hInv hFirstOrder hgap hv hgpos hlam hEabs
    hsmall4 hδgap hEup hΦeff hnorm hEeff hΦmem hΓmem heig
  obtain ⟨a, hadef⟩ : ∃ a : ℂ, a = (inner ℂ Φeff Φ : ℂ) := ⟨_, rfl⟩
  obtain ⟨w, hwdef⟩ : ∃ w : EuclideanSpace ℂ n, w = Φ - a • Φeff := ⟨_, rfl⟩
  rw [← hadef] at hane hG2
  rw [← hwdef] at hG2
  have hΦeffΦeff : (inner ℂ Φeff Φeff : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    norm_num
  have hwperp : (inner ℂ Φeff w : ℂ) = 0 := by
    rw [hwdef, inner_sub_right, inner_smul_right, hΦeffΦeff, mul_one, ← hadef, sub_self]
  have hpyth2 : ‖Φ‖ ^ 2 = ‖a‖ ^ 2 + ‖w‖ ^ 2 := by
    have hin : (inner ℂ (a • Φeff) w : ℂ) = 0 := by rw [inner_smul_left, hwperp, mul_zero]
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) (a • Φeff) w hin
    have hdecomp : a • Φeff + w = Φ := by
      rw [hwdef]
      abel
    rw [hdecomp, norm_smul, hnorm, mul_one] at h
    linarith only [h]
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr hane
  have hΦpos : (0 : ℝ) < ‖Φ‖ ^ 2 := by nlinarith only [hpyth2, sq_nonneg ‖w‖, hapos]
  have hΦle : ‖Φ‖ ^ 2 ≤ 1 := by linarith only [hpyth1, sq_nonneg ‖Γ‖]
  have hale : ‖a‖ ≤ 1 := by nlinarith only [hpyth2, hΦle, sq_nonneg ‖w‖, norm_nonneg a]
  -- Abbreviating the two rate coefficients keeps the arithmetic below small enough to elaborate.
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (c₃ + 4 * v ^ 3 / g ^ 2) * lam := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 4 * v ^ 2 / g ^ 2 := ⟨_, rfl⟩
  rw [← hA] at hG2
  have hBnn : (0 : ℝ) ≤ B := by
    rw [hB]
    positivity
  have hAnn : (0 : ℝ) ≤ A := by
    have hmul : (0 : ℝ) * ‖Φ‖ ^ 2 ≤ A * ‖Φ‖ ^ 2 := by
      rw [zero_mul]
      exact le_trans (mul_nonneg hδpos.le (sq_nonneg _)) hG2
    exact le_of_mul_le_mul_right hmul hΦpos
  have hwbound : δ * ‖w‖ ^ 2 ≤ A := by
    have h := mul_le_mul_of_nonneg_left hΦle hAnn
    rw [mul_one] at h
    exact le_trans hG2 h
  have hΓbound : ‖Γ‖ ^ 2 ≤ B * lam := by
    have hsq := mul_self_le_mul_self (norm_nonneg Γ) hG1
    have hexp2 : 2 * v / g * lam * ‖Φ‖ * (2 * v / g * lam * ‖Φ‖)
        = B * (lam ^ 2 * ‖Φ‖ ^ 2) := by
      rw [hB]
      ring
    rw [hexp2] at hsq
    have h1 : lam ^ 2 * ‖Φ‖ ^ 2 ≤ lam ^ 2 * 1 := mul_le_mul_of_nonneg_left hΦle (sq_nonneg lam)
    have h2 : lam ^ 2 ≤ lam := by nlinarith only [hlam, hlam1]
    have h3 : B * (lam ^ 2 * ‖Φ‖ ^ 2) ≤ B * lam :=
      mul_le_mul_of_nonneg_left (by linarith only [h1, h2]) hBnn
    linarith only [hsq, h3]
  have hcne : ((‖a‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hapos.ne'
  have hcnorm : ‖((‖a‖ : ℝ) : ℂ) / a‖ = 1 := by
    rw [norm_div]
    simp [hapos.ne']
  refine ⟨((‖a‖ : ℝ) : ℂ) / a, hcnorm, ?_⟩
  have hinner : (inner ℂ Φeff φ : ℂ) = a := by
    have hΓperp : (inner ℂ Φeff Γ : ℂ) = 0 := (Submodule.mem_orthogonal _ Γ).mp hΓmem Φeff hΦeff
    rw [← hsum, inner_add_right, hΓperp, add_zero, ← hadef]
  have hinner2 : (inner ℂ Φeff ((((‖a‖ : ℝ) : ℂ) / a) • φ) : ℂ) = ((‖a‖ : ℝ) : ℂ) := by
    rw [inner_smul_right, hinner, div_mul_cancel₀ _ hane]
  have hsub : ‖(((‖a‖ : ℝ) : ℂ) / a) • φ - Φeff‖ ^ 2 = 2 - 2 * ‖a‖ := by
    have hnorm2 : ‖(((‖a‖ : ℝ) : ℂ) / a) • φ‖ = 1 := by
      rw [norm_smul, hcnorm, hφnorm, mul_one]
    have hre2 : RCLike.re (inner ℂ ((((‖a‖ : ℝ) : ℂ) / a) • φ) Φeff) = ‖a‖ := by
      rw [← inner_conj_symm, hinner2]
      simp
    rw [norm_sub_sq (𝕜 := ℂ), hnorm2, hnorm, hre2]
    ring
  rw [hsub, ← hB]
  have hstep1 : 1 - ‖a‖ ≤ ‖w‖ ^ 2 + ‖Γ‖ ^ 2 := by
    nlinarith only [hpyth1, hpyth2, hale, norm_nonneg a]
  have hstep2 : ‖w‖ ^ 2 ≤ (c₃ + 4 * v ^ 3 / g ^ 2) / δ * lam := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hδpos, ← hA]
    linarith only [hwbound]
  linarith only [hstep1, hstep2, hΓbound]

/-- **Uniqueness and the convergence rate, packaged over a threshold** (Tasaki Lemma 10.1,
§10.1, p. 346). Under the hypotheses of the lemma there are `λ₀ > 0` and `K ≥ 0` such that for
every `λ ∈ (0, λ₀)` the perturbed Hamiltonian `Ĥ(λ) = Ĥ₀ + λV̂` has a normalized ground state `φ`
that is unique on the whole space and satisfies `‖φ − Φeff‖² ≤ Kλ`.

Uniqueness is imported from `exists_lam0_isUniqueGroundStateOn_perturbedHamiltonian`, whose
threshold comes from its own internally produced constants; the rate is supplied by
`exists_norm_smul_sub_sq_le_of_isUniqueGroundStateOn` at the constants produced here, and the two
thresholds are combined with `min`. Re-phasing the ground state by the modulus-one `c` of the rate
estimate is legitimate by `IsUniqueGroundStateOn.smul_of_norm_one`. -/
theorem exists_lam0_isUniqueGroundStateOn_norm_sub_sq_le {H0 V H0inv : Matrix n n ℂ} {Eeff : ℝ}
    {Φeff : EuclideanSpace ℂ n} (hH0pos : H0.PosSemidef) (hV : V.IsHermitian)
    (hInv : IsReducedInverse H0 H0inv)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hEffGS : IsUniqueGroundStateOn (matrixKernel H0)
      (secondOrderEffectiveHamiltonian H0 V H0inv) Eeff Φeff) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ lam : ℝ, 0 < lam → lam < lam0 →
      ∃ E φ, IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n))
        (perturbedHamiltonian H0 V lam) E φ ∧ ‖φ - Φeff‖ ^ 2 ≤ K * lam := by
  obtain ⟨lam0U, hlam0U, hU3⟩ :=
    exists_lam0_isUniqueGroundStateOn_perturbedHamiltonian hH0pos hV hInv hFirstOrder hEffGS
  obtain ⟨g, hgpos, hgap⟩ := matrixKernel_orthogonal_gap hH0pos
  obtain ⟨v, hvnn, hv⟩ := exists_norm_toEuclideanLin_le V
  obtain ⟨δ, hδpos, hδgap⟩ := hEffGS.orthogonal_gap
    (secondOrderEffectiveHamiltonian_isHermitian hV hInv.hermitian)
    (fun w _ => toEuclideanLin_secondOrderEffectiveHamiltonian_mem_matrixKernel w)
  obtain ⟨hΦeff, hnorm, hEeff, -, -⟩ := hEffGS
  obtain ⟨c₃, hc₃nn, hc₃⟩ := exists_const_isGroundEigenvalue_perturbedHamiltonian_le hH0pos.1 hV
    hInv hFirstOrder hΦeff hnorm hEeff
  have hCnn : (0 : ℝ) ≤ 4 * v ^ 3 / g ^ 2 := by positivity
  have hKnn : (0 : ℝ) ≤ 2 * ((c₃ + 4 * v ^ 3 / g ^ 2) / δ + 4 * v ^ 2 / g ^ 2) := by
    have h1 : (0 : ℝ) ≤ (c₃ + 4 * v ^ 3 / g ^ 2) / δ := div_nonneg (by linarith) hδpos.le
    have h2 : (0 : ℝ) ≤ 4 * v ^ 2 / g ^ 2 := by positivity
    linarith
  refine ⟨min lam0U (min 1 (min (g / (4 * v + 1)) (δ / (c₃ + 4 * v ^ 3 / g ^ 2 + 1)))),
    lt_min hlam0U (lt_min one_pos (lt_min (div_pos hgpos (by linarith))
      (div_pos hδpos (by linarith)))),
    2 * ((c₃ + 4 * v ^ 3 / g ^ 2) / δ + 4 * v ^ 2 / g ^ 2), hKnn, fun lam hlam hlt => ?_⟩
  have hltU : lam < lam0U := lt_of_lt_of_le hlt (min_le_left _ _)
  have hrest : lam < min 1 (min (g / (4 * v + 1)) (δ / (c₃ + 4 * v ^ 3 / g ^ 2 + 1))) :=
    lt_of_lt_of_le hlt (min_le_right _ _)
  have hlam1 : lam ≤ 1 := (lt_of_lt_of_le hrest (min_le_left _ _)).le
  have hsmall4 : 4 * (lam * v) ≤ g := by
    have hdiv := (lt_div_iff₀ (by linarith : (0 : ℝ) < 4 * v + 1)).mp
      (lt_of_lt_of_le hrest ((min_le_right _ _).trans (min_le_left _ _)))
    nlinarith
  have hsmallδ : (c₃ + 4 * v ^ 3 / g ^ 2) * lam < δ := by
    have hdiv := (lt_div_iff₀ (by linarith : (0 : ℝ) < c₃ + 4 * v ^ 3 / g ^ 2 + 1)).mp
      (lt_of_lt_of_le hrest ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith
  obtain ⟨E, φ, hGS⟩ := hU3 lam hlam hltU
  obtain ⟨c, hcnorm, hrate⟩ := exists_norm_smul_sub_sq_le_of_isUniqueGroundStateOn hH0pos hV hInv
    hFirstOrder hgap hv hgpos hlam hlam1 hsmall4 hδgap hδpos hΦeff hnorm hEeff
    (hc₃ lam E hlam hlam1 hGS.2.2.2.1) hsmallδ hGS
  exact ⟨E, c • φ, hGS.smul_of_norm_one hcnorm, hrate⟩

/-- **Tasaki Lemma 10.1 (degenerate perturbation theory).**
(1st ed., Springer 2020, §10.1, Lemma 10.1 / eqs. (10.1.20)–(10.1.22), pp. 346–347.)

For `Ĥ(λ) = Ĥ₀ + λ V̂` with `Ĥ₀ ≥ 0` Hermitian, `V̂` Hermitian, `H0inv` a reduced inverse of `Ĥ₀`,
and the **first-order term vanishing on the degenerate subspace** (`P̂₀ V̂ P̂₀ = 0`, the condition
under which the effective theory is governed by the second-order term — Tasaki eq. (10.1.6),
`Ĥspin = λ² Ĥeff`, has no `λ¹` term): if the second-order effective Hamiltonian
`Ĥeff = − P̂₀ V̂ Ĥ₀⁻¹ V̂ P̂₀` has a unique ground state `Φeff` on the kernel `H₀ = ker Ĥ₀`, then
there is `λ₀ > 0` such that for every `λ ∈ (0, λ₀)` the perturbed Hamiltonian `Ĥ(λ)` has a unique
ground state on the whole space, and a phase choice of these normalized ground states converges to
`Φeff` as `λ → 0⁺`.

The per-`λ` data is turned into the total functions `Elam`, `Philam` demanded by the statement by
choice, with the junk value `(0, Φeff)` outside `(0, λ₀)`; convergence is then a squeeze of the
`O(√λ)` rate of `exists_lam0_isUniqueGroundStateOn_norm_sub_sq_le` against `√(Kλ)`.

The Hermiticity hypothesis `_hH0` is subsumed by `hH0pos` and is carried only so that the
hypothesis list matches the one Tasaki states (`Ĥ₀ ≥ 0` Hermitian). -/
theorem tasaki_lemma_10_1_degenerate_perturbation [Nonempty n] (H0 V H0inv : Matrix n n ℂ)
    (_hH0 : H0.IsHermitian) (hH0pos : H0.PosSemidef) (hV : V.IsHermitian)
    (hInv : IsReducedInverse H0 H0inv)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (Eeff : ℝ) (Φeff : EuclideanSpace ℂ n)
    (hEffGS : IsUniqueGroundStateOn (matrixKernel H0)
      (secondOrderEffectiveHamiltonian H0 V H0inv) Eeff Φeff) :
    ∃ lam0 : ℝ, 0 < lam0 ∧
      ∃ Elam : ℝ → ℝ, ∃ Philam : ℝ → EuclideanSpace ℂ n,
        (∀ lam : ℝ, 0 < lam → lam < lam0 →
          IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n))
            (perturbedHamiltonian H0 V lam) (Elam lam) (Philam lam)) ∧
        Tendsto Philam (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 Φeff) := by
  classical
  obtain ⟨lam0, hlam0, K, hKnn, hK⟩ :=
    exists_lam0_isUniqueGroundStateOn_norm_sub_sq_le hH0pos hV hInv hFirstOrder hEffGS
  have hex : ∀ lam : ℝ, ∃ p : ℝ × EuclideanSpace ℂ n, 0 < lam → lam < lam0 →
      IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n))
        (perturbedHamiltonian H0 V lam) p.1 p.2 ∧ ‖p.2 - Φeff‖ ^ 2 ≤ K * lam := by
    intro lam
    by_cases hmem : 0 < lam ∧ lam < lam0
    · obtain ⟨E, ψ, hψGS, hψrate⟩ := hK lam hmem.1 hmem.2
      exact ⟨(E, ψ), fun _ _ => ⟨hψGS, hψrate⟩⟩
    · exact ⟨(0, Φeff), fun h1 h2 => absurd ⟨h1, h2⟩ hmem⟩
  choose f hf using hex
  refine ⟨lam0, hlam0, fun lam => (f lam).1, fun lam => (f lam).2,
    fun lam h1 h2 => (hf lam h1 h2).1, ?_⟩
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' (a := fun lam : ℝ => Real.sqrt (K * lam)) ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT hlam0] with lam hlamI
    rw [← Real.sqrt_sq (norm_nonneg ((f lam).2 - Φeff))]
    exact Real.sqrt_le_sqrt (hf lam hlamI.1 hlamI.2).2
  · have h0 : Tendsto (fun lam : ℝ => K * lam) (𝓝 (0 : ℝ)) (𝓝 (K * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at h0
    have hlin : Tendsto (fun lam : ℝ => K * lam) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) :=
      h0.mono_left nhdsWithin_le_nhds
    simpa using (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hlin

end LatticeSystem.Math
