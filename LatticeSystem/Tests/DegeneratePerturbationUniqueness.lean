import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbationUniqueness
import LatticeSystem.Tests.DegeneratePerturbationGroundEnergy

/-!
# Test coverage for ground-state one-dimensionality (Tasaki Lemma 10.1, PR-5)

Pins the API contract of `Math/MatrixAnalysis/DegeneratePerturbationUniqueness.lean`:

1. **N1** `exists_norm_toEuclideanLin_le` — every matrix has an operator-norm bound on
   `EuclideanSpace ℂ n`.
2. **U0** `abs_inner_secondOrderEffectiveHamiltonian_sub_mul_norm_sq_le` — the quadratic-form
   engine, §2 Step 1: `|λ²re⟪Φ,ĤeffΦ⟫ − E‖Φ‖²| ≤ Cλ³‖Φ‖²` for an exact `(Φ,Γ)`-split eigenvector of
   `Ĥ(λ)`.
3. **U1** `perturbedHamiltonian_eigenvector_eq_zero_of_inner_starProjection_eq_zero` — §2 Step 2:
   under the `δ`-gap and energy-order hypotheses, an eigenvector `Ξ` with `⟪Φeff, P₀Ξ⟫ = 0` is
   zero.
4. **U2** `exists_isUniqueGroundStateOn_perturbedHamiltonian` — §2 Step 3: at a fixed small `λ`,
   `Ĥ(λ)` has a unique ground state on the whole space.
5. **U3** `exists_lam0_isUniqueGroundStateOn_perturbedHamiltonian` — §2 Step 4, **the PR's
   headline result**: `∃ λ₀ > 0, ∀ λ ∈ (0, λ₀), Ĥ(λ)` has a unique ground state on the whole
   space — the first conjunct of `tasaki_lemma_10_1_degenerate_perturbation`'s conclusion, under
   exactly its hypotheses.

**Provenance honesty (design report §1, R2).** Step 3's antisymmetric-combination argument is
*not* Tasaki's proof (which uses continuity + linear-independence counting over `D₀` branches);
it is this arc's replacement, reaching the same conclusion by a different, mathlib-only route.

Also machine-checks, reusing the two-site / `Fin 1` witnesses de-privatized in
`Tests/DegeneratePerturbationGroundEnergy.lean` (design report §7 pitfall P-g, so as not to
duplicate declarations):

* the **two-site non-vacuity witness** (design report §9 item 2) — `hEffGS` is fully discharged on
  the two-site data (`ker Ĥ₀ = ℂe₀` is one-dimensional, so uniqueness is free once membership is
  known), instantiating U3's hypothesis bundle non-vacuously;
* the **`hδgap`-is-load-bearing soundness guard** (design report §9 item 4, §11 item 5) — a
  4-dimensional witness (`Ĥ₀ = diag(0,0,1,1)`, `V̂` coupling `e₀↔e₂` and `e₁↔e₃` with equal
  weight) where `Ĥeff` restricted to `ker Ĥ₀` is the scalar matrix `−1·I₂`: genuinely degenerate,
  so `Ĥeff` has **no** unique ground state on `ker Ĥ₀` and `hEffGS` cannot be discharged here. This
  is machine-checked below (`counterexample_hEffGS_fails`); it is the necessity witness for U3's
  `hEffGS` hypothesis. **Deviation from the design report**: §9 item 4 proposed a 3-dimensional
  witness (`Ĥ₀ = diag(0,0,1)`, both kernel vectors coupled symmetrically to a single excited mode
  `e₂`). Hand computation shows that witness is a rank-one correction
  `Ĥeff|_{ker} = −(a,b)ᵀ(a,b)` with `a = b`, which has eigenvalues `{−2a², 0}` — **not** degenerate,
  so it does *not* in fact violate `hEffGS`. The 4-dimensional two-excited-mode witness used here
  is the smallest one the author could verify by hand to genuinely produce a degenerate `Ĥeff`.
  The harder direction — that `Ĥ(λ)`'s ground state is *also* non-unique at this witness, which is
  what shows `hEffGS` cannot be dropped from U3 itself — is *not* machine-checked here (design
  report §11 item 5 permits deferring the harder half to PR-6 if it exceeds ~40 lines): by the
  `0↔1, 2↔3` block-permutation symmetry of both `Ĥ₀` and `V̂`, `Ĥ(λ)` splits into two identical
  `2×2` blocks `!![0, λ; λ, 1]` on `{e₀,e₂}` and `{e₁,e₃}`, so every eigenvalue of `Ĥ(λ)` — in
  particular the ground eigenvalue `(1 − √(1+4λ²))/2` — occurs with multiplicity (at least) `2`,
  with eigenvectors supported on disjoint coordinate pairs and hence not scalar multiples of one
  another, for **every** `λ`, not just small `λ`. This hand computation is recorded here as the
  necessity argument for `hEffGS`; formalizing it is left to PR-6 or a follow-up.

**Not covered here (deliberately):**
* Any test of the explicit `λ₀` value `min 1 (min (g/(4v+1)) (δ/(c₃+C+1)))` — U3 packages `λ₀`
  existentially (design report §11 item 1), so no closed form is pinned.
* `IsReducedInverse.unique`'s disposition (design report §6, §11 item 4) — left to PR-6's
  tier-1 audit per the design report; not a PR-5 test concern.
-/

namespace LatticeSystem.Tests.DegeneratePerturbationUniqueness

open LatticeSystem.Math Matrix
open LatticeSystem.Tests.DegeneratePerturbationGroundEnergy
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Pins **N1**: every matrix has an operator-norm bound on `EuclideanSpace ℂ n`. -/
example (V : Matrix n n ℂ) :
    ∃ v : ℝ, 0 ≤ v ∧ ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖ :=
  exists_norm_toEuclideanLin_le V

/-- Pins **U0**, the quadratic-form engine (design report §2 Step 1, §3 row U0). For an exact
`(Φ,Γ)`-split `E`-eigenvector `Φ + Γ` of `Ĥ(λ) = Ĥ₀ + λV̂` with `Φ ∈ ker Ĥ₀`, `Γ ∈ (ker Ĥ₀)ᗮ`,
under the smallness hypotheses `0 < g`, `0 < λ`, `|E| ≤ λv`, `4λv ≤ g`, the effective-Hamiltonian
energy `λ²re⟪Φ,ĤeffΦ⟫` differs from `E‖Φ‖²` by at most `Cλ³‖Φ‖²`, `C = 4v³/g²`. -/
example {H0 V H0inv : Matrix n n ℂ} {g v lam E : ℝ} {Φ Γ : EuclideanSpace ℂ n}
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
      ≤ (4 * v ^ 3 / g ^ 2) * lam ^ 3 * ‖Φ‖ ^ 2 :=
  abs_inner_secondOrderEffectiveHamiltonian_sub_mul_norm_sq_le hH0 hV hInv hFirstOrder hgap hv
    hgpos hlam hEabs hsmall4 hΦ hΓ heig

/-- Pins **U1**, kernel-triviality (design report §2 Step 2, §3 row U1): under the smallness
hypotheses of U0 (which U1 invokes), the `δ`-gap of `Ĥeff` above its ground state `Φeff` inside
`ker Ĥ₀`, the energy-order bound `E ≤ λ²Eeff + c₃λ³`, and smallness `(c₃ + C)λ < δ`, any
`E`-eigenvector `Ξ` of `Ĥ(λ)` with `⟪Φeff, P₀Ξ⟫ = 0` is zero. -/
example {H0 V H0inv : Matrix n n ℂ} {g v lam E Eeff δ c₃ : ℝ} {Φeff Ξ : EuclideanSpace ℂ n}
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
    Ξ = 0 :=
  perturbedHamiltonian_eigenvector_eq_zero_of_inner_starProjection_eq_zero hH0 hV hInv
    hFirstOrder hgap hv hgpos hlam hEabs hsmall4 hδgap hEup hsmallδ hΞ hperp

/-- Pins **U2** (design report §2 Step 3, §3 row U2): at a fixed `λ` satisfying the smallness
hypotheses (`0 < λ`, `4λv ≤ g`, `(c₃+C)λ < δ`) and given the energy-order bound `hc₃` for
every ground eigenvalue on the whole space, `Ĥ(λ)` has a unique ground state on `⊤`. -/
example {H0 V H0inv : Matrix n n ℂ} {g v lam Eeff δ c₃ : ℝ} {Φeff : EuclideanSpace ℂ n}
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
      (perturbedHamiltonian H0 V lam) E φ :=
  exists_isUniqueGroundStateOn_perturbedHamiltonian hH0pos hV hInv hFirstOrder hgap hv hgpos
    hδgap hΦeff hnorm hlam hsmall4 hsmallδ hc₃

/-- Pins **U3** (design report §2 Step 4, §3 row U3), **the PR's headline result**: exactly the
first conjunct of `tasaki_lemma_10_1_degenerate_perturbation`'s conclusion, under exactly the
axiom's hypotheses (minus the redundant `hH0`/`[Nonempty n]`, design report §7 pitfall P-i). -/
example {H0 V H0inv : Matrix n n ℂ} {Eeff : ℝ} {Φeff : EuclideanSpace ℂ n}
    (hH0pos : H0.PosSemidef) (hV : V.IsHermitian) (hInv : IsReducedInverse H0 H0inv)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hEffGS : IsUniqueGroundStateOn (matrixKernel H0)
      (secondOrderEffectiveHamiltonian H0 V H0inv) Eeff Φeff) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam < lam0 →
      ∃ E φ, IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n))
        (perturbedHamiltonian H0 V lam) E φ :=
  exists_lam0_isUniqueGroundStateOn_perturbedHamiltonian hH0pos hV hInv hFirstOrder hEffGS

/-! ### Two-site non-vacuity witness (design report §9 item 2)

Reuses `twoSiteH0`, `twoSiteV`, `twoSiteGround` etc. de-privatized in
`Tests/DegeneratePerturbationGroundEnergy.lean`. `ker twoSiteH0 = ℂ ∙ twoSiteGround` is
one-dimensional, so the uniqueness clause of `IsUniqueGroundStateOn` on it is automatic once
membership is known (`Submodule.mem_span_singleton`), and only the ground-eigenvalue clause needs
any work — trivial here since there is only one eigenvalue on a line. -/

/-- `hEffGS` is fully discharged at the two-site witness: `Ĥeff = diag(−1,0)` restricted to the
one-dimensional `ker Ĥ₀ = ℂe₀` has `e₀` as its (trivially) unique normalized ground state. -/
theorem twoSite_hEffGS : IsUniqueGroundStateOn (matrixKernel twoSiteH0)
    (secondOrderEffectiveHamiltonian twoSiteH0 twoSiteV twoSiteH0) (-1) twoSiteGround := by
  refine ⟨twoSite_ground_mem, twoSite_norm_ground, twoSite_effective_eigenvector,
    ⟨⟨twoSiteGround, twoSite_ground_mem, ?_, twoSite_effective_eigenvector⟩, ?_⟩, ?_⟩
  · intro h
    have hnz := twoSite_norm_ground
    rw [h, norm_zero] at hnz
    exact zero_ne_one hnz
  · rintro μ ⟨ψ, hψK, hψne, hψeig⟩
    rw [twoSite_matrixKernel, Submodule.mem_span_singleton] at hψK
    obtain ⟨c, rfl⟩ := hψK
    have hc : c ≠ 0 := fun hc0 => hψne (hc0 ▸ zero_smul ℂ twoSiteGround)
    have hgne : twoSiteGround ≠ 0 := by
      have hnz := twoSite_norm_ground
      intro hz
      rw [hz, norm_zero] at hnz
      exact zero_ne_one hnz
    have hcv : c • twoSiteGround ≠ 0 := smul_ne_zero hc hgne
    have key : ((-1 : ℝ) : ℂ) • (c • twoSiteGround) = (μ : ℂ) • (c • twoSiteGround) := by
      rw [smul_comm, ← twoSite_effective_eigenvector, ← map_smul]
      exact hψeig
    have hμ : ((-1 : ℝ) : ℂ) = (μ : ℂ) := (smul_left_inj hcv).mp key
    have hμ' : (-1 : ℝ) = μ := by exact_mod_cast hμ
    exact le_of_eq hμ'
  · intro ψ hψK _
    rw [twoSite_matrixKernel, Submodule.mem_span_singleton] at hψK
    obtain ⟨c, rfl⟩ := hψK
    exact ⟨c, rfl⟩

/-- **Uses U3** at the two-site witness: `twoSite_hEffGS` instantiates U3's hypothesis bundle
non-vacuously, so U3 produces a genuine `λ₀ > 0` for the two-site model. -/
example : ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam < lam0 →
    ∃ E φ, IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin 2)))
      (perturbedHamiltonian twoSiteH0 twoSiteV lam) E φ :=
  exists_lam0_isUniqueGroundStateOn_perturbedHamiltonian twoSite_h0_posSemidef
    twoSite_v_isHermitian twoSite_isReducedInverse twoSite_firstOrder twoSite_hEffGS

/-! ### The `hδgap`-necessity witness (design report §9 item 4, §11 item 5)

`n = Fin 4`, `Ĥ₀ = diag(0,0,1,1)`, `V̂` couples `e₀ ↔ e₂` and `e₁ ↔ e₃` each with unit weight, all
other entries zero. `ker Ĥ₀ = span{e₀, e₁}` (two-dimensional), and
`Ĥeff = −P̂₀V̂Ĥ₀⁻¹V̂P̂₀ = −I₂` on it (`Ĥ₀⁻¹ = Ĥ₀`, its own reduced inverse, since `Ĥ₀` acts as the
identity on `(ker Ĥ₀)ᗮ = span{e₂,e₃}`). This is genuinely degenerate: `e₀` and `e₁` are both
`(−1)`-eigenvectors of `Ĥeff` in `ker Ĥ₀` that are not scalar multiples of one another, so `Ĥeff`
has **no** unique ground state on `ker Ĥ₀` — `hEffGS` fails at this witness, which is exactly what
shows the hypothesis is not vacuous/droppable. -/

/-- The witness unperturbed Hamiltonian `Ĥ₀ = diag(0,0,1,1)`. -/
noncomputable def gapWitnessH0 : Matrix (Fin 4) (Fin 4) ℂ := !![0,0,0,0; 0,0,0,0; 0,0,1,0; 0,0,0,1]

/-- The witness perturbation `V̂`, coupling `e₀ ↔ e₂` and `e₁ ↔ e₃` each with unit weight. -/
noncomputable def gapWitnessV : Matrix (Fin 4) (Fin 4) ℂ := !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]

/-- The kernel projection `P̂₀ = diag(1,1,0,0)` of the witness, identified with
`kernelProjectionMatrix gapWitnessH0` in `gapWitness_kernelProjectionMatrix`. -/
noncomputable def gapWitnessProj : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,0]

/-- `Ĥ₀ = diag(0,0,1,1)` is Hermitian. -/
theorem gapWitness_h0_isHermitian : gapWitnessH0.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gapWitnessH0, Matrix.conjTranspose_apply]

/-- `Ĥ₀ = diag(0,0,1,1)` is positive semidefinite. -/
theorem gapWitness_h0_posSemidef : gapWitnessH0.PosSemidef := by
  have hd : gapWitnessH0 = Matrix.diagonal ![0, 0, 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gapWitnessH0, Matrix.diagonal]
  rw [hd, Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> simp

/-- `V̂` is Hermitian. -/
theorem gapWitness_v_isHermitian : gapWitnessV.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gapWitnessV, Matrix.conjTranspose_apply]

/-- Coordinates of a matrix action on `EuclideanSpace ℂ (Fin 4)`. -/
theorem gapWitness_toEuclideanLin_apply (M : Matrix (Fin 4) (Fin 4) ℂ)
    (x : EuclideanSpace ℂ (Fin 4)) (i : Fin 4) :
    (Matrix.toEuclideanLin M x) i = ∑ j, M i j * x j := rfl

/-- `Ĥ₀` is idempotent: `Ĥ₀ = diag(0,0,1,1)` already *is* the orthogonal projection onto
`span{e₂,e₃}`. This is the only fact `gapWitness_kernelProjectionMatrix` needs — no coordinate
description of `ker Ĥ₀` is required. -/
theorem gapWitness_h0_idempotent : gapWitnessH0 * gapWitnessH0 = gapWitnessH0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gapWitnessH0, Matrix.mul_apply, Fin.sum_univ_four]

/-- **`P̂₀ = diag(1,1,0,0)`.** For an idempotent Hermitian `Ĥ₀`, `1 − Ĥ₀` is already the orthogonal
projection onto `ker Ĥ₀`: it lands in `ker Ĥ₀` (idempotency) and `x − (1−Ĥ₀)x = Ĥ₀x` is orthogonal
to `ker Ĥ₀` for any `x` (`toEuclideanLin_mem_matrixKernel_orthogonal`, PR-1). No coordinate
description of `ker Ĥ₀` is needed. -/
theorem gapWitness_kernelProjectionMatrix :
    kernelProjectionMatrix gapWitnessH0 = gapWitnessProj := by
  have hlit : (1 : Matrix (Fin 4) (Fin 4) ℂ) - gapWitnessH0 = gapWitnessProj := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gapWitnessH0, gapWitnessProj, Matrix.sub_apply]
  rw [← hlit]
  refine Matrix.toEuclideanLin.injective (LinearMap.ext fun x => ?_)
  rw [toEuclideanLin_kernelProjectionMatrix, toEuclideanLin_one_sub_apply]
  refine Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_
  · rw [matrixKernel, LinearMap.mem_ker, map_sub, ← toEuclideanLin_mul_apply,
      gapWitness_h0_idempotent, sub_self]
  · have heq : x - (x - Matrix.toEuclideanLin gapWitnessH0 x)
        = Matrix.toEuclideanLin gapWitnessH0 x := by abel
    rw [heq]
    exact toEuclideanLin_mem_matrixKernel_orthogonal gapWitness_h0_isHermitian x

/-- The first-order term vanishes: `V̂` swaps `{e₀,e₁}` with `{e₂,e₃}`, so `P̂₀V̂P̂₀` restricted to
the `{e₀,e₁}`-plane is `0`. -/
theorem gapWitness_firstOrder :
    kernelProjectionMatrix gapWitnessH0 * gapWitnessV * kernelProjectionMatrix gapWitnessH0
      = 0 := by
  rw [gapWitness_kernelProjectionMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gapWitnessProj, gapWitnessV, Matrix.mul_apply, Fin.sum_univ_four]

/-- `Ĥ₀` is its own reduced inverse: it acts as the identity on `(ker Ĥ₀)ᗮ = span{e₂,e₃}` and
annihilates `ker Ĥ₀`. -/
theorem gapWitness_isReducedInverse : IsReducedInverse gapWitnessH0 gapWitnessH0 := by
  refine ⟨?_, ?_, ?_, ?_, gapWitness_h0_isHermitian⟩ <;>
    rw [gapWitness_kernelProjectionMatrix] <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [gapWitnessH0, gapWitnessProj, Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_four]

/-- The second-order effective Hamiltonian of the witness is `Ĥeff = diag(−1,−1,0,0)`: genuinely
degenerate on `ker Ĥ₀ = span{e₀,e₁}`. -/
theorem gapWitness_secondOrderEffectiveHamiltonian :
    secondOrderEffectiveHamiltonian gapWitnessH0 gapWitnessV gapWitnessH0
      = !![-1,0,0,0; 0,-1,0,0; 0,0,0,0; 0,0,0,0] := by
  rw [secondOrderEffectiveHamiltonian, gapWitness_kernelProjectionMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gapWitnessH0, gapWitnessV, gapWitnessProj]

/-- `Ĥeff = −I₂` on `ker Ĥ₀`: `e₀` is a `(−1)`-eigenvector of the second-order effective
Hamiltonian. -/
theorem gapWitness_effective_eigenvector_e0 :
    Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian gapWitnessH0 gapWitnessV gapWitnessH0)
        (EuclideanSpace.single (0 : Fin 4) (1 : ℂ))
      = ((-1 : ℝ) : ℂ) • EuclideanSpace.single (0 : Fin 4) (1 : ℂ) := by
  rw [gapWitness_secondOrderEffectiveHamiltonian]
  refine PiLp.ext fun i => ?_
  rw [gapWitness_toEuclideanLin_apply]
  fin_cases i <;> simp [PiLp.single_apply]

/-- `Ĥeff = −I₂` on `ker Ĥ₀`: `e₁` is *also* a `(−1)`-eigenvector, not a scalar multiple of `e₀` —
the genuine degeneracy that makes `hEffGS` fail here. -/
theorem gapWitness_effective_eigenvector_e1 :
    Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian gapWitnessH0 gapWitnessV gapWitnessH0)
        (EuclideanSpace.single (1 : Fin 4) (1 : ℂ))
      = ((-1 : ℝ) : ℂ) • EuclideanSpace.single (1 : Fin 4) (1 : ℂ) := by
  rw [gapWitness_secondOrderEffectiveHamiltonian]
  refine PiLp.ext fun i => ?_
  rw [gapWitness_toEuclideanLin_apply]
  fin_cases i <;> simp [PiLp.single_apply]

/-- `e₁ ∈ ker Ĥ₀`: the last two coordinates of `Ĥ₀e₁` are `(e₁) 2 = 0` and `(e₁) 3 = 0`. -/
theorem gapWitness_e1_mem_ker :
    (EuclideanSpace.single (1 : Fin 4) (1 : ℂ) : EuclideanSpace ℂ (Fin 4))
      ∈ matrixKernel gapWitnessH0 := by
  rw [matrixKernel, LinearMap.mem_ker]
  refine PiLp.ext fun i => ?_
  rw [gapWitness_toEuclideanLin_apply]
  fin_cases i <;> simp [gapWitnessH0, PiLp.single_apply]

/-- **The soundness guard**: `Ĥeff` restricted to `ker Ĥ₀` is genuinely degenerate at this
witness — `e₀` and `e₁` are both `(−1)`-eigenvectors and are not scalar multiples of one another —
so no candidate `Φeff = e₀` makes the uniqueness clause of `IsUniqueGroundStateOn` hold: `e₁`
witnesses its failure directly (if every `E`-eigenvector in `ker Ĥ₀` were a multiple of `e₀`, `e₁`
would have to be, contradicting its zero `0`-th coordinate against `e₀`'s nonzero one). This is
the necessity witness for `hEffGS` that design report §9 item 4 / §11 item 5 asks for; the harder
direction (that `Ĥ(λ)`'s ground state is *also* non-unique here, for every `λ`, by the
`0↔1, 2↔3` block-permutation symmetry noted in the module doc) is deferred to PR-6. -/
theorem counterexample_hEffGS_fails :
    ¬ ∀ ψ ∈ matrixKernel gapWitnessH0,
        Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian gapWitnessH0 gapWitnessV
            gapWitnessH0) ψ = ((-1 : ℝ) : ℂ) • ψ →
        ∃ c : ℂ, ψ = c • EuclideanSpace.single (0 : Fin 4) (1 : ℂ) := by
  intro huniq
  obtain ⟨c, hc⟩ := huniq (EuclideanSpace.single (1 : Fin 4) (1 : ℂ)) gapWitness_e1_mem_ker
    gapWitness_effective_eigenvector_e1
  have h1 : (EuclideanSpace.single (1 : Fin 4) (1 : ℂ) : EuclideanSpace ℂ (Fin 4)) 1 = 1 := by
    simp
  rw [hc] at h1
  simp at h1

end LatticeSystem.Tests.DegeneratePerturbationUniqueness
