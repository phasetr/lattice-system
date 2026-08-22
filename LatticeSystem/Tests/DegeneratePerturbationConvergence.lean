import LatticeSystem.Tests.DegeneratePerturbationUniqueness

/-!
# Test coverage for convergence and the capstone discharge (Tasaki Lemma 10.1, PR-6)

Pins the API contract of the not-yet-written
`Math/MatrixAnalysis/DegeneratePerturbationConvergence.lean` (design report
`.self-local/reports/design-lemma101-pr6-capstone-discharge.md`, §3.2, §7). This file is written
**before** that production module exists, so every declaration below that references a `G`-named
lemma is expected to fail to build until PR-6's implementation lands (Red).

## Contents

* **T0** — the single most important test: an `example` reproducing the retired axiom
  `tasaki_lemma_10_1_degenerate_perturbation`'s statement *verbatim*, `[Nonempty n]` and
  `hH0 : H0.IsHermitian` included, so that the eventual `theorem` of the same name (with those two
  hypotheses dropped, design report R6) is checked against a strictly stronger reading. This test
  alone does **not** exercise the new production code — the axiom still exists when this file is
  written — it is the fidelity pin that the arc's final commit must continue to satisfy.
* **T3** — four `example`s pinning the exact statements of G1-G4 (design report §3.2 table),
  the regression guard against hypothesis drift.
* **T1** — non-vacuity of the capstone (G4) at the two-site witness (Tasaki's own suggested check,
  p. 346), reusing `twoSiteH0` / `twoSiteV` / `twoSite_hEffGS` etc. from
  `Tests/DegeneratePerturbationUniqueness.lean` and `Tests/DegeneratePerturbationGroundEnergy.lean`
  — no new witness declarations.
* **T2** — the `V = 0` / `ker Ĥ₀ = ⊤` corner at `n = Fin 1`, where the capstone's rate constant
  collapses to `K = 0`.

## Provenance honesty (design report §1)

Tasaki's own proof of the convergence conjunct is an unproved analytic assumption (Rellich–Kato
continuity of the low-lying eigenstates); the book supplies no argument and no rate. G1-G5 (and
hence this test file) formalize an independent, fully quantitative substitute
`‖Philam λ − Φeff‖² ≤ Kλ`, not "Tasaki's proof, formalized".
-/

namespace LatticeSystem.Tests.DegeneratePerturbationConvergence

open LatticeSystem.Math LatticeSystem.Tests.DegeneratePerturbationWitness
open LatticeSystem.Tests.DegeneratePerturbationGroundEnergy
open LatticeSystem.Tests.DegeneratePerturbationUniqueness
open Matrix Filter Topology
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### T0 — the statement-fidelity pin (design report §7 item 1, risk R1/R6)

Reproduces the retired axiom's statement **verbatim**, `[Nonempty n]` and `hH0` included. Since the
axiom text is slated for deletion, this is the only machine-checkable guard that the eventual
theorem is not a silently weakened statement (wrong filter, `IsUniqueGroundStateOn` on a smaller
subspace, reordered existentials). Both readings (with and without the two extra hypotheses) stay
machine-checked: this `example` only needs the axiom/theorem to accept `hH0`/`[Nonempty n]` as
*additional, ignorable* arguments, which a strictly more general statement always does. -/
example [Nonempty n] (H0 V H0inv : Matrix n n ℂ)
    (hH0 : H0.IsHermitian) (hH0pos : H0.PosSemidef) (hV : V.IsHermitian)
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
        Tendsto Philam (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 Φeff) :=
  tasaki_lemma_10_1_degenerate_perturbation H0 V H0inv hH0 hH0pos hV hInv hFirstOrder Eeff Φeff
    hEffGS

/-! ### T3 — pins for G1-G4 (design report §3.2 table, §7 item 4) -/

/-- Pins **G1** `norm_sub_starProjection_perturbedHamiltonian_le` (design report §3.2, §2 Step 4):
the `Γ`-half of an exact `(Φ,Γ)`-split eigenvector of `Ĥ(λ)` is `O(λ)`. -/
example {H0 V H0inv : Matrix n n ℂ} {g v lam E : ℝ} {Φ Γ : EuclideanSpace ℂ n}
    (hH0 : H0.IsHermitian) (hV : V.IsHermitian) (hInv : IsReducedInverse H0 H0inv)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hgpos : 0 < g) (hlam : 0 < lam) (hEabs : |E| ≤ lam * v) (hsmall4 : 4 * (lam * v) ≤ g)
    (hΦ : Φ ∈ matrixKernel H0) (hΓ : Γ ∈ (matrixKernel H0)ᗮ)
    (heig : Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (Φ + Γ) = (E : ℂ) • (Φ + Γ)) :
    ‖Γ‖ ≤ (2 * v / g) * lam * ‖Φ‖ :=
  norm_sub_starProjection_perturbedHamiltonian_le hH0 hV hInv hFirstOrder hgap hv hgpos hlam hEabs
    hsmall4 hΦ hΓ heig

/-- Pins **G2** `mul_norm_sub_smul_sq_le` (design report §3.2, §2 Steps 2-3): the projection
`Φ` of an exact `(Φ,Γ)`-split eigenvector onto `ker Ĥ₀`, measured against the `Φeff`-axis, is
`O(√λ)` on the `Ĥeff`-quadratic form scale. -/
example {H0 V H0inv : Matrix n n ℂ} {g v lam E Eeff δ c₃ : ℝ} {Φeff Φ Γ : EuclideanSpace ℂ n}
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
    (hΦ : Φ ∈ matrixKernel H0) (hΓ : Γ ∈ (matrixKernel H0)ᗮ) (hΦnorm : ‖Φ‖ ≤ 1)
    (heig : Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (Φ + Γ) = (E : ℂ) • (Φ + Γ)) :
    δ * ‖Φ - (inner ℂ Φeff Φ : ℂ) • Φeff‖ ^ 2 ≤ (c₃ + 4 * v ^ 3 / g ^ 2) * lam :=
  mul_norm_sub_smul_sq_le hH0 hV hInv hFirstOrder hgap hv hgpos hlam hEabs hsmall4 hδgap hEup hΦ hΓ
    hΦnorm heig

/-- Pins **G3** `exists_norm_smul_sub_sq_le_of_isUniqueGroundStateOn` (design report §3.2, §2
Steps 1 and 5): given a unique ground state `φ` of `Ĥ(λ)` on the whole space, some unit-modulus
phase `c` brings `φ` within `O(√λ)` of `Φeff`. -/
example {H0 V H0inv : Matrix n n ℂ} {g v lam Eeff δ c₃ : ℝ} {Φeff φ : EuclideanSpace ℂ n} {E : ℝ}
    (hH0pos : H0.PosSemidef) (hV : V.IsHermitian) (hInv : IsReducedInverse H0 H0inv)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hgpos : 0 < g) (hlam : 0 < lam) (hsmall4 : 4 * (lam * v) ≤ g)
    (hδgap : ∀ w ∈ matrixKernel H0 ⊓ (Submodule.span ℂ {Φeff})ᗮ,
      (Eeff + δ) * ‖w‖ ^ 2
        ≤ RCLike.re (inner ℂ w (Matrix.toEuclideanLin
            (secondOrderEffectiveHamiltonian H0 V H0inv) w)))
    (hΦeff : Φeff ∈ matrixKernel H0) (hnorm : ‖Φeff‖ = 1)
    (hsmallδ : (c₃ + 4 * v ^ 3 / g ^ 2) * lam < δ)
    (hGS : IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n))
      (perturbedHamiltonian H0 V lam) E φ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      ‖c • φ - Φeff‖ ^ 2 ≤ (2 * ((c₃ + 4 * v ^ 3 / g ^ 2) / δ + 4 * v ^ 2 / g ^ 2)) * lam :=
  exists_norm_smul_sub_sq_le_of_isUniqueGroundStateOn hH0pos hV hInv hFirstOrder hgap hv hgpos hlam
    hsmall4 hδgap hΦeff hnorm hsmallδ hGS

/-- Pins **G4** `exists_lam0_isUniqueGroundStateOn_norm_sub_sq_le` (design report §3.2, §2 Step 6,
consuming U3): the packaged existence of a threshold `λ₀` and a uniform rate constant `K`, under
exactly the retired axiom's hypotheses minus `[Nonempty n]`/`hH0` (design report R6). This is the
declaration that G5 (the eventual capstone) wraps with `Skolem` and `Tendsto`. -/
example {H0 V H0inv : Matrix n n ℂ} {Eeff : ℝ} {Φeff : EuclideanSpace ℂ n}
    (hH0pos : H0.PosSemidef) (hV : V.IsHermitian) (hInv : IsReducedInverse H0 H0inv)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hEffGS : IsUniqueGroundStateOn (matrixKernel H0)
      (secondOrderEffectiveHamiltonian H0 V H0inv) Eeff Φeff) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ lam : ℝ, 0 < lam → lam < lam0 →
      ∃ E φ, IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n))
        (perturbedHamiltonian H0 V lam) E φ ∧ ‖φ - Φeff‖ ^ 2 ≤ K * lam :=
  exists_lam0_isUniqueGroundStateOn_norm_sub_sq_le hH0pos hV hInv hFirstOrder hEffGS

/-! ### T1 — two-site non-vacuity (design report §7 item 2, Tasaki's own suggested check, p. 346)

Reuses `twoSiteH0`, `twoSiteV`, `twoSiteGround`, `twoSite_hEffGS` etc. from
`Tests/DegeneratePerturbationUniqueness.lean` and `Tests/DegeneratePerturbationGroundEnergy.lean`.
No new witness declarations are added here. As the design report records honestly: `Philam` is
`Classical.choose`n and opaque, so this pins the *statement* at the witness, not a concrete
converging family. -/

/-- **Uses G4** at the two-site witness: `twoSite_hEffGS` instantiates G4's hypothesis bundle
non-vacuously, so G4 produces a genuine `λ₀ > 0` and rate constant `K` for the two-site model. -/
example : ∃ lam0 : ℝ, 0 < lam0 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ lam : ℝ, 0 < lam → lam < lam0 →
    ∃ E φ, IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin 2)))
      (perturbedHamiltonian twoSiteH0 twoSiteV lam) E φ ∧ ‖φ - twoSiteGround‖ ^ 2 ≤ K * lam :=
  exists_lam0_isUniqueGroundStateOn_norm_sub_sq_le twoSite_h0_posSemidef twoSite_v_isHermitian
    twoSite_isReducedInverse twoSite_firstOrder twoSite_hEffGS

/-! ### T2 — the `V = 0` / `ker Ĥ₀ = ⊤` corner (design report §2 "Sanity checks", §7 item 3)

At `n = Fin 1`, `H0 = V = H0inv = 0`: `ker Ĥ₀ = ⊤` (`fin1_matrixKernel_zero_eq_top`), the
first-order term and `Ĥeff` both vanish, and the unique unit vector up to phase is `e₀`, so `Ĥeff`
trivially has `e₀` as its unique ground state at `Eeff = 0`. The capstone still applies, with rate
constant `K = 0` (design report §2: `v = c₃ = C = 0` forces `w = Γ = 0`, `|a| = 1`). -/

/-- The unique (up to phase) unit vector of the one-dimensional `EuclideanSpace ℂ (Fin 1)`. -/
private noncomputable def fin1Ground : EuclideanSpace ℂ (Fin 1) := EuclideanSpace.single 0 1

private theorem fin1_norm_ground : ‖fin1Ground‖ = 1 := by
  rw [fin1Ground, EuclideanSpace.single, PiLp.norm_single]
  simp

/-- Every vector of `EuclideanSpace ℂ (Fin 1)` is a scalar multiple of `fin1Ground`: the space is
one-dimensional. -/
private theorem fin1_eq_smul_ground (ψ : EuclideanSpace ℂ (Fin 1)) :
    ψ = (ψ 0) • fin1Ground := by
  refine PiLp.ext fun i => ?_
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp [fin1Ground, EuclideanSpace.single, PiLp.smul_apply]

private theorem fin1_isReducedInverse_zero_zero :
    IsReducedInverse (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 := by
  refine ⟨?_, ?_, ?_, ?_, Matrix.isHermitian_zero⟩ <;>
    simp [fin1_kernelProjectionMatrix_zero_eq_one]

/-- `hEffGS` at the `Fin 1`, `H0 = V = H0inv = 0` corner: `Ĥeff = 0` restricted to
`ker (0 : Matrix (Fin 1) (Fin 1) ℂ) = ⊤` has `fin1Ground` as its (trivially) unique normalized
ground state at `Eeff = 0`. -/
theorem fin1_hEffGS : IsUniqueGroundStateOn
    (matrixKernel (0 : Matrix (Fin 1) (Fin 1) ℂ))
    (secondOrderEffectiveHamiltonian (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 0) 0 fin1Ground := by
  have hEff0 : Matrix.toEuclideanLin
      (secondOrderEffectiveHamiltonian (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 0)
      = 0 := by
    simp [secondOrderEffectiveHamiltonian]
  have hmemTop : ∀ ψ : EuclideanSpace ℂ (Fin 1), ψ ∈ matrixKernel (0 : Matrix (Fin 1) (Fin 1) ℂ) :=
    fun ψ => fin1_matrixKernel_zero_eq_top ▸ Submodule.mem_top
  have hgroundne : fin1Ground ≠ 0 := by
    intro h
    have hnz := fin1_norm_ground
    rw [h, norm_zero] at hnz
    exact zero_ne_one hnz
  refine ⟨hmemTop fin1Ground, fin1_norm_ground, ?_,
    ⟨⟨fin1Ground, hmemTop fin1Ground, hgroundne, ?_⟩, ?_⟩, ?_⟩
  · rw [hEff0]; simp
  · rw [hEff0]; simp
  · rintro μ ⟨ψ, -, hψne, hψeig⟩
    rw [hEff0] at hψeig
    simp only [LinearMap.zero_apply] at hψeig
    rcases eq_or_ne μ 0 with rfl | hμne
    · exact le_refl 0
    · rcases smul_eq_zero.mp hψeig.symm with hμ0 | hψ0
      · exact absurd (Complex.ofReal_eq_zero.mp hμ0) hμne
      · exact absurd hψ0 hψne
  · intro ψ _ _
    exact ⟨ψ 0, fin1_eq_smul_ground ψ⟩

/-- **Uses G4** at the `Fin 1` degenerate corner: the capstone still applies when the entire
system is trivial (`Ĥ₀ = V̂ = 0`), with rate constant `K = 0` available in principle (design
report §2 sanity check). -/
example : ∃ lam0 : ℝ, 0 < lam0 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ lam : ℝ, 0 < lam → lam < lam0 →
    ∃ E φ, IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin 1)))
      (perturbedHamiltonian (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 lam) E φ ∧
      ‖φ - fin1Ground‖ ^ 2 ≤ K * lam :=
  exists_lam0_isUniqueGroundStateOn_norm_sub_sq_le Matrix.posSemidef_zero Matrix.isHermitian_zero
    fin1_isReducedInverse_zero_zero (by simp) fin1_hEffGS

end LatticeSystem.Tests.DegeneratePerturbationConvergence
