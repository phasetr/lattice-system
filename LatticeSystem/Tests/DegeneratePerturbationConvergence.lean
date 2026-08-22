import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbationConvergence
import LatticeSystem.Tests.DegeneratePerturbationUniqueness

/-!
# Test coverage for convergence and the capstone discharge (Tasaki Lemma 10.1, PR-6)

Pins the API contract of `Math/MatrixAnalysis/DegeneratePerturbationConvergence.lean`: the
statement of Lemma 10.1 itself, the exact hypothesis lists of the four estimates that build it,
and its non-vacuity at two explicit witnesses.

## Contents

* **T0** — the statement-fidelity pin: an `example` reproducing the capstone's statement
  *verbatim*, so that no later refactor can silently weaken it (wrong filter,
  `IsUniqueGroundStateOn` on a smaller subspace, reordered existentials).
* **T3** — four `example`s pinning the exact statements of G1-G4, the regression guard against
  hypothesis drift.
* **T1** — non-vacuity of the capstone (G4) at the two-site witness (Tasaki's own suggested check,
  p. 346), reusing `twoSiteH0` / `twoSiteV` / `twoSite_hEffGS` etc. from
  `Tests/DegeneratePerturbationUniqueness.lean` and `Tests/DegeneratePerturbationGroundEnergy.lean`
  — no new witness declarations.
* **T2** — the `V = 0` / `ker Ĥ₀ = ⊤` corner at `n = Fin 1`, where the capstone's rate constant
  collapses to `K = 0`.

## Provenance honesty

Tasaki's own proof of the convergence conjunct rests on an unproved analytic assumption
(Rellich–Kato continuity of the low-lying eigenstates); the book supplies no argument and no rate.
The production module (and hence this test file) formalizes an independent, fully quantitative
substitute `‖Philam λ − Φeff‖² ≤ Kλ`, not "Tasaki's proof, formalized".
-/

namespace LatticeSystem.Tests.DegeneratePerturbationConvergence

open LatticeSystem.Math LatticeSystem.Tests.DegeneratePerturbationWitness
open LatticeSystem.Tests.DegeneratePerturbationGroundEnergy
open LatticeSystem.Tests.DegeneratePerturbationUniqueness
open Matrix Filter Topology
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### T0 — the statement-fidelity pin

Reproduces the capstone's statement **verbatim**, `[Nonempty n]` and `hH0` included. This is the
machine-checkable guard that the theorem states exactly what Lemma 10.1 claims: `λ₀ > 0`, unique
ground states on the **whole** space throughout `(0, λ₀)`, and convergence along `𝓝[>] 0`. -/
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

/-! ### T3 — pins for G1-G4 -/

/-- Pins **G1** `norm_sub_starProjection_perturbedHamiltonian_le`: the `Γ`-half of an exact
`(Φ,Γ)`-split eigenvector of `Ĥ(λ)` is `O(λ)`. -/
example {H0 V : Matrix n n ℂ} {g v lam E : ℝ} {Φ Γ : EuclideanSpace ℂ n}
    (hH0 : H0.IsHermitian) (hV : V.IsHermitian)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hgpos : 0 < g) (hlam : 0 < lam) (hEabs : |E| ≤ lam * v) (hsmall4 : 4 * (lam * v) ≤ g)
    (hΦ : Φ ∈ matrixKernel H0) (hΓ : Γ ∈ (matrixKernel H0)ᗮ)
    (heig : Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (Φ + Γ) = (E : ℂ) • (Φ + Γ)) :
    ‖Γ‖ ≤ (2 * v / g) * lam * ‖Φ‖ :=
  norm_sub_starProjection_perturbedHamiltonian_le hH0 hV hFirstOrder hgap hv hgpos hlam hEabs
    hsmall4 hΦ hΓ heig

/-- Pins **G2** `mul_norm_sub_smul_sq_le`: the projection `Φ` of an exact `(Φ,Γ)`-split
eigenvector onto `ker Ĥ₀`, measured against the `Φeff`-axis, is `O(√λ)` on the `Ĥeff`-quadratic
form scale. The three `Φeff`-hypotheses (membership in `ker Ĥ₀`, normalization, and the effective
eigenvalue equation) are load-bearing: without them `w` need not lie in the subspace where the
`δ`-gap applies, and the `Eeff` contribution does not cancel. -/
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
    (hΦeff : Φeff ∈ matrixKernel H0) (hnorm : ‖Φeff‖ = 1)
    (hEeff : Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φeff
      = (Eeff : ℂ) • Φeff)
    (hΦ : Φ ∈ matrixKernel H0) (hΓ : Γ ∈ (matrixKernel H0)ᗮ)
    (heig : Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (Φ + Γ) = (E : ℂ) • (Φ + Γ)) :
    δ * ‖Φ - (inner ℂ Φeff Φ : ℂ) • Φeff‖ ^ 2
      ≤ (c₃ + 4 * v ^ 3 / g ^ 2) * lam * ‖Φ‖ ^ 2 :=
  mul_norm_sub_smul_sq_le hH0 hV hInv hFirstOrder hgap hv hgpos hlam hEabs hsmall4 hδgap hEup
    hΦeff hnorm hEeff hΦ hΓ heig

/-- Pins **G3** `exists_norm_smul_sub_sq_le_of_isUniqueGroundStateOn`: given a unique ground state
`φ` of `Ĥ(λ)` on the whole space, some unit-modulus phase `c` brings `φ` within `O(√λ)` of
`Φeff`. -/
example {H0 V H0inv : Matrix n n ℂ} {g v lam Eeff δ c₃ : ℝ} {Φeff φ : EuclideanSpace ℂ n} {E : ℝ}
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
      ‖c • φ - Φeff‖ ^ 2 ≤ (2 * ((c₃ + 4 * v ^ 3 / g ^ 2) / δ + 4 * v ^ 2 / g ^ 2)) * lam :=
  exists_norm_smul_sub_sq_le_of_isUniqueGroundStateOn hH0pos hV hInv hFirstOrder hgap hv hgpos hlam
    hlam1 hsmall4 hδgap hδpos hΦeff hnorm hEeff hEup hsmallδ hGS

/-- Pins **G4** `exists_lam0_isUniqueGroundStateOn_norm_sub_sq_le`: the packaged existence of a
threshold `λ₀` and a uniform rate constant `K`, under the capstone's hypotheses minus
`[Nonempty n]`/`hH0`. This is the declaration that the capstone wraps with choice and `Tendsto`. -/
example {H0 V H0inv : Matrix n n ℂ} {Eeff : ℝ} {Φeff : EuclideanSpace ℂ n}
    (hH0pos : H0.PosSemidef) (hV : V.IsHermitian) (hInv : IsReducedInverse H0 H0inv)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hEffGS : IsUniqueGroundStateOn (matrixKernel H0)
      (secondOrderEffectiveHamiltonian H0 V H0inv) Eeff Φeff) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ lam : ℝ, 0 < lam → lam < lam0 →
      ∃ E φ, IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n))
        (perturbedHamiltonian H0 V lam) E φ ∧ ‖φ - Φeff‖ ^ 2 ≤ K * lam :=
  exists_lam0_isUniqueGroundStateOn_norm_sub_sq_le hH0pos hV hInv hFirstOrder hEffGS

/-! ### T1 — two-site non-vacuity (Tasaki's own suggested check, p. 346)

Reuses `twoSiteH0`, `twoSiteV`, `twoSiteGround`, `twoSite_hEffGS` etc. from
`Tests/DegeneratePerturbationUniqueness.lean` and `Tests/DegeneratePerturbationGroundEnergy.lean`.
No new witness declarations are added here. The ground state produced by the capstone is chosen,
hence opaque, so this pins the *statement* at the witness, not a concrete converging family. -/

/-- **Uses G4** at the two-site witness: `twoSite_hEffGS` instantiates G4's hypothesis bundle
non-vacuously, so G4 produces a genuine `λ₀ > 0` and rate constant `K` for the two-site model. -/
example : ∃ lam0 : ℝ, 0 < lam0 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ lam : ℝ, 0 < lam → lam < lam0 →
    ∃ E φ, IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin 2)))
      (perturbedHamiltonian twoSiteH0 twoSiteV lam) E φ ∧ ‖φ - twoSiteGround‖ ^ 2 ≤ K * lam :=
  exists_lam0_isUniqueGroundStateOn_norm_sub_sq_le twoSite_h0_posSemidef twoSite_v_isHermitian
    twoSite_isReducedInverse twoSite_firstOrder twoSite_hEffGS

/-! ### T2 — the `V = 0` / `ker Ĥ₀ = ⊤` corner

At `n = Fin 1`, `H0 = V = H0inv = 0`: `ker Ĥ₀ = ⊤` (`fin1_matrixKernel_zero_eq_top`), the
first-order term and `Ĥeff` both vanish, and the unique unit vector up to phase is `e₀`, so `Ĥeff`
trivially has `e₀` as its unique ground state at `Eeff = 0`. The capstone still applies, with rate
constant `K = 0`: `v = c₃ = 0` forces `w = Γ = 0` and `|a| = 1`. -/

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
system is trivial (`Ĥ₀ = V̂ = 0`), with rate constant `K = 0` available in principle. -/
example : ∃ lam0 : ℝ, 0 < lam0 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ lam : ℝ, 0 < lam → lam < lam0 →
    ∃ E φ, IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin 1)))
      (perturbedHamiltonian (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 lam) E φ ∧
      ‖φ - fin1Ground‖ ^ 2 ≤ K * lam :=
  exists_lam0_isUniqueGroundStateOn_norm_sub_sq_le Matrix.PosSemidef.zero Matrix.isHermitian_zero
    fin1_isReducedInverse_zero_zero (by simp) fin1_hEffGS

end LatticeSystem.Tests.DegeneratePerturbationConvergence
