import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbationGroundEnergy

/-!
# Test coverage for the trial-state variational bound (Tasaki Lemma 10.1, PR-4)

Pins the API contract of the declarations that
`Math/MatrixAnalysis/DegeneratePerturbationGroundEnergy.lean` is designed to add on top of
`DegeneratePerturbation.lean` (PR-1 only; see
`.self-local/reports/design-lemma101-pr4-variational-bound.md` §4):

1. `IsGroundEigenvalueOn.mul_norm_sq_le` (B1) — the variational principle in the arc's own
   vocabulary: on an invariant subspace, the ground eigenvalue lower-bounds the energy quadratic
   form.
2. `exists_isGroundEigenvalueOn` (B2) — existence of a ground eigenvalue on any nonzero
   Hermitian-invariant subspace.
3. `perturbedHamiltonian_isHermitian` (B3) — `Ĥ(λ) = Ĥ₀ + λV̂` is Hermitian whenever `Ĥ₀` and `V̂`
   are.
4. `toEuclideanLin_perturbedHamiltonian_trialVector` (L1) — the exact residual
   `Ĥ(λ)(Φ − λĤ₀⁻¹V̂Φ) = −λ²V̂(Ĥ₀⁻¹V̂Φ)`, i.e. eq. (10.1.18) made exact.
5. `inner_trialVector_perturbedHamiltonian` (L2) — the exact energy identity
   `⟪Ψ, Ĥ(λ)Ψ⟫ = λ²⟪Φ, ĤeffΦ⟫ + λ³⟪u, V̂u⟫` for the trial vector `Ψ = Φ − λu`, `u = Ĥ₀⁻¹V̂Φ`.
6. `exists_const_isGroundEigenvalue_perturbedHamiltonian_le` (L4) — **the PR's headline
   result**: the variational upper bound `Elam ≤ λ²Eeff + c₃λ³` for `0 < λ ≤ 1`.
7. `abs_isGroundEigenvalue_perturbedHamiltonian_le` (L5) — the two-sided energy bound
   `|Elam| ≤ λv`, fused, drop-in for PR-3's `perturbedHamiltonian_eigenvector_iff` consumer
   (C6's `hEle` hypothesis).

**Provenance honesty (design report §1, risk R6).** Tasaki's proof of Lemma 10.1 (pp. 346–347)
contains *no* variational estimate: its analytic input is the unproved continuity/Rellich–Kato
sentence "there are exactly `D₀` … eigenstates … depend[ing] continuously on `λ`". None of the
seven declarations pinned below is a transcription of that argument. They are this arc's
**elementary replacement** for it — built from the trial vector of eq. (10.1.18) and the plain
Rayleigh–Ritz variational principle (B1/B2) — and every test below must be read as testing *that
replacement*, not as testing "Tasaki's proof, formalized". The capstone
`tasaki_lemma_10_1_degenerate_perturbation` itself stays a documented axiom until PR-6.

Also machine-checks the **`V = 0` corner** (design report §8, item 2): at `H0 = V = H0inv = 0`
(`n = Fin 1`), `matrixKernel 0 = ⊤`, `hFirstOrder` holds trivially, and L1's residual identity
degenerates to `0 = 0`. This exercises the degenerate `ker Ĥ₀ = ⊤` branch that the two-site
non-vacuity witness (deferred to PR-6, design report §8 item 4 / §10.4) does not cover.

**Not covered here (deliberately, per the design report):**
* The genuine two-site (`n = Fin 2`) non-vacuity witness for the full hypothesis bundle of L4/L5
  — deferred to PR-6 (design report §8, "Deliberately deferred to PR-6").
* Any counterexample family showing `lam ≤ 1` is load-bearing in L4 — the design report classifies
  it as a convenience, not a soundness guard (§8 item 3), so none is supplied; the pin for L4
  already quantifies over every `0 < lam ≤ 1`, including `lam = 1`.
-/

namespace LatticeSystem.Tests.DegeneratePerturbationGroundEnergy

open LatticeSystem.Math Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Pins **B1**: the variational principle. If `H` is Hermitian and preserves `K`, then the
ground eigenvalue `E` of `H` on `K` lower-bounds the energy quadratic form `re ⟪w, Hw⟫` on `K`. -/
example {K : Submodule ℂ (EuclideanSpace ℂ n)} {H : Matrix n n ℂ} {E : ℝ}
    (hH : H.IsHermitian) (hK : ∀ v ∈ K, Matrix.toEuclideanLin H v ∈ K)
    (hE : IsGroundEigenvalueOn K H E) :
    ∀ w ∈ K, E * ‖w‖ ^ 2 ≤ RCLike.re (inner ℂ w (Matrix.toEuclideanLin H w)) :=
  IsGroundEigenvalueOn.mul_norm_sq_le hH hK hE

/-- Pins **B2**: a nonzero Hermitian-invariant subspace has a ground eigenvalue. -/
example {K : Submodule ℂ (EuclideanSpace ℂ n)} {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (hK : ∀ v ∈ K, Matrix.toEuclideanLin H v ∈ K) (hKbot : K ≠ ⊥) :
    ∃ E : ℝ, IsGroundEigenvalueOn K H E :=
  exists_isGroundEigenvalueOn hH hK hKbot

/-- Pins **B3**: `Ĥ(λ) = Ĥ₀ + λV̂` is Hermitian whenever `Ĥ₀` and `V̂` are. -/
example {H0 V : Matrix n n ℂ} {lam : ℝ} (hH0 : H0.IsHermitian) (hV : V.IsHermitian) :
    (perturbedHamiltonian H0 V lam).IsHermitian :=
  perturbedHamiltonian_isHermitian hH0 hV

/-- Pins **L1**: the exact residual of the trial vector `Ψ = Φ − λĤ₀⁻¹V̂Φ` (eq. (10.1.18) made
exact), for `Φ ∈ ker Ĥ₀` with vanishing first-order term and `H0inv` a reduced inverse of `Ĥ₀`. -/
example {H0 V H0inv : Matrix n n ℂ} {lam : ℝ}
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hInv : IsReducedInverse H0 H0inv)
    {Φ : EuclideanSpace ℂ n} (hΦ : Φ ∈ matrixKernel H0) :
    Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam)
        (Φ - (lam : ℂ) • Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φ))
      = -((lam : ℂ) ^ 2) • Matrix.toEuclideanLin V
          (Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φ)) :=
  toEuclideanLin_perturbedHamiltonian_trialVector hΦ hFirstOrder hInv

/-- Pins **L2**: the exact energy identity `⟪Ψ, Ĥ(λ)Ψ⟫ = λ²⟪Φ, ĤeffΦ⟫ + λ³⟪u, V̂u⟫` for the trial
vector `Ψ = Φ − λu`, `u = Ĥ₀⁻¹V̂Φ`, with no eigenvalue/normalisation hypothesis on `Φ`. -/
example {H0 V H0inv : Matrix n n ℂ} {lam : ℝ}
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hInv : IsReducedInverse H0 H0inv)
    {Φ : EuclideanSpace ℂ n} (hΦ : Φ ∈ matrixKernel H0) :
    (inner ℂ
        (Φ - (lam : ℂ) • Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φ))
        (Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam)
          (Φ - (lam : ℂ) • Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φ))) : ℂ)
      = (lam : ℂ) ^ 2
          * (inner ℂ Φ
              (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φ) : ℂ)
        + (lam : ℂ) ^ 3
          * (inner ℂ (Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φ))
              (Matrix.toEuclideanLin V (Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φ)))
              : ℂ) :=
  inner_trialVector_perturbedHamiltonian hΦ hFirstOrder hInv

/-- Pins **L4**, the PR's headline result: the trial-state variational upper bound
`Elam ≤ λ²Eeff + c₃λ³` for every `0 < λ ≤ 1`, given a unique-normalised effective ground state
`Φeff` of `Ĥeff` with ground energy `Eeff`. This is the arc's elementary replacement for Tasaki's
unproved continuity input (see the module doc, provenance honesty). -/
example {H0 V H0inv : Matrix n n ℂ} {Eeff : ℝ} {Φeff : EuclideanSpace ℂ n}
    (hH0 : H0.IsHermitian) (hV : V.IsHermitian) (hInv : IsReducedInverse H0 H0inv)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hΦeff : Φeff ∈ matrixKernel H0) (hnorm : ‖Φeff‖ = 1)
    (hEeff : Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φeff
      = (Eeff : ℂ) • Φeff) :
    ∃ c₃ : ℝ, 0 ≤ c₃ ∧ ∀ lam E : ℝ, 0 < lam → lam ≤ 1 →
      IsGroundEigenvalueOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n))
        (perturbedHamiltonian H0 V lam) E →
      E ≤ lam ^ 2 * Eeff + c₃ * lam ^ 3 :=
  exists_const_isGroundEigenvalue_perturbedHamiltonian_le hH0 hV hInv hFirstOrder hΦeff hnorm hEeff

/-- **L4 instantiated at `λ = 1`** (design report §8 item 3: `lam ≤ 1` is a convenience, not a
soundness guard that needs a dedicated counterexample family). This is a direct corollary of the
pin above, kept as a separate `example` only to record that the bound is genuinely usable at the
right endpoint `λ = 1`, not merely in some open neighbourhood of `0`. -/
example {H0 V H0inv : Matrix n n ℂ} {Eeff E : ℝ} {Φeff : EuclideanSpace ℂ n}
    (hH0 : H0.IsHermitian) (hV : V.IsHermitian) (hInv : IsReducedInverse H0 H0inv)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hΦeff : Φeff ∈ matrixKernel H0) (hnorm : ‖Φeff‖ = 1)
    (hEeff : Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φeff
      = (Eeff : ℂ) • Φeff)
    (hE : IsGroundEigenvalueOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n))
      (perturbedHamiltonian H0 V 1) E) :
    ∃ c₃ : ℝ, 0 ≤ c₃ ∧ E ≤ Eeff + c₃ := by
  obtain ⟨c₃, hc₃nonneg, hbound⟩ :=
    exists_const_isGroundEigenvalue_perturbedHamiltonian_le hH0 hV hInv hFirstOrder hΦeff hnorm
      hEeff
  refine ⟨c₃, hc₃nonneg, ?_⟩
  have := hbound 1 E one_pos le_rfl hE
  simpa using this

/-- Pins **L5**: the fused two-sided energy bound `|Elam| ≤ λv`, drop-in for PR-3's Feshbach
consumer (`perturbedHamiltonian_eigenvector_iff`'s C6-style `hEle` hypothesis). -/
example {H0 V : Matrix n n ℂ} {v lam E : ℝ} {Φeff : EuclideanSpace ℂ n}
    (hH0pos : H0.PosSemidef) (hV : V.IsHermitian)
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hΦeff : Φeff ∈ matrixKernel H0) (hnorm : ‖Φeff‖ = 1) (hlam : 0 < lam)
    (hE : IsGroundEigenvalueOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n))
      (perturbedHamiltonian H0 V lam) E) :
    |E| ≤ lam * v :=
  abs_isGroundEigenvalue_perturbedHamiltonian_le hH0pos hV hv hFirstOrder hΦeff hnorm hlam hE

/-- The kernel of the zero matrix is the whole space (shared scaffolding for the `V = 0` corner
below, mirroring `DegeneratePerturbationFeshbach`'s `fin1_matrixKernel_zero_eq_top`). -/
private theorem fin1_matrixKernel_zero_eq_top :
    matrixKernel (0 : Matrix (Fin 1) (Fin 1) ℂ) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  simp [matrixKernel]

/-- The zero matrix is trivially a reduced inverse of itself: `ker 0 = ⊤`, so the kernel
projection is the identity and every field of `IsReducedInverse` collapses to `0 = 0`. -/
private theorem fin1_isReducedInverse_zero_zero :
    IsReducedInverse (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 := by
  have hP : kernelProjectionMatrix (0 : Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
    refine Matrix.toEuclideanLin.injective ?_
    rw [toEuclideanLin_kernelProjectionMatrix, fin1_matrixKernel_zero_eq_top,
      Submodule.starProjection_top]
    ext x
    simp
  refine ⟨?_, ?_, ?_, ?_, Matrix.isHermitian_zero⟩ <;> simp [hP]

/-- **`V = 0` corner** (design report §8 item 2): at `H0 = V = H0inv = 0` on `n = Fin 1`,
`matrixKernel 0 = ⊤`, `hFirstOrder` holds trivially, and L1's exact residual identity
degenerates to `Ĥ(λ)Φ = 0 = −λ²•0`. Exercises the degenerate `ker Ĥ₀ = ⊤` branch that the
two-site non-vacuity witness (deferred to PR-6) does not cover. -/
example {lam : ℝ} {Φ : EuclideanSpace ℂ (Fin 1)}
    (hΦ : Φ ∈ matrixKernel (0 : Matrix (Fin 1) (Fin 1) ℂ)) :
    Matrix.toEuclideanLin (perturbedHamiltonian (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 lam)
        (Φ - (lam : ℂ) • Matrix.toEuclideanLin (0 : Matrix (Fin 1) (Fin 1) ℂ)
          (Matrix.toEuclideanLin (0 : Matrix (Fin 1) (Fin 1) ℂ) Φ))
      = -((lam : ℂ) ^ 2) • Matrix.toEuclideanLin (0 : Matrix (Fin 1) (Fin 1) ℂ)
          (Matrix.toEuclideanLin (0 : Matrix (Fin 1) (Fin 1) ℂ)
            (Matrix.toEuclideanLin (0 : Matrix (Fin 1) (Fin 1) ℂ) Φ)) :=
  toEuclideanLin_perturbedHamiltonian_trialVector hΦ (by simp) fin1_isReducedInverse_zero_zero

end LatticeSystem.Tests.DegeneratePerturbationGroundEnergy
