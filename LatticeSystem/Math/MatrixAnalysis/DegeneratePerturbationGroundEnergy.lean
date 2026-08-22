import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbation

/-!
# The trial-state variational bound for degenerate perturbation theory (Tasaki §10.1)

Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020,
§10.1, pp. 346–347, eqs. (10.1.18)–(10.1.20).

For `Ĥ(λ) = Ĥ₀ + λV̂` with vanishing first-order term `P̂₀V̂P̂₀ = 0`, this file evaluates the
energy of the trial vector

  `Ψ = Φ − λ Ĥ₀⁻¹V̂Φ`,   `Φ ∈ ker Ĥ₀`,

that is, Tasaki's `|Φ⟩ + |Γ⟩` with `|Γ⟩` taken to be the approximation (10.1.18)
`|Γ⟩ ≃ −λĤ₀⁻¹V̂|Φ⟩`. Two exact identities carry the file: the residual

  `Ĥ(λ)Ψ = −λ² V̂Ĥ₀⁻¹V̂Φ`

and the energy

  `⟪Ψ, Ĥ(λ)Ψ⟫ = λ²⟪Φ, ĤeffΦ⟫ + λ³⟪Ĥ₀⁻¹V̂Φ, V̂Ĥ₀⁻¹V̂Φ⟫`,

where `Ĥeff = −P̂₀V̂Ĥ₀⁻¹V̂P̂₀` is the second-order effective Hamiltonian of eq. (10.1.20).
Combined with the Rayleigh–Ritz variational principle on an invariant subspace, they bound the
ground energy of `Ĥ(λ)` from above by `λ²Eeff + c₃λ³` for `0 < λ ≤ 1`; separately, positivity of
`Ĥ₀` and an operator bound `v` for `V̂` give the two-sided bound `|E(λ)| ≤ λv`.

## Provenance

Tasaki's proof of Lemma 10.1 contains **no** variational estimate. Its analytic input is the
unproved sentence "By continuity there are exactly `D₀` independent eigenstates of `Ĥ(λ)` whose
eigenvalues converge to zero … We can also assume that each of these `D₀` eigenstates depends
continuously on `λ`", i.e. Rellich–Kato perturbation theory. **Nothing in this file transcribes
that argument.** The estimates here are an elementary replacement for the book's continuity
input, and must not be read as "Tasaki's proof, formalized".

The book anchor is nevertheless precise. The trial vector is eq. (10.1.18), and the resulting
bound is the rigorous upper half of eq. (10.1.19) `−λ²P̂₀V̂Ĥ₀⁻¹V̂|Φ⟩ ≃ E|Φ⟩`: the state built
from (10.1.18) really does have energy `λ²Eeff + O(λ³)`. Where the book writes `≃` and then
argues by continuity, this file writes `=` for the trial energy and `≤` for the ground energy.

## Relation to the Feshbach layer

`DegeneratePerturbationFeshbach.lean` reconstructs a genuine eigenvector as `Ξ = Φ − λR(λ,E)V̂Φ`
using the reduced resolvent `R(λ,E)`; the vector used here is its `R(λ,E) → Ĥ₀⁻¹` approximation,
employed only as a *trial* state. The two layers are independent: this file imports the
definitional and spectral-gap layer alone.
-/

namespace LatticeSystem.Math

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The variational principle on an invariant subspace.** If a Hermitian `H` preserves `K` and
`E` is its ground eigenvalue on `K`, then `E` is the sharp lower bound of the energy quadratic
form: `E ‖w‖² ≤ re ⟪w, H w⟫` for every `w ∈ K`. The minimising unit eigenvector supplied by
`exists_unit_eigenvector_min_energy_on_invariant` has eigenvalue `≥ E` and realises the optimal
constant, so the two bounds compose. The subspace is automatically nonzero: the ground-eigenvalue
predicate carries a nonzero eigenvector in `K`. -/
theorem IsGroundEigenvalueOn.mul_norm_sq_le {K : Submodule ℂ (EuclideanSpace ℂ n)}
    {H : Matrix n n ℂ} {E : ℝ} (hH : H.IsHermitian)
    (hK : ∀ v ∈ K, Matrix.toEuclideanLin H v ∈ K) (hE : IsGroundEigenvalueOn K H E) :
    ∀ w ∈ K, E * ‖w‖ ^ 2 ≤ RCLike.re (inner ℂ w (Matrix.toEuclideanLin H w)) := by
  obtain ⟨⟨φ, hφK, hφne, -⟩, hmin⟩ := hE
  have hKbot : K ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hφK
    exact hφne hφK
  obtain ⟨m, x, hxK, hxnorm, hxeig, hbound⟩ :=
    exists_unit_eigenvector_min_energy_on_invariant hH hK hKbot
  have hxne : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hxnorm
    exact zero_ne_one hxnorm
  have hEm : E ≤ m := hmin m ⟨x, hxK, hxne, hxeig⟩
  intro w hw
  exact (mul_le_mul_of_nonneg_right hEm (sq_nonneg ‖w‖)).trans (hbound w hw)

/-- **Existence of a ground eigenvalue on a nonzero invariant subspace.** The minimising unit
eigenvector of `exists_unit_eigenvector_min_energy_on_invariant` witnesses the first clause of
`IsGroundEigenvalueOn`, and its sharp energy bound `m ‖w‖² ≤ re ⟪w, H w⟫` evaluated at any other
eigenvector of `H` in `K` gives the minimality clause. -/
theorem exists_isGroundEigenvalueOn {K : Submodule ℂ (EuclideanSpace ℂ n)} {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (hK : ∀ v ∈ K, Matrix.toEuclideanLin H v ∈ K) (hKbot : K ≠ ⊥) :
    ∃ E : ℝ, IsGroundEigenvalueOn K H E := by
  obtain ⟨m, x, hxK, hxnorm, hxeig, hbound⟩ :=
    exists_unit_eigenvector_min_energy_on_invariant hH hK hKbot
  have hxne : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hxnorm
    exact zero_ne_one hxnorm
  refine ⟨m, ⟨x, hxK, hxne, hxeig⟩, ?_⟩
  rintro μ ⟨ψ, hψK, hψne, hψeig⟩
  have hψpos : (0 : ℝ) < ‖ψ‖ ^ 2 := by
    have : 0 < ‖ψ‖ := norm_pos_iff.mpr hψne
    positivity
  have hre : RCLike.re (inner ℂ ψ (Matrix.toEuclideanLin H ψ)) = μ * ‖ψ‖ ^ 2 := by
    rw [hψeig, inner_smul_right, RCLike.re_to_complex, Complex.re_ofReal_mul,
      ← RCLike.re_to_complex, inner_self_eq_norm_sq]
  have hle := hbound ψ hψK
  rw [hre] at hle
  exact le_of_mul_le_mul_right hle hψpos

omit [Fintype n] [DecidableEq n] in
/-- **The perturbed Hamiltonian `Ĥ(λ) = Ĥ₀ + λV̂` is Hermitian** whenever `Ĥ₀` and `V̂` are, the
coefficient `λ` being real. -/
theorem perturbedHamiltonian_isHermitian {H0 V : Matrix n n ℂ} {lam : ℝ}
    (hH0 : H0.IsHermitian) (hV : V.IsHermitian) :
    (perturbedHamiltonian H0 V lam).IsHermitian := by
  rw [perturbedHamiltonian]
  exact hH0.add (hV.smul (isSelfAdjoint_iff.mpr (by simp)))

/-- **Exact residual of the trial vector** (Tasaki eq. (10.1.18) made exact, p. 346). For
`Φ ∈ ker Ĥ₀` with vanishing first-order term `P̂₀V̂P̂₀ = 0` and `Ĥ₀⁻¹` a reduced inverse of `Ĥ₀`,

  `Ĥ(λ)(Φ − λĤ₀⁻¹V̂Φ) = −λ² V̂Ĥ₀⁻¹V̂Φ`.

The `λ⁰` term vanishes because `Ĥ₀Φ = 0`, and the `λ¹` term vanishes because
`Ĥ₀Ĥ₀⁻¹V̂Φ = (1̂ − P̂₀)V̂Φ = V̂Φ`, the projection dropping out by the first-order condition.
Only the residual `λ²` term survives; no smallness, positivity or normalisation is needed. -/
theorem toEuclideanLin_perturbedHamiltonian_trialVector {H0 V H0inv : Matrix n n ℂ} {lam : ℝ}
    {Φ : EuclideanSpace ℂ n} (hΦ : Φ ∈ matrixKernel H0)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hInv : IsReducedInverse H0 H0inv) :
    Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam)
        (Φ - (lam : ℂ) • Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φ))
      = -((lam : ℂ) ^ 2) • Matrix.toEuclideanLin V
          (Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φ)) := by
  have hΦ0 : Matrix.toEuclideanLin H0 Φ = 0 := LinearMap.mem_ker.mp hΦ
  have hPΦ : Matrix.toEuclideanLin (kernelProjectionMatrix H0) Φ = Φ := by
    rw [toEuclideanLin_kernelProjectionMatrix]
    change (matrixKernel H0).starProjection Φ = Φ
    exact Submodule.starProjection_eq_self_iff.mpr hΦ
  have hPVΦ : Matrix.toEuclideanLin (kernelProjectionMatrix H0)
      (Matrix.toEuclideanLin V Φ) = 0 := by
    have h : Matrix.toEuclideanLin
        (kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0) Φ = 0 := by
      rw [hFirstOrder]
      simp
    rwa [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, hPΦ] at h
  have hH0u : Matrix.toEuclideanLin H0
      (Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φ))
      = Matrix.toEuclideanLin V Φ := by
    rw [← toEuclideanLin_mul_apply, hInv.left_inv_on_compl, toEuclideanLin_one_sub_apply,
      hPVΦ, sub_zero]
  have hHsplit : ∀ y : EuclideanSpace ℂ n,
      Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) y
        = Matrix.toEuclideanLin H0 y + (lam : ℂ) • Matrix.toEuclideanLin V y := by
    intro y
    rw [perturbedHamiltonian, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply]
  have hsq : ((lam : ℂ) * (lam : ℂ)) = (lam : ℂ) ^ 2 := by ring
  rw [hHsplit, map_sub, map_sub, map_smul, map_smul, hΦ0, hH0u, smul_sub, smul_smul, hsq,
    neg_smul]
  abel

/-- **Exact energy of the trial vector.** With `u = Ĥ₀⁻¹V̂Φ` and `Ψ = Φ − λu`,

  `⟪Ψ, Ĥ(λ)Ψ⟫ = λ²⟪Φ, ĤeffΦ⟫ + λ³⟪u, V̂u⟫`   (Tasaki eqs. (10.1.19)–(10.1.20), p. 346),

for every `Φ ∈ ker Ĥ₀`, with no eigenvalue or normalisation hypothesis on `Φ`. Pairing the
exact residual `Ĥ(λ)Ψ = −λ²V̂u` against `Ψ` produces `−λ²⟪Φ, V̂u⟫ + λ³⟪u, V̂u⟫` (the `λ` being
real, its conjugate is itself), and `⟪Φ, ĤeffΦ⟫ = −⟪P̂₀Φ, V̂u⟫ = −⟪Φ, V̂u⟫` identifies the
leading coefficient with the effective energy. -/
theorem inner_trialVector_perturbedHamiltonian {H0 V H0inv : Matrix n n ℂ} {lam : ℝ}
    {Φ : EuclideanSpace ℂ n} (hΦ : Φ ∈ matrixKernel H0)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hInv : IsReducedInverse H0 H0inv) :
    (inner ℂ (Φ - (lam : ℂ) • Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φ))
        (Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam)
          (Φ - (lam : ℂ) • Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φ))) : ℂ)
      = (lam : ℂ) ^ 2
          * (inner ℂ Φ
              (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φ) : ℂ)
        + (lam : ℂ) ^ 3
          * (inner ℂ (Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φ))
              (Matrix.toEuclideanLin V (Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φ)))
              : ℂ) := by
  have hPΦ : Matrix.toEuclideanLin (kernelProjectionMatrix H0) Φ = Φ := by
    rw [toEuclideanLin_kernelProjectionMatrix]
    change (matrixKernel H0).starProjection Φ = Φ
    exact Submodule.starProjection_eq_self_iff.mpr hΦ
  have hPsym : (Matrix.toEuclideanLin (kernelProjectionMatrix H0)).IsSymmetric :=
    Matrix.isHermitian_iff_isSymmetric.mp (kernelProjectionMatrix_isHermitian H0)
  have hEff : (inner ℂ Φ
        (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φ) : ℂ)
      = -(inner ℂ Φ (Matrix.toEuclideanLin V
          (Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φ))) : ℂ) := by
    have happ : Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φ
        = -Matrix.toEuclideanLin (kernelProjectionMatrix H0)
            (Matrix.toEuclideanLin V
              (Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φ))) := by
      rw [secondOrderEffectiveHamiltonian, map_neg, LinearMap.neg_apply, toEuclideanLin_mul_apply,
        toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, hPΦ]
    rw [happ, inner_neg_right, ← hPsym Φ (Matrix.toEuclideanLin V
      (Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φ))), hPΦ]
  rw [toEuclideanLin_perturbedHamiltonian_trialVector hΦ hFirstOrder hInv, hEff,
    inner_smul_right, inner_sub_left, inner_smul_left, Complex.conj_ofReal]
  ring

/-- **The trial-state variational bound** (Tasaki §10.1, eqs. (10.1.18)–(10.1.20), pp. 346–347).
Let `Φeff` be a normalized eigenvector of the second-order effective Hamiltonian
`Ĥeff = −P̂₀V̂Ĥ₀⁻¹V̂P̂₀` inside `ker Ĥ₀`, with eigenvalue `Eeff`. Then there is a constant
`c₃ ≥ 0`, independent of `λ`, such that every ground eigenvalue `E` of `Ĥ(λ) = Ĥ₀ + λV̂` on the
whole space satisfies

  `E ≤ λ²Eeff + c₃λ³`   for `0 < λ ≤ 1`.

This is the rigorous upper half of eq. (10.1.19). The trial vector `Ψ = Φeff − λĤ₀⁻¹V̂Φeff` has
exact energy `λ²Eeff + λ³ re⟪u, V̂u⟫` and exact squared norm `1 + λ²‖u‖²` (`Φeff` is orthogonal
to `u = Ĥ₀⁻¹V̂Φeff`, since `Ĥ₀⁻¹` annihilates `ker Ĥ₀`); feeding both into the variational
principle and clearing the denominator `≥ 1` leaves `c₃ = |re⟪u, V̂u⟫| + |Eeff| ‖u‖²`, the
hypothesis `λ ≤ 1` absorbing the `λ⁴` remainder into `λ³`.

**This bound is not Tasaki's argument**; it replaces the unproved continuity input of his proof.
See the module doc. -/
theorem exists_const_isGroundEigenvalue_perturbedHamiltonian_le {H0 V H0inv : Matrix n n ℂ}
    {Eeff : ℝ} {Φeff : EuclideanSpace ℂ n}
    (hH0 : H0.IsHermitian) (hV : V.IsHermitian) (hInv : IsReducedInverse H0 H0inv)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hΦeff : Φeff ∈ matrixKernel H0) (hnorm : ‖Φeff‖ = 1)
    (hEeff : Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φeff
      = (Eeff : ℂ) • Φeff) :
    ∃ c₃ : ℝ, 0 ≤ c₃ ∧ ∀ lam E : ℝ, 0 < lam → lam ≤ 1 →
      IsGroundEigenvalueOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n))
        (perturbedHamiltonian H0 V lam) E →
      E ≤ lam ^ 2 * Eeff + c₃ * lam ^ 3 := by
  refine ⟨|RCLike.re (inner ℂ (Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φeff))
        (Matrix.toEuclideanLin V
          (Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φeff))))|
      + |Eeff| * ‖Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φeff)‖ ^ 2,
    by positivity, ?_⟩
  intro lam E hlam hlam1 hE
  set u : EuclideanSpace ℂ n :=
    Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φeff) with hu
  set B : ℝ := RCLike.re (inner ℂ u (Matrix.toEuclideanLin V u)) with hB
  have hHerm : (perturbedHamiltonian H0 V lam).IsHermitian :=
    perturbedHamiltonian_isHermitian hH0 hV
  have hTop : ∀ w ∈ (⊤ : Submodule ℂ (EuclideanSpace ℂ n)),
      Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) w
        ∈ (⊤ : Submodule ℂ (EuclideanSpace ℂ n)) := fun _ _ => Submodule.mem_top
  have hB1 := IsGroundEigenvalueOn.mul_norm_sq_le hHerm hTop hE
    (Φeff - (lam : ℂ) • u) Submodule.mem_top
  have hL2 : (inner ℂ (Φeff - (lam : ℂ) • u)
        (Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (Φeff - (lam : ℂ) • u)) : ℂ)
      = (lam : ℂ) ^ 2 * (inner ℂ Φeff
          (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φeff) : ℂ)
        + (lam : ℂ) ^ 3 * (inner ℂ u (Matrix.toEuclideanLin V u) : ℂ) := by
    rw [hu]
    exact inner_trialVector_perturbedHamiltonian hΦeff hFirstOrder hInv
  have hΦΦ : (inner ℂ Φeff Φeff : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    norm_num
  have hEffval : (inner ℂ Φeff
      (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φeff) : ℂ)
      = (Eeff : ℂ) := by
    rw [hEeff, inner_smul_right, hΦΦ, mul_one]
  have hcast2 : ((lam : ℂ)) ^ 2 = (((lam ^ 2 : ℝ)) : ℂ) := by push_cast; ring
  have hcast3 : ((lam : ℂ)) ^ 3 = (((lam ^ 3 : ℝ)) : ℂ) := by push_cast; ring
  have hmul : ∀ (r : ℝ) (z : ℂ), RCLike.re ((r : ℂ) * z) = r * RCLike.re z := by
    intro r z
    rw [RCLike.re_to_complex, Complex.re_ofReal_mul, RCLike.re_to_complex]
  have hre : RCLike.re (inner ℂ (Φeff - (lam : ℂ) • u)
        (Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (Φeff - (lam : ℂ) • u)))
      = lam ^ 2 * Eeff + lam ^ 3 * B := by
    rw [hL2, hEffval, hcast2, hcast3, map_add, hmul, hmul, hB, RCLike.re_to_complex,
      Complex.ofReal_re]
  have hPΦ : Matrix.toEuclideanLin (kernelProjectionMatrix H0) Φeff = Φeff := by
    rw [toEuclideanLin_kernelProjectionMatrix]
    change (matrixKernel H0).starProjection Φeff = Φeff
    exact Submodule.starProjection_eq_self_iff.mpr hΦeff
  have hInvsym : (Matrix.toEuclideanLin H0inv).IsSymmetric :=
    Matrix.isHermitian_iff_isSymmetric.mp hInv.hermitian
  have hH0invΦ : Matrix.toEuclideanLin H0inv Φeff = 0 := by
    rw [← hPΦ, ← toEuclideanLin_mul_apply, hInv.kills_kernel_right]
    simp
  have hΦu : (inner ℂ Φeff u : ℂ) = 0 := by
    rw [hu, ← hInvsym Φeff (Matrix.toEuclideanLin V Φeff), hH0invΦ, inner_zero_left]
  have hns : ‖((lam : ℂ)) • u‖ ^ 2 = lam ^ 2 * ‖u‖ ^ 2 := by
    rw [norm_smul, mul_pow]
    simp [sq_abs]
  have hnormΨ : ‖Φeff - (lam : ℂ) • u‖ ^ 2 = 1 + lam ^ 2 * ‖u‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, hΦu, mul_zero, hnorm, hns]
    simp
  rw [hre, hnormΨ] at hB1
  have hlam3 : (0 : ℝ) < lam ^ 3 := by positivity
  have hlam43 : lam ^ 4 ≤ lam ^ 3 := by
    nlinarith [mul_nonneg hlam3.le (sub_nonneg.mpr hlam1)]
  have hu2 : (0 : ℝ) ≤ ‖u‖ ^ 2 := sq_nonneg _
  have hnum : lam ^ 3 * B - lam ^ 4 * Eeff * ‖u‖ ^ 2
      ≤ lam ^ 3 * (|B| + |Eeff| * ‖u‖ ^ 2) := by
    have hA : lam ^ 3 * B ≤ lam ^ 3 * |B| :=
      mul_le_mul_of_nonneg_left (le_abs_self B) hlam3.le
    have hC : lam ^ 4 * (-Eeff * ‖u‖ ^ 2) ≤ lam ^ 4 * (|Eeff| * ‖u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (neg_le_abs Eeff) hu2) (by positivity)
    have hD : lam ^ 4 * (|Eeff| * ‖u‖ ^ 2) ≤ lam ^ 3 * (|Eeff| * ‖u‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hlam43 (by positivity)
    nlinarith [hA, hC, hD]
  have hN1 : (1 : ℝ) ≤ 1 + lam ^ 2 * ‖u‖ ^ 2 := by nlinarith
  have hDN : (E - lam ^ 2 * Eeff) * (1 + lam ^ 2 * ‖u‖ ^ 2)
      ≤ lam ^ 3 * (|B| + |Eeff| * ‖u‖ ^ 2) := by nlinarith [hB1, hnum]
  rcases le_or_gt (E - lam ^ 2 * Eeff) 0 with h | h
  · have hc : (0 : ℝ) ≤ (|B| + |Eeff| * ‖u‖ ^ 2) * lam ^ 3 :=
      mul_nonneg (by positivity) hlam3.le
    linarith
  · have hstep : (E - lam ^ 2 * Eeff) * 1
        ≤ (E - lam ^ 2 * Eeff) * (1 + lam ^ 2 * ‖u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hN1 h.le
    rw [mul_one] at hstep
    linarith

/-- **Two-sided bound on the perturbed ground energy** `|E(λ)| ≤ λv`, for `Ĥ₀ ≥ 0`, `V̂` Hermitian
with operator bound `v`, vanishing first-order term, and a normalized `Φeff ∈ ker Ĥ₀`. The upper
half is variational: `Φeff` has energy `λ⟪Φeff, V̂Φeff⟫ = λ⟪Φeff, P̂₀V̂P̂₀Φeff⟫ = 0`, so the ground
energy is `≤ 0`. The lower half is read off a ground eigenvector `φ`:
`E‖φ‖² = re⟪φ, Ĥ₀φ⟫ + λ re⟪φ, V̂φ⟫ ≥ 0 − λv‖φ‖²`. -/
theorem abs_isGroundEigenvalue_perturbedHamiltonian_le {H0 V : Matrix n n ℂ} {v lam E : ℝ}
    {Φeff : EuclideanSpace ℂ n} (hH0pos : H0.PosSemidef) (hV : V.IsHermitian)
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hΦeff : Φeff ∈ matrixKernel H0) (hnorm : ‖Φeff‖ = 1) (hlam : 0 < lam)
    (hE : IsGroundEigenvalueOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n))
      (perturbedHamiltonian H0 V lam) E) :
    |E| ≤ lam * v := by
  have hHerm : (perturbedHamiltonian H0 V lam).IsHermitian :=
    perturbedHamiltonian_isHermitian hH0pos.1 hV
  have hTop : ∀ w ∈ (⊤ : Submodule ℂ (EuclideanSpace ℂ n)),
      Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) w
        ∈ (⊤ : Submodule ℂ (EuclideanSpace ℂ n)) := fun _ _ => Submodule.mem_top
  have hHsplit : ∀ y : EuclideanSpace ℂ n,
      Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) y
        = Matrix.toEuclideanLin H0 y + (lam : ℂ) • Matrix.toEuclideanLin V y := by
    intro y
    rw [perturbedHamiltonian, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply]
  have hvnonneg : 0 ≤ v := by
    have h := hv Φeff
    rw [hnorm, mul_one] at h
    exact le_trans (norm_nonneg _) h
  have hPΦ : Matrix.toEuclideanLin (kernelProjectionMatrix H0) Φeff = Φeff := by
    rw [toEuclideanLin_kernelProjectionMatrix]
    change (matrixKernel H0).starProjection Φeff = Φeff
    exact Submodule.starProjection_eq_self_iff.mpr hΦeff
  have hPsym : (Matrix.toEuclideanLin (kernelProjectionMatrix H0)).IsSymmetric :=
    Matrix.isHermitian_iff_isSymmetric.mp (kernelProjectionMatrix_isHermitian H0)
  have hPVΦ : Matrix.toEuclideanLin (kernelProjectionMatrix H0)
      (Matrix.toEuclideanLin V Φeff) = 0 := by
    have h : Matrix.toEuclideanLin
        (kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0) Φeff = 0 := by
      rw [hFirstOrder]
      simp
    rwa [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, hPΦ] at h
  have hEnonpos : E ≤ 0 := by
    have hz : (inner ℂ Φeff (Matrix.toEuclideanLin V Φeff) : ℂ) = 0 := by
      have hsym := hPsym Φeff (Matrix.toEuclideanLin V Φeff)
      rwa [hPΦ, hPVΦ, inner_zero_right] at hsym
    have hzero : (inner ℂ Φeff
        (Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) Φeff) : ℂ) = 0 := by
      rw [hHsplit, LinearMap.mem_ker.mp hΦeff, zero_add, inner_smul_right, hz, mul_zero]
    have hb := IsGroundEigenvalueOn.mul_norm_sq_le hHerm hTop hE Φeff Submodule.mem_top
    rw [hzero, hnorm] at hb
    simpa using hb
  obtain ⟨φ, -, hφne, hφeig⟩ := hE.1
  have hφpos : (0 : ℝ) < ‖φ‖ ^ 2 := by
    have : 0 < ‖φ‖ := norm_pos_iff.mpr hφne
    positivity
  have hmul : ∀ (r : ℝ) (z : ℂ), RCLike.re ((r : ℂ) * z) = r * RCLike.re z := by
    intro r z
    rw [RCLike.re_to_complex, Complex.re_ofReal_mul, RCLike.re_to_complex]
  have hEeq : RCLike.re (inner ℂ φ (Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) φ))
      = E * ‖φ‖ ^ 2 := by
    rw [hφeig, inner_smul_right, hmul, inner_self_eq_norm_sq]
  have hsplitre : RCLike.re (inner ℂ φ
        (Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) φ))
      = RCLike.re (inner ℂ φ (Matrix.toEuclideanLin H0 φ))
        + lam * RCLike.re (inner ℂ φ (Matrix.toEuclideanLin V φ)) := by
    rw [hHsplit, inner_add_right, inner_smul_right, map_add, hmul]
  have hH0nonneg : 0 ≤ RCLike.re (inner ℂ φ (Matrix.toEuclideanLin H0 φ)) :=
    (Matrix.isPositive_toEuclideanLin_iff.mpr hH0pos).re_inner_nonneg_right φ
  have hVlow : -(v * ‖φ‖ ^ 2) ≤ RCLike.re (inner ℂ φ (Matrix.toEuclideanLin V φ)) := by
    have h1 : RCLike.re (inner ℂ φ (-Matrix.toEuclideanLin V φ))
        ≤ ‖φ‖ * ‖-Matrix.toEuclideanLin V φ‖ := re_inner_le_norm _ _
    rw [inner_neg_right, map_neg, norm_neg] at h1
    have h2 : ‖φ‖ * ‖Matrix.toEuclideanLin V φ‖ ≤ ‖φ‖ * (v * ‖φ‖) :=
      mul_le_mul_of_nonneg_left (hv φ) (norm_nonneg φ)
    nlinarith [h1, h2]
  have hkey : -(lam * v) * ‖φ‖ ^ 2 ≤ E * ‖φ‖ ^ 2 := by
    rw [← hEeq, hsplitre]
    nlinarith [hH0nonneg, mul_le_mul_of_nonneg_left hVlow hlam.le]
  rw [abs_le]
  exact ⟨le_of_mul_le_mul_right hkey hφpos, hEnonpos.trans (mul_nonneg hlam.le hvnonneg)⟩

end LatticeSystem.Math
