import LatticeSystem.Quantum.SpinS.SPTSymmetryTransportedMPS
import LatticeSystem.Quantum.Pauli

/-!
# Tests: symmetry-transported MPS injectivity transport (#5306 PR-2)

Behavioural tests for `LatticeSystem.Quantum.SPTSymmetryTransportedMPS` (§8.3.4/§8.3.5's
`Ã_g^σ = Σ_{σ'} ⟨ψ^σ|û(g)|ψ^{σ'}⟩ C_g[A^{σ'}]`, eqs. (8.3.13)-(8.3.14), (8.3.33), (8.3.47)):

* **T1** identity transport: `symmetryTransportMPS 1 1 A = A`.
* **T2** non-vacuity: a concrete `IsInjectiveMPS` instance (bond dimension `D = 1`), transported
  by a nontrivial unitary (`σ^x`) into a second, visibly different, injective instance.
* **T3** the sign twist `ε = -1` is not a no-op on the transported family.
* **T4** composition pins the row/column convention `mpsMix u (mpsMix v A) = mpsMix (u * v) A`
  on a concrete non-commuting pair (`σ^x`, `σ^z`).
* **T5** the book's `S = 1` time-reversal instance (8.3.33),
  `Ã⁺ = (A⁻)^*, Ã⁰ = −(A⁰)^*, Ã⁻ = (A⁺)^*`, as the `ε = -1` instance of the general transport at a
  concrete unitary `û₂`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed.), §8.3.4,
pp. 264-265, eqs. (8.3.13)-(8.3.14); §8.3.5, p. 273, eq. (8.3.33); p. 279, eq. (8.3.47).
Refs #5306, #4718.
-/

namespace LatticeSystem.Tests

open LatticeSystem.Quantum
open LatticeSystem.Math (signConj signConjMatrix signConjMatrix_smul signConjMatrix_one_apply)
open LatticeSystem.Quantum (pauliX pauliZ)

/-! ## T1: identity transport -/

/-- T1: transporting by the trivial sign and the identity mixing matrix is the identity on MPS
families (guards `mpsMix`'s summation convention and the `Fin (N + 1)` indexing). -/
private lemma t1_symmetryTransportMPS_one_one {D N : ℕ} (A : MPSMatrices D N) :
    symmetryTransportMPS (1 : ℤˣ) (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) A = A := by
  unfold symmetryTransportMPS
  have hconj : mpsConjugate (1 : ℤˣ) A = A := by
    funext σ
    exact signConjMatrix_one_apply (A σ)
  rw [hconj, mpsMix_one]

/-! ## T2: non-vacuity of the capstone's hypothesis -/

/-- The cheapest nonzero MPS family: `D = 1`, `N = 1`, `A^0 = 1̂`, `A^1 = 0`. -/
private def fixtureA : MPSMatrices 1 1 := ![1, 0]

/-- `fixtureA` at `σ = 0` is the `1 × 1` identity matrix. -/
private lemma fixtureA_zero : fixtureA 0 = (1 : Matrix (Fin 1) (Fin 1) ℂ) := rfl

/-- `fixtureA` at `σ = 1` is the zero matrix. -/
private lemma fixtureA_one : fixtureA 1 = (0 : Matrix (Fin 1) (Fin 1) ℂ) := rfl

/-- `fixtureA` is normalized with `λ = 1`. -/
private lemma t2_isMPSNormalized : IsMPSNormalized fixtureA (1 : ℝ) := by
  refine ⟨zero_lt_one, ?_⟩
  have hsum : (∑ σ : Fin 2, fixtureA σ * (fixtureA σ).conjTranspose) =
      (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    rw [Fin.sum_univ_two, fixtureA_zero, fixtureA_one]
    simp
  rw [hsum]
  simp

/-- Every ordered product of `fixtureA` along the all-`0` word of length `ℓ` is the identity. -/
private lemma t2_orderedProd_replicate_zero (ℓ : ℕ) :
    orderedProd fixtureA (List.replicate ℓ 0) = 1 := by
  induction ℓ with
  | zero => rfl
  | succ n ih =>
      change fixtureA 0 * orderedProd fixtureA (List.replicate n 0) = 1
      rw [fixtureA_zero, ih, one_mul]

/-- `fixtureA`'s ordered products span the (one-dimensional) `1 × 1` matrix space at every
length `ℓ`. -/
private lemma t2_mpsProductsSpanAt (ℓ : ℕ) : mpsProductsSpanAt fixtureA ℓ := by
  unfold mpsProductsSpanAt
  have hone : (1 : Matrix (Fin 1) (Fin 1) ℂ) ∈
      Submodule.span ℂ {M : Matrix (Fin 1) (Fin 1) ℂ |
        ∃ σs : List (Fin 2), σs.length = ℓ ∧ M = orderedProd fixtureA σs} :=
    Submodule.subset_span ⟨List.replicate ℓ 0, List.length_replicate,
      (t2_orderedProd_replicate_zero ℓ).symm⟩
  refine Submodule.eq_top_iff'.mpr fun M => ?_
  have hM : M = (M 0 0) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [hM]
  exact Submodule.smul_mem _ _ hone

/-- Theorem 7.5(i) holds for `fixtureA` at `ℓ₀ = 0`. -/
private lemma t2_mpsSpansEventually : MPSSpansEventually fixtureA :=
  ⟨0, t2_mpsProductsSpanAt 0⟩

/-- Theorem 7.5(ii) holds for `fixtureA` at every length. -/
private lemma t2_mpsSpansForAllLarge : MPSSpansForAllLarge fixtureA :=
  ⟨0, fun ℓ _ => t2_mpsProductsSpanAt ℓ⟩

/-- `fixtureA`'s transfer matrix is the `1 × 1` identity. -/
private lemma t2_mpsTransferMatrix_eq_one :
    mpsTransferMatrix fixtureA = (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) := by
  ext p q
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  fin_cases p1
  fin_cases p2
  fin_cases q1
  fin_cases q2
  simp [mpsTransferMatrix, fixtureA_zero, fixtureA_one, Fin.sum_univ_two]

/-- `fixtureA` satisfies Theorem 7.5(iii): `λ = 1` is the unique, simple transfer eigenvalue
(vacuously: the transfer matrix is a `1 × 1` identity, so it has a single eigenvalue). -/
private lemma t2_hasPrimitiveTransferSpectrum :
    HasPrimitiveTransferSpectrum fixtureA (1 : ℝ) := by
  unfold HasPrimitiveTransferSpectrum
  rw [t2_mpsTransferMatrix_eq_one]
  haveI : Nontrivial (Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) :=
    ⟨0, 1, by
      intro h
      have h00 := congrFun (congrFun h (0, 0)) (0, 0)
      simp at h00⟩
  have hspec : spectrum ℂ (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) = {1} :=
    spectrum.one_eq
  refine ⟨by rw [hspec]; rfl, ?_, fun μ hμ hne => absurd (by
    rwa [hspec, Set.mem_singleton_iff] at hμ) hne⟩
  have hzero : (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ).mulVecLin -
      ((1 : ℝ) : ℂ) • LinearMap.id = 0 := by
    ext v i
    simp [Matrix.mulVecLin_one]
  rw [hzero, LinearMap.ker_zero, finrank_top]
  simp

/-- `fixtureA` is a genuinely injective MPS family (Tasaki Theorem 7.5). This is the acceptance
condition's non-vacuity witness: without it, the capstone `isInjectiveMPS_symmetryTransportMPS`
below would never be instantiated. -/
private lemma t2_isInjectiveMPS_fixtureA : IsInjectiveMPS fixtureA (1 : ℝ) :=
  ⟨t2_isMPSNormalized, t2_mpsSpansEventually, t2_mpsSpansForAllLarge,
    t2_hasPrimitiveTransferSpectrum⟩

/-- `σ^x` is unitary. -/
private lemma t2_pauliX_mem_unitaryGroup : pauliX ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, pauliX_isHermitian.eq,
    pauliX_mul_self]

/-- T2: the `σ^x`-transported family `symmetryTransportMPS 1 σ^x fixtureA` is again injective, by
the PR-2 capstone. This is the non-vacuity test required by #5306's acceptance criteria. -/
private lemma t2_isInjectiveMPS_symmetryTransportMPS :
    IsInjectiveMPS (symmetryTransportMPS (1 : ℤˣ) pauliX fixtureA) (1 : ℝ) :=
  isInjectiveMPS_symmetryTransportMPS t2_pauliX_mem_unitaryGroup t2_isInjectiveMPS_fixtureA

/-- T2: the transported family is visibly the swap of `fixtureA` (`![0, 1]`), confirming the
capstone is not applied to a degenerate/identity-equal instance. -/
private lemma t2_symmetryTransportMPS_fixtureA_eq :
    symmetryTransportMPS (1 : ℤˣ) pauliX fixtureA =
      ![(0 : Matrix (Fin 1) (Fin 1) ℂ), 1] := by
  unfold symmetryTransportMPS mpsMix mpsConjugate
  funext σ
  fin_cases σ <;>
    simp [pauliX, signConjMatrix, signConj, fixtureA_zero, fixtureA_one, Fin.sum_univ_two]

/-! ## T3: the sign twist `ε = -1` is not a no-op -/

/-- A second `D = 1, N = 1` fixture with a genuinely complex entry, used to exhibit the effect of
the `ε = -1` twist. -/
private def fixtureAI : MPSMatrices 1 1 := ![Complex.I • 1, 0]

/-- `fixtureAI` at `σ = 0` is `i · 1̂`. -/
private lemma fixtureAI_zero :
    fixtureAI 0 = Complex.I • (1 : Matrix (Fin 1) (Fin 1) ℂ) := rfl

/-- T3: transporting `fixtureAI` by the antiunitary sign `ε = -1` (with trivial mixing) differs
from transporting it by the unitary sign `ε = 1`: the twist genuinely conjugates the entries. -/
private lemma t3_symmetryTransportMPS_neg_one_ne_one :
    symmetryTransportMPS (-1 : ℤˣ) (1 : Matrix (Fin 2) (Fin 2) ℂ) fixtureAI ≠
      symmetryTransportMPS (1 : ℤˣ) (1 : Matrix (Fin 2) (Fin 2) ℂ) fixtureAI := by
  rw [t1_symmetryTransportMPS_one_one]
  unfold symmetryTransportMPS mpsConjugate
  rw [mpsMix_one]
  intro h
  have h0 := congrFun h 0
  rw [fixtureAI_zero, signConjMatrix_smul, map_one] at h0
  have hI : signConj (-1 : ℤˣ) Complex.I = Complex.I := by
    have h00 := congrFun (congrFun h0 0) 0
    simpa using h00
  have hconjI : starRingEnd ℂ Complex.I = Complex.I := by
    simpa [signConj] using hI
  rw [Complex.conj_I] at hconjI
  have h2 : (2 : ℂ) * Complex.I = 0 := by linear_combination -hconjI
  rcases mul_eq_zero.mp h2 with h2 | h2
  · norm_num at h2
  · exact Complex.I_ne_zero h2

/-! ## T4: composition pins the row/column convention -/

/-- T4 (abstract): `mpsMix` composes contravariantly, `mpsMix u (mpsMix v A) = mpsMix (u * v) A`,
specialized to the concrete non-commuting pair `σ^x, σ^z` (this is what PR-4's cocycle chase
needs; a transposed convention would instead give `mpsMix (v * u) A`, see T4's concrete check
below). -/
private lemma t4_mpsMix_mpsMix_pauliXZ {D : ℕ} (A : MPSMatrices D 1) :
    mpsMix pauliX (mpsMix pauliZ A) = mpsMix (pauliX * pauliZ) A :=
  mpsMix_mpsMix pauliX pauliZ A

/-- T4 (concrete, `σ^x` after `σ^z`): computed directly by unfolding `mpsMix`, independent of
`mpsMix_mpsMix`. -/
private lemma t4_mpsMix_pauliX_mpsMix_pauliZ_fixtureA :
    mpsMix pauliX (mpsMix pauliZ fixtureA) = ![(0 : Matrix (Fin 1) (Fin 1) ℂ), 1] := by
  unfold mpsMix
  funext σ
  fin_cases σ <;>
    simp [pauliX, pauliZ, fixtureA_zero, fixtureA_one, Fin.sum_univ_two]

/-- T4 (concrete, `σ^x * σ^z`): computed directly by unfolding `mpsMix`, matching the previous
lemma and hence pinning the row/column convention on concrete data (with the transposed
convention `σ^z * σ^x` this would disagree, since `σ^x σ^z ≠ σ^z σ^x`). -/
private lemma t4_mpsMix_mul_pauliXZ_fixtureA :
    mpsMix (pauliX * pauliZ) fixtureA = ![(0 : Matrix (Fin 1) (Fin 1) ℂ), 1] := by
  unfold mpsMix
  funext σ
  fin_cases σ <;>
    simp [pauliX, pauliZ, Matrix.mul_apply, fixtureA_zero, fixtureA_one, Fin.sum_univ_two]

/-- T4: the composition and the direct-computation route agree, on concrete data. -/
private lemma t4_mpsMix_composition_agrees :
    mpsMix pauliX (mpsMix pauliZ fixtureA) = mpsMix (pauliX * pauliZ) fixtureA := by
  rw [t4_mpsMix_pauliX_mpsMix_pauliZ_fixtureA, t4_mpsMix_mul_pauliXZ_fixtureA]

/-- T4: the inverse-transport device `symmetryTransportMPS_symmetryTransportMPS`, specialized to
`ε = 1`, `u = σ^x`, `v = σ^z`. -/
private lemma t4_symmetryTransportMPS_symmetryTransportMPS (A : MPSMatrices 1 1) :
    symmetryTransportMPS (1 : ℤˣ) pauliZ (symmetryTransportMPS (1 : ℤˣ) pauliX A) =
      mpsMix (pauliZ * signConjMatrix (1 : ℤˣ) pauliX) A :=
  symmetryTransportMPS_symmetryTransportMPS (ε := 1) (u := pauliX) (v := pauliZ) A

/-! ## T5: the book's `S = 1` time-reversal instance (8.3.33) -/

/-- `û₂` of eq. (8.3.33): a `3 × 3` antidiagonal unitary with signs `(−1)^{1+σ}`, `σ ∈ {−1,0,1}`
in book order (`Fin 3` index `0 ↦ −1`, `1 ↦ 0`, `2 ↦ +1`). -/
private def uT5 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 1; 0, -1, 0; 1, 0, 0]

/-- T5: `symmetryTransportMPS (-1) û₂ A = (Ã⁺, Ã⁰, Ã⁻) = ((A⁻)^*, −(A⁰)^*, (A⁺)^*)`, the printed
eq. (8.3.33), for a symbolic `S = 1` MPS family `A`. -/
private lemma t5_symmetryTransportMPS_uT5 {D : ℕ} (A : MPSMatrices D 2) :
    symmetryTransportMPS (-1 : ℤˣ) uT5 A =
      ![(A 2).map (starRingEnd ℂ), -(A 1).map (starRingEnd ℂ), (A 0).map (starRingEnd ℂ)] := by
  unfold symmetryTransportMPS mpsMix mpsConjugate
  funext σ
  fin_cases σ <;>
    · ext i j
      simp [uT5, signConjMatrix, signConj, Fin.sum_univ_three, RingHom.mapMatrix_apply]

end LatticeSystem.Tests
