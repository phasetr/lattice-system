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
* **T6** the antiunitary branch of the capstone at bond dimension `D = 2`: the spin-`1` Pauli
  family is injective with `λ = 3` and a gapped transfer spectrum `{3, -1}`, and `û₂` is unitary,
  so the capstone transports a nondegenerate `λ`-eigenspace and a nonempty gap condition through
  the entrywise conjugation.

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

/-- T4 (abstract): `mpsMix` composes covariantly, `mpsMix u (mpsMix v A) = mpsMix (u * v) A`,
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

/-- T5: the printed eq. (8.3.33) `(Ã⁺, Ã⁰, Ã⁻) = ((A⁻)^*, −(A⁰)^*, (A⁺)^*)`, for a symbolic
`S = 1` MPS family `A`.  The book lists the triple in the order `(+, 0, −)` whereas the `Fin 3`
index of an `MPSMatrices D 2` runs in the order `(σ = −1, 0, +1)`, so the `![…]` below is the
book's triple read backwards: its entry `0` is `Ã⁻ = (A⁺)^* = (A 2)^*`, its entry `1` is
`Ã⁰ = −(A⁰)^* = −(A 1)^*`, and its entry `2` is `Ã⁺ = (A⁻)^* = (A 0)^*`. -/
private lemma t5_symmetryTransportMPS_uT5 {D : ℕ} (A : MPSMatrices D 2) :
    symmetryTransportMPS (-1 : ℤˣ) uT5 A =
      ![(A 2).map (starRingEnd ℂ), -(A 1).map (starRingEnd ℂ), (A 0).map (starRingEnd ℂ)] := by
  unfold symmetryTransportMPS mpsMix mpsConjugate
  funext σ
  fin_cases σ <;>
    · ext i j
      simp [uT5, signConjMatrix, signConj, Fin.sum_univ_three, RingHom.mapMatrix_apply]

/-! ## T6: the antiunitary branch of the capstone at bond dimension `D = 2` -/

/-- T6: `û₂` of eq. (8.3.33) is unitary, hence a legal mixing matrix for the capstone. -/
private lemma t6_uT5_mem_unitaryGroup : uT5 ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uT5, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.mul_apply,
      Fin.sum_univ_three]

/-- A spin-`S = 1` MPS family of bond dimension `D = 2`: the three Pauli matrices.  It is
normalized with `λ = 3`, its length-2 ordered products already span all `2 × 2` matrices, and its
transfer matrix is `2|v⟩⟨v| − 1` with the nondegenerate top eigenvalue `3` and the gapped
eigenvalue `−1`, so every clause of `IsInjectiveMPS` is checked here with genuine content (unlike
the `D = 1` fixture of T2, whose transfer matrix is `1 × 1`). -/
private def fixtureP : MPSMatrices 2 2 := ![pauliX, pauliY, pauliZ]

/-- `fixtureP` is normalized with `λ = 3`, since each Pauli matrix is Hermitian and squares
to `1`. -/
private lemma t6_isMPSNormalized : IsMPSNormalized fixtureP (3 : ℝ) := by
  refine ⟨by norm_num, ?_⟩
  rw [Fin.sum_univ_three]
  change pauliX * pauliX.conjTranspose + pauliY * pauliY.conjTranspose
      + pauliZ * pauliZ.conjTranspose = ((3 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  rw [pauliX_isHermitian.eq, pauliY_isHermitian.eq, pauliZ_isHermitian.eq, pauliX_mul_self,
    pauliY_mul_self, pauliZ_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

/-- Any submodule of `2 × 2` matrices containing every product of two matrices of `fixtureP` is
everything, since those products exhaust the Pauli basis `1, σ^x, σ^y, σ^z` up to phases. -/
private lemma t6_eq_top_of_products_mem (W : Submodule ℂ (Matrix (Fin 2) (Fin 2) ℂ))
    (hW : ∀ σ τ : Fin 3, fixtureP σ * fixtureP τ ∈ W) : W = ⊤ := by
  have hone : (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ W := by
    have h : pauliX * pauliX ∈ W := hW 0 0
    rwa [pauliX_mul_self] at h
  have hZ : pauliZ ∈ W := by
    have h : pauliX * pauliY ∈ W := hW 0 1
    rw [pauliX_mul_pauliY] at h
    have h2 := W.smul_mem (-Complex.I) h
    rwa [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul] at h2
  have hY : pauliY ∈ W := by
    have h : pauliZ * pauliX ∈ W := hW 2 0
    rw [pauliZ_mul_pauliX] at h
    have h2 := W.smul_mem (-Complex.I) h
    rwa [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul] at h2
  have hX : pauliX ∈ W := by
    have h : pauliY * pauliZ ∈ W := hW 1 2
    rw [pauliY_mul_pauliZ] at h
    have h2 := W.smul_mem (-Complex.I) h
    rwa [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul] at h2
  refine Submodule.eq_top_iff'.mpr fun M => ?_
  have hM : M = ((M 0 0 + M 1 1) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      + ((M 0 1 + M 1 0) / 2) • pauliX + (Complex.I * (M 0 1 - M 1 0) / 2) • pauliY
      + ((M 0 0 - M 1 1) / 2) • pauliZ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliX, pauliY, pauliZ] <;> ring_nf <;> rw [Complex.I_sq] <;> ring
  rw [hM]
  exact W.add_mem (W.add_mem (W.add_mem (W.smul_mem _ hone) (W.smul_mem _ hX))
    (W.smul_mem _ hY)) (W.smul_mem _ hZ)

/-- Theorem 7.5(i) for `fixtureP` at `ℓ = 2`: the products `σ^α σ^β` span all `2 × 2` matrices
(length `1` cannot span, since three matrices cannot span a four-dimensional space). -/
private lemma t6_mpsProductsSpanAt_two : mpsProductsSpanAt fixtureP 2 :=
  t6_eq_top_of_products_mem _ fun σ τ => Submodule.subset_span
    ⟨[σ, τ], rfl, by rw [show orderedProd fixtureP [σ, τ] = fixtureP σ * (fixtureP τ * 1) from rfl,
      mul_one]⟩

/-- The diagonal indicator vector `v_{(a,b)} = δ_{ab}` of the doubled index, the top transfer
eigenvector of `fixtureP`. -/
private def t6v : Fin 2 × Fin 2 → ℂ := fun p => if p.1 = p.2 then 1 else 0

/-- `v` is nonzero. -/
private lemma t6v_ne_zero : t6v ≠ 0 := by
  intro h
  have h00 := congrFun h (0, 0)
  simp [t6v] at h00

/-- The transfer matrix of `fixtureP` is `T = 2|v⟩⟨v| − 1`, the Pauli completeness relation
`Σ_α (σ^α)^*_{ab} (σ^α)_{cd} = 2 δ_{bd} δ_{ac} − δ_{ab} δ_{cd}`. -/
private lemma t6_mpsTransferMatrix_apply (p q : Fin 2 × Fin 2) :
    mpsTransferMatrix fixtureP p q =
      2 * t6v p * t6v q - (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) p q := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;>
    simp [mpsTransferMatrix, fixtureP, t6v, pauliX, pauliY, pauliZ, Fin.sum_univ_three] <;>
    norm_num

/-- The transfer matrix of `fixtureP` acts by `(T x)_p = 2 v_p (x_{00} + x_{11}) − x_p`. -/
private lemma t6_mulVec_apply (x : Fin 2 × Fin 2 → ℂ) (p : Fin 2 × Fin 2) :
    (mpsTransferMatrix fixtureP).mulVec x p = 2 * t6v p * (x (0, 0) + x (1, 1)) - x p := by
  obtain ⟨p1, p2⟩ := p
  fin_cases p1 <;> fin_cases p2 <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      t6_mpsTransferMatrix_apply, t6v, Matrix.one_apply] <;> ring

/-- `v` is an eigenvector of the transfer matrix for the normalization eigenvalue `λ = 3`. -/
private lemma t6_mulVec_t6v :
    (mpsTransferMatrix fixtureP).mulVec t6v = ((3 : ℝ) : ℂ) • t6v := by
  funext p
  rw [t6_mulVec_apply]
  obtain ⟨p1, p2⟩ := p
  fin_cases p1 <;> fin_cases p2 <;> simp [t6v] <;> norm_num

/-- For a complex matrix, membership in the spectrum is exactly the existence of an
eigenvector. -/
private lemma t6_mem_spectrum_iff {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (μ : ℂ) :
    μ ∈ spectrum ℂ M ↔ ∃ x : n → ℂ, x ≠ 0 ∧ M.mulVec x = μ • x := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_ne_iff,
    ← Matrix.exists_mulVec_eq_zero_iff]
  refine exists_congr fun x => and_congr_right fun _ => ?_
  rw [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    sub_eq_zero, eq_comm]

/-- The transfer spectrum of `fixtureP` is `{3, −1}`: an eigenvector either has a nonzero diagonal
sum, forcing `μ = 3`, or has a vanishing one, forcing `μ = −1`. -/
private lemma t6_spectrum_mem (μ : ℂ) (hμ : μ ∈ spectrum ℂ (mpsTransferMatrix fixtureP)) :
    μ = 3 ∨ μ = -1 := by
  obtain ⟨x, hx0, hx⟩ := (t6_mem_spectrum_iff _ _).mp hμ
  by_cases hS : x (0, 0) + x (1, 1) = 0
  · right
    obtain ⟨p, hp⟩ : ∃ p, x p ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hx0 (funext hcon)
    have hpe := congrFun hx p
    rw [t6_mulVec_apply, hS] at hpe
    simp only [Pi.smul_apply, smul_eq_mul, mul_zero, zero_sub] at hpe
    have hfac : (μ + 1) * x p = 0 := by linear_combination -hpe
    rcases mul_eq_zero.mp hfac with h | h
    · linear_combination h
    · exact absurd h hp
  · left
    have h00 := congrFun hx (0, 0)
    have h11 := congrFun hx (1, 1)
    rw [t6_mulVec_apply] at h00 h11
    simp only [t6v, Pi.smul_apply, smul_eq_mul, reduceIte] at h00 h11
    have hkey : (μ - 3) * (x (0, 0) + x (1, 1)) = 0 := by linear_combination -h00 - h11
    rcases mul_eq_zero.mp hkey with h | h
    · linear_combination h
    · exact absurd h hS

/-- Theorem 7.5(iii) for `fixtureP`: `λ = 3` is a simple transfer eigenvalue and the rest of the
spectrum sits at `−1`, strictly inside the disc of radius `3`. -/
private lemma t6_hasPrimitiveTransferSpectrum :
    HasPrimitiveTransferSpectrum fixtureP (3 : ℝ) := by
  refine ⟨(t6_mem_spectrum_iff _ _).mpr ⟨t6v, t6v_ne_zero, t6_mulVec_t6v⟩, ?_, ?_⟩
  · have hker : LinearMap.ker ((mpsTransferMatrix fixtureP).mulVecLin
        - ((3 : ℝ) : ℂ) • LinearMap.id) = Submodule.span ℂ {t6v} := by
      refine le_antisymm (fun x hx => ?_) ?_
      · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
          Matrix.mulVecLin_apply, sub_eq_zero] at hx
        rw [Submodule.mem_span_singleton]
        refine ⟨(x (0, 0) + x (1, 1)) / 2, funext fun p => ?_⟩
        have hp := congrFun hx p
        rw [t6_mulVec_apply] at hp
        simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_ofNat] at hp ⊢
        linear_combination hp / 4
      · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
          LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
          Matrix.mulVecLin_apply, sub_eq_zero]
        exact t6_mulVec_t6v
    rw [hker, finrank_span_singleton t6v_ne_zero]
  · intro μ hμ hne
    rcases t6_spectrum_mem μ hμ with h | h
    · exact absurd (by rw [h]; norm_num) hne
    · rw [h]
      norm_num

/-- `fixtureP` is injective in the sense of Tasaki Theorem 7.5, with `λ = 3`. -/
private lemma t6_isInjectiveMPS : IsInjectiveMPS fixtureP (3 : ℝ) :=
  ⟨t6_isMPSNormalized, ⟨2, t6_mpsProductsSpanAt_two⟩,
    (mps_spans_eventually_iff_spans_for_all_large fixtureP 3 t6_isMPSNormalized).mp
      ⟨2, t6_mpsProductsSpanAt_two⟩,
    t6_hasPrimitiveTransferSpectrum⟩

/-- T6: the capstone on the antiunitary branch `ε = -1` at bond dimension `D = 2`, at the book's
time-reversal mixing matrix `û₂` of eq. (8.3.33).  Unlike T2 this exercises the entrywise
conjugation on the transfer matrix, its spectrum and its `λ`-eigenspace with a nondegenerate,
genuinely gapped spectrum. -/
private lemma t6_isInjectiveMPS_symmetryTransportMPS :
    IsInjectiveMPS (symmetryTransportMPS (-1 : ℤˣ) uT5 fixtureP) (3 : ℝ) :=
  isInjectiveMPS_symmetryTransportMPS t6_uT5_mem_unitaryGroup t6_isInjectiveMPS

/-- T6: the transported family is the visible `σ^x ↔ σ^z` swap `![σ^z, σ^y, σ^x]`, so the capstone
above is not applied to a fixed point of the transport. -/
private lemma t6_symmetryTransportMPS_fixtureP :
    symmetryTransportMPS (-1 : ℤˣ) uT5 fixtureP = ![pauliZ, pauliY, pauliX] := by
  rw [t5_symmetryTransportMPS_uT5]
  funext σ
  fin_cases σ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [fixtureP, pauliX, pauliY, pauliZ]

end LatticeSystem.Tests
