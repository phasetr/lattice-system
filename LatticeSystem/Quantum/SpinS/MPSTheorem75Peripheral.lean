import LatticeSystem.Quantum.SpinS.MPSTheorem75Choi
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Peripheral-spectrum substrate for Tasaki Theorem 7.5

This file proves the forward word-span-to-primitive-spectrum route for the corrected Tasaki
Theorem 7.5. The proof is specialized to the concrete MPS Kraus transfer. All positivity,
intertwining, commutant, and transfer-similarity helpers remain private.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.2.2, Theorem 7.5, eqs. (7.2.41)–(7.2.42), pp. 202–203.
-/

namespace LatticeSystem.Quantum.MPSTheorem75.Internal

open Matrix Module
open scoped CStarAlgebra ComplexOrder

variable {D N : ℕ}

/-- Finite square `CStarMatrix` spaces are finite-dimensional over `ℂ`. -/
noncomputable local instance cstarMatrixFiniteDimensional :
    FiniteDimensional ℂ (CStarMatrix (Fin D) (Fin D) ℂ) :=
  CStarMatrix.ofMatrixₗ.finiteDimensional

/-- Evaluation commutes with an unindexed finite sum of `CStarMatrix` values. -/
private theorem cstarMatrix_univ_sum_apply {ι : Type*} [Fintype ι]
    (B : ι → CStarMatrix (Fin D) (Fin D) ℂ) (i j : Fin D) :
    (∑ σ, B σ) i j = ∑ σ, B σ i j := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [CStarMatrix.zero_apply]
  | insert a s ha ih => simp [ha, ih, CStarMatrix.add_apply]

/-- Every spectral value of a positive unital finite Kraus transfer has norm at most one. -/
private theorem norm_spectrum_finiteKrausMap_le_one
    [NeZero D] {ι : Type*} [Fintype ι]
    (A : ι → CStarMatrix (Fin D) (Fin D) ℂ)
    (hunital : finiteKrausMap A 1 = 1)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (finiteKrausMap A)) :
    ‖μ‖ ≤ 1 := by
  obtain ⟨X, hX⟩ :=
    (Module.End.HasEigenvalue.of_mem_spectrum hμ).exists_hasEigenvector
  by_contra hnot
  have hgt : 1 < ‖μ‖ := lt_of_not_ge hnot
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt 4 hgt
  have hbound := norm_finiteKrausMap_pow_le A hunital n X
  rw [hX.pow_apply, norm_smul, norm_pow] at hbound
  have hXnorm : 0 < ‖X‖ := norm_pos_iff.mpr hX.2
  have hle : ‖μ‖ ^ n ≤ 4 := by
    exact le_of_mul_le_mul_right (by simpa [mul_assoc] using hbound) hXnorm
  exact (not_lt_of_ge hle) hn

set_option linter.deprecated false in
/-- A faithful positive weight separates a zero positive-semidefinite matrix. -/
private theorem eq_zero_of_posSemidef_of_trace_mul_posDef_eq_zero [NeZero D]
    {ρ Y : Matrix (Fin D) (Fin D) ℂ}
    (hρ : ρ.PosDef) (hY : Y.PosSemidef)
    (htrace : (ρ * Y).trace = 0) :
    Y = 0 := by
  obtain ⟨B, hBunit, rfl⟩ :=
    Matrix.posDef_iff_eq_conjTranspose_mul_self.mp hρ
  have hBYB : (B * Y * B.conjTranspose).PosSemidef :=
    hY.mul_mul_conjTranspose_same B
  have htr : (B * Y * B.conjTranspose).trace = 0 := by
    calc
      (B * Y * B.conjTranspose).trace =
          (B.conjTranspose * B * Y).trace := by
            simpa only [mul_assoc] using
              Matrix.trace_mul_cycle B Y B.conjTranspose
      _ = 0 := htrace
  have hzero : B * Y * B.conjTranspose = 0 :=
    hBYB.trace_eq_zero_iff.mp htr
  have hzero' : B * Y * B.conjTranspose = B * 0 * B.conjTranspose := by
    simpa using hzero
  exact hBunit.mul_left_cancel (hBunit.star.mul_right_cancel hzero')

/-- The defect attached to a peripheral eigenmatrix and one Kraus matrix. -/
private noncomputable def krausPeripheralDefect
    (A X : CStarMatrix (Fin D) (Fin D) ℂ) (μ : ℂ) :
    CStarMatrix (Fin D) (Fin D) ℂ :=
  A * X - μ • (X * A)

/-- A zero finite sum of matrices `C Cᴴ` forces every `C` to vanish. -/
private theorem eq_zero_of_sum_mul_star_eq_zero
    {ι : Type*} [Fintype ι]
    (C : ι → CStarMatrix (Fin D) (Fin D) ℂ)
    (hsum : ∑ σ, C σ * star (C σ) = 0) :
    ∀ σ, C σ = 0 := by
  intro σ
  have htrace : ∑ τ, (C τ * star (C τ)).trace = 0 := by
    change ∑ τ, ∑ i, (C τ * star (C τ)) i i = 0
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    have hii := congrFun (congrFun hsum i) i
    rw [show (∑ τ, C τ * star (C τ)) i i =
        ∑ τ, (C τ * star (C τ)) i i by
          simpa using cstarMatrix_univ_sum_apply
            (fun τ => C τ * star (C τ)) i i] at hii
    simpa [CStarMatrix.zero_apply] using hii
  have hnonneg :
      ∀ τ ∈ (Finset.univ : Finset ι),
        0 ≤ (C τ * star (C τ)).trace := by
    intro τ _
    exact (Matrix.posSemidef_self_mul_conjTranspose (C τ)).trace_nonneg
  have hz :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp htrace σ (Finset.mem_univ σ)
  exact Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp hz

/-- A unit-modulus scalar times its star is one. -/
private theorem mul_star_eq_one_of_norm_eq_one {μ : ℂ} (hμ : ‖μ‖ = 1) :
    μ * star μ = 1 := by
  change μ * (starRingEnd ℂ) μ = 1
  rw [Complex.mul_conj, ← Complex.sq_norm, hμ]
  norm_num

/-- The finite Kraus transfer commutes with star. -/
private theorem finiteKrausMap_star {ι : Type*} [Fintype ι]
    (A : ι → CStarMatrix (Fin D) (Fin D) ℂ)
    (X : CStarMatrix (Fin D) (Fin D) ℂ) :
    finiteKrausMap A (star X) = star (finiteKrausMap A X) := by
  change (∑ σ, A σ * star X * star (A σ)) =
    star (∑ σ, A σ * X * star (A σ))
  ext p q
  rw [show (∑ σ, A σ * star X * star (A σ)) p q =
      ∑ σ, (A σ * star X * star (A σ)) p q by
        simpa using cstarMatrix_univ_sum_apply
          (fun σ => A σ * star X * star (A σ)) p q]
  change (∑ σ, (A σ * star X * star (A σ)) p q) =
    star ((∑ σ, A σ * X * star (A σ)) q p)
  rw [show (∑ σ, A σ * X * star (A σ)) q p =
      ∑ σ, (A σ * X * star (A σ)) q p by
        simpa using cstarMatrix_univ_sum_apply
          (fun σ => A σ * X * star (A σ)) q p]
  have hmapsum :
      (starRingEnd ℂ) (∑ σ, (A σ * X * star (A σ)) q p) =
        ∑ σ, (starRingEnd ℂ) ((A σ * X * star (A σ)) q p) := by
    simpa only [Finset.sum_const_zero] using map_sum (starRingEnd ℂ)
      (fun σ : ι => (A σ * X * star (A σ)) q p) Finset.univ
  change (∑ σ, (A σ * star X * star (A σ)) p q) =
    (starRingEnd ℂ) (∑ σ, (A σ * X * star (A σ)) q p)
  rw [hmapsum]
  apply Finset.sum_congr rfl
  intro σ _
  have hterm :
      A σ * star X * star (A σ) =
        star (A σ * X * star (A σ)) := by
    rw [star_mul, star_mul, star_star]
    simp [mul_assoc]
  exact congrFun (congrFun hterm p) q

/-- Expansion of one peripheral Kraus defect square. -/
private theorem krausPeripheralDefect_mul_star
    (A X : CStarMatrix (Fin D) (Fin D) ℂ) (μ : ℂ) :
    krausPeripheralDefect A X μ * star (krausPeripheralDefect A X μ) =
      A * (X * star X) * star A -
        star μ • ((A * X * star A) * star X) -
        μ • (X * (A * star X * star A)) +
        (μ * star μ) •
          (X * (A * (1 : CStarMatrix (Fin D) (Fin D) ℂ) * star A) * star X) := by
  unfold krausPeripheralDefect
  rw [star_sub, star_mul, StarModule.star_smul, star_mul]
  simp only [mul_sub, sub_mul, CStarMatrix.mul_smul,
    CStarMatrix.smul_mul, smul_smul]
  rw [mul_comm (star μ) μ]
  noncomm_ring

/-- The sum of peripheral defects is the Kraus Schwarz defect. -/
private theorem sum_krausPeripheralDefect_mul_star
    {ι : Type*} [Fintype ι]
    (A : ι → CStarMatrix (Fin D) (Fin D) ℂ)
    (X : CStarMatrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hunital : finiteKrausMap A 1 = 1)
    (heig : finiteKrausMap A X = μ • X) (hμ : ‖μ‖ = 1) :
    (∑ σ, krausPeripheralDefect (A σ) X μ *
      star (krausPeripheralDefect (A σ) X μ)) =
      finiteKrausMap A (X * star X) - X * star X := by
  have hstarEig : finiteKrausMap A (star X) = star μ • star X := by
    rw [finiteKrausMap_star, heig, StarModule.star_smul]
  have hscalar : μ * star μ = 1 := mul_star_eq_one_of_norm_eq_one hμ
  have hscalar' : star μ * μ = 1 := by simpa [mul_comm] using hscalar
  change (∑ σ, A σ * X * star (A σ)) = μ • X at heig
  change (∑ σ, A σ * star X * star (A σ)) = star μ • star X at hstarEig
  change (∑ σ, A σ * 1 * star (A σ)) = 1 at hunital
  simp_rw [krausPeripheralDefect_mul_star]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib]
  change
    (∑ σ, A σ * (X * star X) * star (A σ)) -
          ∑ σ, star μ • ((A σ * X * star (A σ)) * star X) -
        ∑ σ, μ • (X * (A σ * star X * star (A σ))) +
      ∑ σ, (μ * star μ) •
        (X * (A σ * 1 * star (A σ)) * star X) =
      (∑ σ, A σ * (X * star X) * star (A σ)) - X * star X
  simp_rw [← Finset.smul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [heig, hstarEig, hunital]
  simp only [CStarMatrix.smul_mul, CStarMatrix.mul_smul, smul_smul, mul_one]
  rw [hscalar, hscalar']
  module

/-- Weighted trace intertwines the concrete Kraus transfer with its dual action. -/
private theorem weighted_trace_finiteKrausMap
    {ι : Type*} [Fintype ι]
    (A : ι → CStarMatrix (Fin D) (Fin D) ℂ)
    (ρ X : CStarMatrix (Fin D) (Fin D) ℂ) :
    (ρ * finiteKrausMap A X).trace =
      ((∑ σ, star (A σ) * ρ * A σ) * X).trace := by
  change (ρ * ∑ σ, A σ * X * star (A σ)).trace =
    ((∑ σ, star (A σ) * ρ * A σ) * X).trace
  rw [Finset.mul_sum, Finset.sum_mul]
  change (Matrix.traceLinearMap (Fin D) ℂ ℂ)
      (∑ σ, ρ * (A σ * X * star (A σ))) =
    (Matrix.traceLinearMap (Fin D) ℂ ℂ)
      (∑ σ, (star (A σ) * ρ * A σ) * X)
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  calc
    (ρ * (A σ * X * star (A σ))).trace =
        ((ρ * A σ) * X * star (A σ)).trace := by
      congr 1
      noncomm_ring
    _ = (star (A σ) * (ρ * A σ) * X).trace :=
      Matrix.trace_mul_cycle (ρ * A σ) X (star (A σ))
    _ = ((star (A σ) * ρ * A σ) * X).trace := by
      congr 1
      noncomm_ring

/-- Faithful dual invariance forces every peripheral Kraus defect to vanish. -/
private theorem krausPeripheralDefect_eq_zero [NeZero D]
    {ι : Type*} [Fintype ι]
    (A : ι → CStarMatrix (Fin D) (Fin D) ℂ)
    (ρ X : CStarMatrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hunital : finiteKrausMap A 1 = 1)
    (hρ : ρ.PosDef)
    (hdual : ∑ σ, star (A σ) * ρ * A σ = ρ)
    (heig : finiteKrausMap A X = μ • X) (hμ : ‖μ‖ = 1) :
    ∀ σ, krausPeripheralDefect (A σ) X μ = 0 := by
  let Y := finiteKrausMap A (X * star X) - X * star X
  have hsum :
      (∑ σ, krausPeripheralDefect (A σ) X μ *
        star (krausPeripheralDefect (A σ) X μ)) = Y :=
    sum_krausPeripheralDefect_mul_star A X μ hunital heig hμ
  have hYpsd : Y.PosSemidef := by
    rw [← hsum]
    exact Matrix.posSemidef_sum Finset.univ fun σ _ =>
      Matrix.posSemidef_self_mul_conjTranspose
        (krausPeripheralDefect (A σ) X μ)
  have hinvariant :
      (ρ * finiteKrausMap A (X * star X)).trace =
        (ρ * (X * star X)).trace := by
    rw [weighted_trace_finiteKrausMap, hdual]
  have hYtrace : (ρ * Y).trace = 0 := by
    change (ρ *
      (finiteKrausMap A (X * star X) - X * star X)).trace = 0
    rw [show ρ * (finiteKrausMap A (X * star X) - X * star X) =
        ρ * finiteKrausMap A (X * star X) - ρ * (X * star X) by
          noncomm_ring]
    change ∑ i, (ρ * finiteKrausMap A (X * star X) -
      ρ * (X * star X)) i i = 0
    simp only [CStarMatrix.sub_apply, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hinvariant
  have hYzero : Y = 0 :=
    eq_zero_of_posSemidef_of_trace_mul_posDef_eq_zero hρ hYpsd hYtrace
  exact eq_zero_of_sum_mul_star_eq_zero
    (fun σ => krausPeripheralDefect (A σ) X μ) (hsum.trans hYzero)

/-- Each Kraus matrix intertwines a peripheral eigenmatrix with its phase. -/
private theorem kraus_mul_eigenvector_eq_smul
    [NeZero D] {ι : Type*} [Fintype ι]
    (A : ι → CStarMatrix (Fin D) (Fin D) ℂ)
    (ρ X : CStarMatrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hunital : finiteKrausMap A 1 = 1)
    (hρ : ρ.PosDef)
    (hdual : ∑ σ, star (A σ) * ρ * A σ = ρ)
    (heig : finiteKrausMap A X = μ • X) (hμ : ‖μ‖ = 1) :
    ∀ σ, A σ * X = μ • (X * A σ) := by
  intro σ
  exact sub_eq_zero.mp
    (krausPeripheralDefect_eq_zero A ρ X μ hunital hρ hdual heig hμ σ)

/-- Letter intertwining propagates to every existing MPS ordered product. -/
private theorem orderedProd_mul_eigenvector
    (A : MPSMatrices D N) (X : Matrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hletter : ∀ σ, A σ * X = μ • (X * A σ)) :
    ∀ σs : List (Fin (N + 1)),
      orderedProd A σs * X =
        μ ^ σs.length • (X * orderedProd A σs) := by
  intro σs
  induction σs with
  | nil => simp [orderedProd]
  | cons σ σs ih =>
      rw [orderedProd, mul_assoc, ih, Matrix.mul_smul, ← mul_assoc, hletter]
      simp only [Matrix.smul_mul, smul_smul, List.length_cons]
      rw [pow_succ, mul_assoc]

/-- Fixed-length word intertwining extends linearly to every square matrix. -/
private theorem all_matrix_mul_eigenvector_of_mpsProductsSpanAt
    (A : MPSMatrices D N) (X : Matrix (Fin D) (Fin D) ℂ)
    (μ : ℂ) (n : ℕ) (hspan : mpsProductsSpanAt A n)
    (hword : ∀ σs : List (Fin (N + 1)), σs.length = n →
      orderedProd A σs * X = μ ^ n • (X * orderedProd A σs)) :
    ∀ M : Matrix (Fin D) (Fin D) ℂ,
      M * X = μ ^ n • (X * M) := by
  intro M
  unfold mpsProductsSpanAt at hspan
  have hM : M ∈ Submodule.span ℂ {P : Matrix (Fin D) (Fin D) ℂ |
      ∃ σs : List (Fin (N + 1)), σs.length = n ∧ P = orderedProd A σs} := by
    rw [hspan]
    trivial
  induction hM using Submodule.span_induction with
  | mem P hP =>
      obtain ⟨σs, hlen, rfl⟩ := hP
      exact hword σs hlen
  | zero => simp
  | add M₁ M₂ _ _ h₁ h₂ =>
      simp only [add_mul, mul_add, h₁, h₂, smul_add]
  | smul c M _ hM =>
      simp only [Matrix.smul_mul, Matrix.mul_smul, hM, smul_smul]
      module

/-- A square matrix commuting with every square matrix is scalar. -/
private theorem eq_smul_one_of_mul_eq_mul_all [NeZero D]
    (X : Matrix (Fin D) (Fin D) ℂ)
    (hcomm : ∀ M : Matrix (Fin D) (Fin D) ℂ, M * X = X * M) :
    ∃ c : ℂ, X = c • 1 := by
  let k : Fin D := 0
  have hoff : ∀ i j : Fin D, i ≠ j → X i j = 0 := by
    intro i j hij
    have h := congrFun (congrFun (hcomm (Matrix.single i i 1)) i) j
    simpa [Matrix.mul_apply, Matrix.single_apply, hij] using h
  have hdiag : ∀ i : Fin D, X i i = X k k := by
    intro i
    have h := congrFun (congrFun (hcomm (Matrix.single i k 1)) i) k
    simpa [Matrix.mul_apply, Matrix.single_apply] using h.symm
  refine ⟨X k k, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    rw [hdiag]
    simp [Matrix.smul_apply]
  · rw [hoff i j hij]
    simp [Matrix.smul_apply, hij]

/-- A nonzero peripheral eigenmatrix is scalar and its eigenvalue is one. -/
private theorem peripheral_eigenvector_eq_smul_one_and_eigenvalue_eq_one
    [NeZero D]
    (A : MPSMatrices D N)
    (ρ X : CStarMatrix (Fin D) (Fin D) ℂ) (μ : ℂ) (n : ℕ)
    (hunital : finiteKrausMap A 1 = 1)
    (hρ : ρ.PosDef)
    (hdual : ∑ σ,
      star (CStarMatrix.ofMatrix (A σ)) * ρ *
        CStarMatrix.ofMatrix (A σ) = ρ)
    (hspan : mpsProductsSpanAt A n)
    (heig : finiteKrausMap A X = μ • X)
    (hX : X ≠ 0) (hμ : ‖μ‖ = 1) :
    μ = 1 ∧ ∃ c : ℂ, X = c • 1 := by
  have hletter := kraus_mul_eigenvector_eq_smul
    A ρ X μ hunital hρ hdual heig hμ
  have hword : ∀ σs : List (Fin (N + 1)), σs.length = n →
      orderedProd A σs * CStarMatrix.ofMatrix.symm X =
        μ ^ n • (CStarMatrix.ofMatrix.symm X * orderedProd A σs) := by
    intro σs hlen
    have h := orderedProd_mul_eigenvector A
      (CStarMatrix.ofMatrix.symm X) μ
      (fun σ => congrArg CStarMatrix.ofMatrix.symm (hletter σ)) σs
    simpa [hlen] using h
  have hall := all_matrix_mul_eigenvector_of_mpsProductsSpanAt
    A (CStarMatrix.ofMatrix.symm X) μ n hspan hword
  have hpow : μ ^ n = 1 := by
    have hI := hall (1 : Matrix (Fin D) (Fin D) ℂ)
    simp only [one_mul, mul_one] at hI
    have hz : (μ ^ n - 1) • CStarMatrix.ofMatrix.symm X = 0 := by
      calc
        (μ ^ n - 1) • CStarMatrix.ofMatrix.symm X =
            μ ^ n • CStarMatrix.ofMatrix.symm X -
              CStarMatrix.ofMatrix.symm X := by module
        _ = CStarMatrix.ofMatrix.symm X -
              CStarMatrix.ofMatrix.symm X := by rw [← hI]
        _ = 0 := sub_self _
    rcases smul_eq_zero.mp hz with hs | hzero
    · exact sub_eq_zero.mp hs
    · exact (hX (CStarMatrix.ofMatrix.symm.injective hzero)).elim
  have hcomm : ∀ M : Matrix (Fin D) (Fin D) ℂ,
      M * CStarMatrix.ofMatrix.symm X =
        CStarMatrix.ofMatrix.symm X * M := by
    intro M
    simpa [hpow] using hall M
  obtain ⟨c, hc⟩ :=
    eq_smul_one_of_mul_eq_mul_all (CStarMatrix.ofMatrix.symm X) hcomm
  have hc' : X = c • 1 := CStarMatrix.ofMatrix.symm.injective hc
  have hcne : c ≠ 0 := by
    intro hc0
    apply hX
    simpa [hc0] using hc'
  have heig' := heig
  rw [hc'] at heig'
  change finiteKrausMap A (c • 1) = μ • (c • 1) at heig'
  rw [map_smul, hunital] at heig'
  have hscalar : (1 - μ) * c = 0 := by
    have hentry := congrFun (congrFun heig' (0 : Fin D)) (0 : Fin D)
    have hentry' : c = μ * c := by
      simpa [CStarMatrix.smul_apply, CStarMatrix.one_apply, smul_smul] using hentry
    calc
      (1 - μ) * c = c - μ * c := by ring
      _ = 0 := sub_eq_zero.mpr hentry'
  have hμone : μ = 1 := by
    rcases mul_eq_zero.mp hscalar with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact (hcne h).elim
  exact ⟨hμone, c, hc'⟩

/-- The unit eigenvalue of a spanning faithful Kraus transfer has a one-dimensional eigenspace. -/
private theorem finrank_eigenspace_one_finiteKrausMap [NeZero D]
    (A : MPSMatrices D N)
    (ρ : CStarMatrix (Fin D) (Fin D) ℂ) (n : ℕ)
    (hunital : finiteKrausMap A 1 = 1)
    (hρ : ρ.PosDef)
    (hdual : ∑ σ,
      star (CStarMatrix.ofMatrix (A σ)) * ρ *
        CStarMatrix.ofMatrix (A σ) = ρ)
    (hspan : mpsProductsSpanAt A n) :
    finrank ℂ (Module.End.eigenspace (finiteKrausMap A) 1) = 1 := by
  have heq : Module.End.eigenspace (finiteKrausMap A) 1 =
      ℂ ∙ (1 : CStarMatrix (Fin D) (Fin D) ℂ) := by
    ext X
    constructor
    · intro hX
      have heig : finiteKrausMap A X = (1 : ℂ) • X :=
        Module.End.mem_eigenspace_iff.mp hX
      by_cases hzero : X = 0
      · subst X
        exact Submodule.zero_mem _
      · obtain ⟨_, c, hc⟩ :=
          peripheral_eigenvector_eq_smul_one_and_eigenvalue_eq_one
            A ρ X 1 n hunital hρ hdual hspan heig hzero (by simp)
        exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
    · intro hX
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hX
      rw [Module.End.mem_eigenspace_iff, map_smul, hunital, one_smul]
  rw [heq]
  exact finrank_span_singleton one_ne_zero

/-- Every nonunit spectral value of a spanning faithful Kraus transfer lies in the open disk. -/
private theorem norm_lt_one_of_mem_spectrum_of_ne_one [NeZero D]
    (A : MPSMatrices D N)
    (ρ : CStarMatrix (Fin D) (Fin D) ℂ) (n : ℕ)
    (hunital : finiteKrausMap A 1 = 1)
    (hρ : ρ.PosDef)
    (hdual : ∑ σ,
      star (CStarMatrix.ofMatrix (A σ)) * ρ *
        CStarMatrix.ofMatrix (A σ) = ρ)
    (hspan : mpsProductsSpanAt A n)
    {μ : ℂ} (hμspec : μ ∈ spectrum ℂ (finiteKrausMap A))
    (hμne : μ ≠ 1) :
    ‖μ‖ < 1 := by
  have hle := norm_spectrum_finiteKrausMap_le_one A hunital hμspec
  by_contra hnot
  have hnorm : ‖μ‖ = 1 := le_antisymm hle (not_lt.mp hnot)
  obtain ⟨X, hX⟩ :=
    (Module.End.HasEigenvalue.of_mem_spectrum hμspec).exists_hasEigenvector
  have hperipheral :=
    peripheral_eigenvector_eq_smul_one_and_eigenvalue_eq_one
      A ρ X μ n hunital hρ hdual hspan hX.apply_eq_smul hX.2 hnorm
  exact hμne hperipheral.1

/-- Unit primitive-spectrum data for the concrete finite Kraus endomorphism. -/
private theorem finiteKrausMap_has_unit_primitive_spectrum [NeZero D]
    (A : MPSMatrices D N)
    (ρ : CStarMatrix (Fin D) (Fin D) ℂ) (n : ℕ)
    (hunital : finiteKrausMap A 1 = 1)
    (hρ : ρ.PosDef)
    (hdual : ∑ σ,
      star (CStarMatrix.ofMatrix (A σ)) * ρ *
        CStarMatrix.ofMatrix (A σ) = ρ)
    (hspan : mpsProductsSpanAt A n) :
    (1 : ℂ) ∈ spectrum ℂ (finiteKrausMap A) ∧
      finrank ℂ (Module.End.eigenspace (finiteKrausMap A) 1) = 1 ∧
      ∀ μ : ℂ, μ ∈ spectrum ℂ (finiteKrausMap A) →
        μ ≠ 1 → ‖μ‖ < 1 := by
  have honevec : (finiteKrausMap A).HasEigenvector 1 1 :=
    ⟨Module.End.mem_eigenspace_iff.mpr (by simpa using hunital), one_ne_zero⟩
  refine ⟨(Module.End.hasEigenvalue_of_hasEigenvector honevec).mem_spectrum,
    finrank_eigenspace_one_finiteKrausMap A ρ n hunital hρ hdual hspan, ?_⟩
  intro μ hμ hμne
  exact norm_lt_one_of_mem_spectrum_of_ne_one
    A ρ n hunital hρ hdual hspan hμ hμne

/-- Transpose-vectorization identifies square `CStarMatrix` values with transfer vectors. -/
private noncomputable def vecTransposeLinearEquiv :
    CStarMatrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] ((Fin D × Fin D) → ℂ) where
  toFun X p := X p.2 p.1
  invFun v := CStarMatrix.ofMatrix fun i j => v (j, i)
  left_inv X := by ext i j; rfl
  right_inv v := by ext p; rfl
  map_add' X Y := by ext p; rfl
  map_smul' c X := by ext p; rfl

/-- The MPS transfer matrix intertwines transpose-vectorization with the finite Kraus map. -/
private theorem mpsTransferMatrix_mulVec_vecTranspose
    (A : MPSMatrices D N) (X : CStarMatrix (Fin D) (Fin D) ℂ) :
    (mpsTransferMatrix A).mulVec (vecTransposeLinearEquiv X) =
      vecTransposeLinearEquiv (finiteKrausMap A X) := by
  ext p
  simp only [mpsTransferMatrix, Matrix.mulVec, dotProduct, vecTransposeLinearEquiv,
    LinearEquiv.coe_mk, Matrix.of_apply, Fintype.sum_prod_type,
    finiteKrausMap, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [Finset.sum_mul]
  calc
    (∑ α' : Fin D, ∑ β' : Fin D, ∑ σ : Fin (N + 1),
        star (A σ p.1 α') * A σ p.2 β' * X β' α') =
        ∑ α' : Fin D, ∑ σ : Fin (N + 1), ∑ β' : Fin D,
          star (A σ p.1 α') * A σ p.2 β' * X β' α' := by
      apply Finset.sum_congr rfl
      intro α' _
      exact Finset.sum_comm
    _ = ∑ σ : Fin (N + 1), ∑ α' : Fin D, ∑ β' : Fin D,
        star (A σ p.1 α') * A σ p.2 β' * X β' α' := Finset.sum_comm
    _ = ∑ σ : Fin (N + 1), ∑ α' : Fin D, ∑ β' : Fin D,
        A σ p.2 β' * X β' α' * star (A σ p.1 α') := by
      congr 1
      funext σ
      congr 1
      funext α'
      congr 1
      funext β'
      ring
    _ = (∑ σ : Fin (N + 1),
        CStarMatrix.ofMatrix (A σ) * X *
          star (CStarMatrix.ofMatrix (A σ))) p.2 p.1 := by
      rw [cstarMatrix_univ_sum_apply]
      simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply,
        CStarMatrix.ofMatrix_apply]
      simp_rw [Finset.sum_mul]

/-- Conjugating the finite Kraus map by transpose-vectorization gives transfer multiplication. -/
private theorem conj_finiteKrausMap_eq_mulVecLin (A : MPSMatrices D N) :
    (vecTransposeLinearEquiv (D := D)).conjAlgEquiv ℂ (finiteKrausMap A) =
      (mpsTransferMatrix A).mulVecLin := by
  apply LinearMap.ext
  intro v
  obtain ⟨X, rfl⟩ := (vecTransposeLinearEquiv (D := D)).surjective v
  simp only [LinearEquiv.conjAlgEquiv_apply, LinearMap.coe_comp,
    Function.comp_apply]
  simpa using (mpsTransferMatrix_mulVec_vecTranspose A X).symm

/-- Similarity makes the concrete Kraus map and the repository transfer matrix isospectral. -/
private theorem spectrum_mpsTransferMatrix_eq_finiteKrausMap
    (A : MPSMatrices D N) :
    spectrum ℂ (mpsTransferMatrix A) =
      spectrum ℂ (finiteKrausMap A) := by
  rw [← Matrix.spectrum_toLin']
  change spectrum ℂ (mpsTransferMatrix A).mulVecLin =
    spectrum ℂ (finiteKrausMap A)
  rw [← conj_finiteKrausMap_eq_mulVecLin A]
  exact AlgEquiv.spectrum_eq
    ((vecTransposeLinearEquiv (D := D)).conjAlgEquiv ℂ) (finiteKrausMap A)

/-- Transpose-vectorization transports each Kraus eigenspace to the transfer eigenspace. -/
private noncomputable def eigenspaceFiniteKrausMapEquivTransfer
    (A : MPSMatrices D N) (μ : ℂ) :
    Module.End.eigenspace (finiteKrausMap A) μ ≃ₗ[ℂ]
      Module.End.eigenspace (mpsTransferMatrix A).mulVecLin μ where
  toFun X := ⟨vecTransposeLinearEquiv X, by
    rw [Module.End.mem_eigenspace_iff]
    change (mpsTransferMatrix A).mulVec (vecTransposeLinearEquiv X) =
      μ • vecTransposeLinearEquiv X
    calc
      _ = vecTransposeLinearEquiv (finiteKrausMap A X) :=
        mpsTransferMatrix_mulVec_vecTranspose A X
      _ = vecTransposeLinearEquiv
          (μ • (X : CStarMatrix (Fin D) (Fin D) ℂ)) := by
        rw [Module.End.mem_eigenspace_iff.mp X.property]
      _ = μ • vecTransposeLinearEquiv X := map_smul _ _ _⟩
  invFun v := ⟨(vecTransposeLinearEquiv (D := D)).symm v, by
    rw [Module.End.mem_eigenspace_iff]
    apply (vecTransposeLinearEquiv (D := D)).injective
    rw [map_smul]
    rw [← mpsTransferMatrix_mulVec_vecTranspose]
    simpa using Module.End.mem_eigenspace_iff.mp v.property⟩
  left_inv X := by
    apply Subtype.ext
    exact (vecTransposeLinearEquiv (D := D)).symm_apply_apply X
  right_inv v := by
    apply Subtype.ext
    exact (vecTransposeLinearEquiv (D := D)).apply_symm_apply v
  map_add' X Y := by ext p; rfl
  map_smul' c X := by ext p; rfl

/-- Unit normalization, a faithful dual fixed point, and eventual word spanning imply the
primitive transfer spectrum in the forward direction of Tasaki Theorem 7.5. -/
theorem has_primitive_transfer_spectrum_of_unit_faithful_spanning [NeZero D]
    (A : MPSMatrices D N)
    (hnorm : IsMPSNormalized A 1)
    (hfaith : HasFaithfulDualEigenmatrix A 1)
    (hspan : MPSSpansForAllLarge A) :
    HasPrimitiveTransferSpectrum A 1 := by
  obtain ⟨n, hn⟩ := hspan
  obtain ⟨ρ, hρ, hdual⟩ := hfaith
  let ρc : CStarMatrix (Fin D) (Fin D) ℂ := CStarMatrix.ofMatrix ρ
  have hunital : finiteKrausMap A 1 = 1 := by
    apply CStarMatrix.ofMatrix.injective
    simpa [finiteKrausMap] using hnorm.2
  have hρc : ρc.PosDef := hρ
  have hdualc :
      (∑ σ,
        star (CStarMatrix.ofMatrix (A σ)) * ρc *
          CStarMatrix.ofMatrix (A σ)) = ρc := by
    apply CStarMatrix.ofMatrix.injective
    simpa [ρc, mpsDualTransferMap] using hdual
  obtain ⟨hone, hfinrank, hgap⟩ :=
    finiteKrausMap_has_unit_primitive_spectrum
      A ρc n hunital hρc hdualc (hn n le_rfl)
  unfold HasPrimitiveTransferSpectrum
  refine ⟨?_, ?_, ?_⟩
  · rwa [spectrum_mpsTransferMatrix_eq_finiteKrausMap]
  · have hcast : ((1 : ℝ) : ℂ) = (1 : ℂ) := by norm_num
    rw [hcast]
    have htransport := LinearEquiv.finrank_eq
      (eigenspaceFiniteKrausMapEquivTransfer A 1)
    rw [hfinrank] at htransport
    have hker :
        LinearMap.ker ((mpsTransferMatrix A).mulVecLin -
          (1 : ℂ) • LinearMap.id) =
            Module.End.eigenspace (mpsTransferMatrix A).mulVecLin 1 := by
      ext v
      rw [LinearMap.mem_ker, Module.End.mem_eigenspace_iff]
      simp only [one_smul, LinearMap.sub_apply, Matrix.mulVecBilin_apply,
        LinearMap.id_coe, id_eq, sub_eq_zero]
    rw [hker]
    exact htransport.symm
  · intro μ hμ hμne
    exact hgap μ
      (spectrum_mpsTransferMatrix_eq_finiteKrausMap A ▸ hμ) hμne

end Internal

end MPSTheorem75

end Quantum

end LatticeSystem
