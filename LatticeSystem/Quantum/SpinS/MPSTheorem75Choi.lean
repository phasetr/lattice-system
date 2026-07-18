import LatticeSystem.Quantum.SpinS.MPSTheorem75Linear
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# Choi and word-span substrate for Tasaki Theorem 7.5

This file proves the reverse, faithful spectral-gap-to-word-span route for the corrected Tasaki
Theorem 7.5. It expands finite Kraus powers into fixed-length words, identifies Choi positivity
with word spanning, and transports the faithful weighted-trace power limit to eventual MPS
spanning. All Choi and span helpers remain private.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.2.2, Theorem 7.5, eqs. (7.2.41)–(7.2.42), pp. 202–203.
-/

namespace LatticeSystem.Quantum.MPSTheorem75.Internal

open Filter Matrix Module
open scoped CStarAlgebra ComplexOrder Topology

variable {D N : ℕ}

/-! ## Kraus words and Choi positivity -/

/-- Evaluation commutes with finite sums of `CStarMatrix` values. -/
private theorem cstarMatrix_sum_apply {ι : Type*} (s : Finset ι)
    (B : ι → CStarMatrix (Fin D) (Fin D) ℂ) (i j : Fin D) :
    (∑ σ ∈ s, B σ) i j = ∑ σ ∈ s, B σ i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [CStarMatrix.zero_apply]
  | insert a s ha ih => simp [ha, ih, CStarMatrix.add_apply]

/-- The matrix unit with its row and column encoded by two indices. -/
private def matrixUnit (i j : Fin D) : CStarMatrix (Fin D) (Fin D) ℂ :=
  Matrix.single i j 1

/-- The Choi convention `J(F)_(a,i),(b,j) = F(Eᵢⱼ)_(a,b)`. -/
private noncomputable def customChoi
    (F : Module.End ℂ (CStarMatrix (Fin D) (Fin D) ℂ)) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  fun p q => F (matrixUnit p.2 q.2) p.1 q.1

/-- Row-first vectorization used by the Choi convention. -/
private def krausVec (A : CStarMatrix (Fin D) (Fin D) ℂ) :
    (Fin D × Fin D) → ℂ :=
  fun p => A p.1 p.2

/-- Split a nonempty dependent word into its first letter and remaining tail. -/
private def wordSuccEquiv {ι : Type*} (n : ℕ) :
    (Fin (n + 1) → ι) ≃ ι × (Fin n → ι) where
  toFun w := (w 0, fun i => w i.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv w := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv p := by
    apply Prod.ext
    · simp
    · funext i
      simp

/-- The ordered product of a fixed-length Kraus word. -/
private noncomputable def krausWordProduct {ι : Type*}
    (A : ι → CStarMatrix (Fin D) (Fin D) ℂ) {n : ℕ} (w : Fin n → ι) :
    CStarMatrix (Fin D) (Fin D) ℂ :=
  (List.ofFn fun i => A (w i)).prod

/-- A nonempty ordered Kraus word is its head matrix times its tail product. -/
private theorem krausWordProduct_succ {ι : Type*}
    (A : ι → CStarMatrix (Fin D) (Fin D) ℂ)
    {n : ℕ} (w : Fin (n + 1) → ι) :
    krausWordProduct A w =
      A (w 0) * krausWordProduct A (fun i => w i.succ) := by
  simp [krausWordProduct, List.ofFn_succ]

/-- Composition of finite Kraus maps uses the outer-inner product family. -/
private theorem finiteKrausMap_mul
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → CStarMatrix (Fin D) (Fin D) ℂ)
    (B : κ → CStarMatrix (Fin D) (Fin D) ℂ) :
    finiteKrausMap A * finiteKrausMap B =
      finiteKrausMap (fun p : ι × κ => A p.1 * B p.2) := by
  apply LinearMap.ext
  intro X
  change (∑ a, A a * (∑ b, B b * X * star (B b)) * star (A a)) =
    ∑ p : ι × κ, (A p.1 * B p.2) * X * star (A p.1 * B p.2)
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [star_mul]
  noncomm_ring

/-- Reindexing a finite Kraus family along an equivalence leaves its map unchanged. -/
private theorem finiteKrausMap_reindex
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (A : κ → CStarMatrix (Fin D) (Fin D) ℂ) :
    finiteKrausMap (fun i => A (e i)) = finiteKrausMap A := by
  apply LinearMap.ext
  intro X
  change (∑ i, A (e i) * X * star (A (e i))) =
    ∑ k, A k * X * star (A k)
  exact Fintype.sum_equiv e _ _ fun _ => rfl

/-- The `n`th finite Kraus power is represented by all ordered words of length `n`. -/
private theorem finiteKrausMap_pow {ι : Type*} [Fintype ι]
    (A : ι → CStarMatrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    finiteKrausMap A ^ n =
      finiteKrausMap (fun w : Fin n → ι => krausWordProduct A w) := by
  induction n with
  | zero =>
      ext X
      simp [finiteKrausMap, krausWordProduct]
  | succ n ih =>
      rw [pow_succ', ih, finiteKrausMap_mul]
      calc
        finiteKrausMap
              (fun p : ι × (Fin n → ι) =>
                A p.1 * krausWordProduct A p.2) =
            finiteKrausMap
              (fun w : Fin (n + 1) → ι =>
                A ((wordSuccEquiv n w).1) *
                  krausWordProduct A ((wordSuccEquiv n w).2)) :=
          (finiteKrausMap_reindex (wordSuccEquiv n)
            (fun p : ι × (Fin n → ι) =>
              A p.1 * krausWordProduct A p.2)).symm
        _ = finiteKrausMap
              (fun w : Fin (n + 1) → ι => krausWordProduct A w) := by
          apply congrArg finiteKrausMap
          funext w
          exact (krausWordProduct_succ A w).symm

/-- The Choi matrix of a finite Kraus map is its vectorized Gram sum. -/
private theorem customChoi_finiteKrausMap
    {ι : Type*} [Fintype ι]
    (A : ι → CStarMatrix (Fin D) (Fin D) ℂ) :
    customChoi (finiteKrausMap A) =
      ∑ σ, Matrix.vecMulVec (krausVec (A σ)) (star (krausVec (A σ))) := by
  ext p q
  simp only [customChoi, Matrix.sum_apply, Matrix.vecMulVec_apply, krausVec]
  rw [show finiteKrausMap A (matrixUnit p.2 q.2) =
    ∑ σ, A σ * matrixUnit p.2 q.2 * star (A σ) by rfl]
  change (∑ σ, A σ * matrixUnit p.2 q.2 * star (A σ)) p.1 q.1 =
    ∑ σ, A σ p.1 p.2 * star (A σ q.1 q.2)
  rw [show (∑ σ, A σ * matrixUnit p.2 q.2 * star (A σ)) p.1 q.1 =
    ∑ σ, (A σ * matrixUnit p.2 q.2 * star (A σ)) p.1 q.1 by
      simpa using cstarMatrix_sum_apply Finset.univ
        (fun σ => A σ * matrixUnit p.2 q.2 * star (A σ)) p.1 q.1]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [CStarMatrix.mul_apply, matrixUnit, CStarMatrix.star_apply]
  classical
  rw [Finset.sum_eq_single q.2]
  · rw [Finset.sum_eq_single p.2]
    · simp
    · intro b _ hb
      rw [Matrix.single_apply]
      split_ifs with heq
      · exact (hb heq.1.symm).elim
      · simp
    · simp
  · intro b _ hb
    have hz : ∑ j, A σ p.1 j * Matrix.single p.2 q.2 1 j b = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [Matrix.single_apply]
      split_ifs with heq
      · exact (hb heq.2.symm).elim
      · simp
    rw [hz, zero_mul]
  · simp

/-- Every finite Kraus Choi matrix is positive semidefinite. -/
private theorem customChoi_finiteKrausMap_posSemidef
    {ι : Type*} [Fintype ι]
    (A : ι → CStarMatrix (Fin D) (Fin D) ℂ) :
    (customChoi (finiteKrausMap A)).PosSemidef := by
  rw [customChoi_finiteKrausMap]
  simpa using Matrix.posSemidef_sum Finset.univ fun σ _ =>
    Matrix.posSemidef_vecMulVec_self_star (krausVec (A σ))

/-- Every actual finite Kraus power has a positive-semidefinite Choi matrix. -/
private theorem customChoi_finiteKrausMap_pow_posSemidef
    {ι : Type*} [Fintype ι]
    (A : ι → CStarMatrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    (customChoi (finiteKrausMap A ^ n)).PosSemidef := by
  rw [finiteKrausMap_pow]
  exact customChoi_finiteKrausMap_posSemidef _

/-! ## Faithful rank-one Choi limit -/

/-- The faithful weighted-trace rank-one limit map. -/
private noncomputable def traceLimitMap
    (ρ : CStarMatrix (Fin D) (Fin D) ℂ) :
    Module.End ℂ (CStarMatrix (Fin D) (Fin D) ℂ) :=
  (((ρ.trace)⁻¹ •
    (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
      (LinearMap.mulLeft ℂ ρ)).smulRight 1)

/-- Evaluation formula for the faithful weighted-trace limit map. -/
private theorem traceLimitMap_apply
    (ρ X : CStarMatrix (Fin D) (Fin D) ℂ) :
    traceLimitMap ρ X = ((ρ.trace)⁻¹ * (ρ * X).trace) • 1 := by
  rfl

/-- The limit Choi matrix is `(tr ρ)⁻¹ • (I ⊗ ρᵀ)`. -/
private theorem customChoi_traceLimitMap
    (ρ : CStarMatrix (Fin D) (Fin D) ℂ) :
    customChoi (traceLimitMap ρ) =
      (ρ.trace)⁻¹ • Matrix.kronecker
        (1 : Matrix (Fin D) (Fin D) ℂ) ρ.transpose := by
  ext p q
  have ht : (ρ * matrixUnit p.2 q.2).trace = ρ q.2 p.2 := by
    simpa [matrixUnit] using Matrix.trace_mul_single ρ p.2 q.2 1
  change traceLimitMap ρ (matrixUnit p.2 q.2) p.1 q.1 =
    ((ρ.trace)⁻¹ • Matrix.kronecker
      (1 : Matrix (Fin D) (Fin D) ℂ) ρ.transpose) p q
  rw [traceLimitMap_apply, ht]
  simp only [CStarMatrix.smul_apply, Matrix.smul_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, smul_eq_mul]
  by_cases h : p.1 = q.1
  · rw [show (1 : CStarMatrix (Fin D) (Fin D) ℂ) p.1 q.1 = 1 by
      rw [CStarMatrix.one_apply]
      simp [h]]
    rw [show (1 : Matrix (Fin D) (Fin D) ℂ) p.1 q.1 = 1 by
      exact if_pos h]
    rw [show ρ.transpose p.2 q.2 = ρ q.2 p.2 by rfl]
    change (ρ.trace)⁻¹ * ρ q.2 p.2 * 1 =
      (ρ.trace)⁻¹ * (1 * ρ q.2 p.2)
    ring
  · rw [show (1 : CStarMatrix (Fin D) (Fin D) ℂ) p.1 q.1 = 0 by
      rw [CStarMatrix.one_apply]
      simp [h]]
    rw [show (1 : Matrix (Fin D) (Fin D) ℂ) p.1 q.1 = 0 by
      exact if_neg h]
    simp

/-- A faithful dual matrix makes the limit Choi matrix positive definite. -/
private theorem customChoi_traceLimitMap_posDef [NeZero D]
    {ρ : CStarMatrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef) :
    (customChoi (traceLimitMap ρ)).PosDef := by
  rw [customChoi_traceLimitMap]
  exact (Matrix.PosDef.one.kronecker hρ.transpose).smul
    (inv_pos.mpr hρ.trace_pos)

/-- Choi formation as a linear map on continuous endomorphisms. -/
private noncomputable def choiLinear :
    (CStarMatrix (Fin D) (Fin D) ℂ →L[ℂ]
      CStarMatrix (Fin D) (Fin D) ℂ) →ₗ[ℂ]
        CStarMatrix (Fin D × Fin D) (Fin D × Fin D) ℂ where
  toFun F := CStarMatrix.ofMatrix (customChoi F.toLinearMap)
  map_add' F G := by
    ext p q
    rfl
  map_smul' c F := by
    ext p q
    rfl

/-- Operator-norm convergence implies convergence of Choi matrices. -/
private theorem tendsto_choiLinear
    [FiniteDimensional ℂ (CStarMatrix (Fin D) (Fin D) ℂ)]
    {F : ℕ → CStarMatrix (Fin D) (Fin D) ℂ →L[ℂ]
      CStarMatrix (Fin D) (Fin D) ℂ}
    {L : CStarMatrix (Fin D) (Fin D) ℂ →L[ℂ]
      CStarMatrix (Fin D) (Fin D) ℂ}
    (hF : Tendsto F atTop (𝓝 L)) :
    Tendsto (fun n => choiLinear (F n)) atTop (𝓝 (choiLinear L)) :=
  (choiLinear (D := D)).continuous_of_finiteDimensional.tendsto L |>.comp hF

/-- A positive-semidefinite sequence converging to a positive-definite limit is eventually
positive definite. -/
private theorem eventually_posDef_of_tendsto_of_posSemidef
    {C : ℕ → CStarMatrix (Fin D × Fin D) (Fin D × Fin D) ℂ}
    {L : CStarMatrix (Fin D × Fin D) (Fin D × Fin D) ℂ}
    (hC : Tendsto C atTop (𝓝 L))
    (hPSD : ∀ n, (C n).PosSemidef) (hL : L.PosDef) :
    ∀ᶠ n in atTop, (C n).PosDef := by
  have hunit : ∀ᶠ n in atTop, IsUnit (C n) :=
    hC.eventually (Units.isOpen.mem_nhds hL.isUnit)
  filter_upwards [hunit] with n hn
  exact (hPSD n).posDef_iff_isUnit.mpr hn

/-- Convergence to the faithful trace limit makes actual power Choi matrices eventually positive
definite. -/
private theorem eventually_finiteKrausMap_pow_choi_posDef_of_traceLimit
    [NeZero D] [FiniteDimensional ℂ (CStarMatrix (Fin D) (Fin D) ℂ)]
    {ι : Type*} [Fintype ι]
    (A : ι → CStarMatrix (Fin D) (Fin D) ℂ)
    (ρ : CStarMatrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hlim : Tendsto
      (fun n : ℕ => Module.End.toContinuousLinearMap
        (CStarMatrix (Fin D) (Fin D) ℂ) (finiteKrausMap A ^ n))
      atTop
      (𝓝 (Module.End.toContinuousLinearMap
        (CStarMatrix (Fin D) (Fin D) ℂ) (traceLimitMap ρ)))) :
    ∀ᶠ n in atTop, (customChoi (finiteKrausMap A ^ n)).PosDef := by
  apply eventually_posDef_of_tendsto_of_posSemidef
    (tendsto_choiLinear hlim)
  · intro n
    change (customChoi (finiteKrausMap A ^ n)).PosSemidef
    exact customChoi_finiteKrausMap_pow_posSemidef A n
  · change (customChoi (traceLimitMap ρ)).PosDef
    exact customChoi_traceLimitMap_posDef hρ

/-! ## Choi positive definiteness and MPS word spanning -/

/-- The synthesis matrix whose columns are vectorized Kraus matrices. -/
private def krausSynthesisMatrix {ι : Type*}
    (K : ι → CStarMatrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D × Fin D) ι ℂ :=
  fun p σ => krausVec (K σ) p

/-- The Choi Gram sum is the synthesis matrix times its adjoint. -/
private theorem customChoi_finiteKrausMap_eq_synthesis_mul_conjTranspose
    {ι : Type*} [Fintype ι]
    (K : ι → CStarMatrix (Fin D) (Fin D) ℂ) :
    customChoi (finiteKrausMap K) =
      krausSynthesisMatrix K * (krausSynthesisMatrix K).conjTranspose := by
  rw [customChoi_finiteKrausMap]
  ext p q
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, krausSynthesisMatrix,
    krausVec, Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rfl

/-- A finite Kraus Choi matrix is positive definite exactly when its Kraus vectors span. -/
private theorem customChoi_finiteKrausMap_posDef_iff_span_krausVec
    {ι : Type*} [Fintype ι]
    (K : ι → CStarMatrix (Fin D) (Fin D) ℂ) :
    (customChoi (finiteKrausMap K)).PosDef ↔
      Submodule.span ℂ (Set.range fun σ => krausVec (K σ)) = ⊤ := by
  let B := krausSynthesisMatrix K
  have hgram :
      customChoi (finiteKrausMap K) = B * B.conjTranspose :=
    customChoi_finiteKrausMap_eq_synthesis_mul_conjTranspose K
  have hcols :
      Set.range B.col = Set.range fun σ => krausVec (K σ) := by
    rfl
  rw [hgram]
  have hPSD : (B * B.conjTranspose).PosSemidef := by
    rw [← hgram]
    exact customChoi_finiteKrausMap_posSemidef K
  rw [hPSD.posDef_iff_isUnit]
  constructor
  · intro hunit
    apply Submodule.eq_top_of_finrank_eq
    rw [← hcols, ← Matrix.rank_eq_finrank_span_cols]
    rw [← Matrix.rank_self_mul_conjTranspose B]
    simpa [Module.finrank_pi] using
      Matrix.rank_of_isUnit (B * B.conjTranspose) hunit
  · intro hspan
    apply Matrix.mulVec_surjective_iff_isUnit.mp
    change Function.Surjective (B * B.conjTranspose).mulVecLin
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    change (B * B.conjTranspose).rank =
      Module.finrank ℂ ((Fin D × Fin D) → ℂ)
    rw [Matrix.rank_self_mul_conjTranspose,
      Matrix.rank_eq_finrank_span_cols, hcols, hspan]
    simp

/-- Row-first vectorization as a complex-linear matrix equivalence. -/
private def matrixKrausVecLinearEquiv :
    Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] ((Fin D × Fin D) → ℂ) where
  toFun M := fun p => M p.1 p.2
  invFun v := fun i j => v (i, j)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

/-- Matrix spanning is equivalent to spanning by row-first vectorizations. -/
private theorem span_range_krausVec_eq_top_iff_span_range_matrix
    {ι : Type*} (K : ι → Matrix (Fin D) (Fin D) ℂ) :
    Submodule.span ℂ (Set.range fun σ => krausVec (K σ)) = ⊤ ↔
      Submodule.span ℂ (Set.range K) = ⊤ := by
  let e := matrixKrausVecLinearEquiv (D := D)
  have he :
      Submodule.map e.toLinearMap (Submodule.span ℂ (Set.range K)) =
        Submodule.span ℂ (Set.range fun σ => krausVec (K σ)) := by
    rw [Submodule.map_span]
    congr 1
    ext v
    constructor
    · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩
      exact ⟨σ, rfl⟩
    · rintro ⟨σ, rfl⟩
      exact ⟨K σ, ⟨σ, rfl⟩, rfl⟩
  constructor
  · intro hv
    apply (Submodule.map_injective_of_injective e.injective).eq_iff.mp
    rw [he, hv, Submodule.map_top, e.range]
  · intro hK
    rw [← he, hK, Submodule.map_top, e.range]

/-- Ordered Kraus words agree with the existing MPS ordered products. -/
private theorem krausWordProduct_eq_orderedProd
    (A : MPSMatrices D N) {n : ℕ} (w : Fin n → Fin (N + 1)) :
    CStarMatrix.ofMatrix.symm (krausWordProduct A w) =
      orderedProd A (List.ofFn w) := by
  induction n with
  | zero =>
      ext i j
      simp only [krausWordProduct, List.ofFn_zero, List.prod_nil,
        CStarMatrix.ofMatrix_symm_apply, orderedProd, CStarMatrix.one_apply,
        Matrix.one_apply]
  | succ n ih =>
      rw [krausWordProduct_succ, List.ofFn_succ]
      ext i j
      change
        (∑ k, A (w 0) i k *
          krausWordProduct A (fun i => w i.succ) k j) =
        ∑ k, A (w 0) i k *
          orderedProd A (List.ofFn fun i => w i.succ) k j
      apply Finset.sum_congr rfl
      intro k _
      rw [show krausWordProduct A (fun i => w i.succ) k j =
        orderedProd A (List.ofFn fun i => w i.succ) k j by
          exact congrFun (congrFun (ih (fun i => w i.succ)) k) j]

/-- Fixed-length Kraus words span exactly when `mpsProductsSpanAt` holds. -/
private theorem span_range_krausWordProduct_eq_top_iff_mpsProductsSpanAt
    (A : MPSMatrices D N) (n : ℕ) :
    Submodule.span ℂ
        (Set.range fun w : Fin n → Fin (N + 1) => krausWordProduct A w) = ⊤ ↔
      mpsProductsSpanAt A n := by
  unfold mpsProductsSpanAt
  have hsets :
      Set.range (fun w : Fin n → Fin (N + 1) => krausWordProduct A w) =
        {M : Matrix (Fin D) (Fin D) ℂ |
          ∃ σs : List (Fin (N + 1)),
            σs.length = n ∧ M = orderedProd A σs} := by
    ext M
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨List.ofFn w, by simp, ?_⟩
      change CStarMatrix.ofMatrix.symm (krausWordProduct A w) =
        orderedProd A (List.ofFn w)
      exact krausWordProduct_eq_orderedProd A w
    · rintro ⟨σs, hlen, rfl⟩
      subst n
      refine ⟨σs.get, ?_⟩
      change CStarMatrix.ofMatrix.symm (krausWordProduct A σs.get) =
        orderedProd A σs
      rw [krausWordProduct_eq_orderedProd, List.ofFn_get]
  rw [hsets]
  rfl

/-- Choi positive definiteness of the actual `n`th transfer power is equivalent to MPS spanning
at length `n`. -/
private theorem customChoi_finiteKrausMap_pow_posDef_iff_mpsProductsSpanAt
    (A : MPSMatrices D N) (n : ℕ) :
    (customChoi (finiteKrausMap A ^ n)).PosDef ↔
      mpsProductsSpanAt A n := by
  rw [finiteKrausMap_pow,
    customChoi_finiteKrausMap_posDef_iff_span_krausVec]
  exact (span_range_krausVec_eq_top_iff_span_range_matrix
    (fun w : Fin n → Fin (N + 1) => krausWordProduct A w)).trans
      (span_range_krausWordProduct_eq_top_iff_mpsProductsSpanAt A n)

/-- Faithful trace-limit convergence implies MPS spanning at every sufficiently large length. -/
private theorem mpsSpansForAllLarge_of_tendsto_traceLimit
    [NeZero D] [FiniteDimensional ℂ (CStarMatrix (Fin D) (Fin D) ℂ)]
    (A : MPSMatrices D N)
    (ρ : CStarMatrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hlim : Tendsto
      (fun n : ℕ => Module.End.toContinuousLinearMap
        (CStarMatrix (Fin D) (Fin D) ℂ) (finiteKrausMap A ^ n))
      atTop
      (𝓝 (Module.End.toContinuousLinearMap
        (CStarMatrix (Fin D) (Fin D) ℂ) (traceLimitMap ρ)))) :
    MPSSpansForAllLarge A := by
  have hev : ∀ᶠ n in atTop, mpsProductsSpanAt A n := by
    filter_upwards
      [eventually_finiteKrausMap_pow_choi_posDef_of_traceLimit A ρ hρ hlim]
        with n hn
    exact (customChoi_finiteKrausMap_pow_posDef_iff_mpsProductsSpanAt A n).mp hn
  exact Filter.eventually_atTop.1 hev

/-- A unit-normalized finite Kraus transfer with a faithful dual eigenmatrix, simple fixed
direction, and strict spectral gap spans at every sufficiently large word length.

This theorem-specific endpoint is consumed by the corrected Theorem 7.5 assembly in
`MPSTheorem75`. -/
theorem mps_spans_for_all_large_of_unit_faithful_spectral_gap [NeZero D]
    (A : MPSMatrices D N)
    (hnorm : IsMPSNormalized A 1)
    (hfaith : HasFaithfulDualEigenmatrix A 1)
    (heig : ∀ X, finiteKrausMap A X = X →
      ∃ c : ℂ, X = c • (1 : CStarMatrix (Fin D) (Fin D) ℂ))
    (hspec : ∀ μ ∈ spectrum ℂ (finiteKrausMap A),
      μ ≠ 1 → ‖μ‖ < 1) :
    MPSSpansForAllLarge A := by
  obtain ⟨ρ, hρ, hdual⟩ := hfaith
  have hone : finiteKrausMap A 1 =
      (1 : CStarMatrix (Fin D) (Fin D) ℂ) := by
    simpa [finiteKrausMap] using hnorm.2
  have hdual' : ∑ σ, star (A σ) * ρ * A σ = (1 : ℂ) • ρ := by
    simpa [mpsDualTransferMap] using hdual
  letI : FiniteDimensional ℂ (CStarMatrix (Fin D) (Fin D) ℂ) :=
    CStarMatrix.ofMatrixₗ.finiteDimensional
  have hshift :=
    tendsto_normalized_finiteKrausMap_pow_weightedTrace
      A 1 one_ne_zero ρ hρ (by simpa using hone) hdual'
      (by simpa using heig) (by simpa using hspec)
  have hlim : Tendsto
      (fun n : ℕ => Module.End.toContinuousLinearMap
        (CStarMatrix (Fin D) (Fin D) ℂ) (finiteKrausMap A ^ n))
      atTop
      (𝓝 (Module.End.toContinuousLinearMap
        (CStarMatrix (Fin D) (Fin D) ℂ) (traceLimitMap ρ))) := by
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    simpa [traceLimitMap] using hshift
  exact mpsSpansForAllLarge_of_tendsto_traceLimit A ρ hρ hlim

end LatticeSystem.Quantum.MPSTheorem75.Internal
