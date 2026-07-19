import LatticeSystem.Quantum.SpinS.AKLTStringOrderTransfer
import LatticeSystem.Quantum.SpinS.ManyBodyTensorConj
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Finite-axis covariance for the AKLT string correlation

This module proves finite-volume three-axis covariance for the explicit
periodic spin-one AKLT matrix-product state. The shared site-component selector
is `spinSSiteComponentS` on `Fin L`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer, 2020, §7.2.1, corrected eqs. (7.2.6)–(7.2.8),
pp. 193–194.
-/

namespace LatticeSystem.Quantum.AKLTStringOrder

open Matrix

variable {L : ℕ}

/-- The exact existing selector specializes to the axis-three site operator. -/
private theorem spinSSiteComponentS_two (x : Fin L) :
    spinSSiteComponentS (2 : Fin 3) x = spinSSiteOp3 x 2 := by
  unfold spinSSiteComponentS
  rfl

/-- The axis-three strict-window generator is diagonal in the configuration
basis with the sum of local magnetic eigenvalues. -/
private theorem axisThreeGenerator_eq_diagonal (x y : Fin L) :
    (∑ z ∈ Finset.univ.filter (fun z : Fin L =>
        x.val < z.val ∧ z.val < y.val),
      spinSSiteComponentS (2 : Fin 3) z) =
      Matrix.diagonal (fun σ : Fin L → Fin 3 =>
        ∑ z ∈ Finset.univ.filter (fun z : Fin L =>
          x.val < z.val ∧ z.val < y.val),
            (1 - ((σ z).val : ℂ))) := by
  simp_rw [spinSSiteComponentS_two, spinSSiteOp3_def]
  ext σ' σ
  simp only [Matrix.sum_apply, onSiteS_apply, spinSOp3,
    Matrix.diagonal_apply]
  by_cases h : σ' = σ
  · subst σ'
    rw [if_pos rfl]
    apply Finset.sum_congr rfl
    intro z hz
    simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro z hz
    by_cases hoff : ∀ i, i ≠ z → σ' i = σ i
    · have hz_ne : σ' z ≠ σ z := by
        intro heq
        apply h
        funext i
        by_cases hiz : i = z
        · simpa [hiz] using heq
        · exact hoff i hiz
      simp [hz_ne]
    · simp [hoff]

/-- Exponentiating a spin-one magnetic eigenvalue at angle `π` gives the
concrete axis-three string phase. -/
private theorem axisThreeLocalPhase (k : Fin 3) :
  NormedSpace.exp
      ((Complex.I * (Real.pi : ℂ)) * (1 - (k.val : ℂ))) =
        (-1 : ℂ) ^ (k.val + 1) := by
  fin_cases k
  · simp only [CharP.cast_eq_zero, sub_zero, mul_one, zero_add, pow_one]
    rw [show Complex.I * (Real.pi : ℂ) =
        (Real.pi : ℂ) * Complex.I by ring,
      ← Complex.exp_eq_exp_ℂ, Complex.exp_pi_mul_I]
  · simp
  · simp only [Nat.cast_ofNat, Nat.reduceAdd]
    rw [show Complex.I * (Real.pi : ℂ) * (1 - 2) =
        -((Real.pi : ℂ) * Complex.I) by ring,
      ← Complex.exp_eq_exp_ℂ, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num

/-- The axis-indexed exponential specializes exactly to the existing concrete
axis-three diagonal string operator. -/
private theorem stringOperatorAxisS_two (x y : Fin L) :
    stringOperatorAxisS (2 : Fin 3) x y = stringOperatorS x y := by
  unfold stringOperatorAxisS
  rw [axisThreeGenerator_eq_diagonal]
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
  unfold stringOperatorS
  congr 1
  funext σ
  rw [Pi.coe_exp, Pi.smul_apply, smul_eq_mul]
  change
    NormedSpace.exp
      ((Complex.I * (Real.pi : ℂ)) *
        (∑ z ∈ Finset.univ.filter (fun z : Fin L =>
          x.val < z.val ∧ z.val < y.val),
            (1 - ((σ z).val : ℂ)))) = _
  rw [Finset.mul_sum, NormedSpace.exp_sum]
  apply Finset.prod_congr rfl
  intro z hz
  simpa [spinSStringPhaseS1] using axisThreeLocalPhase (σ z)

/-- The axis-indexed correlation specializes exactly to the existing
axis-three correlation for every finite state. -/
private theorem stringCorrelationAxisS_two (x y : Fin L)
    (Φ : (Fin L → Fin 3) → ℂ) :
    stringCorrelationAxisS (2 : Fin 3) x y Φ =
      stringCorrelationS x y Φ := by
  unfold stringCorrelationAxisS stringCorrelationS
  rw [spinSSiteComponentS_two, spinSSiteComponentS_two,
    stringOperatorAxisS_two]

/-- Physical-basis transformation of the periodic AKLT matrices by a single-site
matrix `U`. -/
private noncomputable def transformedMatrices
    (U : Matrix (Fin 3) (Fin 3) ℂ) : MPSMatrices 2 2 :=
  fun s => ∑ t : Fin 3, U s t • akltVBSMatrices t

/-- A tensor product physical transformation of the periodic MPS vector is
the periodic vector built from the correspondingly transformed local
matrices. -/
private theorem physicalTransform_word
    (U : Matrix (Fin 3) (Fin 3) ℂ) (n : ℕ)
    (σ' : Fin n → Fin 3) (p q : Fin 2) :
    (∑ σ : Fin n → Fin 3,
        (∏ z, U (σ' z) (σ z)) *
          orderedProd akltVBSMatrices (List.ofFn σ) p q) =
      orderedProd (transformedMatrices U) (List.ofFn σ') p q := by
  induction n generalizing p q with
  | zero =>
      simp [orderedProd, Matrix.one_apply]
  | succ n ih =>
      rw [← Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (n + 1) => Fin 3)
        (fun a =>
          (∏ z, U (σ' z)
              ((Fin.consEquiv fun _ : Fin (n + 1) => Fin 3) a z)) *
            orderedProd akltVBSMatrices
              (List.ofFn ((Fin.consEquiv
                fun _ : Fin (n + 1) => Fin 3) a)) p q)
        (fun σ =>
          (∏ z, U (σ' z) (σ z)) *
            orderedProd akltVBSMatrices (List.ofFn σ) p q)
        (fun _ => rfl)]
      rw [Fintype.sum_prod_type]
      simp only [Fin.consEquiv_apply, List.ofFn_succ, orderedProd,
        Matrix.mul_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [show
        (∑ s : Fin 3, ∑ τ : Fin n → Fin 3,
          (U (σ' 0) s *
              (∏ z, U (σ' z.succ) (τ z))) *
                ∑ k, akltVBSMatrices s p k *
                  orderedProd akltVBSMatrices (List.ofFn τ) k q) =
          ∑ s : Fin 3, ∑ k : Fin 2,
            U (σ' 0) s * akltVBSMatrices s p k *
              (∑ τ : Fin n → Fin 3,
                (∏ z, U (σ' z.succ) (τ z)) *
                  orderedProd akltVBSMatrices (List.ofFn τ) k q) by
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro τ hτ
        ring]
      simp_rw [ih (fun z => σ' z.succ)]
      unfold transformedMatrices
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Matrix.sum_apply]
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [Finset.sum_mul]

/-- Tensoring a physical basis change over the ring transforms the periodic AKLT
state by the corresponding local MPS matrix change. -/
private theorem manyBodyTensorS_mulVec_state
    (U : Matrix (Fin 3) (Fin 3) ℂ) (n : ℕ) :
    (manyBodyTensorS (fun _ : Fin n => U)).mulVec (akltVBSState n) =
      fun σ' => Matrix.trace
        (orderedProd (transformedMatrices U) (List.ofFn σ')) := by
  funext σ'
  unfold Matrix.mulVec dotProduct akltVBSState Matrix.trace
  simp only [manyBodyTensorS_apply, Matrix.diag]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  exact physicalTransform_word U n σ' p p

/-- The real spin-one quarter-turn taking the third axis to the first axis. -/
private noncomputable def axisThreetoOne :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![(1 / 2 : ℂ), ((Real.sqrt 2 : ℂ)⁻¹), 1 / 2;
    -((Real.sqrt 2 : ℂ)⁻¹), 0, ((Real.sqrt 2 : ℂ)⁻¹);
    1 / 2, -((Real.sqrt 2 : ℂ)⁻¹), 1 / 2]

/-- The inverse real spin-one quarter-turn taking the first axis back to the
third axis. -/
private noncomputable def axisOnetoThree :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![(1 / 2 : ℂ), -((Real.sqrt 2 : ℂ)⁻¹), 1 / 2;
    ((Real.sqrt 2 : ℂ)⁻¹), 0, -((Real.sqrt 2 : ℂ)⁻¹);
    1 / 2, ((Real.sqrt 2 : ℂ)⁻¹), 1 / 2]

/-- The auxiliary spin-half gauge corresponding to `axisThreetoOne`. -/
private noncomputable def auxiliaryThreetoOne :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![((Real.sqrt 2 : ℂ)⁻¹), -((Real.sqrt 2 : ℂ)⁻¹);
    ((Real.sqrt 2 : ℂ)⁻¹), ((Real.sqrt 2 : ℂ)⁻¹)]

/-- The inverse auxiliary gauge corresponding to `axisThreetoOne`. -/
private noncomputable def auxiliaryOnetoThree :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![((Real.sqrt 2 : ℂ)⁻¹), ((Real.sqrt 2 : ℂ)⁻¹);
    -((Real.sqrt 2 : ℂ)⁻¹), ((Real.sqrt 2 : ℂ)⁻¹)]

/-- The two explicit auxiliary quarter-turn gauges multiply to the identity
in the forward order. -/
private theorem auxiliaryThreetoOne_mul_inverse :
    auxiliaryThreetoOne * auxiliaryOnetoThree = 1 := by
  have hsqrt : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
  have hinv :
      ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) =
        (1 / 2 : ℂ) := by
    rw [show
      ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) =
        (((Real.sqrt 2 : ℂ) ^ 2)⁻¹) by ring]
    rw [← Complex.ofReal_pow, hsqrt]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply] <;>
    simp_rw [Fin.sum_univ_two] <;>
    simp [auxiliaryThreetoOne, auxiliaryOnetoThree, hinv] <;>
    ring

/-- The two explicit auxiliary quarter-turn gauges multiply to the identity
in the reverse order. -/
private theorem auxiliaryOnetoThree_mul_inverse :
    auxiliaryOnetoThree * auxiliaryThreetoOne = 1 := by
  have hsqrt : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
  have hinv :
      ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) =
        (1 / 2 : ℂ) := by
    rw [show
      ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) =
        (((Real.sqrt 2 : ℂ) ^ 2)⁻¹) by ring]
    rw [← Complex.ofReal_pow, hsqrt]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply] <;>
    simp_rw [Fin.sum_univ_two] <;>
    simp [auxiliaryThreetoOne, auxiliaryOnetoThree, hinv] <;>
    ring

/-- The explicit physical quarter-turn and its inverse multiply to the
identity. -/
private theorem axisThreetoOne_mul_inverse :
    axisThreetoOne * axisOnetoThree = 1 := by
  have hsqrt : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
  have hinv :
      ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) =
        (1 / 2 : ℂ) := by
    rw [show
      ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) =
        (((Real.sqrt 2 : ℂ) ^ 2)⁻¹) by ring]
    rw [← Complex.ofReal_pow, hsqrt]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply] <;>
    simp_rw [Fin.sum_univ_three] <;>
    simp [axisThreetoOne, axisOnetoThree, hinv] <;>
    ring

/-- The inverse physical quarter-turn and the forward quarter-turn multiply
to the identity. -/
private theorem axisOnetoThree_mul_inverse :
    axisOnetoThree * axisThreetoOne = 1 := by
  have hsqrt : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
  have hinv :
      ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) =
        (1 / 2 : ℂ) := by
    rw [show
      ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) =
        (((Real.sqrt 2 : ℂ) ^ 2)⁻¹) by ring]
    rw [← Complex.ofReal_pow, hsqrt]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply] <;>
    simp_rw [Fin.sum_univ_three] <;>
    simp [axisThreetoOne, axisOnetoThree, hinv] <;>
    ring

/-- The adjoint of the real physical quarter-turn is its explicit inverse. -/
private theorem axisThreetoOne_conjTranspose :
    axisThreetoOne.conjTranspose = axisOnetoThree := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axisThreetoOne, axisOnetoThree, Matrix.conjTranspose_apply]

/-- The inverse physical quarter-turn conjugates the third spin component to
the first spin component. -/
private theorem axisOnetoThree_conj_spinSOp3 :
    axisOnetoThree * spinSOp3 2 * axisThreetoOne = spinSOp1 2 := by
  have hsqrt : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
  have hinv :
      ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) =
        (1 / 2 : ℂ) := by
    rw [show
      ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) =
        (((Real.sqrt 2 : ℂ) ^ 2)⁻¹) by ring]
    rw [← Complex.ofReal_pow, hsqrt]
    norm_num
  have hinvlinear :
      ((Real.sqrt 2 : ℂ)⁻¹) =
        (Real.sqrt 2 : ℂ) * (1 / 2 : ℂ) := by
    have hsqrt_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by norm_num
    field_simp
    rw [← Complex.ofReal_pow, hsqrt]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply] <;>
    simp_rw [Fin.sum_univ_three]
  all_goals
    simp only [Nat.reduceAdd, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Fin.isValue]
  all_goals
    simp only [axisOnetoThree, one_div, Fin.isValue, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val_one, Matrix.cons_val, spinSOp3, Nat.reduceAdd,
      Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      div_self, zero_mul, add_zero, neg_mul, axisThreetoOne, spinSOp1,
      Matrix.smul_apply, Matrix.add_apply, spinSOpPlus,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.one_mod, Nat.mod_succ,
      zero_add, one_ne_zero, ↓reduceIte, Nat.cast_one, sub_add_cancel,
      one_mul, spinSOpMinus, smul_eq_mul, mul_zero, OfNat.one_ne_ofNat,
      CharP.cast_eq_zero, sub_zero, mul_one, OfNat.ofNat_ne_one, sub_self,
      sub_nonneg, Nat.one_le_ofNat, Real.sqrt_mul, Complex.ofReal_mul,
      OfNat.ofNat_eq_ofNat, Nat.succ_ne_self]
  all_goals simp_rw [Fin.sum_univ_three]
  all_goals
    simp only [Fin.isValue, Matrix.diagonal_apply_eq,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, CharP.cast_eq_zero, sub_zero,
      mul_one, ne_eq, one_ne_zero, not_false_eq_true,
      Matrix.diagonal_apply_ne, mul_zero, neg_zero, add_zero, Fin.reduceEq,
      Matrix.cons_val_zero, zero_ne_one, Nat.one_mod, Nat.cast_one,
      sub_self, Matrix.cons_val_one, Nat.mod_succ, Nat.cast_ofNat,
      zero_add, Matrix.cons_val, mul_neg, zero_mul, neg_mul]
  all_goals norm_num [div_eq_mul_inv]
  all_goals rw [hinvlinear]
  all_goals ring

/-- The physical quarter-turn of each AKLT matrix is exactly auxiliary-gauge
conjugation. -/
private theorem transformedMatrices_axisThreetoOne (s : Fin 3) :
    transformedMatrices axisThreetoOne s =
      auxiliaryThreetoOne * akltVBSMatrices s * auxiliaryOnetoThree := by
  have hsqrt : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
  have hinv :
      ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) =
        (1 / 2 : ℂ) := by
    rw [show
      ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) =
        (((Real.sqrt 2 : ℂ) ^ 2)⁻¹) by ring]
    rw [← Complex.ofReal_pow, hsqrt]
    norm_num
  have hinvpow :
      ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) := by
    simpa only [pow_two] using hinv
  ext i j
  fin_cases s <;> fin_cases i <;> fin_cases j <;>
    simp only [transformedMatrices, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.mul_apply] <;>
    simp_rw [Fin.sum_univ_three, Fin.sum_univ_two] <;>
    simp [axisThreetoOne, auxiliaryThreetoOne, auxiliaryOnetoThree,
      akltVBSMatrices, hinv]
  all_goals ring_nf
  all_goals exact hinvpow.symm

/-- A pointwise auxiliary similarity transforms every periodic matrix word
by the same similarity. -/
private theorem orderedProd_gauge
    (B : MPSMatrices 2 2) (G Ginv : Matrix (Fin 2) (Fin 2) ℂ)
    (hGGinv : G * Ginv = 1) (hGinvG : Ginv * G = 1)
    (hB : ∀ s, B s = G * akltVBSMatrices s * Ginv)
    (u : List (Fin 3)) :
    orderedProd B u =
      G * orderedProd akltVBSMatrices u * Ginv := by
  induction u with
  | nil =>
      simp [orderedProd, hGGinv]
  | cons s u ih =>
      rw [orderedProd, hB s, ih]
      rw [orderedProd]
      rw [show
        G * akltVBSMatrices s * Ginv *
            (G * orderedProd akltVBSMatrices u * Ginv) =
          G * akltVBSMatrices s * (Ginv * G) *
            orderedProd akltVBSMatrices u * Ginv by
          noncomm_ring]
      rw [hGinvG]
      simp only [mul_one, mul_assoc]

/-- The explicit axis-three-to-axis-one tensor rotation fixes the periodic
AKLT VBS state exactly. -/
private theorem axisThreetoOne_state_invariant (n : ℕ) :
    (manyBodyTensorS (fun _ : Fin n => axisThreetoOne)).mulVec
        (akltVBSState n) = akltVBSState n := by
  rw [manyBodyTensorS_mulVec_state]
  funext σ
  rw [orderedProd_gauge (transformedMatrices axisThreetoOne)
    auxiliaryThreetoOne auxiliaryOnetoThree
    auxiliaryThreetoOne_mul_inverse auxiliaryOnetoThree_mul_inverse
    transformedMatrices_axisThreetoOne]
  unfold akltVBSState
  rw [Matrix.trace_mul_cycle]
  rw [auxiliaryOnetoThree_mul_inverse, one_mul]

/-- The diagonal physical quarter-turn used after the real axis swap. -/
private noncomputable def axisOnetoTwo :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![Complex.I, 0, 0; 0, 1, 0; 0, 0, -Complex.I]

/-- The inverse diagonal physical quarter-turn. -/
private noncomputable def axisTwotoOne :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![-Complex.I, 0, 0; 0, 1, 0; 0, 0, Complex.I]

/-- The auxiliary gauge for the diagonal physical quarter-turn. -/
private noncomputable def auxiliaryOnetoTwo :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ), 0; 0, Complex.I]

/-- The inverse auxiliary gauge for the diagonal physical quarter-turn. -/
private noncomputable def auxiliaryTwotoOne :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ), 0; 0, -Complex.I]

/-- The diagonal physical quarter-turn has the displayed two-sided inverse. -/
private theorem axisOnetoTwo_mul_inverse :
    axisOnetoTwo * axisTwotoOne = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, axisOnetoTwo, axisTwotoOne]

/-- The inverse diagonal physical quarter-turn has the displayed inverse. -/
private theorem axisTwotoOne_mul_inverse :
    axisTwotoOne * axisOnetoTwo = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, axisOnetoTwo, axisTwotoOne]

/-- The diagonal physical quarter-turn has the expected adjoint. -/
private theorem axisOnetoTwo_conjTranspose :
    axisOnetoTwo.conjTranspose = axisTwotoOne := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axisOnetoTwo, axisTwotoOne, Matrix.conjTranspose_apply]

/-- The two diagonal auxiliary gauges multiply to the identity. -/
private theorem auxiliaryOnetoTwo_mul_inverse :
    auxiliaryOnetoTwo * auxiliaryTwotoOne = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, auxiliaryOnetoTwo,
      auxiliaryTwotoOne]

/-- The inverse and forward diagonal auxiliary gauges multiply to the identity. -/
private theorem auxiliaryTwotoOne_mul_inverse :
    auxiliaryTwotoOne * auxiliaryOnetoTwo = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, auxiliaryOnetoTwo,
      auxiliaryTwotoOne]

/-- The diagonal physical quarter-turn conjugates the first spin component to
the second one. -/
private theorem axisTwotoOne_conj_spinSOp1 :
    axisTwotoOne * spinSOp1 2 * axisOnetoTwo = spinSOp2 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply] <;>
    simp_rw [Fin.sum_univ_three]
  all_goals
    simp only [Nat.reduceAdd, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Fin.isValue]
  all_goals
    simp only [axisTwotoOne, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.cons_val, spinSOp1, Nat.reduceAdd, div_eq_mul_inv, one_mul,
      Matrix.smul_apply, Matrix.add_apply, spinSOpPlus,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.one_mod, Nat.mod_succ,
      zero_add, Nat.cast_ofNat, Nat.cast_nonneg, Real.sqrt_mul,
      Complex.ofReal_mul, spinSOpMinus, Nat.add_eq_zero_iff,
      Fin.val_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_zero,
      smul_eq_mul, mul_ite, mul_zero, neg_mul, Nat.add_eq_right, zero_mul,
      Nat.reduceEqDiff, axisOnetoTwo, ite_mul, ite_self, spinSOp2,
      mul_inv_rev, Complex.inv_I, mul_neg, Matrix.sub_apply, sub_self,
      Nat.cast_one, sub_add_cancel, OfNat.ofNat_ne_zero, sub_zero,
      OfNat.one_ne_ofNat, CharP.cast_eq_zero, mul_one, zero_sub, neg_neg,
      OfNat.ofNat_ne_one, sub_nonneg, Nat.one_le_ofNat,
      OfNat.ofNat_eq_ofNat, Nat.succ_ne_self]
  all_goals simp_rw [Fin.sum_univ_three]
  all_goals simp
  all_goals norm_num
  all_goals ring

/-- The diagonal physical quarter-turn of every AKLT matrix is the displayed
auxiliary similarity. -/
private theorem transformedMatrices_axisOnetoTwo (s : Fin 3) :
    transformedMatrices axisOnetoTwo s =
      auxiliaryOnetoTwo * akltVBSMatrices s * auxiliaryTwotoOne := by
  ext i j
  fin_cases s <;> fin_cases i <;> fin_cases j <;>
    simp only [transformedMatrices, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.mul_apply] <;>
    simp_rw [Fin.sum_univ_three, Fin.sum_univ_two] <;>
    simp [axisOnetoTwo, auxiliaryOnetoTwo, auxiliaryTwotoOne,
      akltVBSMatrices]
  all_goals ring_nf
  all_goals rw [Complex.I_sq]
  all_goals ring

/-- The explicit diagonal quarter-turn fixes the periodic AKLT VBS state
exactly. -/
private theorem axisOnetoTwo_state_invariant (n : ℕ) :
    (manyBodyTensorS (fun _ : Fin n => axisOnetoTwo)).mulVec
        (akltVBSState n) = akltVBSState n := by
  rw [manyBodyTensorS_mulVec_state]
  funext σ
  rw [orderedProd_gauge (transformedMatrices axisOnetoTwo)
    auxiliaryOnetoTwo auxiliaryTwotoOne
    auxiliaryOnetoTwo_mul_inverse auxiliaryTwotoOne_mul_inverse
    transformedMatrices_axisOnetoTwo]
  unfold akltVBSState
  rw [Matrix.trace_mul_cycle]
  rw [auxiliaryTwotoOne_mul_inverse, one_mul]

/-- The composed physical rotation taking the third axis to the second axis. -/
private noncomputable def axisThreetoTwo :
    Matrix (Fin 3) (Fin 3) ℂ :=
  axisThreetoOne * axisOnetoTwo

/-- The inverse of the composed third-to-second-axis rotation. -/
private noncomputable def axisTwotoThree :
    Matrix (Fin 3) (Fin 3) ℂ :=
  axisTwotoOne * axisOnetoThree

/-- The composed third-to-second rotation has the displayed inverse. -/
private theorem axisThreetoTwo_mul_inverse :
    axisThreetoTwo * axisTwotoThree = 1 := by
  unfold axisThreetoTwo axisTwotoThree
  rw [show
    axisThreetoOne * axisOnetoTwo * (axisTwotoOne * axisOnetoThree) =
      axisThreetoOne * (axisOnetoTwo * axisTwotoOne) *
        axisOnetoThree by noncomm_ring]
  rw [axisOnetoTwo_mul_inverse, mul_one, axisThreetoOne_mul_inverse]

/-- The inverse composed rotation has the forward rotation as inverse. -/
private theorem axisTwotoThree_mul_inverse :
    axisTwotoThree * axisThreetoTwo = 1 := by
  unfold axisThreetoTwo axisTwotoThree
  rw [show
    axisTwotoOne * axisOnetoThree * (axisThreetoOne * axisOnetoTwo) =
      axisTwotoOne * (axisOnetoThree * axisThreetoOne) *
        axisOnetoTwo by noncomm_ring]
  rw [axisOnetoThree_mul_inverse, mul_one, axisTwotoOne_mul_inverse]

/-- The adjoint of the composed third-to-second rotation is its inverse. -/
private theorem axisThreetoTwo_conjTranspose :
    axisThreetoTwo.conjTranspose = axisTwotoThree := by
  unfold axisThreetoTwo axisTwotoThree
  rw [Matrix.conjTranspose_mul, axisThreetoOne_conjTranspose,
    axisOnetoTwo_conjTranspose]

/-- The inverse composed rotation conjugates the third spin component to the
second spin component. -/
private theorem axisTwotoThree_conj_spinSOp3 :
    axisTwotoThree * spinSOp3 2 * axisThreetoTwo = spinSOp2 2 := by
  unfold axisTwotoThree axisThreetoTwo
  rw [show
    axisTwotoOne * axisOnetoThree * spinSOp3 2 *
        (axisThreetoOne * axisOnetoTwo) =
      axisTwotoOne *
        (axisOnetoThree * spinSOp3 2 * axisThreetoOne) *
          axisOnetoTwo by noncomm_ring]
  rw [axisOnetoThree_conj_spinSOp3, axisTwotoOne_conj_spinSOp1]

/-- The composed third-to-second-axis rotation fixes the periodic AKLT VBS state. -/
private theorem axisThreetoTwo_state_invariant (n : ℕ) :
    (manyBodyTensorS (fun _ : Fin n => axisThreetoTwo)).mulVec
        (akltVBSState n) = akltVBSState n := by
  unfold axisThreetoTwo
  rw [← manyBodyTensorS_mul]
  rw [← Matrix.mulVec_mulVec, axisOnetoTwo_state_invariant,
    axisThreetoOne_state_invariant]

/-- Taking the adjoint of a constant many-body tensor takes the adjoint at
every site. -/
private theorem manyBodyTensorS_conjTranspose_const
    (n : ℕ) (U Uadj : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : U.conjTranspose = Uadj) :
    (manyBodyTensorS (fun _ : Fin n => U)).conjTranspose =
      manyBodyTensorS (fun _ : Fin n => Uadj) := by
  ext σ τ
  rw [Matrix.conjTranspose_apply]
  simp only [manyBodyTensorS_apply]
  rw [star_prod]
  apply Finset.prod_congr rfl
  intro z hz
  have hentry := congrArg (fun A => A (σ z) (τ z)) hU
  simpa [Matrix.conjTranspose_apply] using hentry

/-- A two-sided many-body rotation carrying the third-axis sites to `α` carries
the full exponential string correlation to axis `α`. -/
private theorem stringCorrelationAxisS_eq_two_of_rotation
    (α : Fin 3) (x y : Fin L)
    (U Uinv : ManyBodyOpS (Fin L) 2)
    (hUUinv : U * Uinv = 1) (hUinvU : Uinv * U = 1)
    (hUinvAdj : Uinv.conjTranspose = U)
    (hstate : U.mulVec (akltVBSState L) = akltVBSState L)
    (hsite : ∀ z : Fin L,
      Uinv * spinSSiteComponentS (2 : Fin 3) z * U =
        spinSSiteComponentS α z) :
    stringCorrelationAxisS α x y (akltVBSState L) =
      stringCorrelationAxisS (2 : Fin 3) x y (akltVBSState L) := by
  let Θ : Units (ManyBodyOpS (Fin L) 2) :=
    { val := Uinv
      inv := U
      val_inv := hUinvU
      inv_val := hUUinv }
  have hgenerator :
      Uinv *
          (∑ z ∈ Finset.univ.filter (fun z : Fin L =>
            x.val < z.val ∧ z.val < y.val),
            spinSSiteComponentS (2 : Fin 3) z) *
          U =
        ∑ z ∈ Finset.univ.filter (fun z : Fin L =>
          x.val < z.val ∧ z.val < y.val),
          spinSSiteComponentS α z := by
    rw [Finset.mul_sum]
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z hz
    exact hsite z
  have hscaled :
      Uinv *
          ((Complex.I * (Real.pi : ℂ)) •
            ∑ z ∈ Finset.univ.filter (fun z : Fin L =>
              x.val < z.val ∧ z.val < y.val),
              spinSSiteComponentS (2 : Fin 3) z) *
          U =
        (Complex.I * (Real.pi : ℂ)) •
          ∑ z ∈ Finset.univ.filter (fun z : Fin L =>
            x.val < z.val ∧ z.val < y.val),
            spinSSiteComponentS α z := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hgenerator]
  have hstring :
      stringOperatorAxisS α x y =
        Uinv * stringOperatorAxisS (2 : Fin 3) x y * U := by
    unfold stringOperatorAxisS
    rw [← hscaled]
    simpa [Θ] using Matrix.exp_units_conj Θ
      ((Complex.I * (Real.pi : ℂ)) •
        ∑ z ∈ Finset.univ.filter (fun z : Fin L =>
          x.val < z.val ∧ z.val < y.val),
          spinSSiteComponentS (2 : Fin 3) z)
  let Othree :=
    spinSSiteComponentS (2 : Fin 3) x *
      stringOperatorAxisS (2 : Fin 3) x y *
        spinSSiteComponentS (2 : Fin 3) y
  have hobservable :
      spinSSiteComponentS α x * stringOperatorAxisS α x y *
          spinSSiteComponentS α y =
        Uinv * Othree * U := by
    rw [← hsite x, hstring, ← hsite y]
    unfold Othree
    rw [show
      (Uinv * spinSSiteComponentS (2 : Fin 3) x * U) *
            (Uinv * stringOperatorAxisS (2 : Fin 3) x y * U) *
          (Uinv * spinSSiteComponentS (2 : Fin 3) y * U) =
        Uinv * spinSSiteComponentS (2 : Fin 3) x * (U * Uinv) *
          stringOperatorAxisS (2 : Fin 3) x y * (U * Uinv) *
          spinSSiteComponentS (2 : Fin 3) y * U by
        noncomm_ring]
    rw [hUUinv]
    simp only [mul_one]
    noncomm_ring
  have hnumerator :
      star (akltVBSState L) ⬝ᵥ
          (spinSSiteComponentS α x * stringOperatorAxisS α x y *
            spinSSiteComponentS α y).mulVec (akltVBSState L) =
        star (akltVBSState L) ⬝ᵥ
          Othree.mulVec (akltVBSState L) := by
    rw [hobservable]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hstate]
    rw [show
      star (akltVBSState L) ⬝ᵥ
          Uinv.mulVec (Othree.mulVec (akltVBSState L)) =
        star (Uinv.conjTranspose.mulVec (akltVBSState L)) ⬝ᵥ
          Othree.mulVec (akltVBSState L) by
        rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
          Matrix.dotProduct_mulVec]]
    rw [hUinvAdj, hstate]
  unfold stringCorrelationAxisS expectationRatioRe
  rw [hnumerator]

/-- Every finite periodic AKLT VBS string correlation agrees exactly with its
axis-three correlation. -/
theorem Internal.stringCorrelationAxisS_akltVBSState_eq_three
    (α : Fin 3) (L : ℕ) (_hL : 2 ≤ L)
    (x y : Fin L) (_hxy : x.val < y.val) :
    stringCorrelationAxisS α x y (akltVBSState L) =
      stringCorrelationS x y (akltVBSState L) := by
  fin_cases α
  · change stringCorrelationAxisS (0 : Fin 3) x y (akltVBSState L) =
      stringCorrelationS x y (akltVBSState L)
    rw [stringCorrelationAxisS_eq_two_of_rotation
      (0 : Fin 3) x y
      (manyBodyTensorS (fun _ : Fin L => axisThreetoOne))
      (manyBodyTensorS (fun _ : Fin L => axisOnetoThree))]
    · exact stringCorrelationAxisS_two x y (akltVBSState L)
    · rw [manyBodyTensorS_mul]
      simpa [axisThreetoOne_mul_inverse] using
        manyBodyTensorS_one (Λ := Fin L) (N := 2)
    · rw [manyBodyTensorS_mul]
      simpa [axisOnetoThree_mul_inverse] using
        manyBodyTensorS_one (Λ := Fin L) (N := 2)
    · apply manyBodyTensorS_conjTranspose_const
      rw [← axisThreetoOne_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
    · exact axisThreetoOne_state_invariant L
    · intro z
      rw [show spinSSiteComponentS (2 : Fin 3) z =
          onSiteS z (spinSOp3 2) by rfl]
      rw [manyBodyTensorS_conj_onSiteS axisOnetoThree_mul_inverse]
      rw [axisOnetoThree_conj_spinSOp3]
      rfl
  · change stringCorrelationAxisS (1 : Fin 3) x y (akltVBSState L) =
      stringCorrelationS x y (akltVBSState L)
    rw [stringCorrelationAxisS_eq_two_of_rotation
      (1 : Fin 3) x y
      (manyBodyTensorS (fun _ : Fin L => axisThreetoTwo))
      (manyBodyTensorS (fun _ : Fin L => axisTwotoThree))]
    · exact stringCorrelationAxisS_two x y (akltVBSState L)
    · rw [manyBodyTensorS_mul]
      simpa [axisThreetoTwo_mul_inverse] using
        manyBodyTensorS_one (Λ := Fin L) (N := 2)
    · rw [manyBodyTensorS_mul]
      simpa [axisTwotoThree_mul_inverse] using
        manyBodyTensorS_one (Λ := Fin L) (N := 2)
    · apply manyBodyTensorS_conjTranspose_const
      rw [← axisThreetoTwo_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
    · exact axisThreetoTwo_state_invariant L
    · intro z
      rw [show spinSSiteComponentS (2 : Fin 3) z =
          onSiteS z (spinSOp3 2) by rfl]
      rw [manyBodyTensorS_conj_onSiteS axisTwotoThree_mul_inverse]
      rw [axisTwotoThree_conj_spinSOp3]
      rfl
  · change stringCorrelationAxisS (2 : Fin 3) x y (akltVBSState L) =
      stringCorrelationS x y (akltVBSState L)
    exact stringCorrelationAxisS_two x y (akltVBSState L)

end LatticeSystem.Quantum.AKLTStringOrder
