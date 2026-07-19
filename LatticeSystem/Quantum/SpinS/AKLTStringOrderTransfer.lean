import LatticeSystem.Quantum.SpinS.AKLTStringOrderDefs

/-!
# Exact axis-three AKLT string-order transfer calculation

This module proves the exact finite axis-three string correlation of the
spin-one periodic AKLT akltVBSState and its thermodynamic epsilon estimate.
Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer, 2020, §7.2.1, eqs. (7.2.6)–(7.2.8), pp. 193–194, and
§7.2.2, eqs. (7.2.12)–(7.2.25), pp. 195–198.
-/

namespace LatticeSystem.Quantum.AKLTStringOrder

open Matrix

/-- A physical-label weight defines the doubled local transfer matrix. -/
private noncomputable def weightedTransfer (w : Fin 3 → ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => ∑ σ : Fin 3, w σ * star (akltVBSMatrices σ p.1 q.1) * akltVBSMatrices σ p.2 q.2

/-- The ordinary doubled transfer matrix. -/
private noncomputable def ordinaryTransfer :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  weightedTransfer 1

/-- The endpoint `S³`-inserted doubled transfer matrix. -/
private noncomputable def endpointTransfer :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  weightedTransfer fun σ => (1 - (σ : ℕ) : ℂ)

/-- The interior `exp(iπS³)`-inserted doubled transfer matrix. -/
private noncomputable def phaseTransfer :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  weightedTransfer fun σ => (-1 : ℂ) ^ (σ.val + 1)

/-- Four finite sums may be reordered by reversing their binder blocks. -/
private theorem sum_four_reverse {α β γ δ R : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [AddCommMonoid R]
    (f : α → β → γ → δ → R) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ d, ∑ c, ∑ a, ∑ b, f a b c d := by
  classical
  calc
    _ = ∑ a, ∑ b, ∑ d, ∑ c, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ b, ∑ c, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := Finset.sum_comm
    _ = ∑ d, ∑ c, ∑ a, ∑ b, f a b c d := by
      apply Finset.sum_congr rfl
      intro d _
      calc
        _ = ∑ a, ∑ c, ∑ b, f a b c d := by
          apply Finset.sum_congr rfl
          intro a _
          exact Finset.sum_comm
        _ = ∑ c, ∑ a, ∑ b, f a b c d := Finset.sum_comm

/-- Three finite sums may be cyclically reordered. -/
private theorem sum_three_rotate {α β γ R : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid R]
    (f : α → β → γ → R) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  calc
    _ = ∑ b, ∑ a, ∑ c, f a b c := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, f a b c := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm

/-- Weighted sums of doubled MPS word entries contract to products of local
transfer akltVBSMatrices. -/
private theorem weighted_word_contraction (n : ℕ) (w : Fin n → Fin 3 → ℂ)
    (p q : Fin 2 × Fin 2) :
    (∑ σ : Fin n → Fin 3,
        (∏ z, w z (σ z)) *
          star (orderedProd akltVBSMatrices (List.ofFn σ) p.1 q.1) *
          orderedProd akltVBSMatrices (List.ofFn σ) p.2 q.2) =
      (List.ofFn fun z => weightedTransfer (w z)).prod p q := by
  induction n generalizing p q with
  | zero =>
      simp [orderedProd, Matrix.one_apply, Prod.ext_iff]
      split_ifs <;> simp_all
  | succ n ih =>
      rw [← Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (n + 1) => Fin 3)
        (fun a =>
          (∏ z, w z ((Fin.consEquiv fun _ : Fin (n + 1) => Fin 3) a z)) *
            star (orderedProd akltVBSMatrices
              (List.ofFn ((Fin.consEquiv fun _ : Fin (n + 1) => Fin 3) a)) p.1 q.1) *
            orderedProd akltVBSMatrices
              (List.ofFn ((Fin.consEquiv fun _ : Fin (n + 1) => Fin 3) a)) p.2 q.2)
        (fun σ =>
          (∏ z, w z (σ z)) *
            star (orderedProd akltVBSMatrices (List.ofFn σ) p.1 q.1) *
            orderedProd akltVBSMatrices (List.ofFn σ) p.2 q.2) (fun _ => rfl)]
      rw [Fintype.sum_prod_type]
      simp only [Fin.consEquiv_apply, List.ofFn_succ, orderedProd, Matrix.mul_apply,
        Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      simp_rw [star_sum, star_mul]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [List.prod_cons, Matrix.mul_apply]
      let tailW : Fin n → Fin 3 → ℂ := fun z => w z.succ
      have htail (i j : Fin 2) :
          (∑ σ : Fin n → Fin 3,
              (∏ z, tailW z (σ z)) *
                star (orderedProd akltVBSMatrices (List.ofFn σ) i q.1) *
                orderedProd akltVBSMatrices (List.ofFn σ) j q.2) =
            (List.ofFn fun z => weightedTransfer (tailW z)).prod (i, j) q :=
        ih tailW (i, j) q
      calc
        _ = ∑ i : Fin 2, ∑ j : Fin 2,
            (∑ σ : Fin 3,
              w 0 σ * star (akltVBSMatrices σ p.1 i) * akltVBSMatrices σ p.2 j) *
            (∑ τ : Fin n → Fin 3,
              (∏ z, tailW z (τ z)) *
                star (orderedProd akltVBSMatrices (List.ofFn fun z => τ z) i q.1) *
                orderedProd akltVBSMatrices (List.ofFn fun z => τ z) j q.2) := by
              dsimp only [tailW]
              rw [sum_four_reverse]
              simp_rw [Finset.sum_mul, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              apply Finset.sum_congr rfl
              intro σ _
              apply Finset.sum_congr rfl
              intro τ _
              ring
        _ = ∑ i : Fin 2, ∑ j : Fin 2,
            weightedTransfer (w 0) p (i, j) *
              (List.ofFn fun z => weightedTransfer (w z.succ)).prod (i, j) q := by
              simp_rw [htail]
              rfl
        _ = _ := by
          rw [← Fintype.sum_prod_type']

/-- A weighted sum of periodic coefficient squares is the trace of the
corresponding doubled-transfer product. -/
private theorem weighted_state_contraction (n : ℕ) (w : Fin n → Fin 3 → ℂ) :
    (∑ σ : Fin n → Fin 3,
        (∏ z, w z (σ z)) * star (akltVBSState n σ) * akltVBSState n σ) =
      Matrix.trace (List.ofFn fun z => weightedTransfer (w z)).prod := by
  unfold akltVBSState Matrix.trace
  simp_rw [star_sum, Finset.mul_sum, Finset.sum_mul]
  simp only [Matrix.diag]
  rw [sum_three_rotate
    (fun σ (j : Fin 2) (i : Fin 2) =>
      (∏ z, w z (σ z)) *
        star (orderedProd akltVBSMatrices (List.ofFn σ) i i) *
        orderedProd akltVBSMatrices (List.ofFn σ) j j)]
  rw [Finset.sum_comm]
  rw [← Fintype.sum_prod_type']
  apply Finset.sum_congr rfl
  intro p _
  simpa [Matrix.diag] using weighted_word_contraction n w p p

/-- The square of the frozen inverse square root is `1/2`. -/
private theorem invSqrtTwo_sq :
    ((Real.sqrt 2 : ℂ)⁻¹) * (Real.sqrt 2 : ℂ)⁻¹ = (1 / 2 : ℂ) := by
  rw [← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  push_cast
  ring

/-- The rank-one projector onto the diagonal auxiliary-pair vector. -/
private noncomputable def diagonalPairProjector :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => if p.1 = p.2 ∧ q.1 = q.2 then (1 / 2 : ℂ) else 0

/-- The diagonal-pair matrix is an idempotent. -/
private theorem diagonalPairProjector_sq :
    diagonalPairProjector * diagonalPairProjector = diagonalPairProjector := by
  ext ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  fin_cases p₁ <;> fin_cases p₂ <;> fin_cases q₁ <;> fin_cases q₂ <;>
    norm_num [diagonalPairProjector]

/-- The ordinary AKLT doubled transfer is `-1/4` off the rank-one sector
and `3/4` on it. -/
private theorem ordinaryTransfer_decomposition :
    ordinaryTransfer =
      (-1 / 4 : ℂ) • (1 - diagonalPairProjector) +
        (3 / 4 : ℂ) • diagonalPairProjector := by
  ext ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
  fin_cases p₁ <;> fin_cases p₂ <;> fin_cases q₁ <;> fin_cases q₂ <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.add_apply,
      Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply_eq, smul_eq_mul] <;>
    (try simp only [ne_eq, Prod.mk.injEq, zero_ne_one, one_ne_zero,
      and_self, and_true, and_false, not_false_eq_true,
      Matrix.one_apply_ne, zero_sub, mul_neg]) <;>
    simp [ordinaryTransfer, weightedTransfer, akltVBSMatrices, diagonalPairProjector,
      invSqrtTwo_sq, Fin.sum_univ_three, map_inv₀, map_ofNat] <;>
    norm_num [div_eq_mul_inv]

/-- Powers of the ordinary transfer split over its two complementary
idempotent sectors. -/
private theorem ordinaryTransfer_pow (n : ℕ) :
    ordinaryTransfer ^ n =
      (-1 / 4 : ℂ) ^ n • (1 - diagonalPairProjector) +
        (3 / 4 : ℂ) ^ n • diagonalPairProjector := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, ordinaryTransfer_decomposition]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        diagonalPairProjector_sq]
      simp [Matrix.sub_mul, Matrix.mul_sub, diagonalPairProjector_sq, pow_succ]
      module

/-- The rank-one projector onto the antisymmetric diagonal-pair vector. -/
private noncomputable def antisymmetricPairProjector :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q =>
    if p.1 = p.2 ∧ q.1 = q.2 then
      if p.1 = q.1 then (1 / 2 : ℂ) else -(1 / 2 : ℂ)
    else 0

/-- The antisymmetric diagonal-pair matrix is an idempotent. -/
private theorem antisymmetricPairProjector_sq :
    antisymmetricPairProjector * antisymmetricPairProjector =
      antisymmetricPairProjector := by
  ext ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  fin_cases p₁ <;> fin_cases p₂ <;> fin_cases q₁ <;> fin_cases q₂ <;>
    norm_num [antisymmetricPairProjector]

/-- The phase-inserted transfer has the same two eigenvalues as the ordinary
transfer, with the antisymmetric rank-one sector dominant. -/
private theorem phaseTransfer_decomposition :
    phaseTransfer =
      (-1 / 4 : ℂ) • (1 - antisymmetricPairProjector) +
        (3 / 4 : ℂ) • antisymmetricPairProjector := by
  ext ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
  fin_cases p₁ <;> fin_cases p₂ <;> fin_cases q₁ <;> fin_cases q₂
  all_goals
    first
    | solve
      | simp [phaseTransfer, weightedTransfer, akltVBSMatrices,
          antisymmetricPairProjector, invSqrtTwo_sq, Fin.sum_univ_three,
          map_inv₀, map_ofNat] <;>
          norm_num [div_eq_mul_inv]
    | solve
      | simp [phaseTransfer, weightedTransfer, akltVBSMatrices,
        antisymmetricPairProjector, Fin.sum_univ_three, map_inv₀]
    | solve
      | simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.add_apply,
          Matrix.smul_apply, Matrix.sub_apply, ne_eq, Prod.mk.injEq,
          zero_ne_one, and_self, not_false_eq_true, Matrix.one_apply_ne,
          zero_sub, smul_eq_mul, mul_neg]
        norm_num [phaseTransfer, weightedTransfer, akltVBSMatrices,
          antisymmetricPairProjector, Fin.sum_univ_three, map_inv₀,
          div_eq_mul_inv]
        change
          (starRingEnd ℂ) ((Real.sqrt 2 : ℂ)⁻¹) *
              (Real.sqrt 2 : ℂ)⁻¹ =
            1 / 2
        simpa using invSqrtTwo_sq

/-- Powers of the phase-inserted transfer split over its complementary
idempotent sectors. -/
private theorem phaseTransfer_pow (n : ℕ) :
    phaseTransfer ^ n =
      (-1 / 4 : ℂ) ^ n • (1 - antisymmetricPairProjector) +
        (3 / 4 : ℂ) ^ n • antisymmetricPairProjector := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, phaseTransfer_decomposition]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        antisymmetricPairProjector_sq]
      simp [Matrix.sub_mul, Matrix.mul_sub, antisymmetricPairProjector_sq, pow_succ]
      module

/-- The endpoint transfer has the frozen `S³` insertion entries. -/
private theorem endpointTransfer_entries :
    endpointTransfer =
      fun p q =>
        if p = ((0, 0) : Fin 2 × Fin 2) ∧ q = (1, 1) then -(1 / 2 : ℂ)
        else if p = (1, 1) ∧ q = (0, 0) then (1 / 2 : ℂ)
        else 0 := by
  ext ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
  fin_cases p₁ <;> fin_cases p₂ <;> fin_cases q₁ <;> fin_cases q₂
  all_goals
    first
    | solve
      | simp [endpointTransfer, weightedTransfer, akltVBSMatrices,
          Fin.sum_univ_three, map_inv₀] <;>
          norm_num [div_eq_mul_inv]
    | solve
      | simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, and_self,
          ↓reduceIte, one_div]
        simp only [Fin.isValue, Prod.mk.injEq, one_ne_zero, and_self,
          zero_ne_one, ↓reduceIte]
        norm_num [endpointTransfer, weightedTransfer, akltVBSMatrices,
          Fin.sum_univ_three, map_inv₀, div_eq_mul_inv]
        first
        | simpa only [one_div] using invSqrtTwo_sq
        | exact invSqrtTwo_sq
        | change
            (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ +
                -((starRingEnd ℂ) 0 * 0) =
              1 / 2
          simpa only [map_zero, zero_mul, neg_zero, add_zero] using invSqrtTwo_sq
    | solve
      | simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, and_self,
          ↓reduceIte, one_div]
        norm_num [endpointTransfer, weightedTransfer, akltVBSMatrices,
          Fin.sum_univ_three, map_inv₀, div_eq_mul_inv]
        first
        | simpa only [one_div] using invSqrtTwo_sq
        | change
            (starRingEnd ℂ) ((Real.sqrt 2 : ℂ)⁻¹) *
                (Real.sqrt 2 : ℂ)⁻¹ =
              1 / 2
          simpa using invSqrtTwo_sq

/-- The endpoint–phase–endpoint contraction has the frozen closed form and is
independent of the number of phase sites except through the total ring length. -/
private theorem endpoint_phase_endpoint_closed (a b c : ℕ) :
    (Matrix.trace
      (ordinaryTransfer ^ a * endpointTransfer * phaseTransfer ^ b *
        endpointTransfer * ordinaryTransfer ^ c)).re =
      -(4 / 9 : ℝ) * (3 / 4 : ℝ) ^ (a + b + c + 2) -
        4 * (-1 / 4 : ℝ) ^ (a + b + c + 2) := by
  have hnegRe (n : ℕ) :
      (((-(1 / 4 : ℂ)) ^ n).re) = (-(1 / 4 : ℝ)) ^ n := by
    rw [show (-(1 / 4 : ℂ)) = ((-(1 / 4 : ℝ) : ℝ) : ℂ) by
      norm_num [div_eq_mul_inv]]
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hnegIm (n : ℕ) : (((-(1 / 4 : ℂ)) ^ n).im) = 0 := by
    rw [show (-(1 / 4 : ℂ)) = ((-(1 / 4 : ℝ) : ℝ) : ℂ) by
      norm_num [div_eq_mul_inv]]
    rw [← Complex.ofReal_pow, Complex.ofReal_im]
  have hnegDivRe (n : ℕ) :
      (((-1 / 4 : ℂ) ^ n).re) = (-1 / 4 : ℝ) ^ n := by
    rw [show (-1 / 4 : ℂ) = ((-1 / 4 : ℝ) : ℂ) by
      norm_num [div_eq_mul_inv]]
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hnegDivIm (n : ℕ) : (((-1 / 4 : ℂ) ^ n).im) = 0 := by
    rw [show (-1 / 4 : ℂ) = ((-1 / 4 : ℝ) : ℂ) by
      norm_num [div_eq_mul_inv]]
    rw [← Complex.ofReal_pow, Complex.ofReal_im]
  have hposRe (n : ℕ) :
      (((3 / 4 : ℂ) ^ n).re) = (3 / 4 : ℝ) ^ n := by
    rw [show (3 / 4 : ℂ) = ((3 / 4 : ℝ) : ℂ) by
      norm_num [div_eq_mul_inv]]
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hposIm (n : ℕ) : (((3 / 4 : ℂ) ^ n).im) = 0 := by
    rw [show (3 / 4 : ℂ) = ((3 / 4 : ℝ) : ℂ) by
      norm_num [div_eq_mul_inv]]
    rw [← Complex.ofReal_pow, Complex.ofReal_im]
  rw [ordinaryTransfer_pow, phaseTransfer_pow, ordinaryTransfer_pow,
    endpointTransfer_entries]
  rw [Matrix.trace, Fintype.sum_prod_type]
  simp only [Matrix.diag]
  simp only [Matrix.mul_apply]
  simp_rw [Fintype.sum_prod_type]
  unfold diagonalPairProjector antisymmetricPairProjector
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  simp only [one_div, mul_ite, mul_zero, Fin.isValue, Prod.mk.injEq,
    mul_neg, Fin.sum_univ_two, and_true, zero_ne_one, and_false, false_and,
    ↓reduceIte, one_ne_zero, true_and, add_zero, zero_add, ite_mul, zero_mul,
    neg_mul, ne_eq, not_false_eq_true, Matrix.one_apply_ne, zero_sub,
    Matrix.one_apply_eq, neg_neg, sub_self, neg_zero, Complex.add_re,
    Complex.mul_re, Complex.neg_re, Complex.inv_re, Complex.re_ofNat,
    Complex.normSq_ofNat, div_self_mul_self', Complex.inv_im,
    Complex.im_ofNat, zero_div, sub_zero, Complex.add_im, Complex.neg_im,
    Complex.mul_im, Complex.sub_re, Complex.one_re, Complex.sub_im,
    Complex.one_im, neg_sub, neg_add_rev]
  rw [hnegDivRe a, hnegDivRe b, hnegDivRe c, hnegDivIm a, hnegDivIm b,
    hnegDivIm c, hposRe a, hposRe b, hposRe c, hposIm a, hposIm b, hposIm c]
  norm_num [div_eq_mul_inv]
  ring

/-- The tail weight after the left endpoint is phase, right endpoint, then
ordinary transfer. -/
private noncomputable def afterEndpointTransfer (y z : ℕ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  if z < y then phaseTransfer else if z = y then endpointTransfer else ordinaryTransfer

/-- The full natural-index transfer word for an ordered string window. -/
private noncomputable def stringTransferAt (x y z : ℕ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  if z < x then ordinaryTransfer
  else if z = x then endpointTransfer
  else if z < y then phaseTransfer
  else if z = y then endpointTransfer
  else ordinaryTransfer

/-- A constant matrix word over a natural range is the corresponding power. -/
private theorem range_const_prod
    (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (n : ℕ) :
    ((List.range n).map fun _ => A).prod = A ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih]
      simp [pow_succ]

/-- The transfer word following the left endpoint has one phase block, the
right endpoint, and an ordinary suffix. -/
private theorem afterEndpointTransfer_prod (L y : ℕ) (hy : y < L) :
    ((List.range L).map (afterEndpointTransfer y)).prod =
      phaseTransfer ^ y * endpointTransfer * ordinaryTransfer ^ (L - y - 1) := by
  induction L generalizing y with
  | zero => omega
  | succ L ih =>
      rw [List.range_succ_eq_map, List.map_cons, List.prod_cons]
      cases y with
      | zero =>
          simp only [afterEndpointTransfer, Nat.not_lt_zero, ↓reduceIte]
          rw [show (List.map (afterEndpointTransfer 0) (List.map Nat.succ (List.range L))).prod =
              ordinaryTransfer ^ L by
            rw [List.map_map]
            convert range_const_prod ordinaryTransfer L using 2]
          simp
      | succ y =>
          have hyL : y < L := by omega
          rw [show
            (List.map (afterEndpointTransfer (y + 1)) (List.map Nat.succ (List.range L))).prod =
              phaseTransfer ^ y * endpointTransfer * ordinaryTransfer ^ (L - y - 1) by
            rw [List.map_map]
            convert ih y hyL using 2
            ext z
            simp [afterEndpointTransfer]]
          unfold afterEndpointTransfer
          rw [if_pos (by omega), pow_succ']
          rw [show L + 1 - (y + 1) - 1 = L - y - 1 by omega]
          noncomm_ring

/-- Every ordered string-transfer word splits into ordinary prefix, endpoint,
phase block, endpoint, and ordinary suffix. -/
private theorem stringTransferAt_prod (L x y : ℕ) (hxy : x < y) (hy : y < L) :
    ((List.range L).map (stringTransferAt x y)).prod =
      ordinaryTransfer ^ x * endpointTransfer * phaseTransfer ^ (y - x - 1) *
        endpointTransfer * ordinaryTransfer ^ (L - y - 1) := by
  induction L generalizing x y with
  | zero => omega
  | succ L ih =>
      rw [List.range_succ_eq_map, List.map_cons, List.prod_cons]
      cases x with
      | zero =>
          obtain ⟨y, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : y ≠ 0)
          have hyL : y < L := by omega
          rw [show
            (List.map (stringTransferAt 0 (y + 1)) (List.map Nat.succ (List.range L))).prod =
              phaseTransfer ^ y * endpointTransfer * ordinaryTransfer ^ (L - y - 1) by
            rw [List.map_map]
            convert afterEndpointTransfer_prod L y hyL using 2
            ext z
            simp [stringTransferAt, afterEndpointTransfer]]
          unfold stringTransferAt
          simp only [Nat.not_lt_zero, ↓reduceIte, pow_zero, one_mul]
          rw [show L + 1 - (y + 1) - 1 = L - y - 1 by omega]
          noncomm_ring
      | succ x =>
          cases y with
          | zero => omega
          | succ y =>
              have hxy' : x < y := by omega
              have hyL : y < L := by omega
              rw [show
                (List.map (stringTransferAt (x + 1) (y + 1))
                    (List.map Nat.succ (List.range L))).prod =
                  ordinaryTransfer ^ x * endpointTransfer *
                    phaseTransfer ^ (y - x - 1) * endpointTransfer *
                      ordinaryTransfer ^ (L - y - 1) by
                rw [List.map_map]
                convert ih x y hxy' hyL using 2
                ext z
                simp [stringTransferAt]]
              unfold stringTransferAt
              rw [if_pos (by omega), pow_succ']
              rw [show y + 1 - (x + 1) - 1 = y - x - 1 by omega]
              rw [show L + 1 - (y + 1) - 1 = L - y - 1 by omega]
              noncomm_ring

/-- The configuration weight for the axis-three string observable. -/
private noncomputable def stringWeight {L : ℕ} (x y z : Fin L) (σ : Fin 3) : ℂ :=
  if z.val < x.val then 1
  else if z.val = x.val then (1 - (σ : ℕ) : ℂ)
  else if z.val < y.val then (-1 : ℂ) ^ (σ.val + 1)
  else if z.val = y.val then (1 - (σ : ℕ) : ℂ)
  else 1

/-- The weighted local transfer agrees with the natural-index transfer word. -/
private theorem weightedTransfer_stringWeight {L : ℕ} (x y z : Fin L) :
    weightedTransfer (stringWeight x y z) = stringTransferAt x.val y.val z.val := by
  unfold stringWeight stringTransferAt ordinaryTransfer endpointTransfer phaseTransfer
  split_ifs <;> rfl

/-- The weighted-transfer list for an ordered window has the exact five-block
factorization consumed by the closed-form contraction. -/
private theorem weightedTransfer_stringWeight_prod {L : ℕ} (x y : Fin L)
    (hxy : x.val < y.val) :
    (List.ofFn fun z : Fin L => weightedTransfer (stringWeight x y z)).prod =
      ordinaryTransfer ^ x.val * endpointTransfer *
        phaseTransfer ^ (y.val - x.val - 1) * endpointTransfer *
          ordinaryTransfer ^ (L - y.val - 1) := by
  rw [List.ofFn_eq_map]
  simp_rw [weightedTransfer_stringWeight x y]
  rw [show
    List.map (fun z : Fin L => stringTransferAt x.val y.val z.val) (List.finRange L) =
      List.map (stringTransferAt x.val y.val) (List.range L) by
    rw [← List.map_coe_finRange_eq_range, List.map_map]
    congr 1]
  exact stringTransferAt_prod L x.val y.val hxy y.isLt

/-- The product of local string weights is the two endpoint factors times
the strict-interior phase product. -/
private theorem stringWeight_prod {L : ℕ} (x y : Fin L) (hxy : x.val < y.val)
    (σ : Fin L → Fin 3) :
    (∏ z, stringWeight x y z (σ z)) =
      (1 - ((σ x).val : ℂ)) *
        (∏ z ∈ Finset.univ.filter fun z : Fin L =>
          x.val < z.val ∧ z.val < y.val, (-1 : ℂ) ^ ((σ z).val + 1)) *
        (1 - ((σ y).val : ℂ)) := by
  classical
  have hxy_ne : x ≠ y := fun h => by subst y; omega
  let interior := Finset.univ.filter fun z : Fin L =>
    x.val < z.val ∧ z.val < y.val
  have hinterior_subset :
      interior ⊆ (Finset.univ.erase x).erase y := by
    intro z hz
    simp only [interior, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    constructor <;> intro h
    · subst z
      omega
    · subst z
      omega
  have hinterior_weight :
      (∏ z ∈ (Finset.univ.erase x).erase y, stringWeight x y z (σ z)) =
        ∏ z ∈ interior, stringWeight x y z (σ z) := by
    apply (Finset.prod_subset hinterior_subset ?_).symm
    intro z hz hnot
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hz
    simp only [interior, Finset.mem_filter, Finset.mem_univ, true_and] at hnot
    by_cases hzx : z.val < x.val
    · simp [stringWeight, hzx]
    · have hz_ne_x : z.val ≠ x.val := by
        intro hval
        apply hz.2
        exact Fin.ext hval
      have hzy : ¬z.val < y.val := by
        intro hlt
        exact hnot ⟨by omega, hlt⟩
      have hz_ne_y : z.val ≠ y.val := by
        intro hval
        apply hz.1
        exact Fin.ext hval
      simp [stringWeight, hzx, hz_ne_x, hzy, hz_ne_y]
  have hinterior_phase :
      (∏ z ∈ interior, stringWeight x y z (σ z)) =
        ∏ z ∈ interior, (-1 : ℂ) ^ ((σ z).val + 1) := by
    apply Finset.prod_congr rfl
    intro z hz
    simp only [interior, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have hzx : ¬z.val < x.val := by omega
    have hz_ne_x : z.val ≠ x.val := by omega
    simp [stringWeight, hzx, hz_ne_x, hz.2]
  calc
    _ = stringWeight x y x (σ x) *
        ∏ z ∈ (Finset.univ.erase x), stringWeight x y z (σ z) :=
      (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)).symm
    _ = stringWeight x y x (σ x) *
        (stringWeight x y y (σ y) *
          ∏ z ∈ (Finset.univ.erase x).erase y, stringWeight x y z (σ z)) := by
      congr 1
      exact (Finset.mul_prod_erase (Finset.univ.erase x)
        (fun z => stringWeight x y z (σ z)) (by
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          exact Ne.symm hxy_ne)).symm
    _ = _ := by
      rw [show stringWeight x y x (σ x) = 1 - ((σ x).val : ℂ) by
        simp [stringWeight],
        show stringWeight x y y (σ y) = 1 - ((σ y).val : ℂ) by
          simp [stringWeight, show ¬y.val < x.val by omega,
            show y.val ≠ x.val by omega]]
      rw [hinterior_weight, hinterior_phase]
      change
        (1 - ((σ x).val : ℂ)) *
            ((1 - ((σ y).val : ℂ)) *
              ∏ z ∈ Finset.univ.filter fun z : Fin L =>
                x.val < z.val ∧ z.val < y.val,
                  (-1 : ℂ) ^ ((σ z).val + 1)) =
          _
      ring

/-- A site-embedded diagonal matrix is diagonal on configurations. -/
private theorem onSite_diagonal {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (i : Λ) (w : Fin 3 → ℂ) :
    (onSiteS i (Matrix.diagonal w) : ManyBodyOpS Λ 2) =
      Matrix.diagonal fun σ => w (σ i) := by
  ext σ' σ
  simp only [onSiteS_apply, Matrix.diagonal_apply]
  by_cases h : σ' = σ
  · subst σ'
    simp
  · rw [if_neg h]
    by_cases hoff : ∀ k, k ≠ i → σ' k = σ k
    · have hi : σ' i ≠ σ i := fun hi => h (funext fun k => by
        by_cases hk : k = i
        · simpa [hk] using hi
        · exact hoff k hk)
      simp [hi]
    · simp [hoff]

/-- The spin-one axis-three matrix has the frozen diagonal weights. -/
private theorem spinSOp3_two_eq_diagonal :
    spinSOp3 2 =
      Matrix.diagonal fun k : Fin 3 => (1 - (k.val : ℂ)) := by
  unfold spinSOp3
  congr 1
  funext k
  norm_num

/-- The concrete axis-three string observable is diagonal with the product
of the frozen local weights. -/
private theorem stringObservable_eq_diagonal {L : ℕ} (x y : Fin L)
    (hxy : x.val < y.val) :
    spinSSiteOp3 x 2 * stringOperatorS x y * spinSSiteOp3 y 2 =
      Matrix.diagonal fun σ => ∏ z, stringWeight x y z (σ z) := by
  rw [spinSSiteOp3_def, spinSSiteOp3_def]
  rw [spinSOp3_two_eq_diagonal]
  rw [onSite_diagonal, onSite_diagonal]
  unfold stringOperatorS
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext σ
  rw [stringWeight_prod x y hxy σ]
  simp [spinSStringPhaseS1]

/-- The unnormalized raw string numerator has the frozen exact finite-volume
closed form. -/
private theorem rawStringNumerator_exact {L : ℕ} (x y : Fin L)
    (hxy : x.val < y.val) :
    (star (akltVBSState L) ⬝ᵥ
      (spinSSiteOp3 x 2 * stringOperatorS x y * spinSSiteOp3 y 2).mulVec
        (akltVBSState L)).re =
      -(4 / 9 : ℝ) * (3 / 4 : ℝ) ^ L - 4 * (-1 / 4 : ℝ) ^ L := by
  rw [stringObservable_eq_diagonal x y hxy]
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
  have h := weighted_state_contraction L (fun z σ => stringWeight x y z σ)
  rw [weightedTransfer_stringWeight_prod x y hxy] at h
  rw [show (∑ σ, star (akltVBSState L σ) *
      ((∏ z, stringWeight x y z (σ z)) * akltVBSState L σ)) =
      ∑ σ, (∏ z, stringWeight x y z (σ z)) *
        star (akltVBSState L σ) * akltVBSState L σ by
      apply Finset.sum_congr rfl
      intro σ _
      ring, h]
  rw [endpoint_phase_endpoint_closed]
  congr 1
  · congr 3
    omega
  · congr 3
    omega

/-- The trace of the ordinary transfer power is the frozen periodic norm
formula. -/
private theorem trace_ordinaryTransfer_pow (n : ℕ) :
    (Matrix.trace (ordinaryTransfer ^ n)).re =
      (3 / 4 : ℝ) ^ n + 3 * (-1 / 4 : ℝ) ^ n := by
  rw [ordinaryTransfer_pow]
  rw [Matrix.trace, Fintype.sum_prod_type]
  unfold diagonalPairProjector
  simp only [Matrix.diag_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.one_apply_eq, smul_eq_mul]
  simp only [and_self, one_div, mul_ite, mul_zero, Fin.sum_univ_two,
    Fin.isValue, ↓reduceIte, zero_ne_one, sub_zero, mul_one, add_zero,
    one_ne_zero, Complex.add_re, Complex.mul_re, Complex.sub_re,
    Complex.one_re, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
    div_self_mul_self', Complex.sub_im, Complex.one_im, Complex.inv_im,
    Complex.im_ofNat, neg_zero, zero_div, sub_self]
  norm_num
  have hneg : (((-(1 / 4 : ℂ)) ^ n).re) = (-(1 / 4 : ℝ)) ^ n := by
    rw [show (-(1 / 4 : ℂ)) = ((-(1 / 4 : ℝ) : ℝ) : ℂ) by
      norm_num [div_eq_mul_inv]]
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hpos : (((3 / 4 : ℂ) ^ n).re) = (3 / 4 : ℝ) ^ n := by
    rw [show (3 / 4 : ℂ) = ((3 / 4 : ℝ) : ℂ) by
      norm_num [div_eq_mul_inv]]
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [hneg, hpos]
  ring

/-- The squared norm of the frozen periodic trace-product akltVBSState has Tasaki's
exact finite-volume formula. -/
private theorem state_norm_exact (L : ℕ) :
    vecNormSqRe (akltVBSState L) =
      (3 / 4 : ℝ) ^ L + 3 * (-1 / 4 : ℝ) ^ L := by
  have hprod :
      (List.ofFn fun _ : Fin L => ordinaryTransfer).prod = ordinaryTransfer ^ L := by
    induction L with
    | zero => rfl
    | succ L ih =>
        rw [List.ofFn_succ, List.prod_cons, pow_succ', ih]
  have h := weighted_state_contraction L (fun _ _ => (1 : ℂ))
  simp only [Finset.prod_const_one, one_mul] at h
  rw [show (List.ofFn fun z : Fin L => weightedTransfer (fun _ => (1 : ℂ))).prod =
      ordinaryTransfer ^ L by simpa only [ordinaryTransfer] using hprod] at h
  unfold vecNormSqRe dotProduct
  simp only [Pi.star_apply]
  rw [h]
  exact trace_ordinaryTransfer_pow L

/-- The frozen periodic akltVBSState has a strictly positive squared norm once the
ring contains at least two sites. -/
private theorem state_norm_pos (L : ℕ) (hL : 2 ≤ L) :
    0 < vecNormSqRe (akltVBSState L) := by
  rw [state_norm_exact]
  have hfactor :
      (3 / 4 : ℝ) ^ L + 3 * (-1 / 4 : ℝ) ^ L =
        (1 / 4 : ℝ) ^ L * ((3 : ℝ) ^ L + 3 * (-1 : ℝ) ^ L) := by
    rw [show (3 / 4 : ℝ) = (1 / 4) * 3 by norm_num,
      show (-1 / 4 : ℝ) = (1 / 4) * (-1) by norm_num,
      mul_pow, mul_pow]
    ring
  rw [hfactor]
  apply mul_pos (pow_pos (by norm_num) L)
  rcases Nat.even_or_odd L with hEven | hOdd
  · rw [hEven.neg_one_pow]
    positivity
  · rw [hOdd.neg_one_pow]
    have hpow : (3 : ℝ) < 3 ^ L := by
      simpa using pow_lt_pow_right₀ (a := (3 : ℝ)) (by norm_num)
        (show 1 < L by omega)
    nlinarith

/-- The normalized axis-three string correlation has the frozen exact
finite-volume formula. -/
private theorem stringCorrelationS_akltVBSState_exact (L : ℕ) (hL : 2 ≤ L)
    (x y : Fin L) (hx : 0 < x.val) (hxy : x.val < y.val) :
    stringCorrelationS x y (akltVBSState L) =
      ((4 / 9 : ℝ) + 4 * (-1 / 3 : ℝ) ^ L) /
        (1 + 3 * (-1 / 3 : ℝ) ^ L) := by
  have _hx : 0 < x.val := hx
  have hnorm_ne : vecNormSqRe (akltVBSState L) ≠ 0 :=
    ne_of_gt (state_norm_pos L hL)
  have hratio :
      (-1 / 4 : ℝ) ^ L =
        (3 / 4 : ℝ) ^ L * (-1 / 3 : ℝ) ^ L := by
    rw [← mul_pow]
    congr 1
    norm_num
  unfold stringCorrelationS expectationRatioRe
  change
    -((star (akltVBSState L) ⬝ᵥ
          (spinSSiteOp3 x 2 * stringOperatorS x y *
            spinSSiteOp3 y 2).mulVec (akltVBSState L)).re /
        vecNormSqRe (akltVBSState L)) = _
  rw [rawStringNumerator_exact x y hxy, state_norm_exact, hratio]
  have hpow_ne : (3 / 4 : ℝ) ^ L ≠ 0 := pow_ne_zero L (by norm_num)
  field_simp
  ring

/-- The normalized finite-volume denominator in ratio coordinates is
strictly positive. -/
private theorem ratioDenominator_pos (L : ℕ) (hL : 2 ≤ L) :
    0 < 1 + 3 * (-1 / 3 : ℝ) ^ L := by
  have hratio :
      (-1 / 4 : ℝ) ^ L =
        (3 / 4 : ℝ) ^ L * (-1 / 3 : ℝ) ^ L := by
    rw [← mul_pow]
    congr 1
    norm_num
  have hnorm := state_norm_pos L hL
  rw [state_norm_exact, hratio] at hnorm
  have hfactor :
      (3 / 4 : ℝ) ^ L +
          3 * ((3 / 4 : ℝ) ^ L * (-1 / 3 : ℝ) ^ L) =
        (3 / 4 : ℝ) ^ L * (1 + 3 * (-1 / 3 : ℝ) ^ L) := by
    ring
  rw [hfactor] at hnorm
  exact pos_of_mul_pos_right hnorm (pow_pos (by norm_num) L).le

/-- Subtracting the thermodynamic value exposes the single decaying
eigenvalue ratio. -/
private theorem stringCorrelationS_state_sub_four_ninths (L : ℕ) (hL : 2 ≤ L)
    (x y : Fin L) (hx : 0 < x.val) (hxy : x.val < y.val) :
    stringCorrelationS x y (akltVBSState L) - (4 / 9 : ℝ) =
      ((8 / 3 : ℝ) * (-1 / 3 : ℝ) ^ L) /
        (1 + 3 * (-1 / 3 : ℝ) ^ L) := by
  rw [stringCorrelationS_akltVBSState_exact L hL x y hx hxy]
  have hden : 1 + 3 * (-1 / 3 : ℝ) ^ L ≠ 0 :=
    ne_of_gt (ratioDenominator_pos L hL)
  rw [div_sub' hden]
  congr 1
  ring

/-- The axis-three finite-volume correlation is uniformly within any
positive tolerance of four ninths for all sufficiently large rings. -/
theorem Internal.axis3Epsilon :
    ∀ ε : ℝ, 0 < ε →
      ∃ L₀ : ℕ, 2 ≤ L₀ ∧
        ∀ L : ℕ, L₀ ≤ L →
          ∀ x y : Fin L, 0 < x.val → x.val < y.val →
            |stringCorrelationS x y (akltVBSState L) - (4 / 9 : ℝ)| < ε := by
  intro ε hε
  have hr :
      Filter.Tendsto (fun L : ℕ => (-1 / 3 : ℝ) ^ L)
        Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  have hnum :
      Filter.Tendsto (fun L : ℕ => (8 / 3 : ℝ) * (-1 / 3 : ℝ) ^ L)
        Filter.atTop (nhds 0) := by
    simpa using Filter.Tendsto.const_mul (8 / 3 : ℝ) hr
  have hden :
      Filter.Tendsto (fun L : ℕ => 1 + 3 * (-1 / 3 : ℝ) ^ L)
        Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add
      (Filter.Tendsto.const_mul (3 : ℝ) hr)
  have hquot :
      Filter.Tendsto
        (fun L : ℕ =>
          ((8 / 3 : ℝ) * (-1 / 3 : ℝ) ^ L) /
            (1 + 3 * (-1 / 3 : ℝ) ^ L))
        Filter.atTop (nhds 0) := by
    simpa using hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hquot) ε hε
  refine ⟨max 2 N, le_max_left _ _, ?_⟩
  intro L hL x y hx hxy
  rw [stringCorrelationS_state_sub_four_ninths L
    (le_trans (le_max_left 2 N) hL) x y hx hxy]
  have hdist := hN L (le_trans (le_max_right 2 N) hL)
  simpa only [Real.dist_eq, sub_zero] using hdist

end LatticeSystem.Quantum.AKLTStringOrder
