import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveSectorGround
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveSU2Invariance
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorReduction
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinChargeCommutation

/-!
# The number-sector compressed `su(2)` algebra for the attractive Hubbard model (Tasaki §10.2.1)

Toward discharging `theorem_10_2_lieb_attractive_unique_singlet`, the Lieb singlet lift applies the
generic angular-momentum engine (`LatticeSystem.Math.ham_eigenstate_spin_zero_or_half`,
`ham_su2_multiplet`) to the `Ne`-electron-sector **compression** of the attractive Hubbard
Hamiltonian and of the three Cartesian total-spin generators `Ŝ⁽¹⁾, Ŝ⁽²⁾, Ŝ³`.  This file supplies
the hypotheses that engine needs: each compressed operator is Hermitian
(`configSectorCompress_isHermitian`), the compressed generators satisfy the `su(2)` relations
(`configSectorNumberCompress_su2_12/23/31`), and the compressed `Ĥ_W` commutes with each compressed
generator (`configSectorNumberCompress_attractive_commute_one/two/three`).

It is the number-sector analogue of `TJFillingCompressSpinAlgebra.lean` (the t-J filling
development, Prop 11.24): the compression is the same generic `configSector` core
(`HubbardImpossibilityLowUVariationalCore.lean`) instantiated at `hubbardNumberSectorPred N Ne`, and
the Cartesian generators `tJTotalSpinOne`/`tJTotalSpinTwo` (defined purely from
`fermionTotalSpinPlus/Minus`, `TJSectorReduction.lean`) are the shared spinful-Fock total-spin
operators reused verbatim for the attractive Hubbard case.

## Main results

* `preservesHubbardSectorW_of_commute`, `preservesHubbardSectorW_smul/add/sub` — the reusable
  `W`-preservation hypothesis (an operator commuting with `N̂` preserves the `Ne`-sector) and its
  submodule closure.
* `preservesHubbardSectorW_fermionTotalSpin{Plus,Minus,Z}`,
  `preservesHubbardSectorW_tJTotalSpin{One,Two}` — total-spin operators preserve the `Ne`-sector.
* `configSectorCompress_smul`, `configSectorCompress_sub` — the compression is `ℂ`-linear.
* `configSectorNumberCompress_mul_of_right_preserves` — the compression homomorphism
  `compress(A) compress(B) = compress(A B)` when `B` preserves the `Ne`-sector.
* `configSectorNumberCompress_su2_12/23/31` — the compressed generators satisfy the `su(2)`
  relations.
* `configSectorNumberCompress_attractive_commute_one/two/three` — `Ĥ_W` commutes with each
  compressed generator.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.1 (Theorem 10.2); Appendix A.3.2 Theorem A.17.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-! ## `W`-preservation from commuting with `N̂` and its submodule closure -/

/-- An operator commuting with the total number `N̂` preserves the `Ne`-electron sector `W`. -/
theorem preservesHubbardSectorW_of_commute (Ne : ℕ) {B : ManyBodyOp (Fin (2 * N + 2))}
    (hN : Commute B (fermionTotalNumber (2 * N + 1))) : PreservesHubbardSectorW N Ne B := by
  intro v hv
  rw [mem_hubbardSectorWSubmodule_iff] at hv ⊢
  rw [Matrix.mulVec_mulVec, ← hN.eq, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]

/-- `PreservesHubbardSectorW` is closed under scalar multiplication (`W` is a submodule). -/
theorem preservesHubbardSectorW_smul (Ne : ℕ) {B : ManyBodyOp (Fin (2 * N + 2))}
    (h : PreservesHubbardSectorW N Ne B) (c : ℂ) : PreservesHubbardSectorW N Ne (c • B) := by
  intro v hv
  rw [Matrix.smul_mulVec]
  exact Submodule.smul_mem _ c (h v hv)

/-- `PreservesHubbardSectorW` is closed under addition. -/
theorem preservesHubbardSectorW_add (Ne : ℕ) {B₁ B₂ : ManyBodyOp (Fin (2 * N + 2))}
    (h₁ : PreservesHubbardSectorW N Ne B₁) (h₂ : PreservesHubbardSectorW N Ne B₂) :
    PreservesHubbardSectorW N Ne (B₁ + B₂) := by
  intro v hv
  rw [Matrix.add_mulVec]
  exact Submodule.add_mem _ (h₁ v hv) (h₂ v hv)

/-- `PreservesHubbardSectorW` is closed under subtraction. -/
theorem preservesHubbardSectorW_sub (Ne : ℕ) {B₁ B₂ : ManyBodyOp (Fin (2 * N + 2))}
    (h₁ : PreservesHubbardSectorW N Ne B₁) (h₂ : PreservesHubbardSectorW N Ne B₂) :
    PreservesHubbardSectorW N Ne (B₁ - B₂) := by
  intro v hv
  rw [Matrix.sub_mulVec]
  exact Submodule.sub_mem _ (h₁ v hv) (h₂ v hv)

/-- `Ŝ³_tot` preserves the `Ne`-sector `W`. -/
theorem preservesHubbardSectorW_fermionTotalSpinZ (Ne : ℕ) :
    PreservesHubbardSectorW N Ne (fermionTotalSpinZ N) :=
  preservesHubbardSectorW_of_commute Ne (fermionTotalSpinZ_commute_fermionTotalNumber N)

/-- `Ŝ⁺_tot` preserves the `Ne`-sector `W`. -/
theorem preservesHubbardSectorW_fermionTotalSpinPlus (Ne : ℕ) :
    PreservesHubbardSectorW N Ne (fermionTotalSpinPlus N) :=
  preservesHubbardSectorW_of_commute Ne (fermionTotalSpinPlus_commute_fermionTotalNumber N)

/-- `Ŝ⁻_tot` preserves the `Ne`-sector `W`. -/
theorem preservesHubbardSectorW_fermionTotalSpinMinus (Ne : ℕ) :
    PreservesHubbardSectorW N Ne (fermionTotalSpinMinus N) :=
  preservesHubbardSectorW_of_commute Ne (fermionTotalSpinMinus_commute_fermionTotalNumber N)

/-- `Ŝ⁽¹⁾_tot = ½(Ŝ⁺+Ŝ⁻)` preserves the `Ne`-sector `W`. -/
theorem preservesHubbardSectorW_tJTotalSpinOne (Ne : ℕ) :
    PreservesHubbardSectorW N Ne (tJTotalSpinOne N) := by
  unfold tJTotalSpinOne
  exact preservesHubbardSectorW_smul Ne (preservesHubbardSectorW_add Ne
    (preservesHubbardSectorW_fermionTotalSpinPlus Ne)
    (preservesHubbardSectorW_fermionTotalSpinMinus Ne)) _

/-- `Ŝ⁽²⁾_tot = −(i/2)(Ŝ⁺−Ŝ⁻)` preserves the `Ne`-sector `W`. -/
theorem preservesHubbardSectorW_tJTotalSpinTwo (Ne : ℕ) :
    PreservesHubbardSectorW N Ne (tJTotalSpinTwo N) := by
  unfold tJTotalSpinTwo
  exact preservesHubbardSectorW_smul Ne (preservesHubbardSectorW_sub Ne
    (preservesHubbardSectorW_fermionTotalSpinPlus Ne)
    (preservesHubbardSectorW_fermionTotalSpinMinus Ne)) _

/-! ## Compression linearity -/

/-- `compress` is `ℂ`-homogeneous: `compress(c • A) = c • compress(A)`. -/
theorem configSectorCompress_smul (P : (Fin (2 * N + 2) → Fin 2) → Prop) [DecidablePred P]
    (c : ℂ) (A : ManyBodyOp (Fin (2 * N + 2))) :
    configSectorCompress N P (c • A) = c • configSectorCompress N P A := by
  unfold configSectorCompress
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- `compress` is additive on differences: `compress(A - B) = compress(A) - compress(B)`. -/
theorem configSectorCompress_sub (P : (Fin (2 * N + 2) → Fin 2) → Prop) [DecidablePred P]
    (A B : ManyBodyOp (Fin (2 * N + 2))) :
    configSectorCompress N P (A - B) = configSectorCompress N P A - configSectorCompress N P B := by
  unfold configSectorCompress
  rw [Matrix.mul_sub, Matrix.sub_mul]

/-! ## The compression homomorphism on the number sector -/

/-- The projection `T Tᴴ` fixes `B T` when `B` preserves the `Ne`-sector `W` (each column
`B |s⟩ ∈ W`). -/
theorem configSectorNumberProjection_mul_of_preserves (Ne : ℕ)
    {B : ManyBodyOp (Fin (2 * N + 2))} (hB : PreservesHubbardSectorW N Ne B) :
    (configSectorEmbedding N (hubbardNumberSectorPred N Ne)
          * (configSectorEmbedding N (hubbardNumberSectorPred N Ne))ᴴ)
        * (B * configSectorEmbedding N (hubbardNumberSectorPred N Ne))
      = B * configSectorEmbedding N (hubbardNumberSectorPred N Ne) := by
  ext w s
  have hcol : (fun x => (B * configSectorEmbedding N (hubbardNumberSectorPred N Ne)) x s)
      = B.mulVec (basisVec s.val) := by
    funext x; rw [Matrix.mul_apply]; rfl
  have hmemW : B.mulVec (basisVec s.val) ∈ hubbardSectorWSubmodule N Ne :=
    hB _ (basisVec_sector_mem Ne s)
  have hsupp : ∀ ww, ¬ hubbardNumberSectorPred N Ne ww → B.mulVec (basisVec s.val) ww = 0 :=
    hubbardNumberSector_supported_of_mem Ne hmemW
  rw [Matrix.mul_apply,
    show (∑ x, (configSectorEmbedding N (hubbardNumberSectorPred N Ne)
            * (configSectorEmbedding N (hubbardNumberSectorPred N Ne))ᴴ) w x *
          (B * configSectorEmbedding N (hubbardNumberSectorPred N Ne)) x s)
        = ((configSectorEmbedding N (hubbardNumberSectorPred N Ne)
            * (configSectorEmbedding N (hubbardNumberSectorPred N Ne))ᴴ).mulVec
            (B.mulVec (basisVec s.val))) w from by
      rw [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl (fun x _ => by rw [congrFun hcol x]),
    configSectorProjection_mulVec_eq_of_supported (hubbardNumberSectorPred N Ne) hsupp,
    ← congrFun hcol w]

/-- **Compression homomorphism (number sector).** `compress(A) compress(B) = compress(A B)` when
`B` preserves the `Ne`-sector `W` (so the intermediate projection `T Tᴴ` between `A` and `B` is
invisible). -/
theorem configSectorNumberCompress_mul_of_right_preserves (Ne : ℕ)
    (A : ManyBodyOp (Fin (2 * N + 2))) {B : ManyBodyOp (Fin (2 * N + 2))}
    (hB : PreservesHubbardSectorW N Ne B) :
    configSectorCompress N (hubbardNumberSectorPred N Ne) A
        * configSectorCompress N (hubbardNumberSectorPred N Ne) B
      = configSectorCompress N (hubbardNumberSectorPred N Ne) (A * B) := by
  unfold configSectorCompress
  rw [show (configSectorEmbedding N (hubbardNumberSectorPred N Ne))ᴴ * A
          * configSectorEmbedding N (hubbardNumberSectorPred N Ne)
          * ((configSectorEmbedding N (hubbardNumberSectorPred N Ne))ᴴ * B
            * configSectorEmbedding N (hubbardNumberSectorPred N Ne))
        = (configSectorEmbedding N (hubbardNumberSectorPred N Ne))ᴴ * A
          * ((configSectorEmbedding N (hubbardNumberSectorPred N Ne)
              * (configSectorEmbedding N (hubbardNumberSectorPred N Ne))ᴴ)
            * (B * configSectorEmbedding N (hubbardNumberSectorPred N Ne))) by
      simp only [Matrix.mul_assoc],
    configSectorNumberProjection_mul_of_preserves Ne hB]
  simp only [Matrix.mul_assoc]

/-! ## The compressed `su(2)` relations -/

/-- The compressed `Ŝ⁽¹⁾_W, Ŝ⁽²⁾_W, Ŝ³_W` satisfy `[Ŝ⁽¹⁾_W, Ŝ⁽²⁾_W] = i Ŝ³_W`. -/
theorem configSectorNumberCompress_su2_12 (Ne : ℕ) :
    configSectorCompress N (hubbardNumberSectorPred N Ne) (tJTotalSpinOne N)
        * configSectorCompress N (hubbardNumberSectorPred N Ne) (tJTotalSpinTwo N)
      - configSectorCompress N (hubbardNumberSectorPred N Ne) (tJTotalSpinTwo N)
        * configSectorCompress N (hubbardNumberSectorPred N Ne) (tJTotalSpinOne N)
      = Complex.I
        • configSectorCompress N (hubbardNumberSectorPred N Ne) (fermionTotalSpinZ N) := by
  rw [configSectorNumberCompress_mul_of_right_preserves Ne _
      (preservesHubbardSectorW_tJTotalSpinTwo Ne),
    configSectorNumberCompress_mul_of_right_preserves Ne _
      (preservesHubbardSectorW_tJTotalSpinOne Ne),
    ← configSectorCompress_sub, tJTotalSpin_su2_12, configSectorCompress_smul]

/-- The compressed operators satisfy `[Ŝ⁽²⁾_W, Ŝ³_W] = i Ŝ⁽¹⁾_W`. -/
theorem configSectorNumberCompress_su2_23 (Ne : ℕ) :
    configSectorCompress N (hubbardNumberSectorPred N Ne) (tJTotalSpinTwo N)
        * configSectorCompress N (hubbardNumberSectorPred N Ne) (fermionTotalSpinZ N)
      - configSectorCompress N (hubbardNumberSectorPred N Ne) (fermionTotalSpinZ N)
        * configSectorCompress N (hubbardNumberSectorPred N Ne) (tJTotalSpinTwo N)
      = Complex.I • configSectorCompress N (hubbardNumberSectorPred N Ne) (tJTotalSpinOne N) := by
  rw [configSectorNumberCompress_mul_of_right_preserves Ne _
      (preservesHubbardSectorW_fermionTotalSpinZ Ne),
    configSectorNumberCompress_mul_of_right_preserves Ne _
      (preservesHubbardSectorW_tJTotalSpinTwo Ne),
    ← configSectorCompress_sub, tJTotalSpin_su2_23, configSectorCompress_smul]

/-- The compressed operators satisfy `[Ŝ³_W, Ŝ⁽¹⁾_W] = i Ŝ⁽²⁾_W`. -/
theorem configSectorNumberCompress_su2_31 (Ne : ℕ) :
    configSectorCompress N (hubbardNumberSectorPred N Ne) (fermionTotalSpinZ N)
        * configSectorCompress N (hubbardNumberSectorPred N Ne) (tJTotalSpinOne N)
      - configSectorCompress N (hubbardNumberSectorPred N Ne) (tJTotalSpinOne N)
        * configSectorCompress N (hubbardNumberSectorPred N Ne) (fermionTotalSpinZ N)
      = Complex.I • configSectorCompress N (hubbardNumberSectorPred N Ne) (tJTotalSpinTwo N) := by
  rw [configSectorNumberCompress_mul_of_right_preserves Ne _
      (preservesHubbardSectorW_tJTotalSpinOne Ne),
    configSectorNumberCompress_mul_of_right_preserves Ne _
      (preservesHubbardSectorW_fermionTotalSpinZ Ne),
    ← configSectorCompress_sub, tJTotalSpin_su2_31, configSectorCompress_smul]

/-! ## `Ĥ_W` commutes with the compressed generators -/

/-- The attractive Hamiltonian commutes with `Ŝ⁽¹⁾_tot = ½(Ŝ⁺+Ŝ⁻)`. -/
theorem attractiveHubbardHamiltonian_mul_tJTotalSpinOne
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT_symm : ∀ i j, T i j = T j i) :
    attractiveHubbardHamiltonian N T U * tJTotalSpinOne N
      = tJTotalSpinOne N * attractiveHubbardHamiltonian N T U := by
  have hcP := (fermionTotalSpinPlus_commute_attractiveHubbardHamiltonian N T U).eq.symm
  have hcM := (fermionTotalSpinMinus_commute_attractiveHubbardHamiltonian N T U hT_symm).eq.symm
  rw [tJTotalSpinOne, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, hcP, hcM]

/-- The attractive Hamiltonian commutes with `Ŝ⁽²⁾_tot = −(i/2)(Ŝ⁺−Ŝ⁻)`. -/
theorem attractiveHubbardHamiltonian_mul_tJTotalSpinTwo
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT_symm : ∀ i j, T i j = T j i) :
    attractiveHubbardHamiltonian N T U * tJTotalSpinTwo N
      = tJTotalSpinTwo N * attractiveHubbardHamiltonian N T U := by
  have hcP := (fermionTotalSpinPlus_commute_attractiveHubbardHamiltonian N T U).eq.symm
  have hcM := (fermionTotalSpinMinus_commute_attractiveHubbardHamiltonian N T U hT_symm).eq.symm
  rw [tJTotalSpinTwo, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, hcP, hcM]

/-- `Ĥ_W` commutes with `Ŝ⁽¹⁾_W`. -/
theorem configSectorNumberCompress_attractive_commute_one (Ne : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT_symm : ∀ i j, T i j = T j i) :
    configSectorCompress N (hubbardNumberSectorPred N Ne) (attractiveHubbardHamiltonian N T U)
        * configSectorCompress N (hubbardNumberSectorPred N Ne) (tJTotalSpinOne N)
      = configSectorCompress N (hubbardNumberSectorPred N Ne) (tJTotalSpinOne N)
        * configSectorCompress N (hubbardNumberSectorPred N Ne)
          (attractiveHubbardHamiltonian N T U) := by
  rw [configSectorNumberCompress_mul_of_right_preserves Ne _
      (preservesHubbardSectorW_tJTotalSpinOne Ne),
    attractiveHubbardHamiltonian_mul_tJTotalSpinOne T U hT_symm,
    ← configSectorNumberCompress_mul_of_right_preserves Ne _
      (preservesHubbardSectorW_attractive Ne T U)]

/-- `Ĥ_W` commutes with `Ŝ⁽²⁾_W`. -/
theorem configSectorNumberCompress_attractive_commute_two (Ne : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT_symm : ∀ i j, T i j = T j i) :
    configSectorCompress N (hubbardNumberSectorPred N Ne) (attractiveHubbardHamiltonian N T U)
        * configSectorCompress N (hubbardNumberSectorPred N Ne) (tJTotalSpinTwo N)
      = configSectorCompress N (hubbardNumberSectorPred N Ne) (tJTotalSpinTwo N)
        * configSectorCompress N (hubbardNumberSectorPred N Ne)
          (attractiveHubbardHamiltonian N T U) := by
  rw [configSectorNumberCompress_mul_of_right_preserves Ne _
      (preservesHubbardSectorW_tJTotalSpinTwo Ne),
    attractiveHubbardHamiltonian_mul_tJTotalSpinTwo T U hT_symm,
    ← configSectorNumberCompress_mul_of_right_preserves Ne _
      (preservesHubbardSectorW_attractive Ne T U)]

/-- `Ĥ_W` commutes with `Ŝ³_W`. -/
theorem configSectorNumberCompress_attractive_commute_three (Ne : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) :
    configSectorCompress N (hubbardNumberSectorPred N Ne) (attractiveHubbardHamiltonian N T U)
        * configSectorCompress N (hubbardNumberSectorPred N Ne) (fermionTotalSpinZ N)
      = configSectorCompress N (hubbardNumberSectorPred N Ne) (fermionTotalSpinZ N)
        * configSectorCompress N (hubbardNumberSectorPred N Ne)
          (attractiveHubbardHamiltonian N T U) := by
  rw [configSectorNumberCompress_mul_of_right_preserves Ne _
      (preservesHubbardSectorW_fermionTotalSpinZ Ne),
    (fermionTotalSpinZ_commute_attractiveHubbardHamiltonian N T U).eq.symm,
    ← configSectorNumberCompress_mul_of_right_preserves Ne _
      (preservesHubbardSectorW_attractive Ne T U)]

end LatticeSystem.Fermion
