import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIILocalSigns
import LatticeSystem.Math.PerronFrobeniusMain

/-!
# Case (ii): parity-gauged shifted block irreducibility

Issue #412 (Tasaki §2.5 Theorem 2.4, Mattis--Nishimori).

This file converts the local strict shifted-entry signs from
`AnisotropicHeisenbergSpinSCaseIILocalSigns` into matrix-power positivity and
conditional irreducibility for the case-(ii) parity-gauged shifted block matrix.

The result is intentionally conditional on entrywise non-negativity and
block-reachability totality.  Boundary move-set choices (`lambda = 1` or
`D = 0`) and the later PF/min identification are separate inputs.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Block-level parity reachability -/

/-- A parity step restricted to a fixed `parityConfigS` block. -/
def parityStepSOnBlock (G : SimpleGraph Λ) {p : ℕ}
    (σ τ : parityConfigS Λ N p) : Prop :=
  ParityStepS G σ.1 τ.1

/-- Reflexive-transitive closure of parity steps inside a fixed parity block. -/
def parityReachableSOnBlock (G : SimpleGraph Λ) {p : ℕ} :
    parityConfigS Λ N p → parityConfigS Λ N p → Prop :=
  Relation.ReflTransGen (parityStepSOnBlock (N := N) G)

omit [DecidableEq Λ] in
/-- Reflexivity of block-level parity reachability. -/
theorem parityReachableSOnBlock_refl (G : SimpleGraph Λ) {p : ℕ}
    (σ : parityConfigS Λ N p) : parityReachableSOnBlock G σ σ :=
  Relation.ReflTransGen.refl

omit [DecidableEq Λ] in
/-- A single block-level parity step is block-reachable. -/
theorem parityReachableSOnBlock_single {G : SimpleGraph Λ} {p : ℕ}
    {σ τ : parityConfigS Λ N p} (h : parityStepSOnBlock G σ τ) :
    parityReachableSOnBlock G σ τ :=
  Relation.ReflTransGen.single h

omit [DecidableEq Λ] in
/-- Transitivity of block-level parity reachability. -/
theorem parityReachableSOnBlock_trans {G : SimpleGraph Λ} {p : ℕ}
    {σ τ υ : parityConfigS Λ N p}
    (h₁ : parityReachableSOnBlock G σ τ) (h₂ : parityReachableSOnBlock G τ υ) :
    parityReachableSOnBlock G σ υ :=
  Relation.ReflTransGen.trans h₁ h₂

/-! ## Step and path positivity -/

/-- In case (ii), any elementary `ParityStepS` gives a strictly positive shifted
parity-gauged block entry in the strict local interior. -/
theorem shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_parityStepS
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hlam_gt : 1 < lam.re)
    {D : ℂ} (hDim : D.im = 0) (hDneg : D.re < 0)
    (c : ℝ) {p : ℕ} {σ τ : parityConfigS Λ N p}
    (hstep : ParityStepS (bipartiteCompleteGraphOf A) σ.1 τ.1) :
    0 < shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p τ σ := by
  rcases hstep with hrl | hbond | hion
  · exact shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_raiseLowerStepS
      A hJim hJnn hJpos hJself hlam hlb c hrl
  · exact shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_parityBondStepS
      A hJim hJnn hJpos hJself hlam hlam_gt c hbond
  · exact shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_singleIonStepS
      A hJself hDim hDneg c hion

/-- Block matrix-power positivity from block-level parity reachability for the
case-(ii) shifted parity-gauged matrix. -/
theorem shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pow_apply_pos_of_blockReachable
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hlam_gt : 1 < lam.re)
    {D : ℂ} (hDim : D.im = 0) (hDneg : D.re < 0)
    {c : ℝ} {p : ℕ}
    (hB_nn : ∀ σ τ : parityConfigS Λ N p,
      0 ≤ shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p σ τ)
    {σ σ' : parityConfigS Λ N p}
    (hreach : parityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ') :
    ∃ k : ℕ,
      0 < (shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p ^ k)
        σ' σ := by
  induction hreach with
  | refl =>
      exact ⟨0, by simp [Matrix.one_apply_eq]⟩
  | tail _h₁ h₂ ih =>
      obtain ⟨k, hpos⟩ := ih
      refine ⟨k + 1, ?_⟩
      rw [pow_succ', Matrix.mul_apply]
      apply Finset.sum_pos'
      · intro l _
        exact mul_nonneg (hB_nn _ _) (Matrix.pow_apply_nonneg hB_nn _ _ _)
      · exact ⟨_, Finset.mem_univ _,
          mul_pos
            (shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pos_of_parityStepS
              A hJim hJnn hJpos hJself hlam hlb hlam_gt hDim hDneg c h₂)
            hpos⟩

/-! ## Conditional irreducibility -/

/-- The case-(ii) shifted parity-gauged block matrix is irreducible from
entrywise non-negativity and block-reachability totality. -/
theorem shiftedCaseIIParityGaugedBlock_isIrreducible_of_blockReachable_total
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hlam_gt : 1 < lam.re)
    {D : ℂ} (hDim : D.im = 0) (hDneg : D.re < 0)
    {c : ℝ} (p : ℕ)
    (hc_strict : ∀ σ : parityConfigS Λ N p,
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ.1 σ.1 < c)
    (hB_nn : ∀ σ τ : parityConfigS Λ N p,
      0 ≤ shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p σ τ)
    [Nonempty (parityConfigS Λ N p)]
    (hreach_total : ∀ σ' σ : parityConfigS Λ N p, σ' ≠ σ →
      parityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ') :
    (shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p).IsIrreducible := by
  rw [Matrix.isIrreducible_iff_exists_pow_pos hB_nn]
  intro σ' σ
  by_cases hsig : σ' = σ
  · subst hsig
    refine ⟨1, one_pos, ?_⟩
    rw [pow_one]
    exact shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_diag_pos
      A J lam D N p (hc_strict σ')
  · obtain ⟨k, hk⟩ :=
      shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock_pow_apply_pos_of_blockReachable
        A hJim hJnn hJpos hJself hlam hlb hlam_gt hDim hDneg hB_nn (hreach_total σ' σ hsig)
    have hk_pos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkp
      · subst hk0
        rw [pow_zero, Matrix.one_apply_ne hsig] at hk
        exact absurd hk (lt_irrefl 0)
      · exact hkp
    exact ⟨k, hk_pos, hk⟩

end LatticeSystem.Quantum
