import LatticeSystem.Quantum.SpinS.SublatticeSpin
import LatticeSystem.Quantum.SpinS.SublatticeSpinLadderDef

/-!
# Sublattice ladder API (build-speed companion)

Build-speed companion to `SublatticeSpin.lean`. Hosts the trailing
sections "Sublattice axis-1 / axis-3 matrix element realness"
through "Cross-sublattice commute for ladder operators" (originally
lines 999..1336 of the parent file).

Splitting these blocks out drops the parent from ~1337 lines to
~998 lines. Downstream files that need only the core sublattice
spin-`S` operators / Cartan / Casimir API can keep importing the
parent; consumers of the ladder/realness blocks should import
this companion.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 Theorem 2.3 (Marshall–Lieb–Mattis).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (N : ℕ)

/-! ## Sublattice axis-1 / axis-3 matrix element realness -/

/-- The sublattice axis-1 operator has real matrix elements:
`((sublatticeSpinSOp1 N A) σ' σ).im = 0`. -/
theorem sublatticeSpinSOp1_apply_im_zero (A : Λ → Bool)
    (σ' σ : Λ → Fin (N + 1)) :
    ((sublatticeSpinSOp1 N A) σ' σ).im = 0 := by
  unfold sublatticeSpinSOp1
  rw [Matrix.sum_apply, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    exact onSiteS_spinSOp1_apply_im_zero x σ' σ
  · cases h : A x
    · rw [if_neg]
      · simp
      · simp
    · exact absurd h hA

/-- The sublattice axis-3 operator has real matrix elements. -/
theorem sublatticeSpinSOp3_apply_im_zero (A : Λ → Bool)
    (σ' σ : Λ → Fin (N + 1)) :
    ((sublatticeSpinSOp3 N A) σ' σ).im = 0 := by
  unfold sublatticeSpinSOp3
  rw [Matrix.sum_apply, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    exact onSiteS_spinSOp3_apply_im_zero x σ' σ
  · cases h : A x
    · rw [if_neg]
      · simp
      · simp
    · exact absurd h hA

/-! ## Sublattice ladder matrix element realness -/

/-- The sublattice raising operator has real matrix elements:
`(Ŝ_A^+) σ' σ` has zero imaginary part. -/
theorem sublatticeSpinSOpPlus_apply_im_zero (A : Λ → Bool)
    (σ' σ : Λ → Fin (N + 1)) :
    ((sublatticeSpinSOpPlus N A) σ' σ).im = 0 := by
  unfold sublatticeSpinSOpPlus
  rw [Matrix.sum_apply, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    exact onSiteS_spinSOpPlus_apply_im_zero x σ' σ
  · cases h : A x
    · rw [if_neg]
      · simp
      · simp
    · exact absurd h hA

/-- The sublattice lowering operator has real matrix elements:
`(Ŝ_A^-) σ' σ` has zero imaginary part. -/
theorem sublatticeSpinSOpMinus_apply_im_zero (A : Λ → Bool)
    (σ' σ : Λ → Fin (N + 1)) :
    ((sublatticeSpinSOpMinus N A) σ' σ).im = 0 := by
  unfold sublatticeSpinSOpMinus
  rw [Matrix.sum_apply, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    exact onSiteS_spinSOpMinus_apply_im_zero x σ' σ
  · cases h : A x
    · rw [if_neg]
      · simp
      · simp
    · exact absurd h hA

/-! ## Sublattice ladder annihilates configurations with extreme A-values -/

/-- `Ŝ_A^+ · basisVecS σ = 0` when `σ x = 0` for all `x ∈ A`.
Generalises `sublatticeSpinSOpPlus_mulVec_allAlignedStateS_zero` (PR #1087)
to allow σ to be arbitrary on `¬A`. -/
theorem sublatticeSpinSOpPlus_mulVec_basisVecS_zero_on (A : Λ → Bool)
    {σ : Λ → Fin (N + 1)} (hσ : ∀ x, A x = true → σ x = 0) :
    (sublatticeSpinSOpPlus N A).mulVec (basisVecS σ) = 0 := by
  unfold sublatticeSpinSOpPlus
  rw [Matrix.sum_mulVec]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    -- Apply on-site raising. For σ x = 0, this annihilates.
    funext τ
    rw [onSiteS_mulVec_basisVecS_apply]
    by_cases h_off : ∀ k, k ≠ x → τ k = σ k
    · rw [onSiteS_apply_of_off_site_agree x _ h_off]
      rw [hσ x hA]
      apply spinSOpPlus_apply_other
      change (τ x).val + 1 ≠ ((0 : Fin (N + 1)).val)
      simp
    · exact onSiteS_apply_eq_zero_of_off_site_diff x _ h_off
  · cases h : A x
    · rw [if_neg, Matrix.zero_mulVec]
      simp
    · exact absurd h hA

/-- `Ŝ_A^- · basisVecS σ = 0` when `σ x = Fin.last N` for all `x ∈ A`. -/
theorem sublatticeSpinSOpMinus_mulVec_basisVecS_last_on (A : Λ → Bool)
    {σ : Λ → Fin (N + 1)} (hσ : ∀ x, A x = true → σ x = Fin.last N) :
    (sublatticeSpinSOpMinus N A).mulVec (basisVecS σ) = 0 := by
  unfold sublatticeSpinSOpMinus
  rw [Matrix.sum_mulVec]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hA : A x = true
  · rw [if_pos hA]
    funext τ
    rw [onSiteS_mulVec_basisVecS_apply]
    by_cases h_off : ∀ k, k ≠ x → τ k = σ k
    · rw [onSiteS_apply_of_off_site_agree x _ h_off]
      rw [hσ x hA]
      apply spinSOpMinus_apply_other
      change ((Fin.last N).val : ℕ) + 1 ≠ (τ x).val
      have hτ_lt : (τ x).val < N + 1 := (τ x).isLt
      simp [Fin.last]; omega
    · exact onSiteS_apply_eq_zero_of_off_site_diff x _ h_off
  · cases h : A x
    · rw [if_neg, Matrix.zero_mulVec]
      simp
    · exact absurd h hA

/-! ## Sublattice ladder adjoint relations -/

/-- `(Ŝ_A^+)† = Ŝ_A^-`: the sublattice raising and lowering operators
are Hermitian conjugates of each other. -/
theorem sublatticeSpinSOpPlus_conjTranspose (A : Λ → Bool) :
    (sublatticeSpinSOpPlus N A).conjTranspose = sublatticeSpinSOpMinus N A := by
  unfold sublatticeSpinSOpPlus sublatticeSpinSOpMinus
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hA : A x = true
  · rw [if_pos hA, if_pos hA]
    rw [onSiteS_conjTranspose, spinSOpPlus_conjTranspose]
  · cases h : A x
    · rw [if_neg, if_neg]
      · rw [Matrix.conjTranspose_zero]
      · simp
      · simp
    · exact absurd h hA

/-- `(Ŝ_A^-)† = Ŝ_A^+`. -/
theorem sublatticeSpinSOpMinus_conjTranspose (A : Λ → Bool) :
    (sublatticeSpinSOpMinus N A).conjTranspose = sublatticeSpinSOpPlus N A := by
  unfold sublatticeSpinSOpPlus sublatticeSpinSOpMinus
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hA : A x = true
  · rw [if_pos hA, if_pos hA]
    rw [onSiteS_conjTranspose, spinSOpMinus_conjTranspose]
  · cases h : A x
    · rw [if_neg, if_neg]
      · rw [Matrix.conjTranspose_zero]
      · simp
      · simp
    · exact absurd h hA

/-! ## Sublattice ladder operators shift the magnetization subspace -/

/-- `Ŝ_A^- · v ∈ magSubspaceS Λ N (M − 1)` for `v ∈ magSubspaceS Λ N M`.
The sublattice lowering operator shifts the (total) magnetisation by `-1`. -/
theorem sublatticeSpinSOpMinus_mulVec_mem_magSubspaceS_of_mem
    (A : Λ → Bool) {M : ℂ} {v : (Λ → Fin (N + 1)) → ℂ}
    (hv : v ∈ magSubspaceS Λ N M) :
    (sublatticeSpinSOpMinus N A).mulVec v ∈ magSubspaceS Λ N (M - 1) := by
  rw [mem_magSubspaceS_iff] at hv ⊢
  have h := totalSpinSOp3_commutator_sublatticeSpinSOpMinus N A
  have hcomm : totalSpinSOp3 Λ N * sublatticeSpinSOpMinus N A =
      sublatticeSpinSOpMinus N A * totalSpinSOp3 Λ N - sublatticeSpinSOpMinus N A := by
    have hadd : totalSpinSOp3 Λ N * sublatticeSpinSOpMinus N A =
        (totalSpinSOp3 Λ N * sublatticeSpinSOpMinus N A -
          sublatticeSpinSOpMinus N A * totalSpinSOp3 Λ N) +
        sublatticeSpinSOpMinus N A * totalSpinSOp3 Λ N := by abel
    rw [hadd, h]; abel
  rw [Matrix.mulVec_mulVec, hcomm, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul, sub_smul, one_smul]

/-- `Ŝ_A^+ · v ∈ magSubspaceS Λ N (M + 1)` for `v ∈ magSubspaceS Λ N M`. -/
theorem sublatticeSpinSOpPlus_mulVec_mem_magSubspaceS_of_mem
    (A : Λ → Bool) {M : ℂ} {v : (Λ → Fin (N + 1)) → ℂ}
    (hv : v ∈ magSubspaceS Λ N M) :
    (sublatticeSpinSOpPlus N A).mulVec v ∈ magSubspaceS Λ N (M + 1) := by
  rw [mem_magSubspaceS_iff] at hv ⊢
  have h := totalSpinSOp3_commutator_sublatticeSpinSOpPlus N A
  have hcomm : totalSpinSOp3 Λ N * sublatticeSpinSOpPlus N A =
      sublatticeSpinSOpPlus N A * totalSpinSOp3 Λ N + sublatticeSpinSOpPlus N A := by
    have hadd : totalSpinSOp3 Λ N * sublatticeSpinSOpPlus N A =
        (totalSpinSOp3 Λ N * sublatticeSpinSOpPlus N A -
          sublatticeSpinSOpPlus N A * totalSpinSOp3 Λ N) +
        sublatticeSpinSOpPlus N A * totalSpinSOp3 Λ N := by abel
    rw [hadd, h]; abel
  rw [Matrix.mulVec_mulVec, hcomm, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul, add_smul, one_smul]

/-! ## Cartan identity for sublattice ladders -/

/-- `Ŝ_A^+ · Ŝ_A^- = (Ŝ_A^(1))² + (Ŝ_A^(2))² + Ŝ_A^(3)`. Sublattice
Cartan identity, derived from `Ŝ^± = Ŝ^(1) ± i Ŝ^(2)` and the SU(2)
commutator `[Ŝ_A^(1), Ŝ_A^(2)] = i Ŝ_A^(3)`. -/
theorem sublatticeSpinSOpPlus_mul_sublatticeSpinSOpMinus_eq (A : Λ → Bool) :
    sublatticeSpinSOpPlus N A * sublatticeSpinSOpMinus N A =
      sublatticeSpinSOp1 N A * sublatticeSpinSOp1 N A +
        sublatticeSpinSOp2 N A * sublatticeSpinSOp2 N A +
        sublatticeSpinSOp3 N A := by
  rw [sublatticeSpinSOpPlus_eq_add, sublatticeSpinSOpMinus_eq_sub]
  have hcomm := sublatticeSpinSOp1_commutator_sublatticeSpinSOp2 N A
  set S1 := sublatticeSpinSOp1 N A with hS1
  set S2 := sublatticeSpinSOp2 N A with hS2
  set S3 := sublatticeSpinSOp3 N A with hS3
  -- Expand (S1 + I • S2)(S1 - I • S2) into elementary form.
  have hexp : (S1 + Complex.I • S2) * (S1 - Complex.I • S2) =
      S1 * S1 - Complex.I • (S1 * S2) + Complex.I • (S2 * S1) -
        Complex.I • Complex.I • (S2 * S2) := by
    rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul]
    abel
  rw [hexp]
  -- I • I • (S2*S2) = -(S2*S2)
  rw [show (Complex.I : ℂ) • Complex.I • (S2 * S2) = -(S2 * S2) from by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]]
  -- I • (S2*S1) - I • (S1*S2) = -I • [S1, S2] = -I • (I • S3) = S3
  have hcommS3 : Complex.I • (S2 * S1) - Complex.I • (S1 * S2) = S3 := by
    rw [← smul_sub]
    have hr : (S2 * S1) - (S1 * S2) = -(S1 * S2 - S2 * S1) := by abel
    rw [hr, hcomm, smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul]
    abel
  -- Combine
  have : S1 * S1 - Complex.I • (S1 * S2) + Complex.I • (S2 * S1) -
      -(S2 * S2) =
    S1 * S1 + S2 * S2 + (Complex.I • (S2 * S1) - Complex.I • (S1 * S2)) := by abel
  rw [this, hcommS3]

/-- Dual: `Ŝ_A^- · Ŝ_A^+ = (Ŝ_A^(1))² + (Ŝ_A^(2))² - Ŝ_A^(3)`. -/
theorem sublatticeSpinSOpMinus_mul_sublatticeSpinSOpPlus_eq (A : Λ → Bool) :
    sublatticeSpinSOpMinus N A * sublatticeSpinSOpPlus N A =
      sublatticeSpinSOp1 N A * sublatticeSpinSOp1 N A +
        sublatticeSpinSOp2 N A * sublatticeSpinSOp2 N A -
        sublatticeSpinSOp3 N A := by
  rw [sublatticeSpinSOpPlus_eq_add, sublatticeSpinSOpMinus_eq_sub]
  have hcomm := sublatticeSpinSOp1_commutator_sublatticeSpinSOp2 N A
  set S1 := sublatticeSpinSOp1 N A
  set S2 := sublatticeSpinSOp2 N A
  set S3 := sublatticeSpinSOp3 N A
  have hexp : (S1 - Complex.I • S2) * (S1 + Complex.I • S2) =
      S1 * S1 + Complex.I • (S1 * S2) - Complex.I • (S2 * S1) -
        Complex.I • Complex.I • (S2 * S2) := by
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul]
    abel
  rw [hexp]
  rw [show (Complex.I : ℂ) • Complex.I • (S2 * S2) = -(S2 * S2) from by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]]
  -- I • (S1*S2) - I • (S2*S1) = I • [S1, S2] = I • (I • S3) = -S3
  have hcommS3 : Complex.I • (S1 * S2) - Complex.I • (S2 * S1) = -S3 := by
    rw [← smul_sub, hcomm, smul_smul, Complex.I_mul_I, neg_one_smul]
  have : S1 * S1 + Complex.I • (S1 * S2) - Complex.I • (S2 * S1) -
      -(S2 * S2) =
    S1 * S1 + S2 * S2 + (Complex.I • (S1 * S2) - Complex.I • (S2 * S1)) := by abel
  rw [this, hcommS3]
  abel

/-- Cross-axis identity: `Ŝ_A^(1)·Ŝ_B^(1) + Ŝ_A^(2)·Ŝ_B^(2) =
(1/2)(Ŝ_A^+·Ŝ_B^- + Ŝ_A^-·Ŝ_B^+)`. Holds for any two sublattices `A, B`;
when `B = ¬A` it gives the cross-flip term in the Casimir decomposition. -/
theorem sublatticeSpinSOp1_mul_op1_add_op2_mul_op2_eq_ladder
    (A B : Λ → Bool) :
    sublatticeSpinSOp1 N A * sublatticeSpinSOp1 N B +
        sublatticeSpinSOp2 N A * sublatticeSpinSOp2 N B =
      (1 / 2 : ℂ) • (sublatticeSpinSOpPlus N A * sublatticeSpinSOpMinus N B +
          sublatticeSpinSOpMinus N A * sublatticeSpinSOpPlus N B) := by
  rw [sublatticeSpinSOpPlus_eq_add, sublatticeSpinSOpMinus_eq_sub,
    sublatticeSpinSOpPlus_eq_add, sublatticeSpinSOpMinus_eq_sub]
  set S1A := sublatticeSpinSOp1 N A with hS1A
  set S2A := sublatticeSpinSOp2 N A with hS2A
  set S1B := sublatticeSpinSOp1 N B with hS1B
  set S2B := sublatticeSpinSOp2 N B with hS2B
  -- (S1A + I S2A)(S1B - I S2B) + (S1A - I S2A)(S1B + I S2B) = 2 (S1A S1B + S2A S2B).
  -- Cross I-terms cancel pairwise; I·I·(S2A S2B) terms simplify via I·I = -1.
  have hexp : (S1A + Complex.I • S2A) * (S1B - Complex.I • S2B) +
      (S1A - Complex.I • S2A) * (S1B + Complex.I • S2B) =
      (2 : ℂ) • (S1A * S1B + S2A * S2B) := by
    rw [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.mul_add, Matrix.mul_add]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I,
      neg_one_smul, smul_add, two_smul]
    abel
  rw [hexp, smul_smul]
  norm_num
theorem sublatticeSpinSOpPlus_commutator_sublatticeSpinSOpMinus (A : Λ → Bool) :
    sublatticeSpinSOpPlus N A * sublatticeSpinSOpMinus N A -
        sublatticeSpinSOpMinus N A * sublatticeSpinSOpPlus N A =
      (2 : ℂ) • sublatticeSpinSOp3 N A := by
  rw [sublatticeSpinSOpPlus_mul_sublatticeSpinSOpMinus_eq,
    sublatticeSpinSOpMinus_mul_sublatticeSpinSOpPlus_eq]
  rw [two_smul]
  abel

/-! ## Cross-sublattice commute for ladder operators -/

/-- `Ŝ_A^+` commutes with `Ŝ_¬A^+`. Direct from
`sublatticeSpinSOpGeneric_cross_commute` with `S = T = spinSOpPlus N`. -/
theorem sublatticeSpinSOpPlus_cross_commute (A : Λ → Bool) :
    Commute (sublatticeSpinSOpPlus N A)
      (sublatticeSpinSOpPlus N (fun x => ! A x)) := by
  unfold sublatticeSpinSOpPlus
  exact sublatticeSpinSOpGeneric_cross_commute N A (spinSOpPlus N) (spinSOpPlus N)

/-- `Ŝ_A^-` commutes with `Ŝ_¬A^-`. -/
theorem sublatticeSpinSOpMinus_cross_commute (A : Λ → Bool) :
    Commute (sublatticeSpinSOpMinus N A)
      (sublatticeSpinSOpMinus N (fun x => ! A x)) := by
  unfold sublatticeSpinSOpMinus
  exact sublatticeSpinSOpGeneric_cross_commute N A (spinSOpMinus N) (spinSOpMinus N)

/-- `Ŝ_A^+` commutes with `Ŝ_¬A^-`. -/
theorem sublatticeSpinSOpPlus_cross_commute_minus (A : Λ → Bool) :
    Commute (sublatticeSpinSOpPlus N A)
      (sublatticeSpinSOpMinus N (fun x => ! A x)) := by
  unfold sublatticeSpinSOpPlus sublatticeSpinSOpMinus
  exact sublatticeSpinSOpGeneric_cross_commute N A (spinSOpPlus N) (spinSOpMinus N)

/-- `Ŝ_A^-` commutes with `Ŝ_¬A^+`. -/
theorem sublatticeSpinSOpMinus_cross_commute_plus (A : Λ → Bool) :
    Commute (sublatticeSpinSOpMinus N A)
      (sublatticeSpinSOpPlus N (fun x => ! A x)) := by
  unfold sublatticeSpinSOpMinus sublatticeSpinSOpPlus
  exact sublatticeSpinSOpGeneric_cross_commute N A (spinSOpMinus N) (spinSOpPlus N)

/-! ## Sublattice-Casimir commute for ladder operators -/

/-- The sublattice Casimir `(Ŝ_A)^2` commutes with the raising ladder
operator `Ŝ_A^+`.

This is the same SU(2) invariance as the Cartesian-axis commutation
lemmas, rewritten in the ladder basis for the Tasaki §2.5 Theorem 2.3
sublattice-component comparison. -/
theorem sublatticeSpinSquaredS_commute_sublatticeSpinSOpPlus (A : Λ → Bool) :
    Commute (sublatticeSpinSquaredS N A) (sublatticeSpinSOpPlus N A) := by
  rw [sublatticeSpinSOpPlus_eq_add]
  exact (sublatticeSpinSquaredS_commute_sublatticeSpinSOp1 N A).add_right
    ((sublatticeSpinSquaredS_commute_sublatticeSpinSOp2 N A).smul_right
      Complex.I)

/-- The sublattice Casimir `(Ŝ_A)^2` commutes with the lowering ladder
operator `Ŝ_A^-`.

This lets the maximum sublattice-Casimir eigenvector identity be
transported from a predicted toy ground state to its `A`-sublattice
lowering component. -/
theorem sublatticeSpinSquaredS_commute_sublatticeSpinSOpMinus (A : Λ → Bool) :
    Commute (sublatticeSpinSquaredS N A) (sublatticeSpinSOpMinus N A) := by
  rw [sublatticeSpinSOpMinus_eq_sub]
  exact (sublatticeSpinSquaredS_commute_sublatticeSpinSOp1 N A).sub_right
    ((sublatticeSpinSquaredS_commute_sublatticeSpinSOp2 N A).smul_right
      Complex.I)

/-- The sublattice Casimir `(Ŝ_A)^2` commutes with the complement
lowering ladder `Ŝ_¬A^-`.

This cross-sublattice companion records that lowering on the opposite
sublattice does not change the `A`-sublattice Casimir eigenspace. -/
theorem sublatticeSpinSquaredS_commute_sublatticeSpinSOpMinus_complement
    (A : Λ → Bool) :
    Commute (sublatticeSpinSquaredS N A)
      (sublatticeSpinSOpMinus N (fun x => ! A x)) := by
  rw [sublatticeSpinSOpMinus_eq_sub]
  exact (sublatticeSpinSquaredS_commute_sublatticeSpinSOp1_complement N A).sub_right
    ((sublatticeSpinSquaredS_commute_sublatticeSpinSOp2_complement N A).smul_right
      Complex.I)

/-- A commuting operator preserves a full-space `mulVec` eigenvalue
after applying a sublattice ladder or any other many-body operator.

This local helper avoids importing the saturated-ladder module just to
reuse its generic preservation lemma in the Tasaki §2.5 Theorem 2.3
sublattice-component chain. -/
theorem mulVec_preserves_eigenvalue_of_commuteS_ladder
    {A B : ManyBodyOpS Λ N} (h : Commute A B)
    {γ : ℂ} {Ψ : (Λ → Fin (N + 1)) → ℂ}
    (hΨ : A.mulVec Ψ = γ • Ψ) :
    A.mulVec (B.mulVec Ψ) = γ • B.mulVec Ψ := by
  rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, hΨ, Matrix.mulVec_smul]


end LatticeSystem.Quantum
