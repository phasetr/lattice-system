import LatticeSystem.Quantum.SpinS.Theorem23PredictedSourceWeight

/-!
# Tasaki §2.5 Theorem 2.3 re-embedded cross-ladder source-weight identities

This module contains the re-embedded cross-ladder source-weight identities at a
lowering predecessor, split as a stable suffix from
`Theorem23PredictedSourceWeight.lean`: the source-site-sum / source-weight RHS
forms, the lowering-predecessor source-weight equality, and its real-part
forms. The parent module keeps the `Ŝ^3` source-weight building blocks
(single-site / sublattice / complement / cross-sublattice) these identities
reuse.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 single-site lowering predecessor**:
if a target configuration `τ` in sector `M + 1` has positive local
value at `x`, lowering that local value by one gives a configuration
in sector `M`.

This private copy keeps the interval-chain module from exporting the
local bookkeeping lemma while preserving the moved local module's public
API surface. -/
private theorem magSumS_single_site_lowering_predecessor {M : ℕ}
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val) :
    magSumS
        (Function.update τ.1 x
          ⟨(τ.1 x).val - 1, by omega⟩) = M := by
  classical
  have hsum_succ :
      magSumS
          (Function.update τ.1 x
            ⟨(τ.1 x).val - 1, by omega⟩) + 1 = magSumS τ.1 := by
    unfold magSumS
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ x)]
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ x)]
    simp only [Function.update_self]
    have hrest :
        (∑ y ∈ (Finset.univ : Finset V) \ {x},
            (Function.update τ.1 x
              ⟨(τ.1 x).val - 1, by omega⟩ y).val) =
          ∑ y ∈ (Finset.univ : Finset V) \ {x}, (τ.1 y).val := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyx : y ≠ x := by
        simpa using hy
      rw [Function.update_of_ne hyx]
    rw [hrest]
    have hpred_val :
        (⟨(τ.1 x).val - 1, by
          omega⟩ : Fin (N + 1)).val + 1 = (τ.1 x).val := by
      simp
      omega
    omega
  have hτ : magSumS τ.1 = M + 1 := τ.2
  omega

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 re-embedded cross-ladder source-weight RHS**:
the re-embedded source-sector cross-ladder site-sum identity can be
rewritten with the explicit `Ŝ_A^3 Ŝ_¬A^3` source-weight product on the
right-hand side.

This substitutes the diagonal `S^3` source-weight evaluation into the
non-ladder term, leaving a scalar multiple of the source coefficient
`Ψ σ`. -/
theorem
    tasaki23_cross_ladder_reembedded_source_site_sum_eq_energy_sub_two_sublattice_weight_product_of_predictedGS
    (A : V → Bool) (N : ℕ) {M : ℕ} {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hA_mag :
      ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)))
    (hB_mag :
      ((sublatticeSpinSOpMinus N (fun x => !A x)).mulVec Ψ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)))
    (σ : magConfigS V N M) :
    (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding
            (magSectorRestriction (M := M + 1)
              ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)))) σ.1) +
      ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding
            (magSectorRestriction (M := M + 1)
              ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) σ.1 =
      (bipartiteToyMinEnergyPredicted (Λ := V) A N -
        (2 : ℂ) *
          ((∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
              ((N : ℂ) / 2 - ((σ.1 x).val : ℂ))) *
            (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
              ((N : ℂ) / 2 - ((σ.1 x).val : ℂ))))) * Ψ σ.1 := by
  rw [tasaki23_cross_ladder_reembedded_source_site_sum_eq_energy_sub_two_op3_of_predictedGS
    (V := V) A N hΨ hA_mag hB_mag σ]
  rw [Pi.sub_apply, Pi.smul_apply, Matrix.smul_mulVec, Pi.smul_apply]
  rw [sublatticeSpinSOp3_mul_complement_mulVec_apply_eq_onA_offA_weight]
  simp [smul_eq_mul]
  ring_nf

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 source-weight identity at a lowering
predecessor**: the re-embedded scalar cross-ladder identity can be
specialized to the source-sector predecessor obtained from a successor
configuration `τ` by lowering a site `x`.

This aligns the source-weight equation with the exact predecessor
configuration used in `tasaki23LoweringPredecessorSignedCoefficient`. -/
theorem
    tasaki23_cross_ladder_reembedded_source_weight_eq_lowering_predecessor_of_predictedGS
    (A : V → Bool) (N : ℕ) {M : ℕ} {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hA_mag :
      ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)))
    (hB_mag :
      ((sublatticeSpinSOpMinus N (fun x => !A x)).mulVec Ψ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)))
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val) :
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    (∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
        ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding
            (magSectorRestriction (M := M + 1)
              ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
      ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
        ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding
            (magSectorRestriction (M := M + 1)
              ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred =
      (bipartiteToyMinEnergyPredicted (Λ := V) A N -
        (2 : ℂ) *
          ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
              ((N : ℂ) / 2 - ((pred y).val : ℂ))) *
            (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
              ((N : ℂ) / 2 - ((pred y).val : ℂ))))) * Ψ pred := by
  classical
  dsimp only
  exact
    tasaki23_cross_ladder_reembedded_source_site_sum_eq_energy_sub_two_sublattice_weight_product_of_predictedGS
      (V := V) A N hΨ hA_mag hB_mag
      ⟨Function.update τ.1 x ⟨(τ.1 x).val - 1, by omega⟩,
        magSumS_single_site_lowering_predecessor τ x hx⟩

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 real source-weight RHS at a lowering
predecessor**: for a Marshall-positive sector embedding, the real part
of the predecessor source-weight right-hand side is the real predicted
toy energy minus twice the real on-`A`/off-`A` source-weight product,
times the signed positive sector coefficient at the predecessor.

This is the real-valued form of the scalar RHS exposed by
`tasaki23_cross_ladder_reembedded_source_weight_eq_lowering_predecessor_of_predictedGS`.
-/
theorem
    tasaki23_cross_ladder_reembedded_source_weight_lowering_predecessor_rhs_re_eq
    (A : V → Bool) (N : ℕ) {M : ℕ} {v : magConfigS V N M → ℝ}
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ_eq :
      Ψ =
        magSectorEmbedding
          (fun ρ : magConfigS V N M =>
            (((marshallSignS A ρ.1).re * v ρ : ℝ) : ℂ)))
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val) :
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    (((bipartiteToyMinEnergyPredicted (Λ := V) A N -
        (2 : ℂ) *
          ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
              ((N : ℂ) / 2 - ((pred y).val : ℂ))) *
            (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
              ((N : ℂ) / 2 - ((pred y).val : ℂ))))) * Ψ pred).re =
      ((bipartiteToyMinEnergyPredicted (Λ := V) A N).re -
          2 *
            ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                ((N : ℝ) / 2 - ((pred y).val : ℝ))) *
              (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                ((N : ℝ) / 2 - ((pred y).val : ℝ))))) *
        ((marshallSignS A pred).re *
          v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩)) := by
  classical
  dsimp only
  subst Ψ
  rw [magSectorEmbedding_apply_of_mem _
    (magSumS_single_site_lowering_predecessor τ x hx)]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  simp only [mul_zero, sub_zero]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.re_sum, Complex.im_sum, Complex.natCast_re, Complex.natCast_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.div_re, Complex.div_im,
    zero_mul, mul_zero, sub_zero]
  norm_num [Complex.normSq]
  ring_nf
  exact Or.inl trivial

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 real predecessor source-weight identity**:
the complex predecessor source-weight equality can be read on the real
axis for a Marshall-positive sector embedding.

This combines `Complex.re` of the predecessor-specialized cross-ladder
equation with
`tasaki23_cross_ladder_reembedded_source_weight_lowering_predecessor_rhs_re_eq`,
so the remaining local comparison may use the real scalar coefficient
directly. -/
theorem
    tasaki23_cross_ladder_reembedded_source_weight_lowering_predecessor_re_eq
    (A : V → Bool) (N : ℕ) {M : ℕ} {v : magConfigS V N M → ℝ}
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ_eq :
      Ψ =
        magSectorEmbedding
          (fun ρ : magConfigS V N M =>
            (((marshallSignS A ρ.1).re * v ρ : ℝ) : ℂ)))
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val)
    (hpred :
      let predVal : Fin (N + 1) :=
        ⟨(τ.1 x).val - 1, by omega⟩
      let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
      (∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
          ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
            (magSectorEmbedding
              (magSectorRestriction (M := M + 1)
                ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
        ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
          ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
            (magSectorEmbedding
              (magSectorRestriction (M := M + 1)
                ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred =
        (bipartiteToyMinEnergyPredicted (Λ := V) A N -
          (2 : ℂ) *
            ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                ((N : ℂ) / 2 - ((pred y).val : ℂ))) *
              (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                ((N : ℂ) / 2 - ((pred y).val : ℂ))))) * Ψ pred) :
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
        ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding
            (magSectorRestriction (M := M + 1)
              ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
      ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
        ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding
            (magSectorRestriction (M := M + 1)
              ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred).re =
      ((bipartiteToyMinEnergyPredicted (Λ := V) A N).re -
          2 *
            ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                ((N : ℝ) / 2 - ((pred y).val : ℝ))) *
              (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                ((N : ℝ) / 2 - ((pred y).val : ℝ))))) *
        ((marshallSignS A pred).re *
          v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩) := by
  classical
  dsimp only at hpred ⊢
  have hre := congrArg Complex.re hpred
  rw [
    tasaki23_cross_ladder_reembedded_source_weight_lowering_predecessor_rhs_re_eq
      (V := V) A N hΨ_eq τ x hx] at hre
  exact hre

end LatticeSystem.Quantum
