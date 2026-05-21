import LatticeSystem.Quantum.SpinS.Theorem23LocalCoefficient

/-!
# Tasaki §2.5 Theorem 2.3 local predecessor-difference API

This module contains the predecessor-difference and lowered site-sum layer
downstream of `Theorem23LocalCoefficient.lean`. The raising-direction
site-sum layer is isolated in `Theorem23LocalDifferenceRaising.lean`, and
the final Marshall-positivity wrappers are isolated in
`Theorem23LocalDifferenceMarshall.lean`. The adjacent-sector energy
comparison wrappers downstream of those layers are isolated in
`Theorem23LocalDifferenceEnergy.lean`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 single-site lowering predecessor**:
if a target configuration `τ` in sector `M + 1` has positive local
value at `x`, lowering that local value by one gives a configuration
in sector `M`.

This private copy keeps the split predecessor-difference module from
exporting local magnetization bookkeeping. -/
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

/-- **Tasaki §2.5 Theorem 2.3 single-site raising successor**:
if a target configuration `τ` in sector `M` has local value below `N`
at `x`, raising that local value by one gives a configuration in
sector `M + 1`.

This private copy keeps the split raising-direction local component
API independent of the base module's private helper. -/
private theorem magSumS_single_site_raising_successor {M : ℕ}
    (τ : magConfigS V N M) (x : V) (hx : (τ.1 x).val < N) :
    magSumS
        (Function.update τ.1 x
          ⟨(τ.1 x).val + 1, by omega⟩) = M + 1 := by
  classical
  have hsum :
      magSumS
          (Function.update τ.1 x
            ⟨(τ.1 x).val + 1, by omega⟩) =
        magSumS τ.1 + 1 := by
    unfold magSumS
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ x)]
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ x)]
    simp only [Function.update_self]
    have hrest :
        (∑ y ∈ (Finset.univ : Finset V) \ {x},
            (Function.update τ.1 x
              ⟨(τ.1 x).val + 1, by omega⟩ y).val) =
          ∑ y ∈ (Finset.univ : Finset V) \ {x}, (τ.1 y).val := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyx : y ≠ x := by
        simpa using hy
      rw [Function.update_of_ne hyx]
    rw [hrest]
    omega
  have hτ : magSumS τ.1 = M := τ.2
  omega

/-- **Tasaki §2.5 Theorem 2.3 off-`A` lowered sublattice coefficient
component**: the Marshall-signed real component of `Ŝ_¬A^- Φ` at a
target configuration is the off-`A` predecessor-coefficient sum.

This turns the off-sublattice half of the coefficient split into a
statement about the actual complement-sublattice lowering operator. -/
theorem tasaki23_signed_lowering_offA_sublattice_component_eq_coefficient_sum
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) :
    (marshallSignS A τ.1).re *
        (((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
          (magSectorEmbedding Φ)) τ.1).re =
      ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        tasaki23LoweringPredecessorSignedCoefficient A Φ τ x := by
  rw [sublatticeSpinSOpMinus_complement_mulVec_magSectorEmbedding_apply_eq_offA_site_sum
    A Φ τ.1]
  rw [Complex.re_sum, Finset.mul_sum]
  change
    (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23SignedLoweringSiteContribution A Φ τ x) =
      ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        tasaki23LoweringPredecessorSignedCoefficient A Φ τ x
  exact tasaki23_signed_lowering_offA_sum_eq_coefficient_sum A Φ τ

/-- **Tasaki §2.5 Theorem 2.3 on-`A` lowered sublattice coefficient
component**: the Marshall-signed real component of `Ŝ_A^- Φ` at a
target configuration is the negative of the on-`A`
predecessor-coefficient sum.

This is the operator-level form of the on-sublattice half of the
coefficient split. -/
theorem tasaki23_signed_lowering_onA_sublattice_component_eq_neg_coefficient_sum
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) :
    (marshallSignS A τ.1).re *
        (((sublatticeSpinSOpMinus N A).mulVec
          (magSectorEmbedding Φ)) τ.1).re =
      -∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        tasaki23LoweringPredecessorSignedCoefficient A Φ τ x := by
  rw [sublatticeSpinSOpMinus_mulVec_magSectorEmbedding_apply_eq_onA_site_sum
    A Φ τ.1]
  rw [Complex.re_sum, Finset.mul_sum]
  change
    (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
      tasaki23SignedLoweringSiteContribution A Φ τ x) =
      -∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        tasaki23LoweringPredecessorSignedCoefficient A Φ τ x
  exact tasaki23_signed_lowering_onA_sum_eq_neg_coefficient_sum A Φ τ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predecessor raising-source difference as a
lowered component**: for a Marshall-signed positive source vector, the
off-`A` minus on-`A` predecessor raising-source difference is exactly the
Marshall-signed real component of the full lowered vector
`Ŝ^-_tot Ψ`.

This identifies the difference-form callback with the operator-level
lowered-vector positivity statement used in the adjacent-sector
comparison. -/
theorem tasaki23_raising_predecessor_source_difference_eq_lowered_marshall_component
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) :
    (∑ x ∈ Finset.univ.filter (fun x : V => A x = false),
        tasaki23RaisingPredecessorSourceCoefficient v τ x) -
      (∑ x ∈ Finset.univ.filter (fun x : V => A x = true),
        tasaki23RaisingPredecessorSourceCoefficient v τ x) =
      (marshallSignS A τ.1).re *
        (((totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re := by
  classical
  let Φ : magConfigS V N M → ℂ :=
    fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)
  have hoff :
      (marshallSignS A τ.1).re *
          (((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
            (magSectorEmbedding Φ)) τ.1).re =
        ∑ x ∈ Finset.univ.filter (fun x : V => A x = false),
          tasaki23RaisingPredecessorSourceCoefficient v τ x := by
    rw [tasaki23_signed_lowering_offA_sublattice_component_eq_coefficient_sum
      A Φ τ]
    rw [show
        (∑ x ∈ Finset.univ.filter (fun x : V => A x = false),
          tasaki23LoweringPredecessorSignedCoefficient A Φ τ x) =
        ∑ x ∈ Finset.univ.filter (fun x : V => A x = false),
          tasaki23LoweringPredecessorSignedCoefficient A
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) τ x from by
        rfl]
    rw [
      tasaki23_lowering_predecessor_coefficient_sum_eq_positive_source_sum
        A v τ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23_positive_source_coefficient_sum_eq_lowerable_sum
        v τ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23_positive_source_lowerable_filter_sum_eq_lowerable_attach_sum
        v τ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23_lowerable_positive_source_attach_sum_eq_raising_predecessor_source_sum
        (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23_raising_predecessor_source_attach_sum_eq_boundary_sum
        (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = false))]
  have hon :
      (marshallSignS A τ.1).re *
          (((sublatticeSpinSOpMinus N A).mulVec
            (magSectorEmbedding Φ)) τ.1).re =
        -∑ x ∈ Finset.univ.filter (fun x : V => A x = true),
          tasaki23RaisingPredecessorSourceCoefficient v τ x := by
    rw [tasaki23_signed_lowering_onA_sublattice_component_eq_neg_coefficient_sum
      A Φ τ]
    rw [show
        (∑ x ∈ Finset.univ.filter (fun x : V => A x = true),
          tasaki23LoweringPredecessorSignedCoefficient A Φ τ x) =
        ∑ x ∈ Finset.univ.filter (fun x : V => A x = true),
          tasaki23LoweringPredecessorSignedCoefficient A
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) τ x from by
        rfl]
    rw [
      tasaki23_lowering_predecessor_coefficient_sum_eq_positive_source_sum
        A v τ (Finset.univ.filter (fun x : V => A x = true)),
      tasaki23_positive_source_coefficient_sum_eq_lowerable_sum
        v τ (Finset.univ.filter (fun x : V => A x = true)),
      tasaki23_positive_source_lowerable_filter_sum_eq_lowerable_attach_sum
        v τ (Finset.univ.filter (fun x : V => A x = true)),
      tasaki23_lowerable_positive_source_attach_sum_eq_raising_predecessor_source_sum
        (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = true)),
      tasaki23_raising_predecessor_source_attach_sum_eq_boundary_sum
        (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = true))]
  rw [show
      (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) =
        ((sublatticeSpinSOpMinus N A).mulVec (magSectorEmbedding Φ)) +
          ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
            (magSectorEmbedding Φ)) from by
      rw [totalSpinSOpMinus_eq_sublattice_sum (N := N) A]
      rw [Matrix.add_mulVec]]
  rw [Pi.add_apply, Complex.add_re, mul_add, hon, hoff]
  ring

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered Marshall positivity from
predecessor raising-source differences**: positivity of the off-`A`
minus on-`A` predecessor raising-source difference proves the
Marshall-positive lowered-vector component.

The proof first rewrites the lowerable attached sums as boundary sums
and then applies
`tasaki23_raising_predecessor_source_difference_eq_lowered_marshall_component`.
This connects the real source-weight difference callback to the
lowered-sector Marshall-positivity hypothesis used by the adjacent-sector
energy comparison. -/
theorem tasaki23_lowered_marshall_pos_of_raising_predecessor_source_difference_pos
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (hdiff :
      ∀ τ : magConfigS V N (M + 1),
        0 <
          (((Finset.univ.filter (fun x : V => A x = false)).filter
              (fun x : V => 0 < (τ.1 x).val)).attach.sum
            (fun x =>
              let predVal : Fin (N + 1) :=
                ⟨(τ.1 x.1).val - 1, by omega⟩
              let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
              (spinSOpPlus N predVal (τ.1 x.1)).re *
                v ⟨pred,
                  magSumS_single_site_lowering_predecessor
                    τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) -
            (((Finset.univ.filter (fun x : V => A x = true)).filter
                (fun x : V => 0 < (τ.1 x).val)).attach.sum
              (fun x =>
                let predVal : Fin (N + 1) :=
                  ⟨(τ.1 x.1).val - 1, by omega⟩
                let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
                (spinSOpPlus N predVal (τ.1 x.1)).re *
                  v ⟨pred,
                    magSumS_single_site_lowering_predecessor
                      τ x.1 ((Finset.mem_filter.mp x.2).2)⟩))) :
    ∀ τ : magConfigS V N (M + 1),
      0 < (marshallSignS A τ.1).re *
        (((totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re := by
  intro τ
  have hτ := hdiff τ
  rw [
    tasaki23_raising_predecessor_source_attach_sum_eq_boundary_sum
      (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = false)),
    tasaki23_raising_predecessor_source_attach_sum_eq_boundary_sum
      (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = true)),
    tasaki23_raising_predecessor_source_difference_eq_lowered_marshall_component
      A v τ] at hτ
  exact hτ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered Marshall positivity from the
unpacked real predecessor difference callback**: the fully threaded local
callback used by the final theorem boundary can be read as a
lowered-sector Marshall-positivity proof.

This is the callback-shaped version of
`tasaki23_lowered_marshall_pos_of_raising_predecessor_source_difference_pos`:
after the predicted-GS, real source-weight, sublattice-Casimir, and
successor-support data have produced the off-`A` minus on-`A`
predecessor raising-source positive difference, the result is converted
directly into the lowered-vector Marshall-positive component. -/
theorem
    tasaki23_lowered_marshall_pos_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (hsource_difference_pos :
      ∀ Ψ : (V → Fin (N + 1)) → ℂ,
        Ψ =
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
        (∀ τ : magConfigS V N (M + 1), ∀ x : V,
          ∀ hx : 0 < (τ.1 x).val,
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
                  v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩)) →
        (sublatticeSpinSquaredS N A).mulVec
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
          ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
            ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)) •
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
        (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
          ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
            ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)) •
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
        ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
          magSubspaceS V N
            (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
        (sublatticeSpinSquaredS N A).mulVec
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
          ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
            ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)) •
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
        (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
          ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
            ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)) •
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
        ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
          magSubspaceS V N
            (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
        ∀ τ : magConfigS V N (M + 1),
          0 <
            (((Finset.univ.filter (fun x : V => A x = false)).filter
                (fun x : V => 0 < (τ.1 x).val)).attach.sum
              (fun x =>
                let predVal : Fin (N + 1) :=
                  ⟨(τ.1 x.1).val - 1, by omega⟩
                let pred : V → Fin (N + 1) :=
                  Function.update τ.1 x.1 predVal
                (spinSOpPlus N predVal (τ.1 x.1)).re *
                  v ⟨pred,
                    magSumS_single_site_lowering_predecessor
                      τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) -
              (((Finset.univ.filter (fun x : V => A x = true)).filter
                  (fun x : V => 0 < (τ.1 x).val)).attach.sum
                (fun x =>
                  let predVal : Fin (N + 1) :=
                    ⟨(τ.1 x.1).val - 1, by omega⟩
                  let pred : V → Fin (N + 1) :=
                    Function.update τ.1 x.1 predVal
                  (spinSOpPlus N predVal (τ.1 x.1)).re *
                    v ⟨pred,
                      magSumS_single_site_lowering_predecessor
                        τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)))
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ_eq :
      Ψ =
        magSectorEmbedding
          (fun τ : magConfigS V N M =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΨ_pred : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hpred :
      ∀ τ : magConfigS V N (M + 1), ∀ x : V,
        ∀ hx : 0 < (τ.1 x).val,
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
                v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩))
    (hA_A :
      (sublatticeSpinSquaredS N A).mulVec
          ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
        ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) + 1)) •
          ((sublatticeSpinSOpMinus N A).mulVec Ψ))
    (hA_B :
      (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
          ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
        ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) + 1)) •
          ((sublatticeSpinSOpMinus N A).mulVec Ψ))
    (hA_mag :
      ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)))
    (hB_A :
      (sublatticeSpinSquaredS N A).mulVec
          ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
        ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) + 1)) •
          ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ))
    (hB_B :
      (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
          ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
        ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) + 1)) •
          ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ))
    (hB_mag :
      ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ))) :
    ∀ τ : magConfigS V N (M + 1),
      0 < (marshallSignS A τ.1).re *
        (((totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re := by
  exact
    tasaki23_lowered_marshall_pos_of_raising_predecessor_source_difference_pos
      (V := V) (N := N) A v
      (hsource_difference_pos Ψ hΨ_eq hΨ_pred hpred hA_A hA_B hA_mag hB_A hB_B hB_mag)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 strict site-sum positivity from the
unpacked real predecessor difference callback**: the same fully threaded
local callback also supplies the single-site lowered sum positivity used
directly by the adjacent-sector chain.

This is the site-sum analogue of
`tasaki23_lowered_marshall_pos_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos`.
It applies the predecessor raising-source difference to site-sum bridge
after the predicted-GS, real source-weight, sublattice-Casimir, and
successor-support data have produced the positive off-`A` minus on-`A`
difference. -/
theorem
    tasaki23_lowered_site_sum_pos_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (hsource_difference_pos :
      ∀ Ψ : (V → Fin (N + 1)) → ℂ,
        Ψ =
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
        (∀ τ : magConfigS V N (M + 1), ∀ x : V,
          ∀ hx : 0 < (τ.1 x).val,
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
                  v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩)) →
        (sublatticeSpinSquaredS N A).mulVec
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
          ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
            ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)) •
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
        (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
          ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
            ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)) •
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
        ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
          magSubspaceS V N
            (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
        (sublatticeSpinSquaredS N A).mulVec
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
          ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
            ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)) •
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
        (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
          ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
            ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)) •
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
        ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
          magSubspaceS V N
            (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
        ∀ τ : magConfigS V N (M + 1),
          0 <
            (((Finset.univ.filter (fun x : V => A x = false)).filter
                (fun x : V => 0 < (τ.1 x).val)).attach.sum
              (fun x =>
                let predVal : Fin (N + 1) :=
                  ⟨(τ.1 x.1).val - 1, by omega⟩
                let pred : V → Fin (N + 1) :=
                  Function.update τ.1 x.1 predVal
                (spinSOpPlus N predVal (τ.1 x.1)).re *
                  v ⟨pred,
                    magSumS_single_site_lowering_predecessor
                      τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) -
              (((Finset.univ.filter (fun x : V => A x = true)).filter
                  (fun x : V => 0 < (τ.1 x).val)).attach.sum
                (fun x =>
                  let predVal : Fin (N + 1) :=
                    ⟨(τ.1 x.1).val - 1, by omega⟩
                  let pred : V → Fin (N + 1) :=
                    Function.update τ.1 x.1 predVal
                  (spinSOpPlus N predVal (τ.1 x.1)).re *
                    v ⟨pred,
                      magSumS_single_site_lowering_predecessor
                        τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)))
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ_eq :
      Ψ =
        magSectorEmbedding
          (fun τ : magConfigS V N M =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΨ_pred : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hpred :
      ∀ τ : magConfigS V N (M + 1), ∀ x : V,
        ∀ hx : 0 < (τ.1 x).val,
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
                v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩))
    (hA_A :
      (sublatticeSpinSquaredS N A).mulVec
          ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
        ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) + 1)) •
          ((sublatticeSpinSOpMinus N A).mulVec Ψ))
    (hA_B :
      (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
          ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
        ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) + 1)) •
          ((sublatticeSpinSOpMinus N A).mulVec Ψ))
    (hA_mag :
      ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)))
    (hB_A :
      (sublatticeSpinSquaredS N A).mulVec
          ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
        ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) + 1)) •
          ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ))
    (hB_B :
      (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
          ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
        ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) + 1)) •
          ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ))
    (hB_mag :
      ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ))) :
    ∀ τ : magConfigS V N (M + 1),
      0 < (marshallSignS A τ.1).re *
        (∑ x : V,
          (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
            (magSectorEmbedding
              (fun σ : magConfigS V N M =>
                (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re) := by
  intro τ
  have hτ :=
    tasaki23_lowered_marshall_pos_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos
      (V := V) (N := N) A v hsource_difference_pos hΨ_eq hΨ_pred hpred
      hA_A hA_B hA_mag hB_A hB_B hB_mag τ
  rw [
    totalSpinSOpMinus_mulVec_magSectorEmbedding_apply_eq_site_sum
      (fun σ : magConfigS V N M =>
        (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) τ.1] at hτ
  simpa [map_sum] using hτ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 callback adapter from unpacked real
predecessor differences to lowered site sums**: the fully threaded
predecessor-difference callback can be consumed directly as the strict
single-site lowered sum positivity callback used by the site-sum
successor chain.

This names the callback-level API of
`tasaki23_lowered_site_sum_pos_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos`
so later final wrappers can route the predecessor-difference boundary to
the lowered site-sum chain without first passing through the
raising-source dominance final wrapper. -/
abbrev
    tasaki23_lowered_site_sum_pos_callback_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ) :=
  tasaki23_lowered_site_sum_pos_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos
    (V := V) (N := N) A v

/-- **Tasaki §2.5 Theorem 2.3 strict off-`A` lowered sign-sum witness**:
if at least one site outside `A` can be lowered in the target
configuration, then the off-`A` filtered signed lowering sum is strictly
positive.

This is the strict companion to
`tasaki23_signed_lowering_offA_sum_nonneg`: all off-`A` terms are
non-negative, and the witness site contributes strictly positively. -/
theorem tasaki23_signed_lowering_offA_sum_pos_of_exists_lowerable_offA
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1))
    (hΦ_pos : ∀ σ : magConfigS V N M,
      0 < (marshallSignS A σ.1).re * (Φ σ).re)
    (hwitness : ∃ x : V, A x = false ∧ 0 < (τ.1 x).val) :
    0 < ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23SignedLoweringSiteContribution A Φ τ x := by
  classical
  obtain ⟨x, hAx, hx⟩ := hwitness
  apply Finset.sum_pos'
  · intro y hy
    unfold tasaki23SignedLoweringSiteContribution
    have hAy : A y = false := by
      simpa using (Finset.mem_filter.mp hy).2
    exact tasaki23_signed_single_site_lowering_component_nonneg_of_A_false
      A Φ τ y hAy hΦ_pos
  · refine ⟨x, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hAx⟩
    · unfold tasaki23SignedLoweringSiteContribution
      exact tasaki23_signed_single_site_lowering_component_pos_of_A_false
        A Φ τ x hx hAx hΦ_pos

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 off-`A` lowerable witness from occupation**:
if the total local occupation on the complement sublattice is positive,
then some site outside `A` has positive local occupation and can
contribute a strict lowered summand. -/
theorem tasaki23_exists_lowerable_offA_of_offA_occupation_pos
    (A : V → Bool) {M : ℕ} (τ : magConfigS V N (M + 1))
    (hoffA_pos :
      0 < ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)), (τ.1 x).val) :
    ∃ x : V, A x = false ∧ 0 < (τ.1 x).val := by
  classical
  by_contra hnone
  have hzero :
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)), (τ.1 x).val) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hAx : A x = false := by
      simpa using (Finset.mem_filter.mp hx).2
    have hxzero : ¬ 0 < (τ.1 x).val := by
      intro hxpos
      exact hnone ⟨x, hAx, hxpos⟩
    omega
  omega

/-- **Tasaki §2.5 Theorem 2.3 strict off-`A` lowered sign-sum from
positive off-`A` occupation**: a positive complement-sublattice
occupation sum supplies the lowerable witness needed for strict
off-`A` lowered signed-sum positivity. -/
theorem tasaki23_signed_lowering_offA_sum_pos_of_offA_occupation_pos
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1))
    (hΦ_pos : ∀ σ : magConfigS V N M,
      0 < (marshallSignS A σ.1).re * (Φ σ).re)
    (hoffA_pos :
      0 < ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)), (τ.1 x).val) :
    0 < ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23SignedLoweringSiteContribution A Φ τ x :=
  tasaki23_signed_lowering_offA_sum_pos_of_exists_lowerable_offA
    A Φ τ hΦ_pos
    (tasaki23_exists_lowerable_offA_of_offA_occupation_pos A τ hoffA_pos)

/-- **Tasaki §2.5 Theorem 2.3 lowered site-sum decomposition**:
the full signed lowered site-sum is the sum of its off-`A` and on-`A`
filtered signed pieces.

This is the exact Boolean partition needed before comparing the
non-negative off-`A` part with the non-positive on-`A` part. -/
theorem tasaki23_signed_lowering_site_sum_eq_offA_add_onA
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) :
    (marshallSignS A τ.1).re *
        (∑ x : V,
          (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
            (magSectorEmbedding Φ)) τ.1).re) =
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        tasaki23SignedLoweringSiteContribution A Φ τ x) +
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        tasaki23SignedLoweringSiteContribution A Φ τ x) := by
  classical
  unfold tasaki23SignedLoweringSiteContribution
  rw [Finset.mul_sum]
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (p := fun x : V => A x = false)
    (f := fun x : V =>
      (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re))]
  congr 1
  apply Finset.sum_congr
  · ext x
    by_cases hAx : A x = false
    · simp [hAx]
    · cases hA : A x <;> simp [hA] at hAx ⊢
  · intro x _hx
    rfl

/-- **Tasaki §2.5 Theorem 2.3 lowered site-sum positivity from
sublattice dominance**: if the negative of the on-`A` signed sum is
strictly smaller than the off-`A` signed sum, then the full signed
lowered site-sum is strictly positive.

This packages the remaining dominance obligation in the site-sum proof. -/
theorem tasaki23_signed_lowering_site_sum_pos_of_onA_neg_lt_offA
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1))
    (hdominates :
      -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23SignedLoweringSiteContribution A Φ τ x) <
        ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
          tasaki23SignedLoweringSiteContribution A Φ τ x) :
    0 < (marshallSignS A τ.1).re *
      (∑ x : V,
        (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) := by
  rw [tasaki23_signed_lowering_site_sum_eq_offA_add_onA A Φ τ]
  linarith

/-- **Tasaki §2.5 Theorem 2.3 lowered site-sum positivity from
coefficient dominance**: if the on-`A` predecessor-coefficient sum is
strictly smaller than the off-`A` predecessor-coefficient sum, then
the full signed lowered site-sum is strictly positive.

This rewrites the earlier signed-contribution dominance callback using
the coefficient-sum split, leaving the remaining proof obligation in
the direct coefficient form. -/
theorem tasaki23_signed_lowering_site_sum_pos_of_onA_coefficient_lt_offA
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1))
    (hdominates :
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23LoweringPredecessorSignedCoefficient A Φ τ x) <
        ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
          tasaki23LoweringPredecessorSignedCoefficient A Φ τ x) :
    0 < (marshallSignS A τ.1).re *
      (∑ x : V,
        (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) := by
  exact
    tasaki23_signed_lowering_site_sum_pos_of_onA_neg_lt_offA
      A Φ τ (by
        rw [tasaki23_signed_lowering_onA_sum_eq_neg_coefficient_sum A Φ τ,
          tasaki23_signed_lowering_offA_sum_eq_coefficient_sum A Φ τ]
        simpa using hdominates)

/-- **Tasaki §2.5 Theorem 2.3 lowered site-sum positivity from
positive-source coefficient dominance**: after cancelling the Marshall
signs in the local predecessor coefficients, it is enough to compare the
positive-source coefficient sums over the two sublattices. -/
theorem tasaki23_signed_lowering_site_sum_pos_of_positive_source_coefficient_lt
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1))
    (hdominates :
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) <
        ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
          tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) :
    0 < (marshallSignS A τ.1).re *
      (∑ x : V,
        (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re) := by
  exact
    tasaki23_signed_lowering_site_sum_pos_of_onA_coefficient_lt_offA
      A
      (fun σ : magConfigS V N M =>
        (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) τ
      (by
        rw [
          tasaki23_lowering_predecessor_coefficient_sum_eq_positive_source_sum
            A v τ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23_lowering_predecessor_coefficient_sum_eq_positive_source_sum
            A v τ (Finset.univ.filter (fun x : V => A x = false))]
        exact hdominates)

/-- **Tasaki §2.5 Theorem 2.3 lowered site-sum positivity from lowerable
positive-source coefficient dominance**: after discarding the boundary
sites where the successor configuration cannot be lowered, dominance of
the remaining positive-source predecessor coefficient sums still implies
strict lowered site-sum positivity. -/
theorem tasaki23_signed_lowering_site_sum_pos_of_positive_source_lowerable_coefficient_lt
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1))
    (hdominates :
      (∑ x ∈ ((Finset.univ.filter (fun x : V => A x = true)).filter
          (fun x : V => 0 < (τ.1 x).val)),
          tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) <
        ∑ x ∈ ((Finset.univ.filter (fun x : V => A x = false)).filter
          (fun x : V => 0 < (τ.1 x).val)),
          tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) :
    0 < (marshallSignS A τ.1).re *
      (∑ x : V,
        (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re) := by
  exact
    tasaki23_signed_lowering_site_sum_pos_of_positive_source_coefficient_lt
      A v τ (by
        rw [
          tasaki23_positive_source_coefficient_sum_eq_lowerable_sum
            v τ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23_positive_source_coefficient_sum_eq_lowerable_sum
            v τ (Finset.univ.filter (fun x : V => A x = false))]
        exact hdominates)

/-- **Tasaki §2.5 Theorem 2.3 lowered site-sum positivity from sublattice
component dominance**: if the negative Marshall-signed `Ŝ_A^-` component
is strictly smaller than the Marshall-signed `Ŝ_¬A^-` component, then the
full signed lowered site-sum is strictly positive.

This is the operator-component form of
`tasaki23_signed_lowering_site_sum_pos_of_onA_coefficient_lt_offA`. -/
theorem tasaki23_signed_lowering_site_sum_pos_of_sublattice_component_lt
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1))
    (hdominates :
      -((marshallSignS A τ.1).re *
          (((sublatticeSpinSOpMinus N A).mulVec
            (magSectorEmbedding Φ)) τ.1).re) <
        (marshallSignS A τ.1).re *
          (((sublatticeSpinSOpMinus N (fun x => !A x)).mulVec
            (magSectorEmbedding Φ)) τ.1).re) :
    0 < (marshallSignS A τ.1).re *
      (∑ x : V,
        (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) := by
  exact
    tasaki23_signed_lowering_site_sum_pos_of_onA_coefficient_lt_offA
      A Φ τ (by
        have honA :=
          tasaki23_signed_lowering_onA_sublattice_component_eq_neg_coefficient_sum
            A Φ τ
        have hoffA :=
          tasaki23_signed_lowering_offA_sublattice_component_eq_coefficient_sum
            A Φ τ
        rw [← hoffA]
        rw [← show
          -((marshallSignS A τ.1).re *
            (((sublatticeSpinSOpMinus N A).mulVec
              (magSectorEmbedding Φ)) τ.1).re) =
              ∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23LoweringPredecessorSignedCoefficient A Φ τ x from by
                rw [honA]
                simp]
        exact hdominates)


end LatticeSystem.Quantum
