import LatticeSystem.Quantum.SpinS.Theorem23LocalDifference

/-!
# Tasaki §2.5 Theorem 2.3 unpacked predecessor-difference callback API

This module contains the fully threaded unpacked real predecessor-difference
callback adapters split from `Theorem23LocalDifference.lean`. The base
module keeps the sublattice coefficient and predecessor raising-source
difference identities, while this module exposes the final callback-shaped
bridges consumed by the interval and outside-ground wrappers.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

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


end LatticeSystem.Quantum
