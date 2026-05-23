import LatticeSystem.Quantum.SpinS.Theorem23LocalDifferenceRaising

/-!
# Tasaki §2.5 Theorem 2.3 raised site-sum API

This module contains the raised site-sum contribution and decomposition API
split from `Theorem23LocalDifferenceRaising.lean`. The base raising module
keeps the single-site raising components and weak filtered sign bounds, while
this module packages the strict off-`A` witness, vacancy bridge, and
dominance-form strict site-sum positivity wrapper.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 signed local raising contribution**:
the real signed contribution of the `x`-summand in the raised
site-sum at a target predecessor-sector configuration.

This packages the repeated real expression used to split the raised
site-sum into its off-`A` and on-`A` filtered pieces. -/
noncomputable def tasaki23SignedRaisingSiteContribution
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M) (x : V) : ℝ :=
  (marshallSignS A τ.1).re *
    ((((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
      (magSectorEmbedding Φ)) τ.1).re)

/-- **Tasaki §2.5 Theorem 2.3 strict off-`A` raised sign-sum witness**:
if at least one site outside `A` can be raised in the target predecessor
configuration, then the off-`A` filtered signed raising sum is strictly
positive.

This is the raising-direction companion to
`tasaki23_signed_lowering_offA_sum_pos_of_exists_lowerable_offA`. -/
theorem tasaki23_signed_raising_offA_sum_pos_of_exists_raiseable_offA
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M)
    (hΦ_pos : ∀ σ : magConfigS V N (M + 1),
      0 < (marshallSignS A σ.1).re * (Φ σ).re)
    (hwitness : ∃ x : V, A x = false ∧ (τ.1 x).val < N) :
    0 < ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23SignedRaisingSiteContribution A Φ τ x := by
  classical
  obtain ⟨x, hAx, hx⟩ := hwitness
  apply Finset.sum_pos'
  · intro y hy
    unfold tasaki23SignedRaisingSiteContribution
    have hAy : A y = false := by
      simpa using (Finset.mem_filter.mp hy).2
    exact tasaki23_signed_single_site_raising_component_nonneg_of_A_false
      A Φ τ y hAy hΦ_pos
  · refine ⟨x, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hAx⟩
    · unfold tasaki23SignedRaisingSiteContribution
      exact tasaki23_signed_single_site_raising_component_pos_of_A_false
        A Φ τ x hx hAx hΦ_pos

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 off-`A` raiseable witness from vacancy**:
if the total local vacancy on the complement sublattice is positive,
then some site outside `A` is below the top local occupation `N` and
can contribute a strict raised summand. -/
theorem tasaki23_exists_raiseable_offA_of_offA_vacancy_pos
    (A : V → Bool) {M : ℕ} (τ : magConfigS V N M)
    (hoffA_pos :
      0 < ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)), (N - (τ.1 x).val)) :
    ∃ x : V, A x = false ∧ (τ.1 x).val < N := by
  classical
  by_contra hnone
  have hzero :
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        (N - (τ.1 x).val)) = 0 := by
    simpa using
      (Finset.sum_eq_zero
        (s := Finset.univ.filter (fun x : V => A x = false))
        (f := fun x : V => N - (τ.1 x).val)
        (by
          intro x hx
          have hAx : A x = false := by
            simpa using (Finset.mem_filter.mp hx).2
          have hxnot : ¬ (τ.1 x).val < N := by
            intro hxlt
            exact hnone ⟨x, hAx, hxlt⟩
          have hxge : N ≤ (τ.1 x).val := by omega
          exact Nat.sub_eq_zero_of_le hxge))
  omega

/-- **Tasaki §2.5 Theorem 2.3 strict off-`A` raised sign-sum from
positive off-`A` vacancy**: a positive complement-sublattice vacancy
sum supplies the raiseable witness needed for strict off-`A` raised
signed-sum positivity. -/
theorem tasaki23_signed_raising_offA_sum_pos_of_offA_vacancy_pos
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M)
    (hΦ_pos : ∀ σ : magConfigS V N (M + 1),
      0 < (marshallSignS A σ.1).re * (Φ σ).re)
    (hoffA_pos :
      0 < ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)), (N - (τ.1 x).val)) :
    0 < ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23SignedRaisingSiteContribution A Φ τ x :=
  tasaki23_signed_raising_offA_sum_pos_of_exists_raiseable_offA
    A Φ τ hΦ_pos
    (tasaki23_exists_raiseable_offA_of_offA_vacancy_pos A τ hoffA_pos)

/-- **Tasaki §2.5 Theorem 2.3 raised site-sum decomposition**:
the full signed raised site-sum is the sum of its off-`A` and on-`A`
filtered signed pieces.

This is the exact Boolean partition needed before comparing the
non-negative off-`A` part with the non-positive on-`A` part. -/
theorem tasaki23_signed_raising_site_sum_eq_offA_add_onA
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M) :
    (marshallSignS A τ.1).re *
        (∑ x : V,
          (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
            (magSectorEmbedding Φ)) τ.1).re) =
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        tasaki23SignedRaisingSiteContribution A Φ τ x) +
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        tasaki23SignedRaisingSiteContribution A Φ τ x) := by
  classical
  unfold tasaki23SignedRaisingSiteContribution
  rw [Finset.mul_sum]
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (p := fun x : V => A x = false)
    (f := fun x : V =>
      (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re))]
  congr 1
  apply Finset.sum_congr
  · ext x
    by_cases hAx : A x = false
    · simp [hAx]
    · cases hA : A x <;> simp [hA] at hAx ⊢
  · intro x _hx
    rfl

/-- **Tasaki §2.5 Theorem 2.3 raised site-sum positivity from
sublattice dominance**: if the negative of the on-`A` signed sum is
strictly smaller than the off-`A` signed sum, then the full signed
raised site-sum is strictly positive.

This is the raising-direction companion to
`tasaki23_signed_lowering_site_sum_pos_of_onA_neg_lt_offA`. -/
theorem tasaki23_signed_raising_site_sum_pos_of_onA_neg_lt_offA
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M)
    (hdominates :
      -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23SignedRaisingSiteContribution A Φ τ x) <
        ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
          tasaki23SignedRaisingSiteContribution A Φ τ x) :
    0 < (marshallSignS A τ.1).re *
      (∑ x : V,
        (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) := by
  rw [tasaki23_signed_raising_site_sum_eq_offA_add_onA A Φ τ]
  linarith


end LatticeSystem.Quantum
