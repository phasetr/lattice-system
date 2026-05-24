import LatticeSystem.Quantum.SpinS.Theorem23LocalCoefficientRaisingSource

/-!
# Tasaki §2.5 Theorem 2.3 raising-predecessor-source sum API

This module contains the boundary-inclusive
`tasaki23RaisingPredecessorSourceCoefficient` definition together with the
raising-predecessor-source attached-sum, positivity, and dominance machinery
and the final raising-source dominance callback, split as a stable suffix from
`Theorem23LocalCoefficientRaisingSource.lean`. The parent module keeps the
lowerable-positive-source coefficient bridges relating the lowerable attached
sums to the raising-predecessor-source sums.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 boundary-inclusive predecessor
raising-source coefficient**: the predecessor raising-source summand at
a successor site, with the non-lowerable boundary case contributing
zero.

This is the `S^+`-coefficient version of the lowerable attached summand
used by the final raising-source dominance callback. -/
noncomputable def tasaki23RaisingPredecessorSourceCoefficient
    {M : ℕ} (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (x : V) : ℝ :=
  if hx : 0 < (τ.1 x).val then
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    (spinSOpPlus N predVal (τ.1 x)).re *
      v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩
  else
    0

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 attached raising-source sum as a boundary
sum**: the attached sum over lowerable sites agrees with the
boundary-inclusive predecessor raising-source coefficient sum over the
ambient finite set.

This removes the proof-carrying lowerable filter before applying Boolean
partitions of the vertex set. -/
theorem tasaki23_raising_predecessor_source_attach_sum_eq_boundary_sum
    {M : ℕ} (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (s : Finset V) :
    ((s.filter (fun x : V => 0 < (τ.1 x).val)).attach.sum
        (fun x =>
          let predVal : Fin (N + 1) :=
            ⟨(τ.1 x.1).val - 1, by omega⟩
          let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
          (spinSOpPlus N predVal (τ.1 x.1)).re *
            v ⟨pred,
              magSumS_single_site_lowering_predecessor
                τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) =
      ∑ x ∈ s, tasaki23RaisingPredecessorSourceCoefficient v τ x := by
  classical
  let f : V → ℝ := fun x => tasaki23RaisingPredecessorSourceCoefficient v τ x
  calc
    ((s.filter (fun x : V => 0 < (τ.1 x).val)).attach.sum
        (fun x =>
          let predVal : Fin (N + 1) :=
            ⟨(τ.1 x.1).val - 1, by omega⟩
          let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
          (spinSOpPlus N predVal (τ.1 x.1)).re *
            v ⟨pred,
              magSumS_single_site_lowering_predecessor
                τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) =
        (s.filter (fun x : V => 0 < (τ.1 x).val)).attach.sum
          (fun x => f x.1) := by
      apply Finset.sum_congr rfl
      intro x _hxmem
      have hx : 0 < (τ.1 x.1).val := (Finset.mem_filter.mp x.2).2
      dsimp [f, tasaki23RaisingPredecessorSourceCoefficient]
      rw [dif_pos hx]
    _ = ∑ x ∈ s.filter (fun x : V => 0 < (τ.1 x).val), f x := by
      simpa using
        (Finset.sum_attach (s.filter (fun x : V => 0 < (τ.1 x).val)) f)
    _ = ∑ x ∈ s, f x := by
      rw [← Finset.sum_filter_add_sum_filter_not
        (s := s) (p := fun x : V => 0 < (τ.1 x).val) (f := f)]
      have hzero :
          (∑ x ∈ s.filter (fun x : V => ¬ 0 < (τ.1 x).val), f x) = 0 := by
        apply Finset.sum_eq_zero
        intro x hxmem
        have hxnot : ¬ 0 < (τ.1 x).val := (Finset.mem_filter.mp hxmem).2
        dsimp [f, tasaki23RaisingPredecessorSourceCoefficient]
        rw [dif_neg hxnot]
      rw [hzero, add_zero]
    _ = ∑ x ∈ s, tasaki23RaisingPredecessorSourceCoefficient v τ x := by
      rfl

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 positive predecessor raising-source
summand**: at a lowerable successor site, the real raising coefficient
from the lowering predecessor back to the successor is strictly positive,
so multiplying by the strictly positive source coefficient gives a
strictly positive raising-source summand.

This is the sign-side input for extracting dominance from the real
predecessor source-weight equation. -/
theorem tasaki23_raising_predecessor_source_summand_pos
    {M : ℕ} (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val)
    (hv_pos : ∀ σ : magConfigS V N M, 0 < v σ) :
    0 <
      (let predVal : Fin (N + 1) :=
        ⟨(τ.1 x).val - 1, by omega⟩
      let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
      (spinSOpPlus N predVal (τ.1 x)).re *
        v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩) := by
  classical
  let predVal : Fin (N + 1) := ⟨(τ.1 x).val - 1, by omega⟩
  let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
  have hstep : predVal.val + 1 = (τ.1 x).val := by
    dsimp [predVal]
    omega
  have hcoef_pos : 0 < (spinSOpPlus N predVal (τ.1 x)).re :=
    spinSOpPlus_apply_re_pos_of_raise N hstep
  change 0 <
    (spinSOpPlus N predVal (τ.1 x)).re *
      v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩
  exact mul_pos hcoef_pos
    (hv_pos ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 non-negative predecessor raising-source
sum**: every attached predecessor raising-source sum over lowerable
successor sites is non-negative for a strictly positive real source
vector.

This packages summand positivity in the exact finite-sum shape used by
the final raising-source dominance callback. -/
theorem tasaki23_raising_predecessor_source_attach_sum_nonneg
    {M : ℕ} (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (s : Finset V)
    (hv_pos : ∀ σ : magConfigS V N M, 0 < v σ) :
    0 ≤
      ((s.filter (fun x : V => 0 < (τ.1 x).val)).attach.sum
        (fun x =>
          let predVal : Fin (N + 1) :=
            ⟨(τ.1 x.1).val - 1, by omega⟩
          let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
          (spinSOpPlus N predVal (τ.1 x.1)).re *
            v ⟨pred,
              magSumS_single_site_lowering_predecessor
                τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) := by
  classical
  apply Finset.sum_nonneg
  intro x _hx
  exact le_of_lt
    (tasaki23_raising_predecessor_source_summand_pos
      (V := V) (N := N) v τ x.1 ((Finset.mem_filter.mp x.2).2) hv_pos)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 total predecessor raising-source sum
partition**: the attached predecessor raising-source sum over all
lowerable successor sites splits into the on-`A` and off-`A` attached
sums used by the final dominance callback.

This is the finite-set partition needed before applying the real
predecessor source-weight equation to the two sublattice sums. -/
theorem tasaki23_raising_predecessor_source_univ_attach_sum_eq_onA_add_offA
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) :
    ((Finset.univ.filter (fun x : V => 0 < (τ.1 x).val)).attach.sum
        (fun x =>
          let predVal : Fin (N + 1) :=
            ⟨(τ.1 x.1).val - 1, by omega⟩
          let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
          (spinSOpPlus N predVal (τ.1 x.1)).re *
            v ⟨pred,
              magSumS_single_site_lowering_predecessor
                τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) =
      (((Finset.univ.filter (fun x : V => A x = true)).filter
            (fun x : V => 0 < (τ.1 x).val)).attach.sum
          (fun x =>
            let predVal : Fin (N + 1) :=
              ⟨(τ.1 x.1).val - 1, by omega⟩
            let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
            (spinSOpPlus N predVal (τ.1 x.1)).re *
              v ⟨pred,
                magSumS_single_site_lowering_predecessor
                  τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) +
        (((Finset.univ.filter (fun x : V => A x = false)).filter
            (fun x : V => 0 < (τ.1 x).val)).attach.sum
          (fun x =>
            let predVal : Fin (N + 1) :=
              ⟨(τ.1 x.1).val - 1, by omega⟩
            let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
            (spinSOpPlus N predVal (τ.1 x.1)).re *
              v ⟨pred,
                magSumS_single_site_lowering_predecessor
                  τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) := by
  classical
  rw [tasaki23_raising_predecessor_source_attach_sum_eq_boundary_sum
    (V := V) (N := N) v τ Finset.univ]
  rw [tasaki23_raising_predecessor_source_attach_sum_eq_boundary_sum
    (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = true))]
  rw [tasaki23_raising_predecessor_source_attach_sum_eq_boundary_sum
    (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = false))]
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (p := fun x : V => A x = true)]
  simp [Bool.not_eq_true]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predecessor raising-source dominance from
positive difference**: positivity of the off-`A` predecessor
raising-source sum minus the on-`A` sum is the strict dominance
condition required by the final raising-source callback.

This states the local comparison in the difference form naturally
produced by the real predecessor source-weight identity. -/
theorem tasaki23_raising_predecessor_source_sum_lt_of_offA_sub_onA_pos
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1))
    (hdiff :
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
    (((Finset.univ.filter (fun x : V => A x = true)).filter
          (fun x : V => 0 < (τ.1 x).val)).attach.sum
        (fun x =>
          let predVal : Fin (N + 1) :=
            ⟨(τ.1 x.1).val - 1, by omega⟩
          let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
          (spinSOpPlus N predVal (τ.1 x.1)).re *
            v ⟨pred,
              magSumS_single_site_lowering_predecessor
                τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) <
      (((Finset.univ.filter (fun x : V => A x = false)).filter
          (fun x : V => 0 < (τ.1 x).val)).attach.sum
        (fun x =>
          let predVal : Fin (N + 1) :=
            ⟨(τ.1 x.1).val - 1, by omega⟩
          let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
          (spinSOpPlus N predVal (τ.1 x.1)).re *
            v ⟨pred,
              magSumS_single_site_lowering_predecessor
                τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) := by
  linarith

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predecessor raising-source dominance
callback from positive differences**: a pointwise callback proving
positivity of the off-`A` minus on-`A` predecessor raising-source sums
supplies the strict dominance callback used by the final theorem
boundary.

This is the quantified callback form of
`tasaki23_raising_predecessor_source_sum_lt_of_offA_sub_onA_pos`. -/
theorem tasaki23_raising_predecessor_source_sum_lt_callback_of_offA_sub_onA_pos
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
      (((Finset.univ.filter (fun x : V => A x = true)).filter
            (fun x : V => 0 < (τ.1 x).val)).attach.sum
          (fun x =>
            let predVal : Fin (N + 1) :=
              ⟨(τ.1 x.1).val - 1, by omega⟩
            let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
            (spinSOpPlus N predVal (τ.1 x.1)).re *
              v ⟨pred,
                magSumS_single_site_lowering_predecessor
                  τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) <
        (((Finset.univ.filter (fun x : V => A x = false)).filter
            (fun x : V => 0 < (τ.1 x).val)).attach.sum
          (fun x =>
            let predVal : Fin (N + 1) :=
              ⟨(τ.1 x.1).val - 1, by omega⟩
            let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
            (spinSOpPlus N predVal (τ.1 x.1)).re *
              v ⟨pred,
                magSumS_single_site_lowering_predecessor
                  τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) := by
  intro τ
  exact
    tasaki23_raising_predecessor_source_sum_lt_of_offA_sub_onA_pos
      (V := V) (N := N) A v τ (hdiff τ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowerable coefficient dominance from
positive predecessor differences**: positivity of the off-`A` minus
on-`A` predecessor raising-source attached sums implies strict
dominance of the matching explicit lowerable positive-source coefficient
sums.

This composes the difference-form dominance bridge with the lowerable
coefficient mirror, so the explicit lowerable callback can consume the
same local comparison shape as the predecessor-difference boundary. -/
theorem tasaki23_lowerable_positive_source_attach_sum_lt_of_offA_sub_onA_pos
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1))
    (hdiff :
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
    (((Finset.univ.filter (fun x : V => A x = true)).filter
          (fun x : V => 0 < (τ.1 x).val)).attach.sum
        (fun x =>
          tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
            v τ x.1 ((Finset.mem_filter.mp x.2).2))) <
      (((Finset.univ.filter (fun x : V => A x = false)).filter
          (fun x : V => 0 < (τ.1 x).val)).attach.sum
        (fun x =>
          tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
            v τ x.1 ((Finset.mem_filter.mp x.2).2))) := by
  exact
    tasaki23_lowerable_positive_source_attach_sum_lt_of_raising_predecessor_source_sum_lt
      (V := V) (N := N) A v τ
      (tasaki23_raising_predecessor_source_sum_lt_of_offA_sub_onA_pos
        (V := V) (N := N) A v τ hdiff)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowerable coefficient dominance callback
from positive predecessor differences**: a pointwise off-`A` minus
on-`A` predecessor raising-source positive-difference callback supplies
the explicit lowerable positive-source coefficient dominance callback.

This is the quantified form of
`tasaki23_lowerable_positive_source_attach_sum_lt_of_offA_sub_onA_pos`. -/
theorem tasaki23_lowerable_positive_source_attach_sum_lt_callback_of_offA_sub_onA_pos
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
      (((Finset.univ.filter (fun x : V => A x = true)).filter
            (fun x : V => 0 < (τ.1 x).val)).attach.sum
          (fun x =>
            tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
              v τ x.1 ((Finset.mem_filter.mp x.2).2))) <
        (((Finset.univ.filter (fun x : V => A x = false)).filter
            (fun x : V => 0 < (τ.1 x).val)).attach.sum
          (fun x =>
            tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
              v τ x.1 ((Finset.mem_filter.mp x.2).2))) := by
  intro τ
  exact
    tasaki23_lowerable_positive_source_attach_sum_lt_of_offA_sub_onA_pos
      (V := V) (N := N) A v τ (hdiff τ)

end LatticeSystem.Quantum
