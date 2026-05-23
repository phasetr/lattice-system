import LatticeSystem.Quantum.SpinS.Theorem23LocalCoefficient

/-!
# Tasaki §2.5 Theorem 2.3 local coefficient raising-source API

This module contains the predecessor raising-source coefficient suffix split
from `Theorem23LocalCoefficient.lean`. The base local-coefficient module keeps
the lowered signed and positive-source coefficient layers, while this module
rewrites the explicit lowerable coefficients into predecessor raising-source
sums. The boundary-inclusive raising-source coefficient definition and the
raising-predecessor-source attached-sum / positivity / dominance machinery and
final callback are split further into
`Theorem23LocalCoefficientRaisingSourceSum.lean`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.style.longLine false in
omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 predecessor ladder coefficient mirror**:
the raising coefficient from the lowering predecessor back to the
successor configuration equals the lowering coefficient used in the
explicit lowerable positive-source predecessor coefficient.

Both sides are the real ladder coefficient
`sqrt (τ_x * (N - τ_x + 1))`. -/
theorem tasaki23_spinSOpPlus_lowering_predecessor_re_eq_spinSOpMinus
    {M : ℕ} (N : ℕ) (τ : magConfigS V N (M + 1)) (x : V)
    (hx : 0 < (τ.1 x).val) :
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    (spinSOpPlus N predVal (τ.1 x)).re =
      (spinSOpMinus N (τ.1 x) predVal).re := by
  classical
  let predVal : Fin (N + 1) := ⟨(τ.1 x).val - 1, by omega⟩
  change (spinSOpPlus N predVal (τ.1 x)).re =
    (spinSOpMinus N (τ.1 x) predVal).re
  have hpredVal : predVal.val = (τ.1 x).val - 1 := rfl
  have hstep : predVal.val + 1 = (τ.1 x).val := by omega
  rw [spinSOpPlus_apply_raise N hstep, spinSOpMinus_apply_lower N hstep]
  simp only [Complex.ofReal_re]
  congr 1
  have hxle : 1 ≤ (τ.1 x).val := Nat.succ_le_of_lt hx
  rw [hpredVal, Nat.cast_sub hxle]
  ring

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowerable coefficient as predecessor
raising coefficient**: the explicit lowerable positive-source coefficient
can be read with the matching raising matrix coefficient at the lowering
predecessor.

This is the coefficient bridge needed to compare the real predecessor
source-weight raising sums with the attached lowerable positive-source
coefficient sums. -/
theorem tasaki23_lowerable_positive_source_coefficient_eq_raising_predecessor_source
    {M : ℕ} (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val) :
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient v τ x hx =
      (spinSOpPlus N predVal (τ.1 x)).re *
        v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩ := by
  classical
  dsimp only [tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient]
  rw [tasaki23_spinSOpPlus_lowering_predecessor_re_eq_spinSOpMinus
    (V := V) N τ x hx]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowerable coefficient sums as predecessor
raising-source sums**: an attached sum of explicit lowerable
positive-source coefficients can be read as the attached sum of the
matching predecessor raising coefficients times the positive predecessor
source values.

This is the finite-sum form of
`tasaki23_lowerable_positive_source_coefficient_eq_raising_predecessor_source`.
-/
theorem tasaki23_lowerable_positive_source_attach_sum_eq_raising_predecessor_source_sum
    {M : ℕ} (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (s : Finset V) :
    ((s.filter (fun x : V => 0 < (τ.1 x).val)).attach.sum
      (fun x =>
        tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
          v τ x.1 ((Finset.mem_filter.mp x.2).2))) =
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
  apply Finset.sum_congr rfl
  intro x _hx
  exact
    tasaki23_lowerable_positive_source_coefficient_eq_raising_predecessor_source
      (V := V) (N := N) v τ x.1 ((Finset.mem_filter.mp x.2).2)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowerable coefficient dominance from
predecessor raising-source dominance**: strict dominance of the attached
predecessor raising-source sums implies strict dominance of the attached
explicit lowerable positive-source coefficient sums.

This removes the coefficient notation from the remaining local estimate
and exposes the same real raising coefficients that occur in the
predecessor source-weight identity. -/
theorem tasaki23_lowerable_positive_source_attach_sum_lt_of_raising_predecessor_source_sum_lt
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1))
    (hdominates :
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
  rw [
    tasaki23_lowerable_positive_source_attach_sum_eq_raising_predecessor_source_sum
      (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = true)),
    tasaki23_lowerable_positive_source_attach_sum_eq_raising_predecessor_source_sum
      (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = false))]
  exact hdominates

end LatticeSystem.Quantum
