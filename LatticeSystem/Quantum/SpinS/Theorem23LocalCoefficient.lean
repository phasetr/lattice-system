import LatticeSystem.Quantum.SpinS.Theorem23Local

/-!
# Tasaki §2.5 Theorem 2.3 local coefficient API

This module contains the lowered coefficient and predecessor raising-source
API used by the local-difference and outside-ground layers of Tasaki
§2.5 Theorem 2.3. It is split from `Theorem23Local.lean` so the core
local ladder and single-site calculation layer can elaborate separately.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 single-site lowering predecessor**:
if a target configuration `τ` in sector `M + 1` has positive local
value at `x`, lowering that local value by one gives a configuration
in sector `M`.

This is the magnetization bookkeeping behind the local component
formula for a single summand in `Ŝ^-_tot`. -/
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
/-- **Tasaki §2.5 Theorem 2.3 signed local lowering contribution**:
the real signed contribution of the `x`-summand in the lowered
site-sum at a target-sector configuration.

This packages the repeated real expression used to split the lowered
site-sum into its off-`A` and on-`A` filtered pieces. -/
noncomputable def tasaki23SignedLoweringSiteContribution
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) (x : V) : ℝ :=
  (marshallSignS A τ.1).re *
    ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
      (magSectorEmbedding Φ)) τ.1).re)

/-- **Tasaki §2.5 Theorem 2.3 lowered predecessor signed coefficient**:
the boundary-inclusive coefficient obtained from the predecessor
configuration of `τ` at `x`.

If the target value `(τ.1 x).val` is positive, this is the positive
`Ŝ^-` matrix coefficient times the Marshall-signed predecessor
coefficient. If the target value is zero, the single-site lowering
summand is zero and this coefficient is defined to be zero as well. -/
noncomputable def tasaki23LoweringPredecessorSignedCoefficient
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) (x : V) : ℝ :=
  if hx : 0 < (τ.1 x).val then
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    let hpredM : magSumS pred = M :=
      magSumS_single_site_lowering_predecessor τ x hx
    (spinSOpMinus N (τ.1 x) predVal).re *
      ((marshallSignS A pred).re * (Φ ⟨pred, hpredM⟩).re)
  else
    0

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 positive predecessor coefficient value**:
for a Marshall-signed real sector vector, the boundary-inclusive lowered
predecessor coefficient at a lowerable site is just the positive
single-site lowering matrix coefficient times the positive real source
coefficient at the predecessor.

The two Marshall signs cancel by `marshallSignS_re_sq`; this is the
local positivity normalization used before comparing the on-`A` and
off-`A` predecessor coefficient sums. -/
theorem tasaki23_lowering_predecessor_signed_coefficient_eq_positive_source
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val) :
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    let hpredM : magSumS pred = M :=
      magSumS_single_site_lowering_predecessor τ x hx
    tasaki23LoweringPredecessorSignedCoefficient A
        (fun σ : magConfigS V N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) τ x =
      (spinSOpMinus N (τ.1 x) predVal).re * v ⟨pred, hpredM⟩ := by
  classical
  dsimp only
  let predVal : Fin (N + 1) := ⟨(τ.1 x).val - 1, by omega⟩
  let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
  let hpredM : magSumS pred = M :=
    magSumS_single_site_lowering_predecessor τ x hx
  have hsq : (marshallSignS A pred).re * (marshallSignS A pred).re = 1 :=
    marshallSignS_re_sq A pred
  rw [tasaki23LoweringPredecessorSignedCoefficient]
  simp only [hx, ↓reduceDIte, Complex.ofReal_re]
  change
    (spinSOpMinus N (τ.1 x) predVal).re *
        ((marshallSignS A pred).re *
          ((marshallSignS A pred).re * v ⟨pred, hpredM⟩)) =
      (spinSOpMinus N (τ.1 x) predVal).re * v ⟨pred, hpredM⟩
  have hcancel :
      (marshallSignS A pred).re *
          ((marshallSignS A pred).re * v ⟨pred, hpredM⟩) =
        v ⟨pred, hpredM⟩ := by
    calc
      (marshallSignS A pred).re *
          ((marshallSignS A pred).re * v ⟨pred, hpredM⟩) =
          ((marshallSignS A pred).re * (marshallSignS A pred).re) *
            v ⟨pred, hpredM⟩ := by ring
      _ = 1 * v ⟨pred, hpredM⟩ := by rw [hsq]
      _ = v ⟨pred, hpredM⟩ := by ring
  rw [hcancel]

/-- **Tasaki §2.5 Theorem 2.3 positive predecessor coefficient at a
lowerable site**: if the real source coefficients are strictly positive,
then every lowerable predecessor coefficient is strictly positive. -/
theorem tasaki23_lowering_predecessor_signed_coefficient_pos_of_lowerable
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val)
    (hv_pos : ∀ σ : magConfigS V N M, 0 < v σ) :
    0 <
      tasaki23LoweringPredecessorSignedCoefficient A
        (fun σ : magConfigS V N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) τ x := by
  classical
  let predVal : Fin (N + 1) := ⟨(τ.1 x).val - 1, by omega⟩
  let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
  have hpredM : magSumS pred = M :=
    magSumS_single_site_lowering_predecessor τ x hx
  have hcoef_lower : predVal.val + 1 = (τ.1 x).val := by
    dsimp [predVal]
    omega
  have hcoef_pos : 0 < (spinSOpMinus N (τ.1 x) predVal).re :=
    spinSOpMinus_apply_re_pos_of_lower N hcoef_lower
  rw [tasaki23_lowering_predecessor_signed_coefficient_eq_positive_source
    A v τ x hx]
  exact mul_pos hcoef_pos (hv_pos ⟨pred, hpredM⟩)

/-- **Tasaki §2.5 Theorem 2.3 non-negative predecessor coefficient**:
for a strictly positive real source vector, the boundary-inclusive
predecessor coefficient is non-negative at every site, with the
non-lowerable boundary case contributing zero. -/
theorem tasaki23_lowering_predecessor_signed_coefficient_nonneg
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (x : V)
    (hv_pos : ∀ σ : magConfigS V N M, 0 < v σ) :
    0 ≤
      tasaki23LoweringPredecessorSignedCoefficient A
        (fun σ : magConfigS V N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) τ x := by
  classical
  by_cases hx : 0 < (τ.1 x).val
  · exact le_of_lt
      (tasaki23_lowering_predecessor_signed_coefficient_pos_of_lowerable
        A v τ x hx hv_pos)
  · simp [tasaki23LoweringPredecessorSignedCoefficient, hx]

/-- **Tasaki §2.5 Theorem 2.3 positive-source predecessor coefficient**:
the boundary-inclusive lowered predecessor coefficient after the
Marshall signs have been cancelled.

At a lowerable site this is the positive single-site lowering matrix
coefficient times the real positive source coefficient at the predecessor;
at the lower boundary it is zero. -/
noncomputable def tasaki23LoweringPredecessorPositiveSourceCoefficient
    {M : ℕ} (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (x : V) : ℝ :=
  if hx : 0 < (τ.1 x).val then
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    let hpredM : magSumS pred = M :=
      magSumS_single_site_lowering_predecessor τ x hx
    (spinSOpMinus N (τ.1 x) predVal).re * v ⟨pred, hpredM⟩
  else
    0

/-- **Tasaki §2.5 Theorem 2.3 lowerable positive-source predecessor
coefficient**: the explicit lowered predecessor coefficient at a site
where the successor configuration can actually be lowered.

This is the non-boundary branch of
`tasaki23LoweringPredecessorPositiveSourceCoefficient`. -/
noncomputable def tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
    {M : ℕ} (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val) : ℝ :=
  let predVal : Fin (N + 1) :=
    ⟨(τ.1 x).val - 1, by omega⟩
  let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
  let hpredM : magSumS pred = M :=
    magSumS_single_site_lowering_predecessor τ x hx
  (spinSOpMinus N (τ.1 x) predVal).re * v ⟨pred, hpredM⟩

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

/-- **Tasaki §2.5 Theorem 2.3 boundary coefficient as lowerable
coefficient**: at a lowerable site, the boundary-inclusive positive-source
coefficient is the explicit lowerable coefficient. -/
theorem tasaki23_positive_source_coefficient_eq_lowerable_coefficient
    {M : ℕ} (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val) :
    tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x =
      tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient v τ x hx := by
  simp [tasaki23LoweringPredecessorPositiveSourceCoefficient,
    tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient, hx]

/-- **Tasaki §2.5 Theorem 2.3 positive-source coefficient sum over
lowerable sites**: the boundary-inclusive positive-source coefficient sum
over a finite set is unchanged after restricting the finite set to sites
where the successor configuration can actually be lowered. -/
theorem tasaki23_positive_source_coefficient_sum_eq_lowerable_sum
    {M : ℕ} (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (s : Finset V) :
    (∑ x ∈ s, tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) =
      ∑ x ∈ s.filter (fun x : V => 0 < (τ.1 x).val),
        tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := s) (p := fun x : V => 0 < (τ.1 x).val)
    (f := fun x : V => tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x)]
  have hzero :
      (∑ x ∈ s.filter (fun x : V => ¬ 0 < (τ.1 x).val),
        tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hxnot : ¬ 0 < (τ.1 x).val := (Finset.mem_filter.mp hx).2
    simp [tasaki23LoweringPredecessorPositiveSourceCoefficient, hxnot]
  rw [hzero, add_zero]

/-- **Tasaki §2.5 Theorem 2.3 explicit lowerable coefficient sum**:
after filtering to sites where the successor configuration can be lowered,
the boundary-inclusive positive-source coefficient sum is the attached
finite sum of the explicit lowerable predecessor coefficients. -/
theorem tasaki23_positive_source_lowerable_filter_sum_eq_lowerable_attach_sum
    {M : ℕ} (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (s : Finset V) :
    (∑ x ∈ s.filter (fun x : V => 0 < (τ.1 x).val),
        tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) =
      (s.filter (fun x : V => 0 < (τ.1 x).val)).attach.sum
        (fun x =>
          tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
            v τ x.1 ((Finset.mem_filter.mp x.2).2)) := by
  classical
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro x _hx
  exact
    tasaki23_positive_source_coefficient_eq_lowerable_coefficient
      v τ x.1 ((Finset.mem_filter.mp x.2).2)

/-- **Tasaki §2.5 Theorem 2.3 explicit lowerable coefficient dominance**:
dominance of the attached sums of explicit lowerable predecessor
coefficients implies the filtered boundary-inclusive positive-source
coefficient dominance used by the previous callback boundary. -/
theorem tasaki23_positive_source_lowerable_coefficient_lt_of_attach_sum_lt
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1))
    (hdominates :
      (((Finset.univ.filter (fun x : V => A x = true)).filter
            (fun x : V => 0 < (τ.1 x).val)).attach.sum
          (fun x =>
            tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
              v τ x.1 ((Finset.mem_filter.mp x.2).2))) <
        (((Finset.univ.filter (fun x : V => A x = false)).filter
            (fun x : V => 0 < (τ.1 x).val)).attach.sum
          (fun x =>
            tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
              v τ x.1 ((Finset.mem_filter.mp x.2).2)))) :
    (∑ x ∈ ((Finset.univ.filter (fun x : V => A x = true)).filter
        (fun x : V => 0 < (τ.1 x).val)),
        tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) <
      ∑ x ∈ ((Finset.univ.filter (fun x : V => A x = false)).filter
        (fun x : V => 0 < (τ.1 x).val)),
        tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x := by
  rw [
    tasaki23_positive_source_lowerable_filter_sum_eq_lowerable_attach_sum
      v τ (Finset.univ.filter (fun x : V => A x = true)),
    tasaki23_positive_source_lowerable_filter_sum_eq_lowerable_attach_sum
      v τ (Finset.univ.filter (fun x : V => A x = false))]
  exact hdominates

/-- **Tasaki §2.5 Theorem 2.3 signed coefficient as positive-source
coefficient**: for a Marshall-signed real source vector, the
boundary-inclusive signed predecessor coefficient is exactly the
sign-normalized positive-source coefficient. -/
theorem tasaki23_lowering_predecessor_signed_coefficient_eq_positive_source_coefficient
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (x : V) :
    tasaki23LoweringPredecessorSignedCoefficient A
        (fun σ : magConfigS V N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) τ x =
      tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x := by
  classical
  by_cases hx : 0 < (τ.1 x).val
  · rw [tasaki23_lowering_predecessor_signed_coefficient_eq_positive_source
      A v τ x hx]
    simp [tasaki23LoweringPredecessorPositiveSourceCoefficient, hx]
  · simp [tasaki23LoweringPredecessorSignedCoefficient,
      tasaki23LoweringPredecessorPositiveSourceCoefficient, hx]

/-- **Tasaki §2.5 Theorem 2.3 signed coefficient sum as positive-source
coefficient sum**: over any finite site set, the Marshall-signed
predecessor coefficient sum for a Marshall-signed real source vector is
the corresponding sign-normalized positive-source coefficient sum. -/
theorem tasaki23_lowering_predecessor_coefficient_sum_eq_positive_source_sum
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (s : Finset V) :
    (∑ x ∈ s,
      tasaki23LoweringPredecessorSignedCoefficient A
        (fun σ : magConfigS V N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) τ x) =
      ∑ x ∈ s, tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x := by
  apply Finset.sum_congr rfl
  intro x _hx
  exact
    tasaki23_lowering_predecessor_signed_coefficient_eq_positive_source_coefficient
      A v τ x

/-- **Tasaki §2.5 Theorem 2.3 off-`A` lowered contribution split**:
outside `A`, the signed single-site lowering contribution is exactly
the boundary-inclusive signed predecessor coefficient.

This packages the off-`A` coefficient identity in a form that can be
summed without carrying a separate lowerability proof for every site. -/
theorem tasaki23_signed_lowering_site_contribution_eq_coefficient_of_A_false
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) (x : V)
    (hAx : A x = false) :
    tasaki23SignedLoweringSiteContribution A Φ τ x =
      tasaki23LoweringPredecessorSignedCoefficient A Φ τ x := by
  classical
  by_cases hx : 0 < (τ.1 x).val
  · simpa [tasaki23SignedLoweringSiteContribution,
      tasaki23LoweringPredecessorSignedCoefficient, hx]
      using
        tasaki23_signed_single_site_lowering_component_eq_of_A_false
          A Φ τ x hx hAx
  · have hzero : (τ.1 x).val = 0 := by omega
    rw [tasaki23SignedLoweringSiteContribution,
      tasaki23LoweringPredecessorSignedCoefficient]
    rw [onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_eq_zero_of_target_zero
      Φ τ x hzero]
    simp [hx]

/-- **Tasaki §2.5 Theorem 2.3 on-`A` lowered contribution split**:
inside `A`, the signed single-site lowering contribution is the
negative of the boundary-inclusive signed predecessor coefficient.

This is the on-`A` companion to
`tasaki23_signed_lowering_site_contribution_eq_coefficient_of_A_false`
and isolates the exact term whose total size must be dominated by the
off-`A` contribution in the final lowered Marshall-positivity proof. -/
theorem tasaki23_signed_lowering_site_contribution_eq_neg_coefficient_of_A_true
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) (x : V)
    (hAx : A x = true) :
    tasaki23SignedLoweringSiteContribution A Φ τ x =
      -tasaki23LoweringPredecessorSignedCoefficient A Φ τ x := by
  classical
  by_cases hx : 0 < (τ.1 x).val
  · simpa [tasaki23SignedLoweringSiteContribution,
      tasaki23LoweringPredecessorSignedCoefficient, hx]
      using
        tasaki23_signed_single_site_lowering_component_eq_neg_of_A_true
          A Φ τ x hx hAx
  · have hzero : (τ.1 x).val = 0 := by omega
    rw [tasaki23SignedLoweringSiteContribution,
      tasaki23LoweringPredecessorSignedCoefficient]
    rw [onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_eq_zero_of_target_zero
      Φ τ x hzero]
    simp [hx]

/-- **Tasaki §2.5 Theorem 2.3 off-`A` coefficient-sum split**:
the off-`A` filtered signed lowering sum is exactly the corresponding
sum of boundary-inclusive predecessor coefficients.

This is the finite-sum form of
`tasaki23_signed_lowering_site_contribution_eq_coefficient_of_A_false`
and is the off-`A` side of the coefficient-level dominance comparison. -/
theorem tasaki23_signed_lowering_offA_sum_eq_coefficient_sum
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) :
    (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23SignedLoweringSiteContribution A Φ τ x) =
    ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23LoweringPredecessorSignedCoefficient A Φ τ x := by
  apply Finset.sum_congr rfl
  intro x hx
  have hAx : A x = false := by
    simpa using (Finset.mem_filter.mp hx).2
  exact tasaki23_signed_lowering_site_contribution_eq_coefficient_of_A_false
    A Φ τ x hAx

/-- **Tasaki §2.5 Theorem 2.3 on-`A` coefficient-sum split**:
the on-`A` filtered signed lowering sum is the negative of the
corresponding boundary-inclusive predecessor coefficient sum.

This is the finite-sum form of
`tasaki23_signed_lowering_site_contribution_eq_neg_coefficient_of_A_true`
and isolates the negative sublattice contribution that must be
controlled in the final lowered Marshall-positivity proof. -/
theorem tasaki23_signed_lowering_onA_sum_eq_neg_coefficient_sum
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) :
    (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
      tasaki23SignedLoweringSiteContribution A Φ τ x) =
    -∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
      tasaki23LoweringPredecessorSignedCoefficient A Φ τ x := by
  calc
    (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
      tasaki23SignedLoweringSiteContribution A Φ τ x) =
        ∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
          -tasaki23LoweringPredecessorSignedCoefficient A Φ τ x := by
          apply Finset.sum_congr rfl
          intro x hx
          have hAx : A x = true := by
            simpa using (Finset.mem_filter.mp hx).2
          exact
            tasaki23_signed_lowering_site_contribution_eq_neg_coefficient_of_A_true
              A Φ τ x hAx
    _ = -∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23LoweringPredecessorSignedCoefficient A Φ τ x := by
          rw [Finset.sum_neg_distrib]


end LatticeSystem.Quantum
