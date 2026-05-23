import LatticeSystem.Quantum.SpinS.Theorem23LocalLowering

/-!
# Tasaki §2.5 Theorem 2.3 local coefficient API

This module contains the lowered signed and positive-source coefficient API
used by the local-difference and outside-ground layers of Tasaki §2.5
Theorem 2.3. The predecessor raising-source coefficient suffix is split into
`Theorem23LocalCoefficientRaisingSource.lean`, and the signed-coefficient
identities (signed predecessor coefficient = positive-source coefficient,
signed lowering site-contribution = ±coefficient, and the off-`A`/on-`A`
filtered signed-lowering sum identities) are split into
`Theorem23LocalCoefficientSignedSum.lean`. This module sits downstream of
`Theorem23LocalLowering.lean` so the core local ladder and lowering component
layers can elaborate separately from the coefficient comparison layer.

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
theorem magSumS_single_site_lowering_predecessor {M : ℕ}
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

end LatticeSystem.Quantum
