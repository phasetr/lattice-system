import LatticeSystem.Quantum.SpinS.DressedAxisSwapBondReStrictNeg
import LatticeSystem.Quantum.SpinS.DressedAxisSwapOffDiag
import LatticeSystem.Quantum.SpinS.DressedAxisSwapPFMatrix
import LatticeSystem.Quantum.SpinS.HeisenbergRaiseLower
import LatticeSystem.Quantum.SpinS.BipartiteCompleteGraphCore

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Strict negativity of the full dressed `Ĥ'` on a transverse step (bipartite, case (i) strict)

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Strict counterpart of `dressedAxisSwappedAnisotropicHeisenbergS_offdiag_re_nonpos` (#3770).  On a
`RaiseLowerStepS` witness at a bipartite bond `{x, y}` of the bipartite complete graph
`bipartiteCompleteGraphOf A` (so `A x ≠ A y`), under case (i) strict (`−1 < λ.re ≤ 1` real,
`D.re ≥ 0`), the full dressed `Ĥ'` off-diagonal entry has **strict negative** real part.

The proof inherits the nonpos sum structure of #3770: every per-bond dressed contribution is
non-positive (#3770's `dressedAxisSwapped_bond_re_nonpos_bipartite_x/y` per (a, b)), and the
dressed single-ion is non-positive (#3770's `dressed_singleIonAnisotropyS2_re_nonpos`).  Strictness
comes from the matching `(x, y)` bond: by #3791 the dressed bond at the witness is strict
negative.  The full real part is then strict negative via a `Finset.sum_neg` helper.

Consequently the shifted PF matrix entry `shiftedDressedAxisSwappedReMatrix A J λ D N c τ σ` is
**strictly positive** on a transverse step — the input `hB_step` of the
`Matrix.isIrreducible_iff_exists_pow_pos` route (PR5 (c) for the transverse `RaiseLowerStepS`
move).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- A finite sum of real numbers is strictly negative if every term is non-positive and at least
one term is strictly negative. -/
theorem Finset.sum_neg_of_forall_nonpos_of_exists_neg
    {α : Type*} {s : _root_.Finset α} {f : α → ℝ}
    (hnp : ∀ a ∈ s, f a ≤ 0) (hex : ∃ a ∈ s, f a < 0) : ∑ a ∈ s, f a < 0 := by
  classical
  obtain ⟨a₀, ha₀, hf₀⟩ := hex
  have hrest : ∑ a ∈ s.erase a₀, f a ≤ 0 :=
    _root_.Finset.sum_nonpos (fun a ha => hnp a (_root_.Finset.mem_of_mem_erase ha))
  calc ∑ a ∈ s, f a
      = f a₀ + ∑ a ∈ s.erase a₀, f a := by rw [_root_.Finset.add_sum_erase _ _ ha₀]
    _ < 0 := by linarith

/-- **Strict negativity of the dressed `Ĥ'` off-diagonal on a `RaiseLowerStepS` witness** (case (i)
strict, bipartite).  For a witness at `{x, y}` with `A x ≠ A y` (one site on `A`, the other not),
real `λ` with `−1 < λ.re ≤ 1` and real `D ≥ 0`, the dressed real part is strictly negative. -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_apply_re_neg_of_raiseLowerStepS_witness_bipartite
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re ≤ 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    {x y : Λ} (hxy : x ≠ y) (hAne : A x ≠ A y)
    (hJpos_xy : 0 < (J x y).re)
    {σ' σ : Λ → Fin (N + 1)}
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N σ' σ).re < 0 := by
  have hne : σ' ≠ σ := by
    intro he
    rcases hsh with ⟨hsx, _⟩ | ⟨hsx, _⟩ <;> · rw [he] at hsx; omega
  -- Per-bond dressed contribution Re ≤ 0 (existing #3770).
  have hbond_nonpos : ∀ a b, (marshallSignS A σ * marshallSignS A σ' *
      (J a b * spinSDotXXZSwap a b lam N σ' σ)).re ≤ 0 := by
    intro a b
    by_cases hJ : J a b = 0
    · rw [hJ, zero_mul, mul_zero, Complex.zero_re]
    · have hAxy := hJbip a b hJ
      have hxy_ab : a ≠ b := fun h => hJ (by rw [h]; exact hJself b)
      by_cases hagree_ab : ∀ k, k ≠ a → k ≠ b → σ' k = σ k
      · have hz : (marshallSignS A σ * marshallSignS A σ' *
            spinSDotXXZSwap a b lam N σ' σ).re ≤ 0 := by
          rcases Bool.eq_false_or_eq_true (A a) with hAa | hAa
          · have hAb : A b = false := by
              rcases Bool.eq_false_or_eq_true (A b) with hAb | hAb
              · exact absurd (hAa.trans hAb.symm) hAxy
              · exact hAb
            exact dressedAxisSwapped_bond_re_nonpos_bipartite_x A hxy_ab hAa hAb hlam
              (le_of_lt hlb) hub hne hagree_ab
          · have hAb : A b = true := by
              rcases Bool.eq_false_or_eq_true (A b) with hAb | hAb
              · exact hAb
              · exact absurd (hAa.trans hAb.symm) hAxy
            exact dressedAxisSwapped_bond_re_nonpos_bipartite_y A hxy_ab hAa hAb hlam
              (le_of_lt hlb) hub hne hagree_ab
        rw [show marshallSignS A σ * marshallSignS A σ' *
              (J a b * spinSDotXXZSwap a b lam N σ' σ) =
            J a b * (marshallSignS A σ * marshallSignS A σ' *
              spinSDotXXZSwap a b lam N σ' σ) from by ring,
          Complex.mul_re, hJim, zero_mul, sub_zero]
        exact mul_nonpos_of_nonneg_of_nonpos (hJnn a b) hz
      · rw [spinSDotXXZSwap_apply_eq_zero_of_not_agree hxy_ab lam hagree_ab,
          mul_zero, mul_zero, Complex.zero_re]
  -- Strict negativity of the (x, y) bond contribution.
  have hbond_xy_neg : (marshallSignS A σ * marshallSignS A σ' *
      (J x y * spinSDotXXZSwap x y lam N σ' σ)).re < 0 := by
    rw [show marshallSignS A σ * marshallSignS A σ' * (J x y * spinSDotXXZSwap x y lam N σ' σ)
        = J x y * (marshallSignS A σ * marshallSignS A σ' *
          spinSDotXXZSwap x y lam N σ' σ) from by ring,
      Complex.mul_re, hJim, zero_mul, sub_zero]
    rcases Bool.eq_false_or_eq_true (A x) with hAx | hAx
    · -- A x = true, hence A y = false; use _x suffix.
      have hAy : A y = false := by
        rcases Bool.eq_false_or_eq_true (A y) with hAy | hAy
        · exact absurd (hAx.trans hAy.symm) hAne
        · exact hAy
      have hbond := dressedAxisSwapped_bond_re_neg_bipartite_x_of_raiseLower_witness A hxy hAx hAy
        hlam hlb hsh hagree
      exact mul_neg_of_pos_of_neg hJpos_xy hbond
    · -- A x = false, hence A y = true; use _y suffix.
      have hAy : A y = true := by
        rcases Bool.eq_false_or_eq_true (A y) with hAy | hAy
        · exact hAy
        · exact absurd (hAx.trans hAy.symm) hAne
      have hbond := dressedAxisSwapped_bond_re_neg_bipartite_y_of_raiseLower_witness A hxy hAx hAy
        hlam hlb hsh hagree
      exact mul_neg_of_pos_of_neg hJpos_xy hbond
  -- The bond-sum off-diagonal entry, pushed through the double sum.
  have hsum : (∑ a : Λ, ∑ b : Λ, J a b • spinSDotXXZSwap a b lam N : ManyBodyOpS Λ N) σ' σ =
      ∑ a : Λ, ∑ b : Λ, J a b * spinSDotXXZSwap a b lam N σ' σ := by
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Matrix.smul_apply, smul_eq_mul]
  rw [dressedAxisSwappedAnisotropicHeisenbergS_apply,
    mul_comm (marshallSignS A σ') (marshallSignS A σ),
    axisSwappedAnisotropicHeisenbergS_def, Matrix.add_apply, hsum, mul_add, Complex.add_re]
  -- Re(dressed bonds) < 0 strict via the (x, y) bond contribution.
  have hbonds_neg : (marshallSignS A σ * marshallSignS A σ' *
      ∑ a : Λ, ∑ b : Λ, J a b * spinSDotXXZSwap a b lam N σ' σ).re < 0 := by
    rw [Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_neg_of_forall_nonpos_of_exists_neg
    · intro a _
      rw [Finset.mul_sum, Complex.re_sum]
      exact Finset.sum_nonpos (fun b _ => hbond_nonpos a b)
    · refine ⟨x, Finset.mem_univ x, ?_⟩
      rw [Finset.mul_sum, Complex.re_sum]
      apply Finset.sum_neg_of_forall_nonpos_of_exists_neg
      · intro b _; exact hbond_nonpos x b
      · exact ⟨y, Finset.mem_univ y, hbond_xy_neg⟩
  exact add_neg_of_neg_of_nonpos hbonds_neg
    (dressed_singleIonAnisotropyS2_re_nonpos A hDim hDnn hne)

/-- The shifted PF matrix entry is strictly positive on a `RaiseLowerStepS` witness on a bipartite
bond (case (i) strict). -/
theorem shiftedDressedAxisSwappedReMatrix_apply_pos_of_raiseLowerStepS_witness_bipartite
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re ≤ 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    (c : ℝ)
    {x y : Λ} (hxy : x ≠ y) (hAne : A x ≠ A y) (hJpos_xy : 0 < (J x y).re)
    {σ' σ : Λ → Fin (N + 1)}
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    0 < shiftedDressedAxisSwappedReMatrix A J lam D N c σ' σ := by
  have hne : σ' ≠ σ := by
    intro he
    rcases hsh with ⟨hsx, _⟩ | ⟨hsx, _⟩ <;> · rw [he] at hsx; omega
  unfold shiftedDressedAxisSwappedReMatrix
  rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hne, smul_zero, zero_sub]
  have hneg :=
    dressedAxisSwappedAnisotropicHeisenbergS_apply_re_neg_of_raiseLowerStepS_witness_bipartite
      A hJim hJnn hJself hJbip hlam hlb hub hDim hDnn hxy hAne hJpos_xy hsh hagree
  change 0 < -((dressedAxisSwappedAnisotropicHeisenbergS A J lam D N) σ' σ).re
  linarith

/-- **Shifted PF matrix entry strictly positive on a transverse step**.  For a
`RaiseLowerStepS` on `bipartiteCompleteGraphOf A`, case (i) strict, the shifted matrix
`shiftedDressedAxisSwappedReMatrix A J λ D N c σ' σ > 0`. -/
theorem shiftedDressedAxisSwappedReMatrix_apply_pos_of_raiseLowerStepS_bipartite
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re ≤ 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    (c : ℝ)
    {σ τ : Λ → Fin (N + 1)} (hstep : RaiseLowerStepS (bipartiteCompleteGraphOf A) σ τ) :
    0 < shiftedDressedAxisSwappedReMatrix A J lam D N c τ σ := by
  obtain ⟨x, y, hadj, hsh, hagree⟩ := hstep
  have hxy : x ≠ y := hadj.ne
  have hAne : A x ≠ A y := bipartiteCompleteGraphOf_adj_sublattice_ne hadj
  exact shiftedDressedAxisSwappedReMatrix_apply_pos_of_raiseLowerStepS_witness_bipartite
    A hJim hJnn hJself hJbip hlam hlb hub hDim hDnn c hxy hAne (hJpos x y hadj) hsh hagree

end LatticeSystem.Quantum
