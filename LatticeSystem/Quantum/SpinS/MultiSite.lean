import LatticeSystem.Quantum.SpinS.Operators
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Multi-site spin-`S` operator space and site-embedded operators
(Tasaki §2.5 Phase B-β β-3a)

This module generalises the spin-1/2 many-body operator space
(`Quantum/ManyBody.lean`, `ManyBodyOp Λ`) to **arbitrary spin** by
indexing configurations on `Λ → Fin (N + 1)` (with `N = 2S`).

The principal construction is the site-embedded operator

  `onSiteS i A : ManyBodyOpS Λ N`

which acts as a single-site spin-`S` operator
`A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ` on site `i ∈ Λ` and as
the identity on every other site.

This is the multi-site analogue needed for the spin-`S` Heisenberg
Hamiltonian and the §2.5 Marshall–Lieb–Mattis machinery for general
spin (Issue #412 Phase B-γ).

Tracked in #412.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The operator space on the spin-`S` many-body Hilbert space indexed
by the lattice `Λ`, represented as matrices indexed by computational-
basis configurations `σ : Λ → Fin (N + 1)`. -/
abbrev ManyBodyOpS (Λ : Type*) (N : ℕ) : Type _ :=
  Matrix (Λ → Fin (N + 1)) (Λ → Fin (N + 1)) ℂ

/-- Definitional unfolding: `ManyBodyOpS Λ N = Matrix (Λ → Fin (N+1)) (Λ → Fin (N+1)) ℂ`. -/
theorem ManyBodyOpS_def (Λ : Type*) (N : ℕ) :
    ManyBodyOpS Λ N = Matrix (Λ → Fin (N + 1)) (Λ → Fin (N + 1)) ℂ := rfl

/-- The site-embedded operator `onSiteS i A` acts as `A` on site `i`
and as the identity on every other site. Its matrix element is
`A (σ' i) (σ i)` when `σ'` and `σ` agree at every site other than
`i`, and `0` otherwise. -/
def onSiteS (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    ManyBodyOpS Λ N :=
  fun σ' σ =>
    if (∀ k, k ≠ i → σ' k = σ k) then A (σ' i) (σ i) else 0

/-- Definitional unfolding of `onSiteS`. -/
theorem onSiteS_def (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS (N := N) i A : ManyBodyOpS Λ N) =
      (fun σ' σ =>
        if (∀ k, k ≠ i → σ' k = σ k) then A (σ' i) (σ i) else 0) := rfl

/-- Unfolding the matrix element of `onSiteS i A`. -/
theorem onSiteS_apply (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (σ' σ : Λ → Fin (N + 1)) :
    onSiteS i A σ' σ =
      if (∀ k, k ≠ i → σ' k = σ k) then A (σ' i) (σ i) else 0 := rfl

/-- The matrix element vanishes when configurations differ off-site. -/
theorem onSiteS_apply_eq_zero_of_off_site_diff
    (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ¬ (∀ k, k ≠ i → σ' k = σ k)) :
    onSiteS i A σ' σ = 0 := by
  rw [onSiteS_apply, if_neg h]

/-- The matrix element when configurations agree off-site. -/
theorem onSiteS_apply_of_off_site_agree
    (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ i → σ' k = σ k) :
    onSiteS i A σ' σ = A (σ' i) (σ i) := by
  rw [onSiteS_apply, if_pos h]

/-- The diagonal matrix element on the same configuration. -/
theorem onSiteS_apply_diag
    (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (σ : Λ → Fin (N + 1)) :
    onSiteS i A σ σ = A (σ i) (σ i) := by
  rw [onSiteS_apply_of_off_site_agree]
  intro _ _; rfl

/-- If every entry of `A` has zero imaginary part, every entry of
`onSiteS i A` has zero imaginary part. -/
theorem onSiteS_apply_im_zero (i : Λ)
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hA : ∀ p q, (A p q).im = 0)
    (σ' σ : Λ → Fin (N + 1)) :
    ((onSiteS i A : ManyBodyOpS Λ N) σ' σ).im = 0 := by
  rw [onSiteS_apply]
  by_cases h : ∀ k, k ≠ i → σ' k = σ k
  · rw [if_pos h]; exact hA _ _
  · rw [if_neg h]; simp

/-- If every entry of `A` has zero real part, every entry of
`onSiteS i A` has zero real part. -/
theorem onSiteS_apply_re_zero (i : Λ)
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hA : ∀ p q, (A p q).re = 0)
    (σ' σ : Λ → Fin (N + 1)) :
    ((onSiteS i A : ManyBodyOpS Λ N) σ' σ).re = 0 := by
  rw [onSiteS_apply]
  by_cases h : ∀ k, k ≠ i → σ' k = σ k
  · rw [if_pos h]; exact hA _ _
  · rw [if_neg h]; simp

/-- If every entry of `A` has non-negative real part, every entry of
`onSiteS i A` has non-negative real part. -/
theorem onSiteS_apply_re_nonneg (i : Λ)
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hA : ∀ p q, 0 ≤ (A p q).re)
    (σ' σ : Λ → Fin (N + 1)) :
    0 ≤ ((onSiteS i A : ManyBodyOpS Λ N) σ' σ).re := by
  rw [onSiteS_apply]
  by_cases h : ∀ k, k ≠ i → σ' k = σ k
  · rw [if_pos h]; exact hA _ _
  · rw [if_neg h]; simp

/-- Every entry of `onSiteS i (Ŝ^+)` has zero imaginary part. -/
theorem onSiteS_spinSOpPlus_apply_im_zero (i : Λ) (σ' σ : Λ → Fin (N + 1)) :
    ((onSiteS i (spinSOpPlus N) : ManyBodyOpS Λ N) σ' σ).im = 0 :=
  onSiteS_apply_im_zero i (spinSOpPlus_apply_im_zero N) σ' σ

/-- Every entry of `onSiteS i (Ŝ^-)` has zero imaginary part. -/
theorem onSiteS_spinSOpMinus_apply_im_zero (i : Λ) (σ' σ : Λ → Fin (N + 1)) :
    ((onSiteS i (spinSOpMinus N) : ManyBodyOpS Λ N) σ' σ).im = 0 :=
  onSiteS_apply_im_zero i (spinSOpMinus_apply_im_zero N) σ' σ

/-- Every entry of `onSiteS i (Ŝ^+)` has non-negative real part. -/
theorem onSiteS_spinSOpPlus_apply_re_nonneg (i : Λ) (σ' σ : Λ → Fin (N + 1)) :
    0 ≤ ((onSiteS i (spinSOpPlus N) : ManyBodyOpS Λ N) σ' σ).re :=
  onSiteS_apply_re_nonneg i (spinSOpPlus_apply_re_nonneg N) σ' σ

/-- Every entry of `onSiteS i (Ŝ^-)` has non-negative real part. -/
theorem onSiteS_spinSOpMinus_apply_re_nonneg
    (i : Λ) (σ' σ : Λ → Fin (N + 1)) :
    0 ≤ ((onSiteS i (spinSOpMinus N) : ManyBodyOpS Λ N) σ' σ).re :=
  onSiteS_apply_re_nonneg i (spinSOpMinus_apply_re_nonneg N) σ' σ

/-- Every entry of `onSiteS i (Ŝ^{(1)})` has zero imaginary part. -/
theorem onSiteS_spinSOp1_apply_im_zero (i : Λ) (σ' σ : Λ → Fin (N + 1)) :
    ((onSiteS i (spinSOp1 N) : ManyBodyOpS Λ N) σ' σ).im = 0 :=
  onSiteS_apply_im_zero i (spinSOp1_apply_im_zero N) σ' σ

/-- Every entry of `onSiteS i (Ŝ^{(1)})` has non-negative real part. -/
theorem onSiteS_spinSOp1_apply_re_nonneg (i : Λ) (σ' σ : Λ → Fin (N + 1)) :
    0 ≤ ((onSiteS i (spinSOp1 N) : ManyBodyOpS Λ N) σ' σ).re :=
  onSiteS_apply_re_nonneg i (spinSOp1_apply_re_nonneg N) σ' σ

/-- Every entry of `onSiteS i (Ŝ^{(2)})` has zero real part. -/
theorem onSiteS_spinSOp2_apply_re_zero (i : Λ) (σ' σ : Λ → Fin (N + 1)) :
    ((onSiteS i (spinSOp2 N) : ManyBodyOpS Λ N) σ' σ).re = 0 :=
  onSiteS_apply_re_zero i (spinSOp2_apply_re_zero N) σ' σ

/-- Every entry of `onSiteS i (Ŝ^{(3)})` has zero imaginary part. -/
theorem onSiteS_spinSOp3_apply_im_zero (i : Λ) (σ' σ : Λ → Fin (N + 1)) :
    ((onSiteS i (spinSOp3 N) : ManyBodyOpS Λ N) σ' σ).im = 0 :=
  onSiteS_apply_im_zero i (spinSOp3_apply_im_zero N) σ' σ


/-- If `A` is Hermitian, so is its site embedding `onSiteS i A`. -/
theorem onSiteS_isHermitian (i : Λ)
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} (hA : A.IsHermitian) :
    (onSiteS (Λ := Λ) (N := N) i A).IsHermitian := by
  ext σ σ'
  simp only [Matrix.conjTranspose_apply, onSiteS_apply]
  by_cases h : ∀ k, k ≠ i → σ k = σ' k
  · have h' : ∀ k, k ≠ i → σ' k = σ k := fun k hki => (h k hki).symm
    rw [if_pos h', if_pos h]
    exact hA.apply (σ i) (σ' i)
  · have h' : ¬ (∀ k, k ≠ i → σ' k = σ k) := by
      intro hp
      exact h (fun k hki => (hp k hki).symm)
    rw [if_neg h', if_neg h, star_zero]

/-! ## Commutativity at distinct sites -/

/-- Pivot configuration used in the proof that distinct-site
embeddings commute: agree with `σ` everywhere except at site `j`,
where it takes the value `σ' j`. -/
private def pivotLeftS {N : ℕ} (σ' σ : Λ → Fin (N + 1)) (j : Λ) :
    Λ → Fin (N + 1) :=
  Function.update σ j (σ' j)

omit [Fintype Λ] in
private lemma pivotLeftS_at_i_of_ne {i j : Λ} (hij : i ≠ j)
    (σ' σ : Λ → Fin (N + 1)) : pivotLeftS σ' σ j i = σ i := by
  rw [pivotLeftS, Function.update_of_ne hij]

omit [Fintype Λ] in
private lemma pivotLeftS_at_j (σ' σ : Λ → Fin (N + 1)) (j : Λ) :
    pivotLeftS σ' σ j j = σ' j := by
  rw [pivotLeftS, Function.update_self]

omit [Fintype Λ] in
private lemma pivotLeftS_off_j {j k : Λ} (hk : k ≠ j)
    (σ' σ : Λ → Fin (N + 1)) :
    pivotLeftS σ' σ j k = σ k := by
  rw [pivotLeftS, Function.update_of_ne hk]

private lemma onSiteS_mul_onSiteS_apply_of_ne_aux {i j : Λ} (hij : i ≠ j)
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (σ' σ : Λ → Fin (N + 1)) :
    (onSiteS i A * onSiteS j B) σ' σ =
      onSiteS i A σ' (pivotLeftS σ' σ j) *
        onSiteS j B (pivotLeftS σ' σ j) σ := by
  rw [Matrix.mul_apply]
  apply Fintype.sum_eq_single
  intro τ hτ
  simp only [onSiteS_apply]
  by_cases hτj : τ j = σ' j
  · have : ¬ (∀ k, k ≠ j → τ k = σ k) := by
      intro hall
      apply hτ
      funext k
      by_cases hkj : k = j
      · subst hkj
        rw [pivotLeftS_at_j]
        exact hτj
      · rw [pivotLeftS_off_j hkj]
        exact hall k hkj
    rw [if_neg this, mul_zero]
  · have hnotall : ¬ (∀ k, k ≠ i → σ' k = τ k) := by
      intro hall
      exact hτj (hall j hij.symm).symm
    rw [if_neg hnotall, zero_mul]

private lemma onSiteS_mul_onSiteS_value_of_agree {i j : Λ} (hij : i ≠ j)
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) {σ' σ : Λ → Fin (N + 1)}
    (hagree : ∀ k, k ≠ i → k ≠ j → σ' k = σ k) :
    onSiteS i A σ' (pivotLeftS σ' σ j) *
      onSiteS j B (pivotLeftS σ' σ j) σ =
      A (σ' i) (σ i) * B (σ' j) (σ j) := by
  simp only [onSiteS_apply]
  rw [if_pos, if_pos]
  · rw [pivotLeftS_at_i_of_ne hij, pivotLeftS_at_j]
  · intro k hkj
    exact pivotLeftS_off_j hkj σ' σ
  · intro k hki
    by_cases hkj : k = j
    · rw [hkj, pivotLeftS_at_j]
    · rw [pivotLeftS_off_j hkj]
      exact hagree k hki hkj

private lemma onSiteS_mul_onSiteS_value_of_disagree {i j : Λ}
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) {σ' σ : Λ → Fin (N + 1)}
    (hdis : ¬ ∀ k, k ≠ i → k ≠ j → σ' k = σ k) :
    onSiteS i A σ' (pivotLeftS σ' σ j) *
      onSiteS j B (pivotLeftS σ' σ j) σ = 0 := by
  simp only [onSiteS_apply]
  rw [if_neg]
  · exact zero_mul _
  · intro hall
    apply hdis
    intro k hki hkj
    have := hall k hki
    rwa [pivotLeftS_off_j hkj] at this

private lemma onSiteS_mul_onSiteS_apply_of_ne {i j : Λ} (hij : i ≠ j)
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (σ' σ : Λ → Fin (N + 1)) :
    (onSiteS i A * onSiteS j B) σ' σ =
      if ∀ k, k ≠ i → k ≠ j → σ' k = σ k then
        A (σ' i) (σ i) * B (σ' j) (σ j)
      else 0 := by
  rw [onSiteS_mul_onSiteS_apply_of_ne_aux hij]
  by_cases h : ∀ k, k ≠ i → k ≠ j → σ' k = σ k
  · rw [if_pos h]
    exact onSiteS_mul_onSiteS_value_of_agree hij A B h
  · rw [if_neg h]
    exact onSiteS_mul_onSiteS_value_of_disagree A B h

/-- Public matrix element formula for the product of distinct-site
embeddings: factors into a per-site product of `A` and `B`'s
matrix elements, with the off-site delta. -/
theorem onSiteS_mul_onSiteS_apply_eq {i j : Λ} (hij : i ≠ j)
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (σ' σ : Λ → Fin (N + 1)) :
    (onSiteS i A * onSiteS j B) σ' σ =
      if ∀ k, k ≠ i → k ≠ j → σ' k = σ k then
        A (σ' i) (σ i) * B (σ' j) (σ j)
      else 0 :=
  onSiteS_mul_onSiteS_apply_of_ne hij A B σ' σ

/-- Operators embedded at distinct sites commute. -/
theorem onSiteS_mul_onSiteS_of_ne {i j : Λ} (hij : i ≠ j)
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A * onSiteS j B : ManyBodyOpS Λ N) =
      onSiteS j B * onSiteS i A := by
  ext σ' σ
  rw [onSiteS_mul_onSiteS_apply_of_ne hij,
      onSiteS_mul_onSiteS_apply_of_ne hij.symm]
  have hcond :
      (∀ k, k ≠ i → k ≠ j → σ' k = σ k) ↔
        (∀ k, k ≠ j → k ≠ i → σ' k = σ k) := by
    constructor <;> intro h k hki hkj <;> exact h k hkj hki
  split_ifs with h1 h2 h2
  · ring
  · exact absurd (hcond.mp h1) h2
  · exact absurd (hcond.mpr h2) h1
  · rfl

/-! ## Linearity of the site embedding -/

/-- `onSiteS` is additive in the operator argument. -/
theorem onSiteS_add (i : Λ) (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i (A + B) : ManyBodyOpS Λ N) = onSiteS i A + onSiteS i B := by
  ext σ' σ
  simp only [onSiteS_apply, Matrix.add_apply]
  by_cases h : ∀ k, k ≠ i → σ' k = σ k
  · simp [if_pos h]
  · simp [if_neg h]

/-- `onSiteS` takes subtraction of operators to subtraction of embeddings. -/
theorem onSiteS_sub (i : Λ) (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i (A - B) : ManyBodyOpS Λ N) = onSiteS i A - onSiteS i B := by
  ext σ' σ
  simp only [onSiteS_apply, Matrix.sub_apply]
  by_cases h : ∀ k, k ≠ i → σ' k = σ k
  · simp [if_pos h]
  · simp [if_neg h]

/-- `onSiteS i 0 = 0`. -/
theorem onSiteS_zero (i : Λ) :
    (onSiteS i (0 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
        ManyBodyOpS Λ N) = 0 := by
  ext σ' σ
  simp only [onSiteS_apply, Matrix.zero_apply]
  split_ifs <;> rfl

/-- `onSiteS i 1 = 1`: the site embedding of the `(N+1) × (N+1)`
identity is the many-body identity. -/
theorem onSiteS_one (i : Λ) :
    (onSiteS i (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
        ManyBodyOpS Λ N) = 1 := by
  ext σ' σ
  simp only [onSiteS_apply, Matrix.one_apply]
  by_cases heq : σ' = σ
  · subst heq
    simp
  · have : ¬ (∀ k, k ≠ i → σ' k = σ k) ∨ σ' i ≠ σ i := by
      by_contra hall
      push Not at hall
      obtain ⟨hoff, hi⟩ := hall
      apply heq
      funext k
      by_cases hki : k = i
      · subst hki; exact hi
      · exact hoff k hki
    rcases this with h | h
    · rw [if_neg h, if_neg heq]
    · by_cases hagree : ∀ k, k ≠ i → σ' k = σ k
      · rw [if_pos hagree, if_neg h, if_neg heq]
      · rw [if_neg hagree, if_neg heq]

/-- `onSiteS` commutes with scalar multiplication. -/
theorem onSiteS_smul (i : Λ) (c : ℂ)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i (c • A) : ManyBodyOpS Λ N) = c • onSiteS i A := by
  ext σ' σ
  simp only [onSiteS_apply, Matrix.smul_apply]
  by_cases h : ∀ k, k ≠ i → σ' k = σ k
  · simp [if_pos h]
  · simp [if_neg h]

/-! ## Same-site multiplication -/

private def fiberUpdateS {N : ℕ} (σ : Λ → Fin (N + 1)) (i : Λ)
    (t : Fin (N + 1)) : Λ → Fin (N + 1) :=
  Function.update σ i t

omit [Fintype Λ] in
private lemma fiberUpdateS_at (σ : Λ → Fin (N + 1)) (i : Λ)
    (t : Fin (N + 1)) :
    fiberUpdateS σ i t i = t := by
  rw [fiberUpdateS, Function.update_self]

omit [Fintype Λ] in
private lemma fiberUpdateS_off {σ : Λ → Fin (N + 1)} {i k : Λ}
    (hk : k ≠ i) (t : Fin (N + 1)) :
    fiberUpdateS σ i t k = σ k := by
  rw [fiberUpdateS, Function.update_of_ne hk]

/-- Same-site product reduces to the site embedding of the
`(N+1) × (N+1)` matrix product. -/
theorem onSiteS_mul_onSiteS_same (i : Λ)
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A * onSiteS i B : ManyBodyOpS Λ N) = onSiteS i (A * B) := by
  ext σ' σ
  rw [Matrix.mul_apply]
  simp only [onSiteS_apply]
  by_cases h : ∀ k, k ≠ i → σ' k = σ k
  · rw [if_pos h, Matrix.mul_apply]
    have hterm : ∀ τ : Λ → Fin (N + 1),
        (if ∀ k, k ≠ i → σ' k = τ k then A (σ' i) (τ i) else 0) *
            (if ∀ k, k ≠ i → τ k = σ k then B (τ i) (σ i) else 0) =
          if τ = fiberUpdateS σ i (τ i) then
            A (σ' i) (τ i) * B (τ i) (σ i)
          else 0 := by
      intro τ
      by_cases hτ : τ = fiberUpdateS σ i (τ i)
      · have hoff_σ : ∀ k, k ≠ i → τ k = σ k := by
          intro k hk
          have hstep : τ k = fiberUpdateS σ i (τ i) k := congrFun hτ k
          rw [hstep, fiberUpdateS_off hk]
        have hoff_σ' : ∀ k, k ≠ i → σ' k = τ k := fun k hk =>
          (h k hk).trans (hoff_σ k hk).symm
        rw [if_pos hoff_σ', if_pos hoff_σ, if_pos hτ]
      · have hnot : ¬ ∀ k, k ≠ i → τ k = σ k := by
          intro hall
          apply hτ
          funext k
          by_cases hki : k = i
          · subst hki; rw [fiberUpdateS_at]
          · rw [fiberUpdateS_off hki]; exact hall k hki
        rw [if_neg hnot, mul_zero, if_neg hτ]
    rw [Finset.sum_congr rfl (fun τ _ => hterm τ)]
    rw [← Finset.sum_filter]
    symm
    refine Finset.sum_bij (fun (t : Fin (N + 1)) _ => fiberUpdateS σ i t)
      ?memImage ?inj ?surj ?eq
    case memImage =>
      intro t _
      simp only
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      funext k
      by_cases hki : k = i
      · subst hki
        rw [fiberUpdateS_at, fiberUpdateS_at]
      · rw [fiberUpdateS_off hki, fiberUpdateS_off hki]
    case inj =>
      intros s _ u _ hsu
      simp only at hsu
      have := congrFun hsu i
      simpa [fiberUpdateS_at] using this
    case surj =>
      intros τ hτ
      rw [Finset.mem_filter] at hτ
      refine ⟨τ i, Finset.mem_univ _, ?_⟩
      simp only
      exact hτ.2.symm
    case eq =>
      intro t _
      simp only
      rw [fiberUpdateS_at]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro τ _
    by_cases h1 : ∀ k, k ≠ i → σ' k = τ k
    · have h2 : ¬ ∀ k, k ≠ i → τ k = σ k := by
        intro hh
        exact h (fun k hk => (h1 k hk).trans (hh k hk))
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

/-! ## Specialised site-embedded spin-`S` operators -/

/-- The site-`i` spin-`S` operator `Ŝ_i^{(1)}` on the many-body
Hilbert space `(Λ → Fin (N + 1)) → ℂ`. -/
noncomputable def spinSSiteOp1 (i : Λ) (N : ℕ) : ManyBodyOpS Λ N :=
  onSiteS i (spinSOp1 N)

/-- The site-`i` spin-`S` operator `Ŝ_i^{(2)}`. -/
noncomputable def spinSSiteOp2 (i : Λ) (N : ℕ) : ManyBodyOpS Λ N :=
  onSiteS i (spinSOp2 N)

/-- The site-`i` spin-`S` operator `Ŝ_i^{(3)}`. -/
noncomputable def spinSSiteOp3 (i : Λ) (N : ℕ) : ManyBodyOpS Λ N :=
  onSiteS i (spinSOp3 N)

/-- The site-`i` spin-`S` raising operator `Ŝ_i^+`. -/
noncomputable def spinSSiteOpPlus (i : Λ) (N : ℕ) : ManyBodyOpS Λ N :=
  onSiteS i (spinSOpPlus N)

/-- The site-`i` spin-`S` lowering operator `Ŝ_i^-`. -/
noncomputable def spinSSiteOpMinus (i : Λ) (N : ℕ) : ManyBodyOpS Λ N :=
  onSiteS i (spinSOpMinus N)

/-! ## Definitional unfoldings for site operators -/

/-- Definitional unfolding of `spinSSiteOp1`. -/
theorem spinSSiteOp1_def (i : Λ) (N : ℕ) :
    spinSSiteOp1 (Λ := Λ) i N = onSiteS i (spinSOp1 N) := rfl

/-- Definitional unfolding of `spinSSiteOp2`. -/
theorem spinSSiteOp2_def (i : Λ) (N : ℕ) :
    spinSSiteOp2 (Λ := Λ) i N = onSiteS i (spinSOp2 N) := rfl

/-- Definitional unfolding of `spinSSiteOp3`. -/
theorem spinSSiteOp3_def (i : Λ) (N : ℕ) :
    spinSSiteOp3 (Λ := Λ) i N = onSiteS i (spinSOp3 N) := rfl

/-- Definitional unfolding of `spinSSiteOpPlus`. -/
theorem spinSSiteOpPlus_def (i : Λ) (N : ℕ) :
    spinSSiteOpPlus (Λ := Λ) i N = onSiteS i (spinSOpPlus N) := rfl

/-- Definitional unfolding of `spinSSiteOpMinus`. -/
theorem spinSSiteOpMinus_def (i : Λ) (N : ℕ) :
    spinSSiteOpMinus (Λ := Λ) i N = onSiteS i (spinSOpMinus N) := rfl

/-! ## Computational basis vectors -/

/-- The standard basis vector at configuration `σ : Λ → Fin (N + 1)`:
the function that is `1` at `σ` and `0` elsewhere. Multi-site spin-`S`
generalisation of `basisVec` (`Quantum/ManyBody.lean`). -/
def basisVecS (σ : Λ → Fin (N + 1)) : (Λ → Fin (N + 1)) → ℂ :=
  fun τ => if τ = σ then 1 else 0

omit [DecidableEq Λ] in
/-- Definitional unfolding of `basisVecS`. -/
theorem basisVecS_def (σ : Λ → Fin (N + 1)) :
    basisVecS σ = (fun τ => if τ = σ then (1 : ℂ) else 0) := rfl

omit [DecidableEq Λ] in
/-- Explicit `if`-form of `basisVecS σ τ`. -/
theorem basisVecS_apply (σ τ : Λ → Fin (N + 1)) :
    basisVecS σ τ = if τ = σ then 1 else 0 := rfl

omit [DecidableEq Λ] in
/-- Diagonal value: `basisVecS σ σ = 1`. -/
@[simp]
theorem basisVecS_self (σ : Λ → Fin (N + 1)) : basisVecS σ σ = 1 := by
  unfold basisVecS; rw [if_pos rfl]

omit [DecidableEq Λ] in
/-- Off-diagonal: `basisVecS σ τ = 0` for `τ ≠ σ`. -/
theorem basisVecS_of_ne {σ τ : Λ → Fin (N + 1)} (hne : τ ≠ σ) :
    basisVecS σ τ = 0 := by
  unfold basisVecS; rw [if_neg hne]

/-- Same-site square: `(onSiteS i A) · (onSiteS i A) = onSiteS i (A * A)`. -/
theorem onSiteS_sq (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A : ManyBodyOpS Λ N) * onSiteS i A = onSiteS i (A * A) :=
  onSiteS_mul_onSiteS_same i A A

/-- Negation distributes over `onSiteS`: `onSiteS i (-A) = -(onSiteS i A)`. -/
theorem onSiteS_neg (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i (-A) : ManyBodyOpS Λ N) = -(onSiteS i A) := by
  rw [show (-A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) =
        (-1 : ℂ) • A from by rw [neg_smul, one_smul]]
  rw [onSiteS_smul]
  rw [show ((-1 : ℂ) • onSiteS (N := N) i A : ManyBodyOpS Λ N) =
        -onSiteS i A from by rw [neg_smul, one_smul]]

/-- Triple-product same-site identity:
`(onSiteS i A) · (onSiteS i A) · (onSiteS i A) = onSiteS i (A * A * A)`. -/
theorem onSiteS_cube (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A : ManyBodyOpS Λ N) * onSiteS i A * onSiteS i A =
      onSiteS i (A * A * A) := by
  rw [onSiteS_mul_onSiteS_same, onSiteS_mul_onSiteS_same]

/-- Power identity: `(onSiteS i A)^k = onSiteS i (A^k)`. -/
theorem onSiteS_pow (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (k : ℕ) :
    (onSiteS i A : ManyBodyOpS Λ N) ^ k = onSiteS i (A ^ k) := by
  induction k with
  | zero =>
    simp only [pow_zero]
    exact (onSiteS_one i).symm
  | succ k ih =>
    rw [pow_succ, ih, onSiteS_mul_onSiteS_same]
    rw [pow_succ]

/-- `onSiteS i 0 ^ k = 0` for `k > 0` (zero embedding stays zero
under repeated multiplication). Specialisation of `onSiteS_pow`. -/
theorem onSiteS_zero_pow (i : Λ) {k : ℕ} (hk : 0 < k) :
    (onSiteS i (0 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
        : ManyBodyOpS Λ N) ^ k = 0 := by
  rw [onSiteS_pow]
  rw [show (0 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) ^ k = 0 from
    zero_pow (Nat.pos_iff_ne_zero.mp hk)]
  exact onSiteS_zero i

/-- The site-embedded sum: `onSiteS i (∑ k, A k) = ∑ k, onSiteS i (A k)`. -/
theorem onSiteS_finset_sum {ι : Type*} (i : Λ) (s : Finset ι)
    (f : ι → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i (∑ k ∈ s, f k) : ManyBodyOpS Λ N) =
      ∑ k ∈ s, onSiteS i (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [onSiteS_zero]
  | @insert a t hat ih =>
    rw [Finset.sum_insert hat, Finset.sum_insert hat,
      onSiteS_add, ih]

/-- Convenience: `onSiteS i A = onSiteS i (A + 0)`. -/
theorem onSiteS_add_zero (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i (A + 0) : ManyBodyOpS Λ N) = onSiteS i A := by
  rw [add_zero]

/-- `onSiteS i A^0 = 1` (zero power gives the identity). -/
theorem onSiteS_pow_zero (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A : ManyBodyOpS Λ N) ^ 0 = 1 := by
  rw [onSiteS_pow]
  rw [pow_zero]
  exact onSiteS_one i

/-- `onSiteS i A ^ 1 = onSiteS i A`. -/
theorem onSiteS_pow_one (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A : ManyBodyOpS Λ N) ^ 1 = onSiteS i A := by
  rw [pow_one]

/-- `onSiteS i A ^ 2 = onSiteS i (A^2)`. -/
theorem onSiteS_pow_two (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A : ManyBodyOpS Λ N) ^ 2 = onSiteS i (A ^ 2) :=
  onSiteS_pow i A 2

/-- `onSiteS i A ^ 3 = onSiteS i (A^3)`. -/
theorem onSiteS_pow_three (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A : ManyBodyOpS Λ N) ^ 3 = onSiteS i (A ^ 3) :=
  onSiteS_pow i A 3

/-- `onSiteS i A ^ 4 = onSiteS i (A^4)`. -/
theorem onSiteS_pow_four (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A : ManyBodyOpS Λ N) ^ 4 = onSiteS i (A ^ 4) :=
  onSiteS_pow i A 4

/-- `onSiteS i A ^ 5 = onSiteS i (A^5)`. -/
theorem onSiteS_pow_five (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A : ManyBodyOpS Λ N) ^ 5 = onSiteS i (A ^ 5) :=
  onSiteS_pow i A 5

/-- `onSiteS i A` commutes with itself trivially. -/
theorem onSiteS_self_commute (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    Commute (onSiteS i A : ManyBodyOpS Λ N) (onSiteS i A) :=
  Commute.refl _

/-- Commute version of distinct-site commutativity. -/
theorem onSiteS_commute_of_ne {i j : Λ} (hij : i ≠ j)
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    Commute (onSiteS i A : ManyBodyOpS Λ N) (onSiteS j B) :=
  onSiteS_mul_onSiteS_of_ne hij A B

/-- The site-`i` zero embedding has every product with anything equal to zero. -/
theorem onSiteS_zero_mul (i : Λ) (B : ManyBodyOpS Λ N) :
    (onSiteS i (0 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) : ManyBodyOpS Λ N) * B = 0 := by
  rw [onSiteS_zero, zero_mul]

/-- The site-`i` smul embedding: `onSiteS i (c • A) = c • onSiteS i A`,
restated in matrix form (already proved in `onSiteS_smul`). -/
theorem onSiteS_smul_apply (i : Λ) (c : ℂ)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (σ' σ : Λ → Fin (N + 1)) :
    (onSiteS i (c • A) : ManyBodyOpS Λ N) σ' σ =
      c * (onSiteS i A : ManyBodyOpS Λ N) σ' σ := by
  rw [onSiteS_smul, Matrix.smul_apply, smul_eq_mul]

/-- The site-`i` add embedding entry-wise:
`(onSiteS i (A + B)) σ' σ = (onSiteS i A) σ' σ + (onSiteS i B) σ' σ`. -/
theorem onSiteS_add_apply (i : Λ)
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (σ' σ : Λ → Fin (N + 1)) :
    (onSiteS i (A + B) : ManyBodyOpS Λ N) σ' σ =
      (onSiteS i A : ManyBodyOpS Λ N) σ' σ +
      (onSiteS i B : ManyBodyOpS Λ N) σ' σ := by
  rw [onSiteS_add, Matrix.add_apply]

/-- The site-`i` sub embedding entry-wise. -/
theorem onSiteS_sub_apply (i : Λ)
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (σ' σ : Λ → Fin (N + 1)) :
    (onSiteS i (A - B) : ManyBodyOpS Λ N) σ' σ =
      (onSiteS i A : ManyBodyOpS Λ N) σ' σ -
      (onSiteS i B : ManyBodyOpS Λ N) σ' σ := by
  rw [onSiteS_sub, Matrix.sub_apply]

/-- The right multiplicative version: `B * onSiteS i 0 = 0`. -/
theorem mul_onSiteS_zero (i : Λ) (B : ManyBodyOpS Λ N) :
    B * (onSiteS i (0 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
        ManyBodyOpS Λ N) = 0 := by
  rw [onSiteS_zero, mul_zero]

/-- Applying `onSiteS i A` to a basis vector and reading the result
at configuration `τ` yields the matrix element `(onSiteS i A) τ σ`:
the basis-vector mulVec collapses to a single matrix entry. -/
theorem onSiteS_mulVec_basisVecS_apply
    (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (σ τ : Λ → Fin (N + 1)) :
    (onSiteS i A : ManyBodyOpS Λ N).mulVec (basisVecS σ) τ =
      (onSiteS i A : ManyBodyOpS Λ N) τ σ := by
  classical
  change ∑ σ' : Λ → Fin (N + 1), (onSiteS i A) τ σ' * basisVecS σ σ' =
        (onSiteS i A) τ σ
  simp_rw [basisVecS_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ σ (fun σ' => (onSiteS i A) τ σ')]
  simp

/-- For distinct sites `x ≠ y`, the product
`onSiteS x (Ŝ^+) * onSiteS y (Ŝ^-)` has non-negative real-part
matrix element on every `(σ', σ)` pair. -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_re_nonneg
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    0 ≤ ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)
          : ManyBodyOpS Λ N) σ' σ).re := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy]
  by_cases h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k
  · rw [if_pos h]
    exact spinSOpPlus_mul_spinSOpMinus_re_nonneg N (σ' x) (σ x) (σ' y) (σ y)
  · rw [if_neg h]; simp

/-- Symmetric: `onSiteS x (Ŝ^-) * onSiteS y (Ŝ^+)` has non-negative
real-part matrix element on every `(σ', σ)` pair. -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_re_nonneg
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    0 ≤ ((onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)
          : ManyBodyOpS Λ N) σ' σ).re := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy]
  by_cases h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k
  · rw [if_pos h]
    exact spinSOpMinus_mul_spinSOpPlus_re_nonneg N (σ' x) (σ x) (σ' y) (σ y)
  · rw [if_neg h]; simp

/-- For distinct sites `x ≠ y`, the product
`onSiteS x (Ŝ^+) * onSiteS y (Ŝ^-)` has zero imaginary part on every
`(σ', σ)` pair. -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_im_zero
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)
          : ManyBodyOpS Λ N) σ' σ).im = 0 := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy]
  by_cases h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k
  · rw [if_pos h]
    rw [Complex.mul_im]
    rw [spinSOpPlus_apply_im_zero, spinSOpMinus_apply_im_zero]
    ring
  · rw [if_neg h]; simp

/-- Symmetric: `onSiteS x (Ŝ^-) * onSiteS y (Ŝ^+)` has zero imaginary
part on every `(σ', σ)` pair. -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_im_zero
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    ((onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)
          : ManyBodyOpS Λ N) σ' σ).im = 0 := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy]
  by_cases h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k
  · rw [if_pos h]
    rw [Complex.mul_im]
    rw [spinSOpMinus_apply_im_zero, spinSOpPlus_apply_im_zero]
    ring
  · rw [if_neg h]; simp


/-- For distinct sites `x ≠ y`, the **sum** `(S+_x S-_y) + (S-_x S+_y)`
matrix element has non-negative real part on every `(σ', σ)` pair. -/
theorem onSiteS_spinSOpPlus_Minus_plus_Minus_Plus_re_nonneg
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    0 ≤ ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) +
          onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)
          : ManyBodyOpS Λ N) σ' σ).re := by
  rw [Matrix.add_apply, Complex.add_re]
  have h1 := onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_re_nonneg hxy σ' σ
  have h2 := onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_re_nonneg hxy σ' σ
  linarith

/-- For distinct sites `x ≠ y`, the product `S^3_x ⊗ S^3_y` matrix
element has zero imaginary part. -/
theorem onSiteS_spinSOp3_mul_onSiteS_spinSOp3_im_zero
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    ((onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)
          : ManyBodyOpS Λ N) σ' σ).im = 0 := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy]
  by_cases h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k
  · rw [if_pos h]
    rw [Complex.mul_im]
    rw [spinSOp3_apply_im_zero, spinSOp3_apply_im_zero]
    ring
  · rw [if_neg h]; simp

/-- For distinct sites `x ≠ y`, the product `onSiteS x (S^3) * onSiteS y (S^3)`
preserves real entries. -/
theorem onSiteS_spinSOp3_mul_onSiteS_spinSOp3_eq_ofReal_re
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)
          : ManyBodyOpS Λ N) σ' σ =
      ((((onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)
          : ManyBodyOpS Λ N) σ' σ).re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
  · rw [Complex.ofReal_im]
    exact onSiteS_spinSOp3_mul_onSiteS_spinSOp3_im_zero hxy σ' σ

/-- For distinct sites `x ≠ y`, the product `S+_x ⊗ S-_y` matrix
element equals its real-part embedding. -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_eq_ofReal_re
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)
          : ManyBodyOpS Λ N) σ' σ =
      ((((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)
          : ManyBodyOpS Λ N) σ' σ).re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
  · rw [Complex.ofReal_im]
    exact onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_im_zero hxy σ' σ

/-- For distinct sites `x ≠ y`, the product `S-_x ⊗ S+_y` matrix
element equals its real-part embedding. -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_eq_ofReal_re
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    (onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)
          : ManyBodyOpS Λ N) σ' σ =
      ((((onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)
          : ManyBodyOpS Λ N) σ' σ).re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
  · rw [Complex.ofReal_im]
    exact onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_im_zero hxy σ' σ

/-- For distinct sites `x ≠ y`, when configurations agree at every
site other than `x` and `y`, the matrix element of `S^3_x S^3_y`
factors into the per-site `S^3` entries. -/
theorem onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_of_off_two_site_agree
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)
          : ManyBodyOpS Λ N) σ' σ =
      spinSOp3 N (σ' x) (σ x) * spinSOp3 N (σ' y) (σ y) := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy, if_pos h]

/-- Same factor formula for `S^+_x ⊗ S^-_y`. -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)
          : ManyBodyOpS Λ N) σ' σ =
      spinSOpPlus N (σ' x) (σ x) * spinSOpMinus N (σ' y) (σ y) := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy, if_pos h]

/-- Same factor formula for `S^-_x ⊗ S^+_y`. -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_of_off_two_site_agree
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)
          : ManyBodyOpS Λ N) σ' σ =
      spinSOpMinus N (σ' x) (σ x) * spinSOpPlus N (σ' y) (σ y) := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy, if_pos h]

/-- For distinct sites `x ≠ y` and configurations differing on at
least one of `{x, y}^c`, the `S+_x ⊗ S-_y` matrix element vanishes. -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_eq_zero_of_off_two_site_diff
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (h : ¬ ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)
          : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy, if_neg h]

/-- Same for `S-_x ⊗ S+_y`. -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_eq_zero_of_off_two_site_diff
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (h : ¬ ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)
          : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy, if_neg h]

/-- Vanishing with witness difference site: if `z ∉ {x, y}` and
`σ' z ≠ σ z`, the product `onSiteS x A * onSiteS y B` vanishes at
`(σ', σ)`. -/
theorem onSiteS_mul_onSiteS_apply_eq_zero_of_diff_outside_pair
    {x y : Λ} (hxy : x ≠ y)
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    {σ' σ : Λ → Fin (N + 1)}
    {z : Λ} (hzx : z ≠ x) (hzy : z ≠ y) (hz : σ' z ≠ σ z) :
    (onSiteS x A * onSiteS y B : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy]
  rw [if_neg]
  intro hagree
  exact hz (hagree z hzx hzy)

/-- Same for `S^3_x ⊗ S^3_y`. -/
theorem onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_eq_zero_of_diff_outside_pair
    {x y : Λ} (hxy : x ≠ y)
    {σ' σ : Λ → Fin (N + 1)}
    {z : Λ} (hzx : z ≠ x) (hzy : z ≠ y) (hz : σ' z ≠ σ z) :
    (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)
          : ManyBodyOpS Λ N) σ' σ = 0 :=
  onSiteS_mul_onSiteS_apply_eq_zero_of_diff_outside_pair hxy _ _ hzx hzy hz

/-- Same for `S+_x ⊗ S-_y`. -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_eq_zero_of_diff_outside_pair
    {x y : Λ} (hxy : x ≠ y)
    {σ' σ : Λ → Fin (N + 1)}
    {z : Λ} (hzx : z ≠ x) (hzy : z ≠ y) (hz : σ' z ≠ σ z) :
    (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)
          : ManyBodyOpS Λ N) σ' σ = 0 :=
  onSiteS_mul_onSiteS_apply_eq_zero_of_diff_outside_pair hxy _ _ hzx hzy hz

/-- Same for `S-_x ⊗ S+_y`. -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_eq_zero_of_diff_outside_pair
    {x y : Λ} (hxy : x ≠ y)
    {σ' σ : Λ → Fin (N + 1)}
    {z : Λ} (hzx : z ≠ x) (hzy : z ≠ y) (hz : σ' z ≠ σ z) :
    (onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)
          : ManyBodyOpS Λ N) σ' σ = 0 :=
  onSiteS_mul_onSiteS_apply_eq_zero_of_diff_outside_pair hxy _ _ hzx hzy hz

/-! ## `(S^3 ⊗ S^3)` matrix element formulas -/

/-- For `x ≠ y`, when `σ' = σ`, the `S^3_x ⊗ S^3_y` matrix element
factors into the per-site `S^3` diagonal entries:
`(N/2 - σ_x.val) * (N/2 - σ_y.val)`. -/
theorem onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_diag
    {x y : Λ} (hxy : x ≠ y) (σ : Λ → Fin (N + 1)) :
    (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)
          : ManyBodyOpS Λ N) σ σ =
      ((N : ℂ) / 2 - (σ x).val) * ((N : ℂ) / 2 - (σ y).val) := by
  rw [onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_of_off_two_site_agree hxy
    (fun _ _ _ => rfl)]
  rw [spinSOp3_apply_diag, spinSOp3_apply_diag]

/-- For `x ≠ y` and `σ' σ` agreeing off `{x, y}` with `σ' x ≠ σ x`,
the `S^3_x ⊗ S^3_y` matrix element vanishes (`S^3` is diagonal). -/
theorem onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_eq_zero_of_off_diag_at_x
    {x y : Λ} (hxy : x ≠ y)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) (hσx : σ' x ≠ σ x) :
    (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)
          : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_of_off_two_site_agree hxy h]
  rw [show spinSOp3 N (σ' x) (σ x) = 0 from
    Matrix.diagonal_apply_ne _ hσx]
  ring

/-- Symmetric: vanishes if `σ' y ≠ σ y`. -/
theorem onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_eq_zero_of_off_diag_at_y
    {x y : Λ} (hxy : x ≠ y)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) (hσy : σ' y ≠ σ y) :
    (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)
          : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_of_off_two_site_agree hxy h]
  rw [show spinSOp3 N (σ' y) (σ y) = 0 from
    Matrix.diagonal_apply_ne _ hσy]
  ring

/-- For `x ≠ y` and `σ', σ` agreeing off `{x, y}` with `σ_x = σ'_x + 1`
("S+ raises k=σ from σ' = σ - 1"), the `S-_x ⊗ S+_y` matrix element
vanishes (wrong direction at site `x`). -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_eq_zero_of_raising_x
    {x y : Λ} (hxy : x ≠ y)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ' x).val + 1 = (σ x).val) :
    (onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)
          : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy, if_pos h]
  rw [show spinSOpMinus N (σ' x) (σ x) = 0 from
    spinSOpMinus_apply_other N (by omega)]
  ring

/-- For `x ≠ y` and `σ', σ` agreeing off `{x, y}` with
`σ'_x = σ_x + 1` ("S- lowers k=σ to σ' = σ + 1"), the `S+_x ⊗ S-_y`
matrix element vanishes (wrong direction at site `x`). -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_eq_zero_of_lowering_x
    {x y : Λ} (hxy : x ≠ y)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ x).val + 1 = (σ' x).val) :
    (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)
          : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy, if_pos h]
  rw [show spinSOpPlus N (σ' x) (σ x) = 0 from
    spinSOpPlus_apply_other N (by omega)]
  ring

/-- For any matrix `M` and basis vector `|σ⟩ = basisVecS σ`:
`<σ | M | σ> = M σ σ`. The expectation value of a matrix on a basis vector
equals its diagonal element at that basis. -/
theorem basisVecS_expectation_eq_diagonal
    (σ : Λ → Fin (N + 1)) (M : ManyBodyOpS Λ N) :
    dotProduct (star (basisVecS σ : (Λ → Fin (N + 1)) → ℂ))
        (M.mulVec (basisVecS σ)) = M σ σ := by
  unfold dotProduct
  rw [Finset.sum_eq_single σ]
  · simp only [Pi.star_apply, basisVecS_self, star_one, one_mul]
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single σ]
    · rw [basisVecS_self, mul_one]
    · intros τ _ hτne
      rw [basisVecS_of_ne hτne]
      simp
    · intro h
      exact (h (Finset.mem_univ _)).elim
  · intros τ _ hτne
    simp [basisVecS_of_ne hτne]
  · intro h
    exact (h (Finset.mem_univ _)).elim

end LatticeSystem.Quantum
