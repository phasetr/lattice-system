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


end LatticeSystem.Quantum
