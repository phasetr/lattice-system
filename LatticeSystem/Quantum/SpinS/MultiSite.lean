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

/-- The site-embedded operator `onSiteS i A` acts as `A` on site `i`
and as the identity on every other site. Its matrix element is
`A (σ' i) (σ i)` when `σ'` and `σ` agree at every site other than
`i`, and `0` otherwise. -/
def onSiteS (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    ManyBodyOpS Λ N :=
  fun σ' σ =>
    if (∀ k, k ≠ i → σ' k = σ k) then A (σ' i) (σ i) else 0

/-- Unfolding the matrix element of `onSiteS i A`. -/
theorem onSiteS_apply (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (σ' σ : Λ → Fin (N + 1)) :
    onSiteS i A σ' σ =
      if (∀ k, k ≠ i → σ' k = σ k) then A (σ' i) (σ i) else 0 := rfl

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

end LatticeSystem.Quantum
