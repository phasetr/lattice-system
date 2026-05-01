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
