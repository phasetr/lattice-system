import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonian
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Transporting single-cluster Hamiltonians along site equivalences

This file adds the reindexing bridge needed for Tasaki §2.5 Problem 2.5.b:
the abstract single-cluster Hamiltonian on `Fin (z + 1)` can be transported
along any equivalence of site types, and the transported matrix is the sum of
the corresponding transported two-site dot products.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
  §2.5 Problem 2.5.b, p. 38, solution p. 497.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {α β : Type*}

/-! ## Configuration equivalences induced by site equivalences -/

/-- The equivalence on configuration spaces induced by an equivalence of site
types.  A configuration on `α` is transported to a configuration on `β` by
precomposing with `e.symm`. -/
def siteConfigEquiv (e : α ≃ β) (N : ℕ) :
    (α → Fin (N + 1)) ≃ (β → Fin (N + 1)) where
  toFun σ := fun b => σ (e.symm b)
  invFun τ := fun a => τ (e a)
  left_inv σ := by
    funext a
    simp
  right_inv τ := by
    funext b
    simp

/-- Evaluation of the transported configuration equivalence. -/
@[simp] theorem siteConfigEquiv_apply (e : α ≃ β) (N : ℕ)
    (σ : α → Fin (N + 1)) (b : β) :
    siteConfigEquiv e N σ b = σ (e.symm b) := rfl

/-- Evaluation of the inverse transported configuration equivalence. -/
@[simp] theorem siteConfigEquiv_symm_apply (e : α ≃ β) (N : ℕ)
    (τ : β → Fin (N + 1)) (a : α) :
    (siteConfigEquiv e N).symm τ a = τ (e a) := rfl

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-! ## Transport of local spin operators -/

/-- Reindexing a site-embedded spin-`S` operator along a site equivalence sends
the site label through that equivalence. -/
theorem reindex_onSiteS_siteEquiv (e : α ≃ β) (a : α) (N : ℕ)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (Matrix.reindex (siteConfigEquiv e N) (siteConfigEquiv e N)
        (onSiteS a A : ManyBodyOpS α N) : ManyBodyOpS β N) =
      onSiteS (e a) A := by
  ext σ' σ
  rw [Matrix.reindex_apply]
  simp only [Matrix.submatrix_apply, siteConfigEquiv_symm_apply, onSiteS_apply]
  have hiff :
      (∀ k : α, k ≠ a → σ' (e k) = σ (e k)) ↔
        (∀ k : β, k ≠ e a → σ' k = σ k) := by
    constructor
    · intro h k hk
      simpa using h (e.symm k) (by
        intro hs
        apply hk
        rw [← hs]
        simp)
    · intro h k hk
      exact h (e k) (by
        intro hEq
        exact hk (e.injective hEq))
  by_cases h : ∀ k : α, k ≠ a → σ' (e k) = σ (e k)
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (mt hiff.mpr h)]

/-- Reindexing a two-site spin dot product along a site equivalence sends both
site labels through that equivalence. -/
theorem reindex_spinSDot_siteEquiv (e : α ≃ β) (a b : α) (N : ℕ) :
    (Matrix.reindex (siteConfigEquiv e N) (siteConfigEquiv e N)
        (spinSDot a b N : ManyBodyOpS α N) : ManyBodyOpS β N) =
      spinSDot (e a) (e b) N := by
  change Matrix.reindexAlgEquiv ℂ ℂ (siteConfigEquiv e N)
        (spinSDot a b N : ManyBodyOpS α N) = spinSDot (e a) (e b) N
  rw [spinSDot_def, spinSDot_def]
  simp only [map_add, map_mul, Matrix.reindexAlgEquiv_apply]
  rw [reindex_onSiteS_siteEquiv e a N (spinSOp1 N),
    reindex_onSiteS_siteEquiv e b N (spinSOp1 N),
    reindex_onSiteS_siteEquiv e a N (spinSOp2 N),
    reindex_onSiteS_siteEquiv e b N (spinSOp2 N),
    reindex_onSiteS_siteEquiv e a N (spinSOp3 N),
    reindex_onSiteS_siteEquiv e b N (spinSOp3 N)]

/-! ## Transported single-cluster Hamiltonians -/

/-- The single-cluster Hamiltonian transported along a site equivalence
`Fin (z + 1) ≃ β`. -/
noncomputable def transportedSingleClusterHamiltonianS (z N : ℕ)
    (e : Fin (z + 1) ≃ β) : ManyBodyOpS β N :=
  Matrix.reindex (siteConfigEquiv e N) (siteConfigEquiv e N)
    (singleClusterHamiltonianS z N : ManyBodyOpS (Fin (z + 1)) N)

/-- The transported single-cluster Hamiltonian is the sum of transported
center-leaf dot products. -/
theorem transportedSingleClusterHamiltonianS_eq_sum (z N : ℕ)
    (e : Fin (z + 1) ≃ β) :
    transportedSingleClusterHamiltonianS z N e =
      ∑ j ∈ (Finset.univ : Finset (Fin (z + 1))).erase 0,
        spinSDot (e 0) (e j) N := by
  unfold transportedSingleClusterHamiltonianS singleClusterHamiltonianS
  change Matrix.reindexAlgEquiv ℂ ℂ (siteConfigEquiv e N)
        (∑ j ∈ (Finset.univ : Finset (Fin (z + 1))).erase 0,
          spinSDot 0 j N : ManyBodyOpS (Fin (z + 1)) N) =
      ∑ j ∈ (Finset.univ : Finset (Fin (z + 1))).erase 0,
        spinSDot (e 0) (e j) N
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Matrix.reindexAlgEquiv_apply, reindex_spinSDot_siteEquiv e 0 j N]

/-! ## Canonical option-star transport -/

/-- The center-plus-leaves Hamiltonian on `Option s`, with center `none` and
leaves `some y` for `y : s`. -/
noncomputable def optionClusterHamiltonianS {α : Type*} [DecidableEq α]
    (s : Finset α) (N : ℕ) : ManyBodyOpS (Option s) N :=
  ∑ y : s, spinSDot none (some y) N

/-- The canonical equivalence from `Fin (s.card + 1)` to `Option s`: zero maps
to the center `none`, and successors enumerate the leaves using
`Finset.equivFin`. -/
noncomputable def singleClusterOptionEquiv {α : Type*} (s : Finset α) :
    Fin (s.card + 1) ≃ Option s :=
  (finSuccEquiv s.card).trans (Equiv.optionCongr (Finset.equivFin s).symm)

/-- The finite sum over nonzero `Fin (n + 1)` sites is the sum over successor
indices. -/
theorem sum_fin_erase_zero_eq_sum_succ {M : Type*} [AddCancelCommMonoid M]
    {n : ℕ} (f : Fin (n + 1) → M) :
    ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase 0, f j =
      ∑ j : Fin n, f j.succ := by
  have htotal : (∑ j : Fin (n + 1), f j) =
      f 0 + ∑ j : Fin n, f j.succ := Fin.sum_univ_succ f
  have herase0 :
      ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase 0, f j + f 0 =
        ∑ j : Fin (n + 1), f j := by
    exact Finset.sum_erase_add (Finset.univ : Finset (Fin (n + 1))) f (Finset.mem_univ 0)
  have herase : (∑ j : Fin (n + 1), f j) =
      f 0 + ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase 0, f j := by
    rw [← herase0, add_comm]
  have h : f 0 + ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase 0, f j =
      f 0 + ∑ j : Fin n, f j.succ := by
    rw [← herase, htotal]
  exact add_left_cancel h

/-- Transporting the abstract single-cluster Hamiltonian by the canonical
`Fin (s.card + 1) ≃ Option s` equivalence gives the option-star Hamiltonian. -/
theorem transportedSingleClusterHamiltonianS_option_eq {α : Type*} [DecidableEq α]
    (s : Finset α) (N : ℕ) :
    transportedSingleClusterHamiltonianS s.card N (singleClusterOptionEquiv s) =
      optionClusterHamiltonianS s N := by
  rw [transportedSingleClusterHamiltonianS_eq_sum]
  unfold optionClusterHamiltonianS singleClusterOptionEquiv
  rw [sum_fin_erase_zero_eq_sum_succ]
  have hsum := Equiv.sum_comp (Finset.equivFin s).symm
      (fun y : s => spinSDot (none : Option s) (some y) N)
  simpa [finSuccEquiv_zero, finSuccEquiv_symm_some] using hsum

end LatticeSystem.Quantum
