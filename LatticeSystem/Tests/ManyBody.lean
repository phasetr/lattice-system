/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.ManyBody

/-!
# Test coverage for many-body basis-vector orthonormality

Foundational `basisVec` lemmas: `_apply`, `_self`, `_of_ne`,
`sum_mul_basisVec`, `basisVec_sum_mul`, `basisVec_inner`.
-/

namespace LatticeSystem.Tests.ManyBody

open LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## `basisVec_apply` -/

example (σ τ : Λ → Fin 2) :
    basisVec σ τ = if τ = σ then 1 else 0 :=
  basisVec_apply σ τ

/-! ## `basisVec_self` -/

example (σ : Λ → Fin 2) : basisVec σ σ = 1 := basisVec_self σ

example : basisVec (fun _ : Fin 2 => (0 : Fin 2))
    (fun _ : Fin 2 => (0 : Fin 2)) = 1 := by simp

/-! ## `basisVec_of_ne` -/

example {σ τ : Λ → Fin 2} (h : τ ≠ σ) : basisVec σ τ = 0 :=
  basisVec_of_ne h

/-! ## Selector sums -/

example (σ : Λ → Fin 2) (f : (Λ → Fin 2) → ℂ) :
    ∑ τ : Λ → Fin 2, f τ * basisVec σ τ = f σ :=
  sum_mul_basisVec σ f

example (σ : Λ → Fin 2) (f : (Λ → Fin 2) → ℂ) :
    ∑ τ : Λ → Fin 2, basisVec σ τ * f τ = f σ :=
  basisVec_sum_mul σ f

/-! ## `basisVec_inner` orthonormality -/

example (σ ρ : Λ → Fin 2) :
    ∑ τ : Λ → Fin 2, basisVec σ τ * basisVec ρ τ =
      if ρ = σ then 1 else 0 :=
  basisVec_inner σ ρ

example (σ : Λ → Fin 2) :
    ∑ τ : Λ → Fin 2, basisVec σ τ * basisVec σ τ = 1 := by
  rw [basisVec_inner]; simp

/-! ## A. decide-based universal: `Fin 2 → Fin 2` exhaustive (Phase
1 PR 14 strengthening, refactor plan v4 §2.1 method A) -/

/-- Self-equality on `Fin 2 → Fin 2` configurations: `basisVec σ σ
= 1` for every σ (universally over the 4 configurations). -/
example : ∀ σ : Fin 2 → Fin 2, basisVec σ σ = (1 : ℂ) := by
  intro σ; exact basisVec_self σ

end LatticeSystem.Tests.ManyBody
