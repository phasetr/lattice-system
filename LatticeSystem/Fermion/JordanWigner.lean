/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.ManyBody
import LatticeSystem.Quantum.Pauli
import LatticeSystem.Quantum.SpinHalfBasis
import LatticeSystem.Fermion.Mode

/-!
# Multi-mode fermion via Jordan–Wigner mapping

This module lifts the single-mode CAR algebra (see
`LatticeSystem/Fermion/Mode.lean`) to a multi-mode fermion system on
the linearly-ordered lattice `Λ = Fin (N + 1)` via the Jordan–Wigner
mapping.

## Conventions

The Hilbert space is the spin-1/2 many-body space
`ManyBodyOp (Fin (N + 1)) = Matrix (Fin (N + 1) → Fin 2) (...) ℂ`,
with the convention from `Fermion/Mode.lean`:
`|0⟩` (vacuum) on each site corresponds to spin-up,
`|1⟩` (occupied) to spin-down.

## Definitions

The Jordan–Wigner string at site `i` is

```
jwString N i = ∏_{j : Fin (N+1), j.val < i.val} σ^z_j
```

and the multi-mode fermion operators are

```
c_i  = jwString N i · σ^+_i
c_i† = jwString N i · σ^-_i
```

The string makes the otherwise-bosonic spin raising / lowering
operators anticommute across distinct sites, giving the correct
fermion statistics.

## Results

* `jwString_zero` — `jwString N 0 = 1` (empty product at the leftmost
  site).
* `fermionMultiAnnihilation_zero`, `fermionMultiCreation_zero` —
  `c_0 = σ^+_0`, `c_0† = σ^-_0` (no JW string at the leftmost site).
* `jwString_commute_onSite` — `[jwString N i, onSite i A] = 0` for
  any `A`.
* `fermionMultiAnnihilation_sq` — `c_i² = 0` (Pauli exclusion).
* `fermionMultiCreation_sq` — `(c_i†)² = 0`.

The cross-site anticommutation relations
`{c_i, c_j†} = δ_ij` and `{c_i, c_j} = 0` for `i ≠ j` are deferred
to follow-up PRs (they require sign-cancellation tracking through
the JW string acting on intermediate sites).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-! ## Jordan–Wigner string -/

/-- The Jordan–Wigner string at site `i` on a chain of `N + 1` sites:
the product `∏_{j.val < i.val} σ^z_j` of `σ^z` operators on all
sites strictly to the left of `i`.

Uses `Finset.noncommProd` because `ManyBodyOp` is a non-commutative
ring. The pairwise-commutativity certificate comes from
`onSite_mul_onSite_of_ne` (different-site `σ^z` operators commute). -/
noncomputable def jwString (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (N + 1)) :=
  ((Finset.univ.filter fun j : Fin (N + 1) => j.val < i.val)).noncommProd
    (fun j => onSite j pauliZ)
    (fun _ _ _ _ hab => onSite_mul_onSite_of_ne hab pauliZ pauliZ)

/-- The Jordan–Wigner string at site `0` is the identity (empty
product, since no `j` satisfies `j.val < 0`). -/
theorem jwString_zero (N : ℕ) :
    jwString N (0 : Fin (N + 1)) = 1 := by
  unfold jwString
  simp

/-! ## Multi-mode creation and annihilation operators -/

/-- The multi-mode fermion annihilation operator at site `i`:
`c_i = jwString_i · σ^+_i`. -/
noncomputable def fermionMultiAnnihilation (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (N + 1)) :=
  jwString N i * onSite i spinHalfOpPlus

/-- The multi-mode fermion creation operator at site `i`:
`c_i† = jwString_i · σ^-_i`. -/
noncomputable def fermionMultiCreation (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (N + 1)) :=
  jwString N i * onSite i spinHalfOpMinus

/-- At site `0` the JW string is the identity, so `c_0 = σ^+_0`. -/
theorem fermionMultiAnnihilation_zero (N : ℕ) :
    fermionMultiAnnihilation N (0 : Fin (N + 1))
      = onSite (0 : Fin (N + 1)) spinHalfOpPlus := by
  unfold fermionMultiAnnihilation
  rw [jwString_zero, Matrix.one_mul]

/-- At site `0` the JW string is the identity, so `c_0† = σ^-_0`. -/
theorem fermionMultiCreation_zero (N : ℕ) :
    fermionMultiCreation N (0 : Fin (N + 1))
      = onSite (0 : Fin (N + 1)) spinHalfOpMinus := by
  unfold fermionMultiCreation
  rw [jwString_zero, Matrix.one_mul]

/-! ## On-site CAR vanishing -/

/-- The Jordan–Wigner string at site `i` commutes with any single-site
operator at site `i`: the string lives on sites strictly less than
`i`, so each factor `σ^z_j` (for `j.val < i.val`, hence `j ≠ i`)
commutes with the site-`i` operator via `onSite_mul_onSite_of_ne`. -/
theorem jwString_commute_onSite (N : ℕ) (i : Fin (N + 1))
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Commute (jwString N i) (onSite i A) := by
  unfold jwString
  apply Commute.symm
  apply Finset.noncommProd_commute
  intro j hj
  rw [Finset.mem_filter] at hj
  exact onSite_mul_onSite_of_ne (Fin.ne_of_val_ne (Nat.ne_of_lt hj.2).symm) A pauliZ

/-- `c_i² = 0`: cannot annihilate the same fermion mode twice
(Pauli exclusion at a single mode). -/
theorem fermionMultiAnnihilation_sq (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiAnnihilation N i * fermionMultiAnnihilation N i = 0 := by
  unfold fermionMultiAnnihilation
  have hcomm : Commute (onSite i spinHalfOpPlus) (jwString N i) :=
    (jwString_commute_onSite N i spinHalfOpPlus).symm
  rw [show jwString N i * onSite i spinHalfOpPlus *
          (jwString N i * onSite i spinHalfOpPlus)
        = jwString N i * jwString N i *
          (onSite i spinHalfOpPlus * onSite i spinHalfOpPlus) by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (onSite i spinHalfOpPlus),
          hcomm.eq, Matrix.mul_assoc, Matrix.mul_assoc]]
  rw [onSite_mul_onSite_same]
  have h_sq : spinHalfOpPlus * spinHalfOpPlus = (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
    unfold spinHalfOpPlus
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [h_sq]
  have h_zero : onSite i (0 : Matrix (Fin 2) (Fin 2) ℂ)
              = (0 : ManyBodyOp (Fin (N + 1))) := by
    ext σ' σ
    simp [onSite_apply]
  rw [h_zero, Matrix.mul_zero]

/-- `(c_i†)² = 0`: cannot create the same fermion mode twice. -/
theorem fermionMultiCreation_sq (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiCreation N i * fermionMultiCreation N i = 0 := by
  unfold fermionMultiCreation
  have hcomm : Commute (onSite i spinHalfOpMinus) (jwString N i) :=
    (jwString_commute_onSite N i spinHalfOpMinus).symm
  rw [show jwString N i * onSite i spinHalfOpMinus *
          (jwString N i * onSite i spinHalfOpMinus)
        = jwString N i * jwString N i *
          (onSite i spinHalfOpMinus * onSite i spinHalfOpMinus) by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (onSite i spinHalfOpMinus),
          hcomm.eq, Matrix.mul_assoc, Matrix.mul_assoc]]
  rw [onSite_mul_onSite_same]
  have h_sq : spinHalfOpMinus * spinHalfOpMinus = (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
    unfold spinHalfOpMinus
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [h_sq]
  have h_zero : onSite i (0 : Matrix (Fin 2) (Fin 2) ℂ)
              = (0 : ManyBodyOp (Fin (N + 1))) := by
    ext σ' σ
    simp [onSite_apply]
  rw [h_zero, Matrix.mul_zero]

end LatticeSystem.Fermion
