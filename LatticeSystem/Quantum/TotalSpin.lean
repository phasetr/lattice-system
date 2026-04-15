/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinHalf
import LatticeSystem.Quantum.ManyBody

/-!
# Total spin operator (Tasaki §2.2)

Formalizes Tasaki *Physics and Mathematics of Quantum Many-Body Systems*,
§2.2, eq. (2.2.7) for the `S = 1/2` case: the total spin operator is the
sum of site-embedded single-spin operators,

```
Ŝ_tot^(α) := Σ_{x ∈ Λ} Ŝ_x^(α) = Σ_{x ∈ Λ} onSite x Ŝ^(α).
```

We prove Hermiticity of each axis component. The distinct-site
commutation `[Ŝ_x^(α), Ŝ_y^(β)] = 0` for `x ≠ y` — the S = 1/2 case of
Tasaki eq. (2.2.6) — is already available via `onSite_mul_onSite_of_ne`.

Specific topics deferred to later work include the global rotation
operator `Û^(α)_θ = exp(-iθ Ŝ_tot^(α))` (eq. (2.2.11)), the SU(2) /
U(1) invariance characterization (eqs. (2.2.12), (2.2.13)), and the
two-site dot product `Ŝ_x · Ŝ_y` (eqs. (2.2.16) onward).
-/

namespace LatticeSystem.Quantum

open Matrix

variable (Λ : Type*) [Fintype Λ] [DecidableEq Λ]

/-- Total spin operator in the 1-axis: `Ŝ_tot^(1) := Σ_{x ∈ Λ} Ŝ_x^(1)`. -/
noncomputable def totalSpinHalfOp1 : ManyBodyOp Λ :=
  ∑ x : Λ, onSite x spinHalfOp1

/-- Total spin operator in the 2-axis. -/
noncomputable def totalSpinHalfOp2 : ManyBodyOp Λ :=
  ∑ x : Λ, onSite x spinHalfOp2

/-- Total spin operator in the 3-axis. -/
noncomputable def totalSpinHalfOp3 : ManyBodyOp Λ :=
  ∑ x : Λ, onSite x spinHalfOp3

/-! ## Hermiticity -/

private lemma isHermitian_sum {ι : Type*} {n : Type*}
    (s : Finset ι) {f : ι → Matrix n n ℂ} (hf : ∀ i ∈ s, (f i).IsHermitian) :
    (∑ i ∈ s, f i).IsHermitian := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.IsHermitian]
  | @insert a t hns ih =>
    rw [Finset.sum_insert hns]
    refine Matrix.IsHermitian.add (hf a (Finset.mem_insert_self a t)) ?_
    exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- `Ŝ_tot^(1)` is Hermitian. -/
theorem totalSpinHalfOp1_isHermitian : (totalSpinHalfOp1 Λ).IsHermitian := by
  unfold totalSpinHalfOp1
  exact isHermitian_sum Finset.univ
    (fun x _ => onSite_isHermitian x spinHalfOp1_isHermitian)

/-- `Ŝ_tot^(2)` is Hermitian. -/
theorem totalSpinHalfOp2_isHermitian : (totalSpinHalfOp2 Λ).IsHermitian := by
  unfold totalSpinHalfOp2
  exact isHermitian_sum Finset.univ
    (fun x _ => onSite_isHermitian x spinHalfOp2_isHermitian)

/-- `Ŝ_tot^(3)` is Hermitian. -/
theorem totalSpinHalfOp3_isHermitian : (totalSpinHalfOp3 Λ).IsHermitian := by
  unfold totalSpinHalfOp3
  exact isHermitian_sum Finset.univ
    (fun x _ => onSite_isHermitian x spinHalfOp3_isHermitian)

/-! ## Distinct-site commutation (Tasaki eq 2.2.6, S = 1/2, `x ≠ y` case)

For `x ≠ y`, the site-embedded spin operators `onSite x Sα` and
`onSite y Sβ` commute. This is exactly `onSite_mul_onSite_of_ne` from
`ManyBody.lean`. We expose a Spin-1/2-specific named wrapper for use
downstream.
-/

/-- Distinct-site commutation for S = 1/2 spin operators: for `x ≠ y`,
`Ŝ_x^(α) · Ŝ_y^(β) = Ŝ_y^(β) · Ŝ_x^(α)`. -/
theorem spinHalfOp_onSite_comm_of_ne {x y : Λ} (hxy : x ≠ y)
    (Sα Sβ : Matrix (Fin 2) (Fin 2) ℂ) :
    onSite x Sα * onSite y Sβ = onSite y Sβ * onSite x Sα :=
  onSite_mul_onSite_of_ne hxy Sα Sβ

end LatticeSystem.Quantum
