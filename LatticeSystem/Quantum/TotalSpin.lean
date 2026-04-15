/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinHalf
import LatticeSystem.Quantum.SpinHalfBasis
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

/-! ## Same-site commutation (Tasaki eq (2.2.6), `x = y` case, S = 1/2)

These are the diagonal cases of Tasaki eq. (2.2.6): at the same site
`x`, the spin operators obey the single-site commutation relations
(2.1.1) lifted by `onSite`. -/

/-- Same-site commutator: `[Ŝ_x^(1), Ŝ_x^(2)] = i · Ŝ_x^(3)`. -/
theorem spinHalfOp1_onSite_commutator_spinHalfOp2_onSite (x : Λ) :
    (onSite x spinHalfOp1 * onSite x spinHalfOp2
        - onSite x spinHalfOp2 * onSite x spinHalfOp1 : ManyBodyOp Λ) =
      Complex.I • onSite x spinHalfOp3 := by
  rw [onSite_commutator_same, spinHalfOp1_commutator_spinHalfOp2, onSite_smul]

/-- Same-site commutator: `[Ŝ_x^(2), Ŝ_x^(3)] = i · Ŝ_x^(1)`. -/
theorem spinHalfOp2_onSite_commutator_spinHalfOp3_onSite (x : Λ) :
    (onSite x spinHalfOp2 * onSite x spinHalfOp3
        - onSite x spinHalfOp3 * onSite x spinHalfOp2 : ManyBodyOp Λ) =
      Complex.I • onSite x spinHalfOp1 := by
  rw [onSite_commutator_same, spinHalfOp2_commutator_spinHalfOp3, onSite_smul]

/-- Same-site commutator: `[Ŝ_x^(3), Ŝ_x^(1)] = i · Ŝ_x^(2)`. -/
theorem spinHalfOp3_onSite_commutator_spinHalfOp1_onSite (x : Λ) :
    (onSite x spinHalfOp3 * onSite x spinHalfOp1
        - onSite x spinHalfOp1 * onSite x spinHalfOp3 : ManyBodyOp Λ) =
      Complex.I • onSite x spinHalfOp2 := by
  rw [onSite_commutator_same, spinHalfOp3_commutator_spinHalfOp1, onSite_smul]

/-! ## Total raising/lowering operators (Tasaki eq (2.2.8)) -/

/-- Total raising operator: `Ŝ^+_tot := Σ_{x ∈ Λ} Ŝ_x^+`. -/
def totalSpinHalfOpPlus : ManyBodyOp Λ :=
  ∑ x : Λ, onSite x spinHalfOpPlus

/-- Total lowering operator: `Ŝ^-_tot := Σ_{x ∈ Λ} Ŝ_x^-`. -/
def totalSpinHalfOpMinus : ManyBodyOp Λ :=
  ∑ x : Λ, onSite x spinHalfOpMinus

/-- The defining identity (Tasaki eq (2.2.8)):
`Ŝ^+_tot = Ŝ^(1)_tot + i · Ŝ^(2)_tot`. -/
theorem totalSpinHalfOpPlus_eq_add :
    (totalSpinHalfOpPlus Λ : ManyBodyOp Λ) =
      totalSpinHalfOp1 Λ + Complex.I • totalSpinHalfOp2 Λ := by
  unfold totalSpinHalfOpPlus totalSpinHalfOp1 totalSpinHalfOp2
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [← onSite_smul, ← onSite_add, spinHalfOpPlus_eq_add]

/-- The defining identity (Tasaki eq (2.2.8)):
`Ŝ^-_tot = Ŝ^(1)_tot - i · Ŝ^(2)_tot`. -/
theorem totalSpinHalfOpMinus_eq_sub :
    (totalSpinHalfOpMinus Λ : ManyBodyOp Λ) =
      totalSpinHalfOp1 Λ - Complex.I • totalSpinHalfOp2 Λ := by
  unfold totalSpinHalfOpMinus totalSpinHalfOp1 totalSpinHalfOp2
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [← onSite_smul, ← onSite_sub, spinHalfOpMinus_eq_sub]

/-! ## Total magnetization (Tasaki eq (2.2.2))

Tasaki eq. (2.2.2) defines the total magnetization `|σ| := Σ_{x ∈ Λ} σ_x`
for `σ_x ∈ {-1, +1}`. In our encoding `σ_x : Fin 2` with `0 ↦ +1/2`
(spin up) and `1 ↦ -1/2` (spin down), the natural integer-valued
magnetization is `Σ_x (1 - 2 · σ_x)`. -/

/-- Sign-of-spin function: `0 ↦ 1` (spin up), `1 ↦ -1` (spin down). -/
def spinSign (s : Fin 2) : ℤ := if s = 0 then 1 else -1

/-- Total magnetization of a basis state `σ : Λ → Fin 2`:
`|σ| := Σ_{x ∈ Λ} spinSign (σ x) ∈ {-|Λ|, ..., |Λ|}`. -/
def magnetization (σ : Λ → Fin 2) : ℤ :=
  ∑ x : Λ, spinSign (σ x)

end LatticeSystem.Quantum
