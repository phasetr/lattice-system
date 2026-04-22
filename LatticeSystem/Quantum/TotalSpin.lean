/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinHalf
import LatticeSystem.Quantum.SpinHalfBasis
import LatticeSystem.Quantum.SpinHalfRotation
import LatticeSystem.Quantum.ManyBody
import Mathlib.Topology.UniformSpace.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

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

/-- A finite sum of Hermitian matrices is Hermitian. -/
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
noncomputable def totalSpinHalfOpPlus : ManyBodyOp Λ :=
  ∑ x : Λ, onSite x spinHalfOpPlus

/-- Total lowering operator: `Ŝ^-_tot := Σ_{x ∈ Λ} Ŝ_x^-`. -/
noncomputable def totalSpinHalfOpMinus : ManyBodyOp Λ :=
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

/-! ## Ŝ^(3)_tot eigenvalue on basis states (Tasaki eq (2.2.10))

Each computational-basis state `|σ⟩` is an eigenvector of `Ŝ_tot^(3)`
with eigenvalue `(1/2) · |σ|`, where `|σ| = Σ_x spinSign(σ_x)` is the
total magnetization. -/

/-- Half-spin eigenvalue as a complex number. -/
noncomputable def spinHalfSign (s : Fin 2) : ℂ :=
  if s = 0 then (1 / 2 : ℂ) else -(1 / 2 : ℂ)

/-- `Ŝ_x^(3) · |σ⟩ = ±(1/2) · |σ⟩` depending on `σ_x`. -/
theorem onSite_spinHalfOp3_mulVec_basisVec (x : Λ) (σ : Λ → Fin 2) :
    (onSite x spinHalfOp3 : ManyBodyOp Λ).mulVec (basisVec σ) =
      spinHalfSign (σ x) • basisVec σ := by
  rw [onSite_mulVec_basisVec]
  funext τ
  simp only [Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two,
    spinHalfSign, spinHalfOp3, pauliZ]
  match hsx : σ x with
  | 0 =>
    have : Function.update σ x (0 : Fin 2) = σ := by
      rw [← hsx]; exact Function.update_eq_self _ _
    rw [this]; simp
  | 1 =>
    have : Function.update σ x (1 : Fin 2) = σ := by
      rw [← hsx]; exact Function.update_eq_self _ _
    rw [this]; simp

/-- `Ŝ_tot^(3) · |σ⟩ = (Σ_x spinHalfSign(σ_x)) · |σ⟩`, so every
computational-basis state is an eigenvector of `Ŝ_tot^(3)`. -/
theorem totalSpinHalfOp3_mulVec_basisVec (σ : Λ → Fin 2) :
    (totalSpinHalfOp3 Λ).mulVec (basisVec σ) =
      (∑ x : Λ, spinHalfSign (σ x)) • basisVec σ := by
  unfold totalSpinHalfOp3
  funext τ
  change ∑ ρ, (∑ x, onSite x spinHalfOp3) τ ρ * basisVec σ ρ =
       ((∑ x, spinHalfSign (σ x)) • basisVec σ) τ
  simp only [Matrix.sum_apply, Finset.sum_mul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h := onSite_spinHalfOp3_mulVec_basisVec Λ x σ
  have hτ := congrFun h τ
  change ∑ ρ, onSite x spinHalfOp3 τ ρ * basisVec σ ρ = spinHalfSign (σ x) * basisVec σ τ
  convert hτ using 1

/-- `Ŝ_tot^(3) · |s..s⟩ = (|Λ| · spinHalfSign s) · |s..s⟩`: every
constant-spin basis state is an `Ŝ_tot^(3)` eigenvector with
eigenvalue `|Λ| · (±1/2)` depending on `s`. -/
theorem totalSpinHalfOp3_mulVec_basisVec_const (s : Fin 2) :
    (totalSpinHalfOp3 Λ).mulVec (basisVec (fun _ : Λ => s)) =
      ((Fintype.card Λ : ℂ) * spinHalfSign s) •
        basisVec (fun _ : Λ => s) := by
  rw [totalSpinHalfOp3_mulVec_basisVec]
  congr 1
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- All-up specialisation: `Ŝ_tot^(3) · |↑..↑⟩ = (|Λ|/2) · |↑..↑⟩`. -/
theorem totalSpinHalfOp3_mulVec_basisVec_all_up :
    (totalSpinHalfOp3 Λ).mulVec (basisVec (fun _ : Λ => (0 : Fin 2))) =
      ((Fintype.card Λ : ℂ) / 2) • basisVec (fun _ : Λ => (0 : Fin 2)) := by
  rw [totalSpinHalfOp3_mulVec_basisVec_const]
  have hsign : spinHalfSign (0 : Fin 2) = (1 / 2 : ℂ) := by
    simp [spinHalfSign]
  rw [hsign]
  congr 1; ring

/-- All-down specialisation: `Ŝ_tot^(3) · |↓..↓⟩ = -(|Λ|/2) · |↓..↓⟩`. -/
theorem totalSpinHalfOp3_mulVec_basisVec_all_down :
    (totalSpinHalfOp3 Λ).mulVec (basisVec (fun _ : Λ => (1 : Fin 2))) =
      (-((Fintype.card Λ : ℂ) / 2)) • basisVec (fun _ : Λ => (1 : Fin 2)) := by
  rw [totalSpinHalfOp3_mulVec_basisVec_const]
  have hsign : spinHalfSign (1 : Fin 2) = -(1 / 2 : ℂ) := by
    simp [spinHalfSign]
  rw [hsign]
  congr 1; ring

/-- `Ŝ_tot^(3) · |σ⟩ = (|σ| / 2) · |σ⟩`: the `Ŝ_tot^(3)` eigenvalue is
half the total magnetization (Tasaki eq. (2.2.10)). -/
theorem totalSpinHalfOp3_mulVec_basisVec_eq_magnetization (σ : Λ → Fin 2) :
    (totalSpinHalfOp3 Λ).mulVec (basisVec σ) =
      ((magnetization Λ σ : ℂ) / 2) • basisVec σ := by
  rw [totalSpinHalfOp3_mulVec_basisVec]
  congr 1
  have heach : ∀ x : Λ, spinHalfSign (σ x) = ((spinSign (σ x) : ℂ) / 2) := by
    intro x
    unfold spinHalfSign spinSign
    match hsx : σ x with
    | 0 => simp
    | 1 => push_cast; ring
  rw [Finset.sum_congr rfl (fun x _ => heach x)]
  unfold magnetization
  push_cast
  rw [div_eq_mul_inv, Finset.sum_mul]
  simp only [div_eq_mul_inv]

/-- `Ŝ_x^+ · |σ⟩`: acts as raising on a down spin at site `x`
(annihilates an up spin). -/
theorem onSite_spinHalfOpPlus_mulVec_basisVec (x : Λ) (σ : Λ → Fin 2) :
    (onSite x spinHalfOpPlus : ManyBodyOp Λ).mulVec (basisVec σ) =
      if σ x = 1 then basisVec (Function.update σ x 0) else 0 := by
  rw [onSite_mulVec_basisVec]
  funext τ
  simp only [Fin.sum_univ_two, spinHalfOpPlus]
  match hsx : σ x with
  | 0 =>
    have h0 : Function.update σ x (0 : Fin 2) = σ := by
      rw [← hsx]; exact Function.update_eq_self _ _
    rw [h0]
    simp
  | 1 =>
    have h1 : Function.update σ x (1 : Fin 2) = σ := by
      rw [← hsx]; exact Function.update_eq_self _ _
    rw [h1]
    simp

/-- `Ŝ_x^- · |σ⟩`: acts as lowering on an up spin at site `x`
(annihilates a down spin). -/
theorem onSite_spinHalfOpMinus_mulVec_basisVec (x : Λ) (σ : Λ → Fin 2) :
    (onSite x spinHalfOpMinus : ManyBodyOp Λ).mulVec (basisVec σ) =
      if σ x = 0 then basisVec (Function.update σ x 1) else 0 := by
  rw [onSite_mulVec_basisVec]
  funext τ
  simp only [Fin.sum_univ_two, spinHalfOpMinus]
  match hsx : σ x with
  | 0 =>
    have h0 : Function.update σ x (0 : Fin 2) = σ := by
      rw [← hsx]; exact Function.update_eq_self _ _
    rw [h0]
    simp
  | 1 =>
    have h1 : Function.update σ x (1 : Fin 2) = σ := by
      rw [← hsx]; exact Function.update_eq_self _ _
    rw [h1]
    simp

/-- `Ŝ^+_tot · |σ⟩` is the sum of site-wise raising actions. -/
theorem totalSpinHalfOpPlus_mulVec_basisVec (σ : Λ → Fin 2) :
    (totalSpinHalfOpPlus Λ).mulVec (basisVec σ) =
      ∑ x : Λ, (if σ x = 1 then basisVec (Function.update σ x 0)
                           else (0 : (Λ → Fin 2) → ℂ)) := by
  unfold totalSpinHalfOpPlus
  funext τ
  change ∑ ρ, (∑ x, onSite x spinHalfOpPlus) τ ρ * basisVec σ ρ =
       (∑ x : Λ, (if σ x = 1 then basisVec (Function.update σ x 0)
                              else (0 : (Λ → Fin 2) → ℂ))) τ
  simp only [Matrix.sum_apply, Finset.sum_mul, Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h := onSite_spinHalfOpPlus_mulVec_basisVec Λ x σ
  have hτ := congrFun h τ
  change ∑ ρ, onSite x spinHalfOpPlus τ ρ * basisVec σ ρ = _
  rw [← hτ]
  rfl

/-- `Ŝ^-_tot · |σ⟩` is the sum of site-wise lowering actions. -/
theorem totalSpinHalfOpMinus_mulVec_basisVec (σ : Λ → Fin 2) :
    (totalSpinHalfOpMinus Λ).mulVec (basisVec σ) =
      ∑ x : Λ, (if σ x = 0 then basisVec (Function.update σ x 1)
                           else (0 : (Λ → Fin 2) → ℂ)) := by
  unfold totalSpinHalfOpMinus
  funext τ
  change ∑ ρ, (∑ x, onSite x spinHalfOpMinus) τ ρ * basisVec σ ρ =
       (∑ x : Λ, (if σ x = 0 then basisVec (Function.update σ x 1)
                              else (0 : (Λ → Fin 2) → ℂ))) τ
  simp only [Matrix.sum_apply, Finset.sum_mul, Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h := onSite_spinHalfOpMinus_mulVec_basisVec Λ x σ
  have hτ := congrFun h τ
  change ∑ ρ, onSite x spinHalfOpMinus τ ρ * basisVec σ ρ = _
  rw [← hτ]
  rfl

/-! ## Ladder termination on the fully-polarised states (Tasaki §2.4 boundary)

The lowering operator annihilates the all-down state (already at the
minimum `Sz = -Smax`); the raising operator annihilates the all-up
state. These are the boundary conditions ensuring Tasaki's
ferromagnetic ground-state ladder `(Ŝtot^-)^k · |↑..↑⟩` (Tasaki §2.4
eq. (2.4.9), p. 33) terminates: the iterates pass through the
magnetisation sectors `H_{Smax}, H_{Smax-1}, …, H_{-Smax}` and
become the zero vector beyond. -/

/-- `Ŝtot^- · |↓..↓⟩ = 0`: the global lowering operator annihilates
the all-down state. -/
theorem totalSpinHalfOpMinus_mulVec_basisVec_all_down :
    (totalSpinHalfOpMinus Λ).mulVec (basisVec (fun _ : Λ => (1 : Fin 2))) = 0 := by
  unfold totalSpinHalfOpMinus
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [onSite_spinHalfOpMinus_mulVec_basisVec]
  simp

/-- `Ŝtot^+ · |↑..↑⟩ = 0`: the global raising operator annihilates
the all-up state. -/
theorem totalSpinHalfOpPlus_mulVec_basisVec_all_up :
    (totalSpinHalfOpPlus Λ).mulVec (basisVec (fun _ : Λ => (0 : Fin 2))) = 0 := by
  unfold totalSpinHalfOpPlus
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [onSite_spinHalfOpPlus_mulVec_basisVec]
  simp

/-! ## Total spin commutation relations

The total spin operators `Ŝ_tot^(α)` satisfy the same commutation
relation (2.1.1) as single-site spin operators. This follows by
distributing the double sum and combining the diagonal (`x = y`,
Tasaki eq. (2.2.6) diagonal) with the off-diagonal contribution
(`x ≠ y`, vanishing by `onSite_mul_onSite_of_ne`).
-/

/-- General total-spin commutator: if `[Sα, Sβ] = I • Sγ` then
`[Σ_x onSite x Sα, Σ_x onSite x Sβ] = I • Σ_x onSite x Sγ`. -/
private lemma totalSpin_commutator_general
    {Sα Sβ Sγ : Matrix (Fin 2) (Fin 2) ℂ}
    (hab : Sα * Sβ - Sβ * Sα = Complex.I • Sγ) :
    ((∑ x : Λ, onSite x Sα) * (∑ x : Λ, onSite x Sβ)
        - (∑ x : Λ, onSite x Sβ) * (∑ x : Λ, onSite x Sα) : ManyBodyOp Λ) =
      Complex.I • ∑ x : Λ, onSite x Sγ := by
  calc (∑ x : Λ, onSite x Sα) * (∑ x : Λ, onSite x Sβ)
          - (∑ x : Λ, onSite x Sβ) * (∑ x : Λ, onSite x Sα)
      = ∑ x : Λ, ∑ y : Λ, (onSite x Sα * onSite y Sβ - onSite y Sβ * onSite x Sα) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm (f := fun y x => onSite y Sβ * onSite x Sα)
            (s := Finset.univ) (t := Finset.univ)]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_sub_distrib]
    _ = ∑ x : Λ, (Complex.I • onSite x Sγ) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_eq_single x]
        · rw [onSite_commutator_same, hab, onSite_smul]
        · intros y _ hyx
          rw [onSite_mul_onSite_of_ne hyx.symm]
          simp
        · intro h; exact absurd (Finset.mem_univ x) h
    _ = Complex.I • ∑ x : Λ, onSite x Sγ := by
        rw [← Finset.smul_sum]

/-- Total spin commutator: `[Ŝ_tot^(1), Ŝ_tot^(2)] = i · Ŝ_tot^(3)`. -/
theorem totalSpinHalfOp1_commutator_totalSpinHalfOp2 :
    (totalSpinHalfOp1 Λ * totalSpinHalfOp2 Λ
        - totalSpinHalfOp2 Λ * totalSpinHalfOp1 Λ : ManyBodyOp Λ) =
      Complex.I • totalSpinHalfOp3 Λ := by
  unfold totalSpinHalfOp1 totalSpinHalfOp2 totalSpinHalfOp3
  exact totalSpin_commutator_general Λ spinHalfOp1_commutator_spinHalfOp2

/-- Total spin commutator: `[Ŝ_tot^(2), Ŝ_tot^(3)] = i · Ŝ_tot^(1)`. -/
theorem totalSpinHalfOp2_commutator_totalSpinHalfOp3 :
    (totalSpinHalfOp2 Λ * totalSpinHalfOp3 Λ
        - totalSpinHalfOp3 Λ * totalSpinHalfOp2 Λ : ManyBodyOp Λ) =
      Complex.I • totalSpinHalfOp1 Λ := by
  unfold totalSpinHalfOp1 totalSpinHalfOp2 totalSpinHalfOp3
  exact totalSpin_commutator_general Λ spinHalfOp2_commutator_spinHalfOp3

/-- Total spin commutator: `[Ŝ_tot^(3), Ŝ_tot^(1)] = i · Ŝ_tot^(2)`. -/
theorem totalSpinHalfOp3_commutator_totalSpinHalfOp1 :
    (totalSpinHalfOp3 Λ * totalSpinHalfOp1 Λ
        - totalSpinHalfOp1 Λ * totalSpinHalfOp3 Λ : ManyBodyOp Λ) =
      Complex.I • totalSpinHalfOp2 Λ := by
  unfold totalSpinHalfOp1 totalSpinHalfOp2 totalSpinHalfOp3
  exact totalSpin_commutator_general Λ spinHalfOp3_commutator_spinHalfOp1

/-! ## On-site operator commutes with total spin via its single-site commutator -/

/-- For any single-site operator `onSite x Sα` and any total-spin-like sum
`Σ_z onSite z Sβ`, the commutator concentrates at site `x`:
`[onSite x Sα, Σ_z onSite z Sβ] = onSite x [Sα, Sβ]`. -/
theorem onSite_commutator_totalOnSite
    (x : Λ) (Sα Sβ : Matrix (Fin 2) (Fin 2) ℂ) :
    (onSite x Sα : ManyBodyOp Λ) * (∑ z : Λ, onSite z Sβ)
        - (∑ z : Λ, onSite z Sβ) * onSite x Sα =
      onSite x (Sα * Sβ - Sβ * Sα) := by
  rw [Finset.mul_sum, Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single x]
  · rw [onSite_mul_onSite_same, onSite_mul_onSite_same, ← onSite_sub]
  · intros z _ hzx
    rw [onSite_mul_onSite_of_ne hzx.symm]
    simp
  · intro h; exact absurd (Finset.mem_univ x) h

/-! ## Adjoint relations and ladder commutator for total raising/lowering -/

/-- The conjugate transpose of `onSite i A` equals `onSite i Aᴴ`. -/
private lemma onSite_conjTranspose (i : Λ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (onSite i A).conjTranspose = (onSite i A.conjTranspose : ManyBodyOp Λ) := by
  ext σ' σ
  simp only [Matrix.conjTranspose_apply, onSite_apply]
  by_cases h : ∀ k, k ≠ i → σ' k = σ k
  · have h' : ∀ k, k ≠ i → σ k = σ' k := fun k hk => (h k hk).symm
    rw [if_pos h, if_pos h']
  · have h' : ¬ ∀ k, k ≠ i → σ k = σ' k := fun hp =>
      h (fun k hk => (hp k hk).symm)
    rw [if_neg h, if_neg h', star_zero]

omit [Fintype Λ] [DecidableEq Λ] in
/-- Conjugate transpose distributes over finite sums in `ManyBodyOp Λ`. -/
private lemma sum_conjTranspose_manyBody
    {s : Finset Λ} (f : Λ → ManyBodyOp Λ) :
    (∑ x ∈ s, f x).conjTranspose = ∑ x ∈ s, (f x).conjTranspose := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a t hns ih =>
    rw [Finset.sum_insert hns, Finset.sum_insert hns,
      Matrix.conjTranspose_add, ih]

/-- `(Ŝ^+_tot)† = Ŝ^-_tot`. -/
theorem totalSpinHalfOpPlus_conjTranspose :
    (totalSpinHalfOpPlus Λ).conjTranspose = totalSpinHalfOpMinus Λ := by
  unfold totalSpinHalfOpPlus totalSpinHalfOpMinus
  rw [sum_conjTranspose_manyBody]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [onSite_conjTranspose, spinHalfOpPlus_conjTranspose]

/-- `(Ŝ^-_tot)† = Ŝ^+_tot`. -/
theorem totalSpinHalfOpMinus_conjTranspose :
    (totalSpinHalfOpMinus Λ).conjTranspose = totalSpinHalfOpPlus Λ := by
  unfold totalSpinHalfOpPlus totalSpinHalfOpMinus
  rw [sum_conjTranspose_manyBody]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [onSite_conjTranspose, spinHalfOpMinus_conjTranspose]

/-- Cartan ladder relation: `[Ŝ_tot^(3), Ŝ^+_tot] = Ŝ^+_tot`.
Derived from `[Ŝ_tot^(3), Ŝ_tot^(α)]` for `α = 1, 2` and
`Ŝ^+_tot = Ŝ_tot^(1) + i · Ŝ_tot^(2)` (Tasaki eq (2.2.8)). -/
theorem totalSpinHalfOp3_commutator_totalSpinHalfOpPlus :
    (totalSpinHalfOp3 Λ * totalSpinHalfOpPlus Λ
        - totalSpinHalfOpPlus Λ * totalSpinHalfOp3 Λ : ManyBodyOp Λ) =
      totalSpinHalfOpPlus Λ := by
  set A := totalSpinHalfOp1 Λ
  set B := totalSpinHalfOp2 Λ
  set C := totalSpinHalfOp3 Λ
  have hCA : C * A - A * C = Complex.I • B :=
    totalSpinHalfOp3_commutator_totalSpinHalfOp1 Λ
  have hBC : B * C - C * B = Complex.I • A :=
    totalSpinHalfOp2_commutator_totalSpinHalfOp3 Λ
  rw [totalSpinHalfOpPlus_eq_add]
  rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  have step1 : C * A + Complex.I • (C * B) - (A * C + Complex.I • (B * C)) =
      (C * A - A * C) + Complex.I • (C * B - B * C) := by
    rw [smul_sub]; abel
  rw [step1, hCA]
  have hCB : C * B - B * C = -(Complex.I • A) := by
    rw [show C * B - B * C = -(B * C - C * B) from by abel, hBC]
  rw [hCB, smul_neg, smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  abel

/-- Cartan ladder relation: `[Ŝ_tot^(3), Ŝ^-_tot] = -Ŝ^-_tot`. -/
theorem totalSpinHalfOp3_commutator_totalSpinHalfOpMinus :
    (totalSpinHalfOp3 Λ * totalSpinHalfOpMinus Λ
        - totalSpinHalfOpMinus Λ * totalSpinHalfOp3 Λ : ManyBodyOp Λ) =
      -(totalSpinHalfOpMinus Λ) := by
  set A := totalSpinHalfOp1 Λ
  set B := totalSpinHalfOp2 Λ
  set C := totalSpinHalfOp3 Λ
  have hCA : C * A - A * C = Complex.I • B :=
    totalSpinHalfOp3_commutator_totalSpinHalfOp1 Λ
  have hBC : B * C - C * B = Complex.I • A :=
    totalSpinHalfOp2_commutator_totalSpinHalfOp3 Λ
  rw [totalSpinHalfOpMinus_eq_sub]
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
  have step1 : C * A - Complex.I • (C * B) - (A * C - Complex.I • (B * C)) =
      (C * A - A * C) - Complex.I • (C * B - B * C) := by
    rw [smul_sub]; abel
  rw [step1, hCA]
  have hCB : C * B - B * C = -(Complex.I • A) := by
    rw [show C * B - B * C = -(B * C - C * B) from by abel, hBC]
  rw [hCB, smul_neg, smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  abel

end LatticeSystem.Quantum
