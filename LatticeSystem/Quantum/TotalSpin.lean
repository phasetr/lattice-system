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

/-! ## Total spin commutation relations

The total spin operators `Ŝ_tot^(α)` satisfy the same commutation
relation (2.1.1) as single-site spin operators. This follows by
distributing the double sum and combining the diagonal (`x = y`,
Tasaki eq. (2.2.6) diagonal) with the off-diagonal contribution
(`x ≠ y`, vanishing by `onSite_mul_onSite_of_ne`).
-/

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

/-- Total ladder commutator: `[Ŝ^+_tot, Ŝ^-_tot] = 2 · Ŝ_tot^(3)`. -/
theorem totalSpinHalfOpPlus_commutator_totalSpinHalfOpMinus :
    (totalSpinHalfOpPlus Λ * totalSpinHalfOpMinus Λ
        - totalSpinHalfOpMinus Λ * totalSpinHalfOpPlus Λ : ManyBodyOp Λ) =
      (2 : ℂ) • totalSpinHalfOp3 Λ := by
  unfold totalSpinHalfOpPlus totalSpinHalfOpMinus totalSpinHalfOp3
  -- Reuse the generic commutator framework with Sα=Ŝ^+, Sβ=Ŝ^-, but the RHS
  -- is `2 • Ŝ^(3)` rather than `I • Sγ`; we redo the calculation directly.
  calc (∑ x : Λ, onSite x spinHalfOpPlus) * (∑ x : Λ, onSite x spinHalfOpMinus)
          - (∑ x : Λ, onSite x spinHalfOpMinus) * (∑ x : Λ, onSite x spinHalfOpPlus)
      = ∑ x : Λ, ∑ y : Λ,
          (onSite x spinHalfOpPlus * onSite y spinHalfOpMinus
            - onSite y spinHalfOpMinus * onSite x spinHalfOpPlus) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm (f := fun y x =>
          onSite y spinHalfOpMinus * onSite x spinHalfOpPlus)
          (s := Finset.univ) (t := Finset.univ)]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_sub_distrib]
    _ = ∑ x : Λ, ((2 : ℂ) • onSite x spinHalfOp3) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_eq_single x]
        · rw [onSite_commutator_same, spinHalfOpPlus_commutator_spinHalfOpMinus,
              onSite_smul]
        · intros y _ hyx
          rw [onSite_mul_onSite_of_ne hyx.symm]
          simp
        · intro h; exact absurd (Finset.mem_univ x) h
    _ = (2 : ℂ) • ∑ x : Λ, onSite x spinHalfOp3 := by
        rw [← Finset.smul_sum]

end LatticeSystem.Quantum
