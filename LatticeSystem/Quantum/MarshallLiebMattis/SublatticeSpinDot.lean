import LatticeSystem.Quantum.MarshallLiebMattis.SublatticeSpin
import LatticeSystem.Quantum.SpinDot

/-!
# Cross-sublattice spin dot product `Ŝ_A · Ŝ_B`

To express the MLM toy Hamiltonian (Tasaki §2.5 eq. (2.5.10)–(2.5.11))
through the Casimir identity, we introduce the **cross-sublattice
spin dot product**:

  `Ŝ_A · Ŝ_B := Σ_{α=1,2,3} Ŝ_A^(α) Ŝ_B^(α)`,

where `A, B : Λ → Bool` are sublattice indicators. The key structural
fact is the bilinear expansion

  `Ŝ_A · Ŝ_B = Σ_{x : A x = true} Σ_{y : B y = true} Ŝ_x · Ŝ_y`,

which connects the operator-level Casimir form to the bond-level
Heisenberg expression used in the toy Hamiltonian.

This module:

1. Defines `sublatticeSpinDot A B`.
2. Proves the bilinear expansion to `Σ_{x ∈ A, y ∈ B} spinHalfDot x y`
   (formulated as `∑ x, ∑ y, if A x ∧ B y then spinHalfDot x y else 0`).

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 eqs. (2.5.10)–(2.5.11).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Cross-sublattice spin dot product -/

/-- The cross-sublattice spin dot product:
`Ŝ_A · Ŝ_B := Σ_α Ŝ_A^(α) Ŝ_B^(α)`. -/
noncomputable def sublatticeSpinDot (A B : Λ → Bool) : ManyBodyOp Λ :=
  sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp1 B +
    sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp2 B +
    sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp3 B

/-- `Ŝ_A · Ŝ_B = Σ_α Ŝ_A^(α) Ŝ_B^(α)` is the explicit definition. -/
@[simp] theorem sublatticeSpinDot_def (A B : Λ → Bool) :
    sublatticeSpinDot A B =
      sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp1 B +
        sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp2 B +
        sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp3 B := rfl

/-! ## Bilinear expansion (helper) -/

/-- Per-axis expansion: a single product
`Ŝ_A^(α) Ŝ_B^(α)` factors as a double sum
`Σ_x Σ_y (if A x ∧ B y then onSite x σ_α * onSite y σ_α else 0)`.

This is the bridge from the sublattice-operator product form to the
site-pair form used in the Heisenberg Hamiltonian. -/
private theorem sublatticeSpinHalfOp_mul_eq_sum_sum
    (A B : Λ → Bool) (S : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ x : Λ, if A x then onSite x S else 0) *
        (∑ y : Λ, if B y then onSite y S else 0) =
      ∑ x : Λ, ∑ y : Λ,
        if A x ∧ B y then onSite x S * onSite y S else 0 := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hAx : A x = true
  · by_cases hBy : B y = true
    · rw [if_pos hAx, if_pos hBy, if_pos ⟨hAx, hBy⟩]
    · rw [if_pos hAx, if_neg hBy, mul_zero, if_neg]
      rintro ⟨_, h⟩; exact hBy h
  · rw [if_neg hAx, zero_mul, if_neg]
    rintro ⟨h, _⟩; exact hAx h

/-! ## Hermiticity of `Ŝ_A · Ŝ_¬A` -/

/-- The cross-sublattice spin dot product `Ŝ_A · Ŝ_¬A` is Hermitian.
Each axis-`α` summand `Ŝ_A^(α) Ŝ_¬A^(α)` is the product of two
commuting Hermitian operators (cross-commute lemmas), hence Hermitian. -/
theorem sublatticeSpinDot_complement_isHermitian (A : Λ → Bool) :
    (sublatticeSpinDot A (fun x => ! A x)).IsHermitian := by
  unfold sublatticeSpinDot
  refine ((?_ : Matrix.IsHermitian _).add ?_).add ?_
  · exact Matrix.IsHermitian.mul_of_commute
      (sublatticeSpinHalfOp1_isHermitian A)
      (sublatticeSpinHalfOp1_isHermitian (fun x => ! A x))
      (sublatticeSpinHalfOp1_cross_commute A).eq
  · exact Matrix.IsHermitian.mul_of_commute
      (sublatticeSpinHalfOp2_isHermitian A)
      (sublatticeSpinHalfOp2_isHermitian (fun x => ! A x))
      (sublatticeSpinHalfOp2_cross_commute A).eq
  · exact Matrix.IsHermitian.mul_of_commute
      (sublatticeSpinHalfOp3_isHermitian A)
      (sublatticeSpinHalfOp3_isHermitian (fun x => ! A x))
      (sublatticeSpinHalfOp3_cross_commute A).eq

/-! ## Bilinear expansion -/

/-- The cross-sublattice spin dot product expands as a double sum
over sites of the spin-dot products:
`Ŝ_A · Ŝ_B = Σ_{x : A x} Σ_{y : B y} Ŝ_x · Ŝ_y`.

This is formulated using `if A x ∧ B y then ... else 0` so that the
sums are over all of `Λ`. -/
theorem sublatticeSpinDot_eq_sum_sum (A B : Λ → Bool) :
    sublatticeSpinDot A B =
      ∑ x : Λ, ∑ y : Λ,
        if A x ∧ B y then spinHalfDot x y else 0 := by
  unfold sublatticeSpinDot sublatticeSpinHalfOp1
    sublatticeSpinHalfOp2 sublatticeSpinHalfOp3
  rw [sublatticeSpinHalfOp_mul_eq_sum_sum A B spinHalfOp1,
      sublatticeSpinHalfOp_mul_eq_sum_sum A B spinHalfOp2,
      sublatticeSpinHalfOp_mul_eq_sum_sum A B spinHalfOp3]
  -- Combine the three axis sums into a single sum of `spinHalfDot`.
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hAB : A x ∧ B y
  · simp only [if_pos hAB]
    unfold spinHalfDot
    rfl
  · simp only [if_neg hAB, add_zero]

/-! ## Sublattice spin squared as a double-sum of spin-dot products -/

/-- The cross-sublattice spin dot product with `B = A` equals the
sublattice Casimir: `Ŝ_A · Ŝ_A = (Ŝ_A)²`. Definitional identity
since both unfold to `Σ_α Ŝ_A^(α) Ŝ_A^(α)`. Spin-`1/2` mirror of
`sublatticeSpinSDot_self_eq_sublatticeSpinSquaredS` (γ-4 step 49). -/
theorem sublatticeSpinDot_self_eq_sublatticeSpinHalfSquared (A : Λ → Bool) :
    sublatticeSpinDot A A = sublatticeSpinHalfSquared A := rfl

/-- `(Ŝ_A)² = Σ_{x ∈ A} Σ_{y ∈ A} Ŝ_x · Ŝ_y`.  Specialisation of
`sublatticeSpinDot_eq_sum_sum` to `B = A`, since `(Ŝ_A)² = Ŝ_A · Ŝ_A`
definitionally. -/
theorem sublatticeSpinHalfSquared_eq_sum_dot (A : Λ → Bool) :
    sublatticeSpinHalfSquared A =
      ∑ x : Λ, ∑ y : Λ,
        if A x ∧ A y then spinHalfDot x y else 0 :=
  sublatticeSpinDot_eq_sum_sum A A

/-! ## Casimir eigenvalue on the all-up / all-down basis state -/

/-- `(Ŝ_A)² · |s s … s⟩ = (|A|·(|A|+2)/4) · |s s … s⟩` for any
`s : Fin 2` and any sublattice indicator `A`. The all-aligned basis
state is an eigenvector of the sublattice Casimir with eigenvalue
`S_A_max(S_A_max+1) = (|A|/2)·(|A|/2+1) = |A|(|A|+2)/4`, the maximum
spin of the `A`-subsystem. -/
theorem sublatticeSpinHalfSquared_mulVec_basisVec_const (A : Λ → Bool) (s : Fin 2) :
    (sublatticeSpinHalfSquared A).mulVec (basisVec (fun _ : Λ => s)) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => A x = true)).card + 2) / 4) •
        basisVec (fun _ : Λ => s) := by
  rw [sublatticeSpinHalfSquared_eq_sum_dot]
  rw [Matrix.sum_mulVec]
  simp_rw [Matrix.sum_mulVec]
  -- The action on |s..s⟩ at indicator-positive (x, y) is the constant-config
  -- formula; otherwise the term is 0.
  have hterm : ∀ x y : Λ, (if A x ∧ A y then (spinHalfDot x y) else 0).mulVec
        (basisVec (fun _ : Λ => s)) =
      (if A x ∧ A y then (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ)) else 0) •
        basisVec (fun _ : Λ => s) := by
    intro x y
    by_cases hAA : A x ∧ A y
    · rw [if_pos hAA, if_pos hAA]
      by_cases hxy : x = y
      · subst hxy
        rw [if_pos rfl, spinHalfDot_self]
        rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      · rw [if_neg hxy]
        exact spinHalfDot_mulVec_basisVec_parallel hxy _ rfl
    · rw [if_neg hAA, if_neg hAA, Matrix.zero_mulVec, zero_smul]
  simp_rw [hterm, ← Finset.sum_smul]
  congr 1
  -- Helper: ∑_x (if A x then C else 0) = |A| * C.
  have hindicator_sum : ∀ (C : ℂ),
      (∑ x : Λ, if A x = true then C else 0) =
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * C := by
    intro C
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul]
  -- Compute the double sum: |A| diagonal terms (3/4) + (|A|² - |A|) off-diagonal (1/4).
  have hinner : ∀ x : Λ, (∑ y : Λ,
        if A x ∧ A y then (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ)) else 0) =
      if A x = true then
        (((Finset.univ.filter (fun z : Λ => A z = true)).card : ℂ) / 4 + 1 / 2)
      else 0 := by
    intro x
    by_cases hAx : A x = true
    · rw [if_pos hAx]
      have hsplit : ∀ y : Λ,
          (if A x ∧ A y then (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ)) else 0) =
            (if A y = true then (1 / 4 : ℂ) else 0) +
              (if x = y then (1 / 2 : ℂ) else 0) := by
        intro y
        by_cases hAy : A y = true
        · rw [if_pos ⟨hAx, hAy⟩, if_pos hAy]
          by_cases hxy : x = y
          · simp [hxy]; ring
          · simp [hxy]
        · rw [if_neg (fun ⟨_, h⟩ => hAy h), if_neg hAy]
          have : x ≠ y := fun heq => hAy (heq ▸ hAx)
          simp [this]
      simp_rw [hsplit, Finset.sum_add_distrib]
      rw [hindicator_sum, Finset.sum_ite_eq Finset.univ x (fun _ => (1 / 2 : ℂ))]
      rw [if_pos (Finset.mem_univ _)]
      ring
    · rw [if_neg hAx]
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [if_neg]
      rintro ⟨h, _⟩; exact hAx h
  simp_rw [hinner]
  -- Outer sum: indicator-restricted sum of `(|A|/4 + 1/2)`.
  rw [hindicator_sum]
  ring

/-- Specialisation to all-up state. -/
theorem sublatticeSpinHalfSquared_mulVec_basisVec_all_up (A : Λ → Bool) :
    (sublatticeSpinHalfSquared A).mulVec (basisVec (fun _ : Λ => (0 : Fin 2))) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => A x = true)).card + 2) / 4) •
        basisVec (fun _ : Λ => (0 : Fin 2)) :=
  sublatticeSpinHalfSquared_mulVec_basisVec_const A 0

/-- Specialisation to all-down state. -/
theorem sublatticeSpinHalfSquared_mulVec_basisVec_all_down (A : Λ → Bool) :
    (sublatticeSpinHalfSquared A).mulVec (basisVec (fun _ : Λ => (1 : Fin 2))) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => A x = true)).card + 2) / 4) •
        basisVec (fun _ : Λ => (1 : Fin 2)) :=
  sublatticeSpinHalfSquared_mulVec_basisVec_const A 1

/-! ## Casimir eigenvalue on configurations constant on the sublattice -/

/-- More general: if `σ : Λ → Fin 2` is **constant on `A`** (i.e.
`σ x = s` for some `s : Fin 2` whenever `A x = true`), then `|σ⟩` is
an eigenvector of `(Ŝ_A)²` with the maximum-spin eigenvalue
`|A|·(|A|+2)/4`.

The action of `(Ŝ_A)²` involves only sites `x ∈ A`, so it depends only
on the values `σ x` for `x ∈ A`; constant-on-`A` is exactly the
hypothesis needed for the all-aligned eigenvalue formula. -/
theorem sublatticeSpinHalfSquared_mulVec_basisVec_of_const_on
    (A : Λ → Bool) {σ : Λ → Fin 2} {s : Fin 2}
    (hσ : ∀ x : Λ, A x = true → σ x = s) :
    (sublatticeSpinHalfSquared A).mulVec (basisVec σ) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => A x = true)).card + 2) / 4) •
        basisVec σ := by
  rw [sublatticeSpinHalfSquared_eq_sum_dot]
  rw [Matrix.sum_mulVec]
  simp_rw [Matrix.sum_mulVec]
  have hterm : ∀ x y : Λ, (if A x ∧ A y then (spinHalfDot x y) else 0).mulVec
        (basisVec σ) =
      (if A x ∧ A y then (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ)) else 0) •
        basisVec σ := by
    intro x y
    by_cases hAA : A x ∧ A y
    · obtain ⟨hAx, hAy⟩ := hAA
      rw [if_pos ⟨hAx, hAy⟩, if_pos ⟨hAx, hAy⟩]
      by_cases hxy : x = y
      · subst hxy
        rw [if_pos rfl, spinHalfDot_self]
        rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      · rw [if_neg hxy]
        have hpar : σ x = σ y := (hσ x hAx).trans (hσ y hAy).symm
        exact spinHalfDot_mulVec_basisVec_parallel hxy _ hpar
    · rw [if_neg hAA, if_neg hAA, Matrix.zero_mulVec, zero_smul]
  simp_rw [hterm, ← Finset.sum_smul]
  congr 1
  have hindicator_sum : ∀ (C : ℂ),
      (∑ x : Λ, if A x = true then C else 0) =
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * C := by
    intro C
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hinner : ∀ x : Λ, (∑ y : Λ,
        if A x ∧ A y then (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ)) else 0) =
      if A x = true then
        (((Finset.univ.filter (fun z : Λ => A z = true)).card : ℂ) / 4 + 1 / 2)
      else 0 := by
    intro x
    by_cases hAx : A x = true
    · rw [if_pos hAx]
      have hsplit : ∀ y : Λ,
          (if A x ∧ A y then (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ)) else 0) =
            (if A y = true then (1 / 4 : ℂ) else 0) +
              (if x = y then (1 / 2 : ℂ) else 0) := by
        intro y
        by_cases hAy : A y = true
        · rw [if_pos ⟨hAx, hAy⟩, if_pos hAy]
          by_cases hxy : x = y
          · simp [hxy]; ring
          · simp [hxy]
        · rw [if_neg (fun ⟨_, h⟩ => hAy h), if_neg hAy]
          have : x ≠ y := fun heq => hAy (heq ▸ hAx)
          simp [this]
      simp_rw [hsplit, Finset.sum_add_distrib]
      rw [hindicator_sum, Finset.sum_ite_eq Finset.univ x (fun _ => (1 / 2 : ℂ))]
      rw [if_pos (Finset.mem_univ _)]
      ring
    · rw [if_neg hAx]
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [if_neg]
      rintro ⟨h, _⟩; exact hAx h
  simp_rw [hinner]
  rw [hindicator_sum]
  ring

end LatticeSystem.Quantum
