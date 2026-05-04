import LatticeSystem.Quantum.SpinS.SublatticeSpin
import LatticeSystem.Quantum.SpinS.MultiSiteDot

/-!
# Spin-`S` cross-sublattice spin dot product (Tasaki §2.5 Theorem 2.3 prep)

Spin-`S` analog of `Quantum/MarshallLiebMattis/SublatticeSpinDot.lean`.
The cross-sublattice spin dot product

  `Ŝ_A · Ŝ_B := Σ_α Ŝ_A^(α) Ŝ_B^(α)`

bridges the operator-level decomposition of the toy Hamiltonian
`Ĥ_toy_S` (Tasaki §2.5 (2.5.10)) into the Casimir form (Tasaki §2.5
(2.5.11)).

Establishes:

1. `sublatticeSpinSDot` definition and definitional unfolding.
2. Bilinear expansion: `Ŝ_A · Ŝ_B = Σ_{x : A x} Σ_{y : B y} Ŝ_x · Ŝ_y`.
3. Hermiticity for `B = ¬A` (each axis-`α` summand is the product of
   two commuting Hermitian operators).

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 eqs. (2.5.10)–(2.5.11).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (N : ℕ)

/-! ## Cross-sublattice spin dot product -/

/-- The spin-`S` cross-sublattice spin dot product:
`Ŝ_A · Ŝ_B := Σ_α Ŝ_A^(α) Ŝ_B^(α)`. -/
noncomputable def sublatticeSpinSDot (A B : Λ → Bool) : ManyBodyOpS Λ N :=
  sublatticeSpinSOp1 N A * sublatticeSpinSOp1 N B +
    sublatticeSpinSOp2 N A * sublatticeSpinSOp2 N B +
    sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N B

/-- `Ŝ_A · Ŝ_B = Σ_α Ŝ_A^(α) Ŝ_B^(α)` is the explicit definition. -/
@[simp] theorem sublatticeSpinSDot_def (A B : Λ → Bool) :
    sublatticeSpinSDot N A B =
      sublatticeSpinSOp1 N A * sublatticeSpinSOp1 N B +
        sublatticeSpinSOp2 N A * sublatticeSpinSOp2 N B +
        sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N B := rfl

/-! ## Bilinear expansion (helper) -/

/-- Per-axis expansion: a single product
`Ŝ_A^(α) Ŝ_B^(α)` factors as a double sum
`Σ_x Σ_y (if A x ∧ B y then onSiteS x S * onSiteS y S else 0)`. -/
private theorem sublatticeSpinSOp_mul_eq_sum_sum
    (A B : Λ → Bool) (S : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (∑ x : Λ, if A x then onSiteS x S else 0) *
        (∑ y : Λ, if B y then onSiteS y S else 0) =
      ∑ x : Λ, ∑ y : Λ,
        if A x ∧ B y then onSiteS x S * onSiteS y S else 0 := by
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

/-! ## Bilinear expansion -/

/-- The cross-sublattice spin dot product expands as a double sum
of the two-site spin dot products:
`Ŝ_A · Ŝ_B = Σ_{x : A x} Σ_{y : B y} Ŝ_x · Ŝ_y`. -/
theorem sublatticeSpinSDot_eq_sum_sum (A B : Λ → Bool) :
    sublatticeSpinSDot N A B =
      ∑ x : Λ, ∑ y : Λ,
        if A x ∧ B y then spinSDot x y N else 0 := by
  unfold sublatticeSpinSDot sublatticeSpinSOp1
    sublatticeSpinSOp2 sublatticeSpinSOp3
  rw [sublatticeSpinSOp_mul_eq_sum_sum N A B (spinSOp1 N),
      sublatticeSpinSOp_mul_eq_sum_sum N A B (spinSOp2 N),
      sublatticeSpinSOp_mul_eq_sum_sum N A B (spinSOp3 N)]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hAB : A x ∧ B y
  · simp only [if_pos hAB]
    unfold spinSDot
    rfl
  · simp only [if_neg hAB, add_zero]

/-! ## Hermiticity of `Ŝ_A · Ŝ_¬A` -/

/-- The spin-`S` cross-sublattice spin dot product `Ŝ_A · Ŝ_¬A` is
Hermitian. Each axis-`α` summand `Ŝ_A^(α) Ŝ_¬A^(α)` is the product of
two commuting Hermitian operators (cross-commute lemmas), hence
Hermitian. -/
theorem sublatticeSpinSDot_complement_isHermitian (A : Λ → Bool) :
    (sublatticeSpinSDot N A (fun x => ! A x)).IsHermitian := by
  unfold sublatticeSpinSDot
  refine ((?_ : Matrix.IsHermitian _).add ?_).add ?_
  · exact Matrix.IsHermitian.mul_of_commute
      (sublatticeSpinSOp1_isHermitian N A)
      (sublatticeSpinSOp1_isHermitian N (fun x => ! A x))
      (sublatticeSpinSOp1_cross_commute N A).eq
  · exact Matrix.IsHermitian.mul_of_commute
      (sublatticeSpinSOp2_isHermitian N A)
      (sublatticeSpinSOp2_isHermitian N (fun x => ! A x))
      (sublatticeSpinSOp2_cross_commute N A).eq
  · exact Matrix.IsHermitian.mul_of_commute
      (sublatticeSpinSOp3_isHermitian N A)
      (sublatticeSpinSOp3_isHermitian N (fun x => ! A x))
      (sublatticeSpinSOp3_cross_commute N A).eq

end LatticeSystem.Quantum
