import LatticeSystem.Quantum.SpinS.SublatticeSpin
import LatticeSystem.Quantum.SpinS.MultiSiteDot
import LatticeSystem.Quantum.SpinS.SpinSDotAllAlignedZero

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

/-! ## Sublattice spin squared as a double-sum of spin-dot products -/

/-- `(Ŝ_A)² = Σ_{x ∈ A} Σ_{y ∈ A} Ŝ_x · Ŝ_y`. Specialisation of
`sublatticeSpinSDot_eq_sum_sum` to `B = A`, since `(Ŝ_A)² = Ŝ_A · Ŝ_A`
definitionally. -/
theorem sublatticeSpinSquaredS_eq_sum_dot (A : Λ → Bool) :
    sublatticeSpinSquaredS N A =
      ∑ x : Λ, ∑ y : Λ,
        if A x ∧ A y then spinSDot x y N else 0 :=
  sublatticeSpinSDot_eq_sum_sum N A A

/-! ## Casimir eigenvalue on the all-up state -/

/-- `(Ŝ_A)² · |σ_⊤⟩ = ((|A|·N/2)·(|A|·N/2+1)) · |σ_⊤⟩` for any
sublattice indicator `A`. The all-up basis state is an eigenvector
of the `A`-sublattice Casimir at the maximum-spin value `J_A = |A|·N/2`,
which is the highest-weight Casimir of the `(|A|·N/2)`-irrep of SU(2)
on the `A`-subsystem.

Proof: from the bilinear expansion
`(Ŝ_A)² = Σ_{x,y ∈ A} Ŝ_x · Ŝ_y`, the `|A|` diagonal terms contribute
`N(N+2)/4` each (`spinSDot_self`) and the `|A|² − |A|` off-diagonal
terms contribute `N²/4` each (`spinSDot_mulVec_allAlignedStateS_zero_of_ne`).
Algebraic simplification:
`|A|·N(N+2)/4 + (|A|²-|A|)·N²/4 = (|A|·N/2)·(|A|·N/2 + 1)`. -/
theorem sublatticeSpinSquaredS_mulVec_allAlignedStateS_zero (A : Λ → Bool) :
    (sublatticeSpinSquaredS N A).mulVec
        (allAlignedStateS Λ N (0 : Fin (N + 1))) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((N : ℂ) / 2) *
          (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) + 1)) •
        allAlignedStateS Λ N (0 : Fin (N + 1)) := by
  rw [sublatticeSpinSquaredS_eq_sum_dot]
  rw [Matrix.sum_mulVec]
  simp_rw [Matrix.sum_mulVec]
  -- Each term `(if A x ∧ A y then spinSDot x y N else 0) · |⊤⟩` is a
  -- scalar multiple of `|⊤⟩`. Diagonal x = y gives `N(N+2)/4`,
  -- off-diagonal gives `N²/4`.
  have hterm : ∀ x y : Λ, (if A x ∧ A y then (spinSDot x y N) else 0).mulVec
        (allAlignedStateS Λ N (0 : Fin (N + 1))) =
      (if A x ∧ A y then
        (if x = y then ((N : ℂ) * (N + 2) / 4) else ((N : ℂ) * (N : ℂ) / 4))
        else 0) •
        allAlignedStateS Λ N (0 : Fin (N + 1)) := by
    intro x y
    by_cases hAA : A x ∧ A y
    · rw [if_pos hAA, if_pos hAA]
      by_cases hxy : x = y
      · subst hxy
        rw [if_pos rfl, spinSDot_self]
        rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      · rw [if_neg hxy]
        exact spinSDot_mulVec_allAlignedStateS_zero_of_ne hxy
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
  -- Compute the double sum: |A| diagonal at N(N+2)/4 + (|A|² - |A|) off-diagonal at N²/4.
  have hinner : ∀ x : Λ, (∑ y : Λ,
        if A x ∧ A y then
          (if x = y then ((N : ℂ) * (N + 2) / 4) else ((N : ℂ) * (N : ℂ) / 4))
          else 0) =
      if A x = true then
        (((Finset.univ.filter (fun z : Λ => A z = true)).card : ℂ) *
            ((N : ℂ) * (N : ℂ) / 4) + ((N : ℂ) / 2))
      else 0 := by
    intro x
    by_cases hAx : A x = true
    · rw [if_pos hAx]
      have hsplit : ∀ y : Λ,
          (if A x ∧ A y then
            (if x = y then ((N : ℂ) * (N + 2) / 4) else ((N : ℂ) * (N : ℂ) / 4))
            else 0) =
            (if A y = true then ((N : ℂ) * (N : ℂ) / 4) else 0) +
              (if x = y then ((N : ℂ) / 2) else 0) := by
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
      rw [hindicator_sum,
          Finset.sum_ite_eq Finset.univ x (fun _ => ((N : ℂ) / 2))]
      rw [if_pos (Finset.mem_univ _)]
    · rw [if_neg hAx]
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [if_neg]
      rintro ⟨h, _⟩; exact hAx h
  simp_rw [hinner]
  rw [hindicator_sum]
  ring

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
