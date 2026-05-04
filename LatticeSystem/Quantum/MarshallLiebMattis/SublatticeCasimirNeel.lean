import LatticeSystem.Quantum.MarshallLiebMattis.SublatticeSpinDot
import LatticeSystem.Quantum.MarshallLiebMattis.ToyHamiltonianCasimir
import LatticeSystem.Quantum.NeelState

/-!
# Sublattice Casimir eigenvalues on the Néel state

The graph-centric Néel state `Φ_Néel(A) := basisVec (neelConfigOf A)`
on a bipartite graph `(Λ, A)` (Tasaki §2.5 eq. (2.5.2)) sets
`σ x = 0` for `A x = true` and `σ x = 1` for `A x = false` — it is
**constant on each sublattice**.

By the constant-on-`A` Casimir eigenvalue formula
(`sublatticeSpinHalfSquared_mulVec_basisVec_of_const_on`), the Néel
state is simultaneously an eigenvector of both sublattice Casimirs
`(Ŝ_A)²` and `(Ŝ_¬A)²` at their respective maximum-spin eigenvalues:

  `(Ŝ_A)² · |Φ_Néel(A)⟩ = (|A|(|A|+2)/4) · |Φ_Néel(A)⟩`,
  `(Ŝ_¬A)² · |Φ_Néel(A)⟩ = (|¬A|(|¬A|+2)/4) · |Φ_Néel(A)⟩`.

Combined with the Casimir identity
`(Ŝ_tot)² = (Ŝ_A)² + 2 (Ŝ_A · Ŝ_¬A) + (Ŝ_¬A)²` and the closed form
`Ĥ_toy = (Ŝ_tot)² − (Ŝ_A)² − (Ŝ_¬A)²`, this is a key ingredient in
Tasaki's analysis of the toy Hamiltonian's ground state in §2.5.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 eqs. (2.5.2)–(2.5.11).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- `(Ŝ_A)² · |Φ_Néel(A)⟩ = (|A|(|A|+2)/4) · |Φ_Néel(A)⟩`.
The Néel state is an eigenvector of the `A`-sublattice Casimir
with maximum-spin eigenvalue, since `neelConfigOf A` is `0` on `A`. -/
theorem sublatticeSpinHalfSquared_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfSquared A).mulVec (neelStateOf A) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => A x = true)).card + 2) / 4) •
        neelStateOf A := by
  unfold neelStateOf
  refine sublatticeSpinHalfSquared_mulVec_basisVec_of_const_on A (s := 0) ?_
  intro x hAx
  unfold neelConfigOf
  rw [if_pos hAx]

/-- `(Ŝ_¬A)² · |Φ_Néel(A)⟩ = (|¬A|(|¬A|+2)/4) · |Φ_Néel(A)⟩`.
The Néel state is an eigenvector of the `¬A`-sublattice Casimir
with maximum-spin eigenvalue, since `neelConfigOf A` is `1` on `¬A`. -/
theorem sublatticeSpinHalfSquared_complement_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfSquared (fun x => ! A x)).mulVec (neelStateOf A) =
      (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card + 2) / 4) •
        neelStateOf A := by
  unfold neelStateOf
  refine sublatticeSpinHalfSquared_mulVec_basisVec_of_const_on
    (fun x => ! A x) (s := 1) ?_
  intro x hnAx
  -- `(! A x) = true ↔ A x = false`
  have hAxF : A x = false := by
    cases h : A x
    · rfl
    · simp [h] at hnAx
  unfold neelConfigOf
  rw [if_neg (by rw [hAxF]; decide : ¬ (A x = true))]

/-! ## Toy Hamiltonian Néel diagonal -/

/-- Diagonal matrix element of the spin-`1/2` two-site dot product
`Ŝ_x · Ŝ_y` at an antiparallel configuration:
`(Ŝ_x · Ŝ_y) σ σ = -1/4` when `σ x ≠ σ y` (and `x ≠ y`).

Spin-`1/2` analog of `spinSDot_apply_diag_of_ne` (spin-`S` version
`m_x · m_y = (1/2)(-1/2) = -1/4`). Extracted from
`spinHalfDot_mulVec_basisVec_antiparallel` by evaluating both sides
at `σ`. -/
theorem spinHalfDot_apply_diag_of_ne_antiparallel
    {x y : Λ} (hxy : x ≠ y) (σ : Λ → Fin 2) (h : σ x ≠ σ y) :
    (spinHalfDot x y : ManyBodyOp Λ) σ σ = -(1 / 4 : ℂ) := by
  have hmulVec := spinHalfDot_mulVec_basisVec_antiparallel hxy σ h
  -- Evaluate both sides at σ.
  have heval := congrArg (fun v => v σ) hmulVec
  simp only at heval
  -- LHS = (spinHalfDot x y) σ σ via mulVec definition.
  have hLHS : ((spinHalfDot x y).mulVec (basisVec σ)) σ =
      (spinHalfDot x y : ManyBodyOp Λ) σ σ := by
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single σ]
    · rw [basisVec_self, mul_one]
    · intros τ _ hτ
      rw [basisVec_of_ne hτ, mul_zero]
    · intro h; exact (h (Finset.mem_univ _)).elim
  -- RHS: (1/2) basisVec (basisSwap σ x y) σ - (1/4) basisVec σ σ.
  have hRHS : ((1 / 2 : ℂ) • basisVec (basisSwap σ x y) -
      (1 / 4 : ℂ) • basisVec σ) σ = -(1 / 4 : ℂ) := by
    rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply]
    rw [basisVec_self]
    -- basisSwap σ x y ≠ σ since σ_x ≠ σ_y.
    have hswap_ne : basisSwap σ x y ≠ σ := by
      intro heq
      have hx : basisSwap σ x y x = σ x := congr_fun heq x
      unfold basisSwap at hx
      rw [Function.update_of_ne hxy] at hx
      rw [Function.update_self] at hx
      exact h hx.symm
    rw [basisVec_of_ne (Ne.symm hswap_ne)]
    simp
  rw [hLHS] at heval
  rw [heval, hRHS]

/-- Diagonal of the spin-`1/2` toy Hamiltonian on the Néel
configuration:

  `(Ĥ_toy A) (neelConfigOf A) (neelConfigOf A) = -|A|·|¬A|/2`.

Spin-`1/2` (`N=1`) specialisation of the spin-`S` formula
`-|A|·|¬A|·N²/2` (PR #1070). Negative of the all-up state eigenvalue
(PR α-6m's specialisation), demonstrating the variational separation
that underpins the AFM ground-state argument. -/
theorem heisenbergToyHamiltonian_apply_diag_neel (A : Λ → Bool) :
    (heisenbergToyHamiltonian A : ManyBodyOp Λ) (neelConfigOf A)
        (neelConfigOf A) =
      - (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) / 2) := by
  rw [heisenbergToyHamiltonian_eq_two_sublatticeSpinDot]
  rw [Matrix.smul_apply, sublatticeSpinDot_eq_sum_sum]
  rw [smul_eq_mul]
  -- Apply the bilinear sum at (neel, neel).
  rw [show (∑ x : Λ, ∑ y : Λ,
        if A x ∧ (fun z : Λ => ! A z) y = true then spinHalfDot x y else 0)
        (neelConfigOf A) (neelConfigOf A) =
      ∑ x : Λ, ∑ y : Λ,
        ((if A x ∧ (! A y) = true then spinHalfDot x y else 0)
          (neelConfigOf A) (neelConfigOf A)) from by
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.sum_apply]]
  have hterm : ∀ x y : Λ,
      ((if A x ∧ (! A y) = true then spinHalfDot x y else 0)
          (neelConfigOf A) (neelConfigOf A) : ℂ) =
      if A x ∧ (! A y) = true then -(1 / 4 : ℂ) else 0 := by
    intro x y
    by_cases hAB : A x ∧ (! A y) = true
    · obtain ⟨hAx, hAy⟩ := hAB
      rw [if_pos ⟨hAx, hAy⟩, if_pos ⟨hAx, hAy⟩]
      have hxy : x ≠ y := by
        intro heq
        subst heq
        rw [hAx] at hAy
        simp at hAy
      -- σ x ≠ σ y at the Néel config.
      have hAyF : A y = false := by
        cases h : A y
        · rfl
        · simp [h] at hAy
      have hne : neelConfigOf A x ≠ neelConfigOf A y := by
        unfold neelConfigOf
        rw [if_pos hAx, if_neg (by rw [hAyF]; decide : ¬ A y = true)]
        decide
      exact spinHalfDot_apply_diag_of_ne_antiparallel hxy _ hne
    · rw [if_neg hAB, if_neg hAB]
      rfl
  simp_rw [hterm]
  -- Sum: |A| · |¬A| · (-1/4).
  have hindicator_outer : ∀ (x : Λ) (C : ℂ),
      (∑ y : Λ, if A x ∧ (! A y) = true then C else 0) =
        if A x then ((Finset.univ.filter (fun y : Λ => (! A y) = true)).card : ℂ) * C
        else 0 := by
    intro x C
    by_cases hAx : A x = true
    · rw [if_pos hAx]
      classical
      rw [show (∑ y : Λ, if A x ∧ (! A y) = true then C else 0) =
          ∑ y : Λ, if (! A y) = true then C else 0 from by
            refine Finset.sum_congr rfl fun y _ => ?_
            by_cases hAy : (! A y) = true
            · rw [if_pos ⟨hAx, hAy⟩, if_pos hAy]
            · rw [if_neg, if_neg hAy]
              rintro ⟨_, h⟩; exact hAy h]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    · rw [if_neg hAx]
      apply Finset.sum_eq_zero
      intro y _
      rw [if_neg]
      rintro ⟨h, _⟩; exact hAx h
  simp_rw [hindicator_outer]
  classical
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

/-! ## Magnetization on the Néel state -/

/-- `magnetization Λ (neelConfigOf A) = |A| − |¬A|`: the Néel
configuration contributes `+1` on `A` (since `σ x = 0`) and `-1` on
`¬A` (since `σ x = 1`).

Spin-`1/2` specialisation of `magSumS_neelConfigOfS` (PR #1068). -/
theorem magnetization_neelConfigOf (A : Λ → Bool) :
    magnetization Λ (neelConfigOf A) =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℤ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℤ) := by
  unfold magnetization neelConfigOf
  classical
  -- Each term: spinSign(if A x then 0 else 1) = if A x then 1 else -1.
  have hterm : ∀ x : Λ,
      spinSign (if A x then (0 : Fin 2) else 1) =
        if A x = true then (1 : ℤ) else -1 := by
    intro x
    by_cases hAx : A x = true
    · rw [if_pos hAx, if_pos hAx]; simp [spinSign]
    · cases h : A x
      · rw [if_neg, if_neg]
        · simp [spinSign]
        · simp [h]
        · simp [h]
      · exact absurd h hAx
  simp_rw [hterm]
  have hsplit : ∀ x : Λ, (if A x = true then (1 : ℤ) else -1) =
      (if A x = true then (1 : ℤ) else 0) +
        (if (! A x) = true then (-1 : ℤ) else 0) := by
    intro x
    by_cases hAx : A x = true
    · rw [if_pos hAx, if_pos hAx]
      have : (! A x) = false := by simp [hAx]
      rw [if_neg]
      · ring
      · simp [this]
    · cases h : A x
      · simp
      · exact absurd h hAx
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_filter, Finset.sum_const]
  rw [← Finset.sum_filter, Finset.sum_const]
  push_cast
  ring

/-- `Ŝ_tot^(3) · |Φ_Néel⟩ = ((|A| − |¬A|)/2) · |Φ_Néel⟩`. The spin-`1/2`
Néel state is a `Ŝ_tot^(3)`-eigenvector with magnetization
`(|A| − |¬A|)/2`. For `|A| = |¬A|` the magnetization is zero (e.g.,
chain / square / cube); for `|A| ≠ |¬A|` (the Tasaki Theorem 2.3 case),
the absolute value `||A| − |¬A||/2 = ||A| − |¬A||·S` matches the
conjectured ground-state total spin.

Spin-`1/2` specialisation of `totalSpinSOp3_mulVec_neelStateOfS` (PR #1068). -/
theorem totalSpinHalfOp3_mulVec_neelStateOf (A : Λ → Bool) :
    (totalSpinHalfOp3 Λ).mulVec (neelStateOf A) =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) / 2) •
        neelStateOf A := by
  unfold neelStateOf
  rw [totalSpinHalfOp3_mulVec_basisVec_eq_magnetization]
  rw [magnetization_neelConfigOf]
  push_cast
  ring_nf

/-! ## Ladder annihilation of the Néel state -/

/-- `Ŝ_A^+ · |Φ_Néel⟩ = 0` (highest weight on A). Spin-`1/2` mirror of γ-4 step 65. -/
theorem sublatticeSpinHalfOpPlus_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfOpPlus A).mulVec (neelStateOf A) = 0 := by
  unfold neelStateOf
  refine sublatticeSpinHalfOpPlus_mulVec_basisVec_zero_on A ?_
  intro x hAx
  unfold neelConfigOf
  rw [if_pos hAx]

/-- `Ŝ_¬A^- · |Φ_Néel⟩ = 0` (lowest weight on ¬A). -/
theorem sublatticeSpinHalfOpMinus_complement_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfOpMinus (fun x => ! A x)).mulVec (neelStateOf A) = 0 := by
  unfold neelStateOf
  refine sublatticeSpinHalfOpMinus_mulVec_basisVec_one_on (fun x => ! A x) ?_
  intro x hnAx
  have hAxF : A x = false := by
    cases h : A x
    · rfl
    · simp [h] at hnAx
  unfold neelConfigOf
  rw [if_neg (by rw [hAxF]; decide : ¬ (A x = true))]

/-- On the spin-`1/2` Néel state: `Ŝ_tot^+ · |Φ_Néel⟩ = Ŝ_¬A^+ · |Φ_Néel⟩`.
Spin-`1/2` mirror of γ-4 step 67. -/
theorem totalSpinHalfOpPlus_mulVec_neelStateOf_eq_complement (A : Λ → Bool) :
    (totalSpinHalfOpPlus Λ).mulVec (neelStateOf A) =
      (sublatticeSpinHalfOpPlus (fun x => ! A x)).mulVec (neelStateOf A) := by
  rw [totalSpinHalfOpPlus_eq_sublattice_sum A]
  rw [Matrix.add_mulVec]
  rw [sublatticeSpinHalfOpPlus_mulVec_neelStateOf A]
  rw [zero_add]

/-- On the spin-`1/2` Néel state: `Ŝ_tot^- · |Φ_Néel⟩ = Ŝ_A^- · |Φ_Néel⟩`. -/
theorem totalSpinHalfOpMinus_mulVec_neelStateOf_eq_A (A : Λ → Bool) :
    (totalSpinHalfOpMinus Λ).mulVec (neelStateOf A) =
      (sublatticeSpinHalfOpMinus A).mulVec (neelStateOf A) := by
  rw [totalSpinHalfOpMinus_eq_sublattice_sum A]
  rw [Matrix.add_mulVec]
  rw [sublatticeSpinHalfOpMinus_complement_mulVec_neelStateOf A]
  rw [add_zero]

/-- `Ŝ_A^(3) · |Φ_Néel⟩ = (|A|/2) · |Φ_Néel⟩`. The sublattice z-axis acts
as `|A|/2` on the spin-`1/2` Néel state (highest weight on A:
`neelConfigOf A x = 0` for `x ∈ A`, contributing `+1/2`). Spin-`1/2`
mirror of γ-4 step 73 (`sublatticeSpinSOp3_mulVec_neelStateOfS`). -/
theorem sublatticeSpinHalfOp3_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfOp3 A).mulVec (neelStateOf A) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) / 2) •
        neelStateOf A := by
  unfold sublatticeSpinHalfOp3 neelStateOf
  rw [Matrix.sum_mulVec]
  rw [show (∑ x : Λ, (if A x then onSite x spinHalfOp3 else 0 : ManyBodyOp Λ).mulVec
        (basisVec (neelConfigOf A))) =
      ∑ x : Λ, (if A x then ((1 : ℂ) / 2) else 0) •
        basisVec (neelConfigOf A) from by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hA : A x = true
    · rw [if_pos hA, if_pos hA]
      rw [onSite_spinHalfOp3_mulVec_basisVec]
      have hσx : neelConfigOf A x = 0 := by
        unfold neelConfigOf; rw [if_pos hA]
      rw [hσx]
      rfl
    · cases h : A x
      · rw [if_neg, if_neg]
        · rw [Matrix.zero_mulVec, zero_smul]
        · simp
        · simp
      · exact absurd h hA]
  rw [← Finset.sum_smul]
  congr 1
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

/-- `Ŝ_¬A^(3) · |Φ_Néel⟩ = -(|¬A|/2) · |Φ_Néel⟩`. The complement sublattice
z-axis acts as `-|¬A|/2` on the spin-`1/2` Néel state (lowest weight on
¬A: `neelConfigOf A x = 1` for `x ∉ A`, contributing `-1/2`). Spin-`1/2`
mirror of γ-4 step 74 (`sublatticeSpinSOp3_complement_mulVec_neelStateOfS`). -/
theorem sublatticeSpinHalfOp3_complement_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfOp3 (fun x => ! A x)).mulVec (neelStateOf A) =
      (-(((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) / 2)) •
        neelStateOf A := by
  unfold sublatticeSpinHalfOp3 neelStateOf
  rw [Matrix.sum_mulVec]
  rw [show (∑ x : Λ, (if (! A x) then onSite x spinHalfOp3 else 0 : ManyBodyOp Λ).mulVec
        (basisVec (neelConfigOf A))) =
      ∑ x : Λ, (if (! A x) then -((1 : ℂ) / 2) else 0) •
        basisVec (neelConfigOf A) from by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hA : (! A x) = true
    · rw [if_pos hA, if_pos hA]
      rw [onSite_spinHalfOp3_mulVec_basisVec]
      have hAxF : A x = false := by
        cases h : A x
        · rfl
        · simp [h] at hA
      have hσx : neelConfigOf A x = 1 := by
        unfold neelConfigOf
        rw [if_neg (by rw [hAxF]; decide : ¬ A x = true)]
      rw [hσx]
      rfl
    · cases h : (! A x)
      · rw [if_neg, if_neg]
        · rw [Matrix.zero_mulVec, zero_smul]
        · simp
        · simp
      · exact absurd h hA]
  rw [← Finset.sum_smul]
  congr 1
  have hrw : ∀ x : Λ, (if (! A x) = true then -((1 : ℂ) / 2) else 0) =
      -(if (! A x) = true then ((1 : ℂ) / 2) else 0) := by
    intro x
    by_cases h : (! A x) = true
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, neg_zero]
  rw [Finset.sum_congr rfl (fun x _ => hrw x)]
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

/-- `(Ŝ_A^(3))² · |Φ_Néel⟩ = (|A|/2)² · |Φ_Néel⟩`. Square of γ-4 step 75.
Spin-`1/2` mirror of γ-4 step 77. -/
theorem sublatticeSpinHalfOp3_sq_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp3 A).mulVec (neelStateOf A) =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) / 2) ^ 2) •
        neelStateOf A := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOp3_mulVec_neelStateOf]
  rw [Matrix.mulVec_smul]
  rw [sublatticeSpinHalfOp3_mulVec_neelStateOf]
  rw [smul_smul]
  congr 1
  ring

/-- `(Ŝ_¬A^(3))² · |Φ_Néel⟩ = (|¬A|/2)² · |Φ_Néel⟩`. Square of γ-4 step 76.
Spin-`1/2` mirror of γ-4 step 77 complement. -/
theorem sublatticeSpinHalfOp3_complement_sq_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfOp3 (fun x => ! A x) *
        sublatticeSpinHalfOp3 (fun x => ! A x)).mulVec (neelStateOf A) =
      ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) / 2) ^ 2) •
        neelStateOf A := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOp3_complement_mulVec_neelStateOf]
  rw [Matrix.mulVec_smul]
  rw [sublatticeSpinHalfOp3_complement_mulVec_neelStateOf]
  rw [smul_smul]
  congr 1
  ring

/-- `Ŝ_A^(3) · Ŝ_¬A^(3) · |Φ_Néel⟩ = -|A|·|¬A|/4 · |Φ_Néel⟩`. Spin-`1/2`
mirror of γ-4 step 79: cross-sublattice z-axis product. -/
theorem sublatticeSpinHalfOp3_cross_complement_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp3 (fun x => ! A x)).mulVec
        (neelStateOf A) =
      (-(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) /
            4)) •
        neelStateOf A := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOp3_complement_mulVec_neelStateOf]
  rw [Matrix.mulVec_smul]
  rw [sublatticeSpinHalfOp3_mulVec_neelStateOf]
  rw [smul_smul]
  congr 1
  ring

/-! ## Per-pair `spinHalfDot` diagonal at the Néel configuration -/

/-- For a cross-sublattice pair `x ∈ A`, `y ∈ ¬A`, the spin-`1/2`
two-site dot product diagonal at the Néel configuration is `-1/4`:

  `(Ŝ_x · Ŝ_y) (neel) (neel) = -1/4`.

Spin-`1/2` mirror of γ-4 step 69. -/
theorem spinHalfDot_apply_diag_neelConfigOf_of_cross
    (A : Λ → Bool)
    {x y : Λ} (hAx : A x = true) (hAy : A y = false) :
    (spinHalfDot x y : ManyBodyOp Λ) (neelConfigOf A) (neelConfigOf A) =
      -(1 / 4 : ℂ) := by
  have hxy : x ≠ y := by
    intro heq
    rw [heq, hAy] at hAx
    exact Bool.noConfusion hAx
  have hne : neelConfigOf A x ≠ neelConfigOf A y := by
    unfold neelConfigOf
    rw [if_pos hAx, if_neg (by rw [hAy]; decide : ¬ A y = true)]
    decide
  exact spinHalfDot_apply_diag_of_ne_antiparallel hxy _ hne

/-- `Ŝ_A^+ · Ŝ_¬A^- · |Φ_Néel⟩ = 0`. Spin-`1/2` mirror of γ-4 step 81:
the cross-ladder product annihilates the Néel state via `Ŝ_¬A^- · Néel = 0`. -/
theorem sublatticeSpinHalfOpPlus_complement_minus_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOpPlus A *
        sublatticeSpinHalfOpMinus (fun x => ! A x)).mulVec
        (neelStateOf A) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOpMinus_complement_mulVec_neelStateOf]
  rw [Matrix.mulVec_zero]

/-- `Ŝ_A^- · Ŝ_¬A^- · |Φ_Néel⟩ = 0`. Spin-`1/2` mirror of γ-4 step 83:
cross-ladder lowering annihilates Néel via `Ŝ_¬A^- · Néel = 0`. -/
theorem sublatticeSpinHalfOpMinus_complement_minus_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOpMinus A *
        sublatticeSpinHalfOpMinus (fun x => ! A x)).mulVec
        (neelStateOf A) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOpMinus_complement_mulVec_neelStateOf]
  rw [Matrix.mulVec_zero]

/-- `Ŝ_¬A^+ · Ŝ_A^+ · |Φ_Néel⟩ = 0`. Spin-`1/2` mirror of γ-4 step 85:
cross-ladder raising annihilates Néel via `Ŝ_A^+ · Néel = 0`. -/
theorem sublatticeSpinHalfOpComplementPlus_plus_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOpPlus (fun x => ! A x) *
        sublatticeSpinHalfOpPlus A).mulVec
        (neelStateOf A) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOpPlus_mulVec_neelStateOf]
  rw [Matrix.mulVec_zero]

/-- `Ŝ_A^+ · Ŝ_¬A^+ · |Φ_Néel⟩ = 0`. Spin-`1/2` mirror of γ-4 step 89: uses
cross-commute to swap factors, then `Ŝ_A^+ · Néel = 0`. -/
theorem sublatticeSpinHalfOpPlus_complement_plus_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOpPlus A *
        sublatticeSpinHalfOpPlus (fun x => ! A x)).mulVec
        (neelStateOf A) = 0 := by
  rw [(sublatticeSpinHalfOpPlus_cross_commute A).eq]
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOpPlus_mulVec_neelStateOf]
  rw [Matrix.mulVec_zero]

/-- `Ŝ_¬A^- · Ŝ_A^+ · |Φ_Néel⟩ = 0`. Spin-`1/2` mirror of γ-4 step 91:
trivial via `Ŝ_A^+ · Néel = 0`. -/
theorem sublatticeSpinHalfOpComplementMinus_plus_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOpMinus (fun x => ! A x) *
        sublatticeSpinHalfOpPlus A).mulVec
        (neelStateOf A) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOpPlus_mulVec_neelStateOf]
  rw [Matrix.mulVec_zero]

/-- `Ŝ_A^- · Ŝ_A^+ · |Φ_Néel⟩ = 0`. Spin-`1/2` mirror of γ-4 step 93. -/
theorem sublatticeSpinHalfOpMinus_plus_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOpMinus A * sublatticeSpinHalfOpPlus A).mulVec
        (neelStateOf A) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOpPlus_mulVec_neelStateOf]
  rw [Matrix.mulVec_zero]

/-- `Ŝ_¬A^+ · Ŝ_¬A^- · |Φ_Néel⟩ = 0`. Spin-`1/2` mirror of γ-4 step 93. -/
theorem sublatticeSpinHalfOpComplementPlus_minus_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOpPlus (fun x => ! A x) *
        sublatticeSpinHalfOpMinus (fun x => ! A x)).mulVec
        (neelStateOf A) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOpMinus_complement_mulVec_neelStateOf]
  rw [Matrix.mulVec_zero]

/-- `((Ŝ_A^(1))² + (Ŝ_A^(2))²) · |Φ_Néel⟩ = (|A|/2) · |Φ_Néel⟩`. Spin-`1/2`
mirror of γ-4 step 95: derived as `(Ŝ_A)² · Néel - (Ŝ_A^(3))² · Néel`,
where `(Ŝ_A)²` has eigenvalue `|A|(|A|+2)/4` and `(Ŝ_A^(3))²` has
eigenvalue `(|A|/2)² = |A|²/4`. -/
theorem sublatticeSpinHalfOp12sq_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp1 A +
        sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp2 A).mulVec
        (neelStateOf A) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) / 2) •
        neelStateOf A := by
  have hCasimir := sublatticeSpinHalfSquared_mulVec_neelStateOf A
  rw [sublatticeSpinHalfSquared_def] at hCasimir
  rw [Matrix.add_mulVec, Matrix.add_mulVec] at hCasimir
  have hSq3 := sublatticeSpinHalfOp3_sq_mulVec_neelStateOf A
  rw [hSq3] at hCasimir
  set k : ℂ := ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) / 2
  rw [Matrix.add_mulVec]
  have h := hCasimir
  have hab : (sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp1 A).mulVec
        (neelStateOf A) +
      (sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp2 A).mulVec
        (neelStateOf A) =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) + 2) / 4) -
        k ^ 2) • neelStateOf A := by
    rw [sub_smul]
    rw [eq_sub_iff_add_eq]
    exact h
  rw [hab]
  congr 1
  simp only [k]
  ring

/-- `Ŝ_A^+·Ŝ_A^- · |Φ_Néel⟩ = |A| · |Φ_Néel⟩`. Spin-`1/2` mirror of
γ-4 step 100: highest-weight Casimir formula 2s = |A| for s = |A|/2. -/
theorem sublatticeSpinHalfOpPlus_minus_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfOpPlus A * sublatticeSpinHalfOpMinus A).mulVec
        (neelStateOf A) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ)) •
        neelStateOf A := by
  rw [sublatticeSpinHalfOpPlus_mul_sublatticeSpinHalfOpMinus_eq]
  rw [Matrix.add_mulVec]
  rw [sublatticeSpinHalfOp12sq_mulVec_neelStateOf]
  rw [sublatticeSpinHalfOp3_mulVec_neelStateOf]
  rw [← add_smul]
  congr 1
  ring

/-- `((Ŝ_¬A^(1))² + (Ŝ_¬A^(2))²) · |Φ_Néel⟩ = (|¬A|/2) · |Φ_Néel⟩`.
Spin-`1/2` complement of γ-4 step 96. -/
theorem sublatticeSpinHalfOp12sq_complement_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfOp1 (fun x => ! A x) *
        sublatticeSpinHalfOp1 (fun x => ! A x) +
      sublatticeSpinHalfOp2 (fun x => ! A x) *
        sublatticeSpinHalfOp2 (fun x => ! A x)).mulVec
        (neelStateOf A) =
      (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) / 2) •
        neelStateOf A := by
  have hCasimir := sublatticeSpinHalfSquared_complement_mulVec_neelStateOf A
  rw [sublatticeSpinHalfSquared_def] at hCasimir
  rw [Matrix.add_mulVec, Matrix.add_mulVec] at hCasimir
  have hSq3 := sublatticeSpinHalfOp3_complement_sq_mulVec_neelStateOf A
  rw [hSq3] at hCasimir
  set k : ℂ := ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) / 2
  rw [Matrix.add_mulVec]
  have h := hCasimir
  have hab : (sublatticeSpinHalfOp1 (fun x => ! A x) *
        sublatticeSpinHalfOp1 (fun x => ! A x)).mulVec
        (neelStateOf A) +
      (sublatticeSpinHalfOp2 (fun x => ! A x) *
        sublatticeSpinHalfOp2 (fun x => ! A x)).mulVec
        (neelStateOf A) =
      ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
        (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) + 2) / 4) -
        k ^ 2) • neelStateOf A := by
    rw [sub_smul]
    rw [eq_sub_iff_add_eq]
    exact h
  rw [hab]
  congr 1
  simp only [k]
  ring

/-- `Ŝ_¬A^- · Ŝ_¬A^+ · |Φ_Néel⟩ = |¬A| · |Φ_Néel⟩`. Spin-`1/2` mirror of
γ-4 step 104 via dual Cartan identity. -/
theorem sublatticeSpinHalfOpComplementMinus_complement_plus_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOpMinus (fun x => ! A x) *
        sublatticeSpinHalfOpPlus (fun x => ! A x)).mulVec
        (neelStateOf A) =
      (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) •
        neelStateOf A := by
  rw [sublatticeSpinHalfOpMinus_mul_sublatticeSpinHalfOpPlus_eq]
  rw [Matrix.sub_mulVec]
  rw [sublatticeSpinHalfOp12sq_complement_mulVec_neelStateOf]
  rw [sublatticeSpinHalfOp3_complement_mulVec_neelStateOf]
  rw [← sub_smul]
  congr 1
  ring

end LatticeSystem.Quantum
