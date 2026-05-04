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
private theorem spinHalfDot_apply_diag_of_ne_antiparallel
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

end LatticeSystem.Quantum
