import LatticeSystem.Quantum.SpinS.SublatticeSpinDot
import LatticeSystem.Quantum.SpinS.SublatticeSpinLadderDef
import LatticeSystem.Quantum.SpinS.MultiSiteMatrixElement
import LatticeSystem.Quantum.SpinS.Magnetization
import LatticeSystem.Quantum.SpinS.ToyHamiltonianCasimir
import LatticeSystem.Quantum.SpinS.BasisVecSOrthonormal
import LatticeSystem.Quantum.SpinS.MagConfig
import LatticeSystem.Quantum.SpinS.SingleSiteCasimirExpectation
import LatticeSystem.Quantum.SpinS.BipartiteCompleteGraph
import LatticeSystem.Quantum.SpinS.AllAlignedStateOrthogonal
import LatticeSystem.Quantum.SpinS.SingleSiteTransverseMeanZero
import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelCore

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false


/-!
# Spin-`S` Néel state and sublattice Casimir eigenvalues

Spin-`S` analog of `Quantum/MarshallLiebMattis/SublatticeCasimirNeel.lean`.

The graph-centric spin-`S` Néel state on a bipartite graph `(Λ, A)` is

  `Φ_Néel(A, N) := basisVecS (neelConfigOfS A N)`,

where `neelConfigOfS A N x := 0` if `A x = true` (highest weight) and
`Fin.last N` otherwise (lowest weight). The state is **constant on
each sublattice** at the extreme spin values.

By the constant-on-`A` Casimir eigenvalue formulas (PR #1066), the
Néel state is simultaneously an eigenvector of both sublattice
Casimirs `(Ŝ_A)²` and `(Ŝ_¬A)²` at their respective maximum-spin
eigenvalues:

  `(Ŝ_A)² · |Φ_Néel⟩ = ((|A|·N/2)·(|A|·N/2+1)) · |Φ_Néel⟩`,
  `(Ŝ_¬A)² · |Φ_Néel⟩ = ((|¬A|·N/2)·(|¬A|·N/2+1)) · |Φ_Néel⟩`.

Combined with the Casimir identity (PR #1056) and the closed form of
`Ĥ_toy_S` (PR #1060), this is a key ingredient in Tasaki's analysis
of the toy Hamiltonian's ground state in §2.5 for general spin-`S`.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 eqs. (2.5.2)–(2.5.11).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
/-! ## Per-pair `spinSDot` diagonal at the Néel configuration -/

/-- For a cross-sublattice pair `x ∈ A`, `y ∈ ¬A`, the two-site dot
product diagonal at the Néel configuration is `-N²/4`:

  `(Ŝ_x · Ŝ_y) (neel) (neel) = (N/2)·(-N/2) = -N²/4`.

Direct from `spinSDot_apply_diag_of_ne` with `m_x = N/2` and
`m_y = -N/2` from the Néel config values. -/
theorem spinSDot_apply_diag_neelConfigOfS_of_cross
    (A : Λ → Bool) (N : ℕ)
    {x y : Λ} (hAx : A x = true) (hAy : A y = false) :
    (spinSDot x y N : ManyBodyOpS Λ N)
        (neelConfigOfS A N) (neelConfigOfS A N) =
      -((N : ℂ) * (N : ℂ) / 4) := by
  have hxy : x ≠ y := by
    intro heq
    rw [heq, hAy] at hAx
    exact Bool.noConfusion hAx
  rw [spinSDot_apply_diag_of_ne hxy]
  -- m_x = N/2 since σ_x = 0; m_y = -N/2 since σ_y = Fin.last N.
  have hmx : ((N : ℂ) / 2 - (neelConfigOfS A N x).val) = (N : ℂ) / 2 := by
    unfold neelConfigOfS
    rw [if_pos hAx]; simp
  have hmy : ((N : ℂ) / 2 - (neelConfigOfS A N y).val) = -((N : ℂ) / 2) := by
    unfold neelConfigOfS
    rw [if_neg (by rw [hAy]; decide : ¬ (A y = true))]
    push_cast [Fin.last]; ring
  rw [hmx, hmy]
  ring

/-- For a same-sublattice pair `x ≠ y` with `A x = A y` (both in `A`
or both in `¬A`), the two-site dot product diagonal at the spin-`S`
Néel configuration is `+N²/4`:

  `(Ŝ_x · Ŝ_y) (neel) (neel) = (N/2)² = N²/4` when both in `A`,
  `(Ŝ_x · Ŝ_y) (neel) (neel) = (-N/2)² = N²/4` when both in `¬A`.

Direct from `spinSDot_apply_diag_of_ne`: the same `Ŝ^{(3)}` eigenvalue
on both sites yields the squared magnitude `(N/2)² = N²/4`, with sign
cancelled by the same-sign property. -/
theorem spinSDot_apply_diag_neelConfigOfS_of_same
    (A : Λ → Bool) (N : ℕ)
    {x y : Λ} (hxy : x ≠ y) (h : A x = A y) :
    (spinSDot x y N : ManyBodyOpS Λ N)
        (neelConfigOfS A N) (neelConfigOfS A N) =
      ((N : ℂ) * (N : ℂ) / 4) := by
  rw [spinSDot_apply_diag_of_ne hxy]
  by_cases hAx : A x = true
  · -- Both in A: σ_x = σ_y = 0.
    have hAy : A y = true := by rw [← h]; exact hAx
    have hmx : ((N : ℂ) / 2 - (neelConfigOfS A N x).val) = (N : ℂ) / 2 := by
      unfold neelConfigOfS
      rw [if_pos hAx]; simp
    have hmy : ((N : ℂ) / 2 - (neelConfigOfS A N y).val) = (N : ℂ) / 2 := by
      unfold neelConfigOfS
      rw [if_pos hAy]; simp
    rw [hmx, hmy]; ring
  · -- Both in ¬A: σ_x = σ_y = Fin.last N.
    have hAxF : A x = false := by
      cases hAxx : A x with
      | true => exact absurd hAxx hAx
      | false => rfl
    have hAyF : A y = false := by rw [← h]; exact hAxF
    have hmx : ((N : ℂ) / 2 - (neelConfigOfS A N x).val) = -((N : ℂ) / 2) := by
      unfold neelConfigOfS
      rw [if_neg (by rw [hAxF]; decide : ¬ (A x = true))]
      push_cast [Fin.last]; ring
    have hmy : ((N : ℂ) / 2 - (neelConfigOfS A N y).val) = -((N : ℂ) / 2) := by
      unfold neelConfigOfS
      rw [if_neg (by rw [hAyF]; decide : ¬ (A y = true))]
      push_cast [Fin.last]; ring
    rw [hmx, hmy]; ring

/-! ## Toy Hamiltonian diagonal matrix element on the Néel state -/

/-- The diagonal matrix element of the cross-sublattice spin dot
product `Ŝ_A · Ŝ_¬A` at the spin-`S` Néel configuration:

  `(Ŝ_A · Ŝ_¬A) (neel) (neel) = -|A|·|¬A|·N²/4`.

Each `(x ∈ A, y ∈ ¬A)` pair contributes
`(spinSDot x y) (neel) (neel) = m_x · m_y = (N/2)·(−N/2) = -N²/4`
(diagonal formula `spinSDot_apply_diag_of_ne`, since `A x ≠ A y`
implies `x ≠ y`); summing over the `|A|·|¬A|` such pairs gives the
result. -/
theorem sublatticeSpinSDot_apply_diag_neel (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSDot N A (fun x => ! A x))
        (neelConfigOfS A N) (neelConfigOfS A N) =
      -(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          ((N : ℂ) * (N : ℂ)) / 4) := by
  rw [sublatticeSpinSDot_eq_sum_sum]
  -- Apply at (neel, neel).
  rw [show (∑ x : Λ, ∑ y : Λ,
        if A x ∧ (fun z : Λ => ! A z) y = true then spinSDot x y N else 0)
        (neelConfigOfS A N) (neelConfigOfS A N) =
      ∑ x : Λ, ∑ y : Λ,
        ((if A x ∧ (! A y) = true then spinSDot x y N else 0)
          (neelConfigOfS A N) (neelConfigOfS A N)) from by
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.sum_apply]]
  have hterm : ∀ x y : Λ,
      ((if A x ∧ (! A y) = true then spinSDot x y N else 0)
          (neelConfigOfS A N) (neelConfigOfS A N) : ℂ) =
      if A x ∧ (! A y) = true then -((N : ℂ) * (N : ℂ) / 4) else 0 := by
    intro x y
    by_cases hAB : A x ∧ (! A y) = true
    · obtain ⟨hAx, hAy⟩ := hAB
      rw [if_pos ⟨hAx, hAy⟩, if_pos ⟨hAx, hAy⟩]
      have hxy : x ≠ y := by
        intro heq
        subst heq
        rw [hAx] at hAy
        simp at hAy
      rw [spinSDot_apply_diag_of_ne hxy]
      -- m_x = N/2 (since A x = true, neel x = 0).
      have hmx : ((N : ℂ) / 2 - (neelConfigOfS A N x).val) = (N : ℂ) / 2 := by
        unfold neelConfigOfS
        rw [if_pos hAx]; simp
      -- m_y = -N/2 (since A y = false, neel y = Fin.last N).
      have hAyF : A y = false := by
        cases h : A y
        · rfl
        · simp [h] at hAy
      have hmy : ((N : ℂ) / 2 - (neelConfigOfS A N y).val) = -((N : ℂ) / 2) := by
        unfold neelConfigOfS
        rw [if_neg (by rw [hAyF]; decide : ¬ (A y = true))]
        push_cast [Fin.last]; ring
      rw [hmx, hmy]
      ring
    · rw [if_neg hAB, if_neg hAB]
      rfl
  simp_rw [hterm]
  -- Sum: |A| · |¬A| · (-N²/4).
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

/-- The Néel-state expectation value of the spin-`S` toy Hamiltonian:

  `⟨Φ_Néel | Ĥ_toy_S | Φ_Néel⟩ = -|A|·|¬A|·N²/2`,

i.e., the diagonal matrix element at the Néel configuration is
`-|A|·|¬A|·N²/2`. This is the **negative** of the all-up state
eigenvalue (PR #1061), `+|A|·|¬A|·N²/2`.

The negative sign is the variational signature: the Néel state has
strictly lower toy-Hamiltonian expectation value than the all-up
state, demonstrating that the ground state has `S_tot < |Λ|·S` —
consistent with the Tasaki §2.5 Theorem 2.3 prediction
`S_tot = ||A|−|B||·S`. -/
theorem heisenbergToyHamiltonianS_apply_diag_neel (A : Λ → Bool) (N : ℕ) :
    (heisenbergToyHamiltonianS (Λ := Λ) A N) (neelConfigOfS A N)
        (neelConfigOfS A N) =
      - (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          ((N : ℂ) * (N : ℂ)) / 2) := by
  rw [heisenbergToyHamiltonianS_eq_two_sublatticeSpinSDot]
  rw [Matrix.smul_apply, sublatticeSpinSDot_apply_diag_neel]
  rw [smul_eq_mul]
  ring

/-! ## Ladder annihilation of the Néel state -/

/-- `Ŝ_A^+ · |Φ_Néel⟩ = 0`: the sublattice A raising operator annihilates
the Néel state, since the Néel state has `σ|_A = 0` (highest weight on
`A`). -/
theorem sublatticeSpinSOpPlus_mulVec_neelStateOfS (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSOpPlus N A).mulVec (neelStateOfS A N) = 0 := by
  unfold neelStateOfS
  refine sublatticeSpinSOpPlus_mulVec_basisVecS_zero_on N A ?_
  intro x hAx
  unfold neelConfigOfS
  rw [if_pos hAx]

/-- `Ŝ_¬A^- · |Φ_Néel⟩ = 0`: the sublattice ¬A lowering operator
annihilates the Néel state, since the Néel state has `σ|_¬A = Fin.last N`
(lowest weight on `¬A`). -/
theorem sublatticeSpinSOpMinus_complement_mulVec_neelStateOfS
    (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec (neelStateOfS A N) = 0 := by
  unfold neelStateOfS
  refine sublatticeSpinSOpMinus_mulVec_basisVecS_last_on N (fun x => ! A x) ?_
  intro x hnAx
  have hAxF : A x = false := by
    cases h : A x
    · rfl
    · simp [h] at hnAx
  unfold neelConfigOfS
  rw [if_neg (by rw [hAxF]; decide : ¬ (A x = true))]

/-- On the Néel state: `Ŝ_tot^+ · |Φ_Néel⟩ = Ŝ_¬A^+ · |Φ_Néel⟩`.
The total raising decomposes as `Ŝ_A^+ + Ŝ_¬A^+`, and `Ŝ_A^+` annihilates
the Néel state (PR #1111). -/
theorem totalSpinSOpPlus_mulVec_neelStateOfS_eq_complement
    (A : Λ → Bool) (N : ℕ) :
    (totalSpinSOpPlus Λ N).mulVec (neelStateOfS A N) =
      (sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec (neelStateOfS A N) := by
  rw [totalSpinSOpPlus_eq_sublattice_sum (N := N) A]
  rw [Matrix.add_mulVec]
  rw [sublatticeSpinSOpPlus_mulVec_neelStateOfS A N]
  rw [zero_add]

/-- On the Néel state: `Ŝ_tot^- · |Φ_Néel⟩ = Ŝ_A^- · |Φ_Néel⟩`.
The total lowering decomposes as `Ŝ_A^- + Ŝ_¬A^-`, and `Ŝ_¬A^-` annihilates
the Néel state. -/
theorem totalSpinSOpMinus_mulVec_neelStateOfS_eq_A
    (A : Λ → Bool) (N : ℕ) :
    (totalSpinSOpMinus Λ N).mulVec (neelStateOfS A N) =
      (sublatticeSpinSOpMinus N A).mulVec (neelStateOfS A N) := by
  rw [totalSpinSOpMinus_eq_sublattice_sum (N := N) A]
  rw [Matrix.add_mulVec]
  rw [sublatticeSpinSOpMinus_complement_mulVec_neelStateOfS A N]
  rw [add_zero]

/-- `Ŝ_A^+ · Ŝ_¬A^- · |Φ_Néel⟩ = 0`. The cross product of raising on `A` with
lowering on `¬A` annihilates the Néel state, since `Ŝ_¬A^- · |Φ_Néel⟩ = 0`.
Direct ingredient for `(Ŝ_tot)² · |Φ_Néel⟩` (one of the cross-ladder terms
in the Casimir identity vanishes). -/
theorem sublatticeSpinSOpPlus_complement_minus_mulVec_neelStateOfS
    (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSOpPlus N A *
        sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
        (neelStateOfS A N) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinSOpMinus_complement_mulVec_neelStateOfS]
  rw [Matrix.mulVec_zero]

/-- `Ŝ_A^- · Ŝ_¬A^- · |Φ_Néel⟩ = 0`. Cross-ladder lowering annihilates the
Néel state via `Ŝ_¬A^- · Néel = 0`. -/
theorem sublatticeSpinSOpMinus_complement_minus_mulVec_neelStateOfS
    (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSOpMinus N A *
        sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
        (neelStateOfS A N) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinSOpMinus_complement_mulVec_neelStateOfS]
  rw [Matrix.mulVec_zero]

/-- `Ŝ_¬A^+ · Ŝ_A^+ · |Φ_Néel⟩ = 0`. The cross-ladder raising annihilates the
Néel state via `Ŝ_A^+ · Néel = 0`. -/
theorem sublatticeSpinSOpComplementPlus_plus_mulVec_neelStateOfS
    (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSOpPlus N (fun x => ! A x) *
        sublatticeSpinSOpPlus N A).mulVec
        (neelStateOfS A N) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinSOpPlus_mulVec_neelStateOfS]
  rw [Matrix.mulVec_zero]

/-- `Ŝ_A^+ · Ŝ_¬A^+ · |Φ_Néel⟩ = 0`. Uses cross-sublattice commute to move
`Ŝ_A^+` to the right, then `Ŝ_A^+ · Néel = 0`. -/
theorem sublatticeSpinSOpPlus_complement_plus_mulVec_neelStateOfS
    (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSOpPlus N A *
        sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec
        (neelStateOfS A N) = 0 := by
  rw [(sublatticeSpinSOpPlus_cross_commute N A).eq]
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinSOpPlus_mulVec_neelStateOfS]
  rw [Matrix.mulVec_zero]

/-- `Ŝ_¬A^- · Ŝ_A^+ · |Φ_Néel⟩ = 0`. Cross-ladder annihilation via
`Ŝ_A^+ · Néel = 0`. -/
theorem sublatticeSpinSOpComplementMinus_plus_mulVec_neelStateOfS
    (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSOpMinus N (fun x => ! A x) *
        sublatticeSpinSOpPlus N A).mulVec
        (neelStateOfS A N) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinSOpPlus_mulVec_neelStateOfS]
  rw [Matrix.mulVec_zero]

/-- `Ŝ_A^- · Ŝ_A^+ · |Φ_Néel⟩ = 0`. Same-sublattice annihilation via
`Ŝ_A^+ · Néel = 0`. -/
theorem sublatticeSpinSOpMinus_plus_mulVec_neelStateOfS
    (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSOpMinus N A *
        sublatticeSpinSOpPlus N A).mulVec
        (neelStateOfS A N) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinSOpPlus_mulVec_neelStateOfS]
  rw [Matrix.mulVec_zero]

/-- `Ŝ_¬A^+ · Ŝ_¬A^- · |Φ_Néel⟩ = 0`. Same-sublattice annihilation via
`Ŝ_¬A^- · Néel = 0`. -/
theorem sublatticeSpinSOpComplementPlus_minus_mulVec_neelStateOfS
    (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSOpPlus N (fun x => ! A x) *
        sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
        (neelStateOfS A N) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinSOpMinus_complement_mulVec_neelStateOfS]
  rw [Matrix.mulVec_zero]


end LatticeSystem.Quantum
