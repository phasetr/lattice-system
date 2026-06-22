import LatticeSystem.Quantum.SpinS.AllAlignedState

/-!
# All-aligned-state magnetization shifts: single-step on the all-aligned state (foundation)

Foundational layer extracted from `AllAlignedStateMagShift.lean` for build speed.  This file
collects the single-step magnetic-quantum-number shifts on the all-aligned state.

The generic single-step shifts with their iterated form and the ladder-operator
magnetization-subspace shifts are kept in the capstone module `AllAlignedStateMagShift.lean`.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Single-step magnetic-quantum-number shifts on the all-aligned state

The Cartan relations `[Ŝ^z_{tot}, Ŝ^±_{tot}] = ±Ŝ^±_{tot}` immediately
give the single-step magnetic-quantum-number shifts:

  `Ŝ^z_{tot} · Ŝ^-_{tot} · |σ_⊤⟩ = (|V|·N/2 − 1) · Ŝ^-_{tot} · |σ_⊤⟩`
  `Ŝ^z_{tot} · Ŝ^+_{tot} · |σ_⊥⟩ = (−|V|·N/2 + 1) · Ŝ^+_{tot} · |σ_⊥⟩`

These are the operator-level form of "the single application of
`Ŝ^-_{tot}` (resp. `Ŝ^+_{tot}`) shifts the magnetic quantum number
by `−1` (resp. `+1`)" — the building block for the iterated-ladder
labelling along the full `J_{tot} = |V|·S` irreducible SU(2)
representation (deferred to a follow-up textbook unit using
inductive Cartan).
-/

/-- **Single-step magnetic-quantum-number shift** along the lowering
ladder from the all-up state:

  `Ŝ^z_{tot} · Ŝ^-_{tot} · |σ_⊤⟩ = (|V|·N/2 − 1) · Ŝ^-_{tot} · |σ_⊤⟩`.

Direct corollary of `totalSpinSOp3_commutator_totalSpinSOpMinus`
(Cartan relation, PR #883) and `totalSpinSOp3_mulVec_allAlignedStateS`
(`Ŝ^z` eigenvalue of all-up). -/
theorem totalSpinSOp3_mulVec_totalSpinSOpMinus_mulVec_allAlignedStateS_zero :
    (totalSpinSOp3 V N).mulVec
      ((totalSpinSOpMinus V N).mulVec
        (allAlignedStateS V N (0 : Fin (N + 1)))) =
      ((Fintype.card V : ℂ) * (N : ℂ) / 2 - 1) •
        (totalSpinSOpMinus V N).mulVec
          (allAlignedStateS V N (0 : Fin (N + 1))) := by
  -- Cartan: Ŝ^z · Ŝ^- = Ŝ^- · Ŝ^z - Ŝ^- (rearranged form of #883).
  have hcart : (totalSpinSOp3 V N : ManyBodyOpS V N) * totalSpinSOpMinus V N =
      totalSpinSOpMinus V N * totalSpinSOp3 V N -
        totalSpinSOpMinus V N := by
    have h := totalSpinSOp3_commutator_totalSpinSOpMinus (V := V) (N := N)
    -- h : Ŝ^z · Ŝ^- − Ŝ^- · Ŝ^z = −Ŝ^-.
    have h' : (totalSpinSOp3 V N : ManyBodyOpS V N) * totalSpinSOpMinus V N =
        -totalSpinSOpMinus V N + totalSpinSOpMinus V N * totalSpinSOp3 V N :=
      sub_eq_iff_eq_add.mp h
    rw [h']; abel
  rw [Matrix.mulVec_mulVec, hcart, Matrix.sub_mulVec,
    ← Matrix.mulVec_mulVec, totalSpinSOp3_mulVec_allAlignedStateS,
    magEigenvalueS_allAlignedConfigS, Matrix.mulVec_smul]
  rw [show ((0 : Fin (N + 1)).val : ℂ) = 0 from by simp,
    mul_zero, sub_zero]
  -- Goal: m_max • (Ŝ^- · |⊤⟩) - (Ŝ^- · |⊤⟩) = (m_max - 1) • (Ŝ^- · |⊤⟩).
  rw [sub_smul, one_smul]

/-- **Single-step magnetic-quantum-number shift** along the raising
ladder from the all-down state:

  `Ŝ^z_{tot} · Ŝ^+_{tot} · |σ_⊥⟩ = (−|V|·N/2 + 1) · Ŝ^+_{tot} · |σ_⊥⟩`. -/
theorem totalSpinSOp3_mulVec_totalSpinSOpPlus_mulVec_allAlignedStateS_last :
    (totalSpinSOp3 V N).mulVec
      ((totalSpinSOpPlus V N).mulVec
        (allAlignedStateS V N (Fin.last N))) =
      (-((Fintype.card V : ℂ) * (N : ℂ) / 2) + 1) •
        (totalSpinSOpPlus V N).mulVec
          (allAlignedStateS V N (Fin.last N)) := by
  -- Cartan: Ŝ^z · Ŝ^+ = Ŝ^+ · Ŝ^z + Ŝ^+ (rearranged form of #883).
  have hcart : (totalSpinSOp3 V N : ManyBodyOpS V N) * totalSpinSOpPlus V N =
      totalSpinSOpPlus V N * totalSpinSOp3 V N + totalSpinSOpPlus V N := by
    have h := totalSpinSOp3_commutator_totalSpinSOpPlus (V := V) (N := N)
    -- h : Ŝ^z · Ŝ^+ − Ŝ^+ · Ŝ^z = Ŝ^+.
    have h' : (totalSpinSOp3 V N : ManyBodyOpS V N) * totalSpinSOpPlus V N =
        totalSpinSOpPlus V N + totalSpinSOpPlus V N * totalSpinSOp3 V N :=
      sub_eq_iff_eq_add.mp h
    rw [h']; abel
  rw [Matrix.mulVec_mulVec, hcart, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, totalSpinSOp3_mulVec_allAlignedStateS,
    magEigenvalueS_allAlignedConfigS, Matrix.mulVec_smul]
  rw [show ((Fin.last N).val : ℂ) = N from by simp [Fin.last]]
  rw [show ((Fintype.card V : ℂ) * (N : ℂ) / 2 -
        (Fintype.card V : ℂ) * (N : ℂ)) =
      -((Fintype.card V : ℂ) * (N : ℂ) / 2) from by ring]
  -- Goal: -(m_max) • (Ŝ^+ · |⊥⟩) + (Ŝ^+ · |⊥⟩) = (-m_max + 1) • (Ŝ^+ · |⊥⟩).
  rw [add_smul, one_smul]

end LatticeSystem.Quantum
