import LatticeSystem.Quantum.SpinS.ParityReachable
import LatticeSystem.Quantum.SpinS.AxisSwapParityBlock

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Parity-block reachability preserves the magnetization parity

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Every parity-block move changes the total occupation `magSumS` by an **even** amount (transverse:
`+1` and `−1`; bond parity hop: `+1, +1` or `−1, −1`; single-ion: `±2`).  Hence
`ParityReachableS` configurations lie in the same magnetization-parity block — confirming that the
reachability relation is internal to each block (the well-formedness needed for the parity-block
irreducibility argument).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- A single parity-block step preserves the magnetization parity. -/
theorem parityStepS_magSumS_parity_eq {G : SimpleGraph V} {σ σ' : V → Fin (N + 1)}
    (h : ParityStepS G σ σ') : magSumS σ' % 2 = magSumS σ % 2 := by
  rcases h with hrl | hbond | hsi
  · obtain ⟨x, y, hadj, hval, hagree⟩ := hrl
    have hp := magSumS_add_parity_eq_of_agree_off_two_site hadj.ne hagree
    rcases hval with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega
  · obtain ⟨x, y, hadj, hval, hagree⟩ := hbond
    have hp := magSumS_add_parity_eq_of_agree_off_two_site hadj.ne hagree
    rcases hval with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega
  · obtain ⟨x, hval, hagree⟩ := hsi
    have hp := magSumS_add_parity_eq_of_agree_off_site x hagree
    omega

/-- `ParityReachableS` configurations have equal magnetization parity. -/
theorem parityReachableS_magSumS_parity_eq {G : SimpleGraph V} {σ σ' : V → Fin (N + 1)}
    (h : ParityReachableS G σ σ') : magSumS σ' % 2 = magSumS σ % 2 := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [parityStepS_magSumS_parity_eq hstep, ih]

end LatticeSystem.Quantum
