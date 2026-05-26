import LatticeSystem.Quantum.SpinS.JointLadderRaiseB

/-!
# Boundary annihilation of the joint ladder iterates under raising

Scaffold for the minimal-total-spin joint eigenstate (Issue #3687 / #3674, the
final obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

At the boundary indices the total raising operators annihilate the joint iterate:
`Ŝ_A^+` kills `jointIterate 0 k_B` (the `A`-block is fully up) and `Ŝ_¬A^+` kills
`jointIterate k_A 0` (the `¬A`-block is fully up).  Together with the interior
raising identities (#3701, #3702) this shows `Ŝ⁺_tot` maps the diagonal family into
the span of the lower-index family — the rank–nullity step producing the
minimal-total-spin highest-weight state.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- `Ŝ_A^+` annihilates `jointIterate 0 k_B` (the `A`-block is the highest weight). -/
theorem sublatticeSpinSOpPlus_mulVec_jointLadderIterateDownS_zeroA (A : Λ → Bool) (kB : ℕ) :
    (sublatticeSpinSOpPlus N A).mulVec (jointLadderIterateDownS A N 0 kB) = 0 := by
  unfold jointLadderIterateDownS
  rw [pow_zero, Matrix.one_mulVec, Matrix.mulVec_mulVec,
      (sublatticeSpinSOpPlus_cross_commute_minus (Λ := Λ) (N := N) A).pow_right kB |>.eq,
      ← Matrix.mulVec_mulVec, sublatticeSpinSOpPlus_mulVec_allAlignedStateS_zero (N := N) A,
      Matrix.mulVec_zero]

/-- `Ŝ_¬A^+` annihilates `jointIterate k_A 0` (the `¬A`-block is the highest weight). -/
theorem sublatticeSpinSOpPlus_complement_mulVec_jointLadderIterateDownS_zeroB (A : Λ → Bool) (kA : ℕ) :
    (sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec (jointLadderIterateDownS A N kA 0) = 0 := by
  unfold jointLadderIterateDownS
  rw [pow_zero, Matrix.one_mulVec, Matrix.mulVec_mulVec,
      ((sublatticeSpinSOpMinus_cross_commute_plus (Λ := Λ) (N := N) A).symm.pow_right kA).eq,
      ← Matrix.mulVec_mulVec,
      sublatticeSpinSOpPlus_mulVec_allAlignedStateS_zero (N := N) (fun x => ! A x),
      Matrix.mulVec_zero]

end LatticeSystem.Quantum
