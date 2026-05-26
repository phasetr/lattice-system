import LatticeSystem.Quantum.SpinS.SublatticeMagnetization
import LatticeSystem.Quantum.SpinS.SublatticeSpinLadder

/-!
# Sublattice raising/lowering shift the sublattice magnetization grading

Scaffold for the sublattice Casimir spectral max bound (Issue #3658, the final
obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

The sublattice ladder operators step the sublattice grading
(`SublatticeMagnetization.lean`) by one unit:
`Ŝ_A^+ : sublatticeMagSubspaceS A M → sublatticeMagSubspaceS A (M+1)` and
`Ŝ_A^- : sublatticeMagSubspaceS A M → sublatticeMagSubspaceS A (M−1)`.

These are the sublattice analogues of `totalSpinSOpPlus_mulVec_mem_magSubspaceS_of_mem`,
derived from the sublattice grading commutators
`[Ŝ_A^(3), Ŝ_A^+] = Ŝ_A^+` and `[Ŝ_A^(3), Ŝ_A^-] = −Ŝ_A^-`
(`sublatticeSpinSOp3_commutator_sublatticeSpinSOpPlus/Minus`).  They drive the
termination of the highest-weight raising procedure for `(Ŝ_A)²`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- `Ŝ_A^+ · v ∈ sublatticeMagSubspaceS A (M + 1)` for
`v ∈ sublatticeMagSubspaceS A M`. -/
theorem sublatticeSpinSOpPlus_mulVec_mem_sublatticeMagSubspaceS_of_mem
    (A : Λ → Bool) {M : ℂ} {v : (Λ → Fin (N + 1)) → ℂ}
    (hv : v ∈ sublatticeMagSubspaceS A M) :
    (sublatticeSpinSOpPlus N A).mulVec v ∈ sublatticeMagSubspaceS A (M + 1) := by
  rw [mem_sublatticeMagSubspaceS_iff] at hv ⊢
  have h := sublatticeSpinSOp3_commutator_sublatticeSpinSOpPlus (Λ := Λ) (N := N) A
  have hcomm : sublatticeSpinSOp3 N A * sublatticeSpinSOpPlus N A =
      sublatticeSpinSOpPlus N A * sublatticeSpinSOp3 N A + sublatticeSpinSOpPlus N A := by
    have hadd : sublatticeSpinSOp3 N A * sublatticeSpinSOpPlus N A =
        (sublatticeSpinSOp3 N A * sublatticeSpinSOpPlus N A -
          sublatticeSpinSOpPlus N A * sublatticeSpinSOp3 N A) +
        sublatticeSpinSOpPlus N A * sublatticeSpinSOp3 N A := by abel
    rw [hadd, h]; abel
  rw [Matrix.mulVec_mulVec, hcomm, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul, add_smul, one_smul]

/-- `Ŝ_A^- · v ∈ sublatticeMagSubspaceS A (M − 1)` for
`v ∈ sublatticeMagSubspaceS A M`. -/
theorem sublatticeSpinSOpMinus_mulVec_mem_sublatticeMagSubspaceS_of_mem
    (A : Λ → Bool) {M : ℂ} {v : (Λ → Fin (N + 1)) → ℂ}
    (hv : v ∈ sublatticeMagSubspaceS A M) :
    (sublatticeSpinSOpMinus N A).mulVec v ∈ sublatticeMagSubspaceS A (M - 1) := by
  rw [mem_sublatticeMagSubspaceS_iff] at hv ⊢
  have h := sublatticeSpinSOp3_commutator_sublatticeSpinSOpMinus (Λ := Λ) (N := N) A
  have hcomm : sublatticeSpinSOp3 N A * sublatticeSpinSOpMinus N A =
      sublatticeSpinSOpMinus N A * sublatticeSpinSOp3 N A - sublatticeSpinSOpMinus N A := by
    have hadd : sublatticeSpinSOp3 N A * sublatticeSpinSOpMinus N A =
        (sublatticeSpinSOp3 N A * sublatticeSpinSOpMinus N A -
          sublatticeSpinSOpMinus N A * sublatticeSpinSOp3 N A) +
        sublatticeSpinSOpMinus N A * sublatticeSpinSOp3 N A := by abel
    rw [hadd, h]; abel
  rw [Matrix.mulVec_mulVec, hcomm, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul, sub_smul, one_smul]

end LatticeSystem.Quantum
