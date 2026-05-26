import LatticeSystem.Quantum.SpinS.JointLadderIterate
import LatticeSystem.Quantum.SpinS.SublatticeLadderIterateMag
import LatticeSystem.Quantum.SpinS.SublatticeMagWeightComponent

/-!
# Sublattice magnetization of the joint ladder iterates

Scaffold for the minimal-total-spin joint eigenstate (Issue #3687 / #3674, the
final obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

The joint iterate `(Ŝ_A^-)^{k_A} (Ŝ_¬A^-)^{k_B} · |σ_⊤⟩` lies in the `A`-sublattice
magnetization subspace at `s_A − k_A`: the complement lowering `Ŝ_¬A^-` preserves the
`A`-magnetization (it commutes with `Ŝ_A^(3)`), while each `Ŝ_A^-` drops it by one.
Distinct `k_A` therefore give distinct `A`-magnetizations, which (with non-vanishing)
yields the linear independence of the diagonal family for the rank–nullity argument.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- `Ŝ_A^(3)` commutes with the complement lowering `Ŝ_¬A^-`. -/
theorem sublatticeSpinSOp3_cross_commute_sublatticeSpinSOpMinus (A : Λ → Bool) :
    Commute (sublatticeSpinSOp3 N A) (sublatticeSpinSOpMinus N (fun x => ! A x)) := by
  rw [sublatticeSpinSOpMinus_eq_sub]
  exact (sublatticeSpinSOp3_cross_commute_op1 (Λ := Λ) (N := N) A).sub_right
    ((sublatticeSpinSOp3_cross_commute_op2 (Λ := Λ) (N := N) A).smul_right Complex.I)

/-- A `k`-fold complement lowering `(Ŝ_¬A^-)^k` preserves the `A`-magnetization. -/
theorem sublatticeSpinSOpMinus_complement_pow_mulVec_mem_sublatticeMagSubspaceS (A : Λ → Bool)
    (k : ℕ) {M : ℂ} {v : (Λ → Fin (N + 1)) → ℂ} (hv : v ∈ sublatticeMagSubspaceS A M) :
    ((sublatticeSpinSOpMinus N (fun x => ! A x)) ^ k).mulVec v ∈ sublatticeMagSubspaceS A M := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    have hpow : ((sublatticeSpinSOpMinus N (fun x => ! A x)) ^ (k + 1)).mulVec v =
        (sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
          (((sublatticeSpinSOpMinus N (fun x => ! A x)) ^ k).mulVec v) := by
      rw [pow_succ', Matrix.mulVec_mulVec]
    rw [hpow]
    exact mem_sublatticeMagSubspaceS_of_commute A M
      (sublatticeSpinSOpMinus N (fun x => ! A x))
      (sublatticeSpinSOp3_cross_commute_sublatticeSpinSOpMinus A) ih

/-- A `k`-fold sublattice lowering `(Ŝ_A^-)^k` drops the `A`-magnetization by `k`. -/
theorem sublatticeSpinSOpMinus_pow_mulVec_mem_sublatticeMagSubspaceS (A : Λ → Bool)
    (k : ℕ) {M : ℂ} {v : (Λ → Fin (N + 1)) → ℂ} (hv : v ∈ sublatticeMagSubspaceS A M) :
    ((sublatticeSpinSOpMinus N A) ^ k).mulVec v ∈ sublatticeMagSubspaceS A (M - (k : ℂ)) := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    have hstep := sublatticeSpinSOpMinus_mulVec_mem_sublatticeMagSubspaceS_of_mem A ih
    have hval : (M - (k : ℂ)) - 1 = M - ((k + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hval] at hstep
    have hpow : ((sublatticeSpinSOpMinus N A) ^ (k + 1)).mulVec v =
        (sublatticeSpinSOpMinus N A).mulVec (((sublatticeSpinSOpMinus N A) ^ k).mulVec v) := by
      rw [pow_succ', Matrix.mulVec_mulVec]
    rw [hpow]
    exact hstep

/-- **`A`-magnetization of the joint iterate**:
`(Ŝ_A^-)^{k_A} (Ŝ_¬A^-)^{k_B} · |σ_⊤⟩ ∈ sublatticeMagSubspaceS A (s_A − k_A)`. -/
theorem jointLadderIterateDownS_mem_sublatticeMagSubspaceS (A : Λ → Bool) (kA kB : ℕ) :
    jointLadderIterateDownS A N kA kB ∈
      sublatticeMagSubspaceS A
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2 - (kA : ℂ)) := by
  unfold jointLadderIterateDownS
  -- all-up lies in the top `A`-magnetization sector `s_A`.
  have h0 : allAlignedStateS Λ N (0 : Fin (N + 1)) ∈
      sublatticeMagSubspaceS A
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2) := by
    have h := basisVecS_mem_sublatticeMagSubspaceS A (allAlignedConfigS Λ N (0 : Fin (N + 1)))
    rw [sublatticeMagEigenvalueS_allUp A] at h
    simpa [allAlignedStateS] using h
  -- `(Ŝ_¬A^-)^{kB}` preserves the `A`-magnetization; `(Ŝ_A^-)^{kA}` drops it by `kA`.
  have hkB := sublatticeSpinSOpMinus_complement_pow_mulVec_mem_sublatticeMagSubspaceS A kB h0
  exact sublatticeSpinSOpMinus_pow_mulVec_mem_sublatticeMagSubspaceS A kA hkB

end LatticeSystem.Quantum
