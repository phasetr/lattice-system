import LatticeSystem.Quantum.SpinS.JointLadderIterate
import LatticeSystem.Quantum.SpinS.AllAlignedStateMagSubspace

/-!
# Total magnetization of the joint ladder iterates

Scaffold for the minimal-total-spin joint eigenstate (Issue #3687 / #3674, the
final obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

Each total ladder lowering (`Ŝ_A^-` or `Ŝ_¬A^-`) drops the total magnetization by
one, so the joint iterate `(Ŝ_A^-)^{k_A} (Ŝ_¬A^-)^{k_B} · |σ_⊤⟩` lies in the total
magnetization subspace at `|V|·N/2 − (k_A + k_B)`.  Within a fixed total
magnetization, the joint iterates are distinguished by their `A`-magnetization, so
their count is the dimension input for the rank–nullity argument producing the
minimal-total-spin highest-weight state.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- A `k`-fold sublattice lowering drops the total magnetization by `k`. -/
theorem sublatticeSpinSOpMinus_pow_mulVec_mem_magSubspaceS (A : Λ → Bool) (k : ℕ)
    {M : ℂ} {v : (Λ → Fin (N + 1)) → ℂ} (hv : v ∈ magSubspaceS Λ N M) :
    ((sublatticeSpinSOpMinus N A) ^ k).mulVec v ∈ magSubspaceS Λ N (M - (k : ℂ)) := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    have hstep := sublatticeSpinSOpMinus_mulVec_mem_magSubspaceS_of_mem (N := N) A ih
    have hval : (M - (k : ℂ)) - 1 = M - ((k + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hval] at hstep
    have hpow : ((sublatticeSpinSOpMinus N A) ^ (k + 1)).mulVec v =
        (sublatticeSpinSOpMinus N A).mulVec (((sublatticeSpinSOpMinus N A) ^ k).mulVec v) := by
      rw [pow_succ', Matrix.mulVec_mulVec]
    rw [hpow]
    exact hstep

/-- **Total magnetization of the joint iterate**:
`(Ŝ_A^-)^{k_A} (Ŝ_¬A^-)^{k_B} · |σ_⊤⟩ ∈ magSubspaceS V N (|V|·N/2 − (k_A + k_B))`. -/
theorem jointLadderIterateDownS_mem_magSubspaceS (A : Λ → Bool) (kA kB : ℕ) :
    jointLadderIterateDownS A N kA kB ∈
      magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - ((kA + kB : ℕ) : ℂ)) := by
  unfold jointLadderIterateDownS
  -- all-up lies in the top total-magnetization sector.
  have h0 : allAlignedStateS Λ N (0 : Fin (N + 1)) ∈
      magSubspaceS Λ N ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) := by
    have := allAlignedStateS_mem_magSubspaceS (V := Λ) (N := N) (0 : Fin (N + 1))
    simpa using this
  -- lower kB times on ¬A, then kA times on A.
  have hkB := sublatticeSpinSOpMinus_pow_mulVec_mem_magSubspaceS (fun x => ! A x) kB h0
  have hkA := sublatticeSpinSOpMinus_pow_mulVec_mem_magSubspaceS A kA hkB
  have hval : (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (kB : ℂ)) - (kA : ℂ) =
      ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - ((kA + kB : ℕ) : ℂ) := by push_cast; ring
  rwa [hval] at hkA

end LatticeSystem.Quantum
