import LatticeSystem.Quantum.SpinS.SublatticeLadderIterate

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Joint (two-sublattice) ladder iterates of the all-up state

Scaffold for the minimal-total-spin joint eigenstate (Issue #3687 / #3674, the
final obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

The two-dimensional family `(Ŝ_A^-)^{k_A} (Ŝ_¬A^-)^{k_B} · |σ_⊤⟩` lies in the joint
maximal-sublattice-Casimir eigenspace `W = jointSublatticeCasimirEigenspace A N`
(`(Ŝ_A)² = s_A(s_A+1)` and `(Ŝ_¬A)² = s_B(s_B+1)`): each sublattice Casimir commutes
with both ladder powers (same sublattice via `Commute.pow_right`, cross sublattice
via the complement commute), and `|σ_⊤⟩` realizes both maximal Casimirs.  These
iterates (one per `(A,¬A)`-magnetization pair) are the spanning family of `W`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The two-sublattice ladder iterate `(Ŝ_A^-)^{k_A} (Ŝ_¬A^-)^{k_B} · |σ_⊤⟩`. -/
noncomputable def jointLadderIterateDownS (A : Λ → Bool) (N : ℕ) (kA kB : ℕ) :
    (Λ → Fin (N + 1)) → ℂ :=
  ((sublatticeSpinSOpMinus N A) ^ kA).mulVec
    (((sublatticeSpinSOpMinus N (fun x => ! A x)) ^ kB).mulVec
      (allAlignedStateS Λ N (0 : Fin (N + 1))))

/-- The joint iterate as a single `mulVec` of the product of ladder powers. -/
private theorem jointLadderIterateDownS_eq_prod (A : Λ → Bool) (kA kB : ℕ) :
    jointLadderIterateDownS A N kA kB =
      ((sublatticeSpinSOpMinus N A) ^ kA *
        (sublatticeSpinSOpMinus N (fun x => ! A x)) ^ kB).mulVec
        (allAlignedStateS Λ N (0 : Fin (N + 1))) := by
  unfold jointLadderIterateDownS
  rw [Matrix.mulVec_mulVec]

/-- `(Ŝ_A)²` acts on the joint iterate by the maximal `A`-Casimir `s_A(s_A+1)`. -/
theorem sublatticeSpinSquaredS_mulVec_jointLadderIterateDownS (A : Λ → Bool) (kA kB : ℕ) :
    (sublatticeSpinSquaredS N A).mulVec (jointLadderIterateDownS A N kA kB) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * ((N : ℂ) / 2) *
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * ((N : ℂ) / 2) + 1)) •
        jointLadderIterateDownS A N kA kB := by
  rw [jointLadderIterateDownS_eq_prod]
  have hcomm : Commute (sublatticeSpinSquaredS N A)
      ((sublatticeSpinSOpMinus N A) ^ kA *
        (sublatticeSpinSOpMinus N (fun x => ! A x)) ^ kB) :=
    ((sublatticeSpinSquaredS_commute_sublatticeSpinSOpMinus (Λ := Λ) (N := N) A).pow_right
        kA).mul_right
      ((sublatticeSpinSquaredS_commute_sublatticeSpinSOpMinus_complement (Λ := Λ) (N := N)
          A).pow_right kB)
  rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec,
      sublatticeSpinSquaredS_mulVec_allAlignedStateS_zero (N := N) A, Matrix.mulVec_smul]

/-- `(Ŝ_¬A)²` acts on the joint iterate by the maximal `¬A`-Casimir `s_B(s_B+1)`. -/
theorem sublatticeSpinSquaredS_complement_mulVec_jointLadderIterateDownS (A : Λ → Bool) (kA kB : ℕ)
    :
    (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec (jointLadderIterateDownS A N kA kB) =
      (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) * ((N : ℂ) / 2) *
        (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) * ((N : ℂ) / 2) + 1)) •
        jointLadderIterateDownS A N kA kB := by
  rw [jointLadderIterateDownS_eq_prod]
  -- `Commute (Ŝ_¬A)² (Ŝ_A^-)`: the complement commute at `¬A` (with `¬¬A = A`).
  have hcomm_cross : Commute (sublatticeSpinSquaredS N (fun x => ! A x)) (sublatticeSpinSOpMinus N
      A) := by
    have h := sublatticeSpinSquaredS_commute_sublatticeSpinSOpMinus_complement
      (Λ := Λ) (N := N) (fun x => ! A x)
    have hnotnot : (fun x => ! (! A x)) = A := by funext x; simp
    rwa [hnotnot] at h
  have hcomm : Commute (sublatticeSpinSquaredS N (fun x => ! A x))
      ((sublatticeSpinSOpMinus N A) ^ kA *
        (sublatticeSpinSOpMinus N (fun x => ! A x)) ^ kB) :=
    (hcomm_cross.pow_right kA).mul_right
      ((sublatticeSpinSquaredS_commute_sublatticeSpinSOpMinus (Λ := Λ) (N := N)
        (fun x => ! A x)).pow_right kB)
  rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec,
      sublatticeSpinSquaredS_mulVec_allAlignedStateS_zero (N := N) (fun x => ! A x),
      Matrix.mulVec_smul]

end LatticeSystem.Quantum
