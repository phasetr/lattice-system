import LatticeSystem.Quantum.SpinS.JointLadderRaiseA
import LatticeSystem.Quantum.SpinS.SublatticeLadderIdentity

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Raising the `¬A`-index of the joint ladder iterate

Scaffold for the minimal-total-spin joint eigenstate (Issue #3687 / #3674, the
final obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

`Ŝ_¬A^+` lowers the `¬A`-ladder index of the joint iterate:
`Ŝ_¬A^+ (Ŝ_A^-)^{k_A} (Ŝ_¬A^-)^{k_B+1} |σ_⊤⟩ =
  (k_B+1)(|¬A|·N − k_B) · (Ŝ_A^-)^{k_A} (Ŝ_¬A^-)^{k_B} |σ_⊤⟩`.

The complement companion of `sublatticeSpinSOpPlus_mulVec_jointLadderIterateDownS_succA`
(#3701): `Ŝ_¬A^+` commutes past `(Ŝ_A^-)^{k_A}` (cross-sublattice), and the inner
single-sublattice ladder identity (#3693 at `¬A`) lowers the `¬A`-index.  Together
with the `A`-version, `Ŝ⁺_tot = Ŝ_A^+ + Ŝ_¬A^+` maps the diagonal family into the
span of the lower-index diagonal family — the rank–nullity step.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Raising the `¬A`-index**: `Ŝ_¬A^+ · jointIterate k_A (k_B+1) =
(k_B+1)(|¬A|·N − k_B) · jointIterate k_A k_B`. -/
theorem sublatticeSpinSOpPlus_complement_mulVec_jointLadderIterateDownS_succB
    (A : Λ → Bool) (kA kB : ℕ) :
    (sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec (jointLadderIterateDownS A N kA (kB + 1)) =
      (((kB + 1 : ℕ) : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card * (N : ℂ) - (kB : ℂ))) •
        jointLadderIterateDownS A N kA kB := by
  -- The joint iterate as `(Ŝ_A^-)^{kA}` applied to the `¬A`-iterate.
  have hj : ∀ m : ℕ, jointLadderIterateDownS A N kA m =
      ((sublatticeSpinSOpMinus N A) ^ kA).mulVec
        (sublatticeLadderIterateDownS (fun x => ! A x) N m) := fun m => rfl
  rw [hj (kB + 1), Matrix.mulVec_mulVec,
      ((sublatticeSpinSOpMinus_cross_commute_plus (Λ := Λ) (N := N) A).symm.pow_right kA).eq,
      ← Matrix.mulVec_mulVec,
      sublatticeSpinSOpPlus_mulVec_sublatticeLadderIterateDownS_succ (Λ := Λ) (N := N) (fun x => ! A x) kB,
      Matrix.mulVec_smul, ← hj kB]

end LatticeSystem.Quantum
