import LatticeSystem.Quantum.SpinS.SublatticeMaxCasimirEigenspaceNeBot

/-!
# The complement maximal-Casimir eigenspace is non-trivial

Scaffold for the minimal-total-spin joint eigenstate (Issue #3687 / #3674, the
final obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

The `(Ŝ_¬A)²`-eigenspace at the maximal complement Casimir `s_B(s_B+1)` (the
"`¬A`-symmetric subspace") is non-trivial: the all-up state lies in it.  This is
the complement companion of `sublatticeMaxCasimirEigenspace_ne_bot`, obtained by
applying it to the negated sublattice `fun x => ! A x`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **The complement maximal sublattice-Casimir eigenspace is non-trivial**: the
`(Ŝ_¬A)²` eigenspace at `s_B(s_B+1)` contains the non-zero all-up state. -/
theorem sublatticeMaxCasimirEigenspace_complement_ne_bot [Nonempty Λ] (A : Λ → Bool) :
    Module.End.eigenspace (sublatticeSpinSquaredS N (fun x => ! A x)).mulVecLin
        (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) * ((N : ℂ) / 2) *
          (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) * ((N : ℂ) / 2) + 1)) ≠ ⊥ :=
  sublatticeMaxCasimirEigenspace_ne_bot (Λ := Λ) (N := N) (fun x => ! A x)

end LatticeSystem.Quantum
