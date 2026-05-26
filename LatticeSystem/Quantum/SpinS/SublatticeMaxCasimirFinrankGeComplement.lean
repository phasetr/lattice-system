import LatticeSystem.Quantum.SpinS.SublatticeMaxCasimirFinrankGe

/-!
# Lower bound on the dimension of the complement-symmetric subspace

Scaffold for the minimal-total-spin joint eigenstate (Issue #3687 / #3674, the
final obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

The complement companion of `sublatticeMaxCasimirEigenspace_finrank_ge`: the
maximal `(Ŝ_¬A)²`-eigenspace (the `¬A`-symmetric subspace) has dimension at least
`|¬A|·N + 1`, by applying the `A`-version to the negated sublattice.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Lower bound on the `¬A`-symmetric subspace dimension**:
`|¬A|·N + 1 ≤ finrank((Ŝ_¬A)²-eigenspace at s_B(s_B+1))`. -/
theorem sublatticeMaxCasimirEigenspace_complement_finrank_ge (A : Λ → Bool) :
    (Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N + 1 ≤
      Module.finrank ℂ
        (Module.End.eigenspace (sublatticeSpinSquaredS N (fun x => ! A x)).mulVecLin
          (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) * ((N : ℂ) / 2) *
            (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) * ((N : ℂ) / 2) + 1))) :=
  sublatticeMaxCasimirEigenspace_finrank_ge (Λ := Λ) (N := N) (fun x => ! A x)

end LatticeSystem.Quantum
