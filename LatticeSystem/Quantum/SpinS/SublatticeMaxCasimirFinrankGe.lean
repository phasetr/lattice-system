import LatticeSystem.Quantum.SpinS.SublatticeLadderLI

/-!
# Lower bound on the dimension of the A-symmetric subspace

Scaffold for the minimal-total-spin joint eigenstate (Issue #3687 / #3674, the
final obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

The maximal `(Ŝ_A)²`-eigenspace (the A-symmetric subspace) has dimension at least
`|A|·N + 1`: the `|A|·N + 1` sublattice ladder iterates `(Ŝ_A^-)^k · |σ_⊤⟩`
(`k = 0, …, |A|·N`) lie in it (#3691) and are linearly independent (#3695).
Sublattice analogue of `totalSpinSSquared_eigenspace_finrank_ge_succ_card_mul_N`
(§2.4).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- Each Fin-indexed sublattice ladder iterate lies in the maximal `(Ŝ_A)²`-
eigenspace. -/
theorem sublatticeLadderIterateDownFin_mem_maxCasimirEigenspace (A : Λ → Bool)
    (k : Fin ((Finset.univ.filter (fun x : Λ => A x = true)).card * N + 1)) :
    sublatticeLadderIterateDownFin A N k ∈
      Module.End.eigenspace (sublatticeSpinSquaredS N A).mulVecLin
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * ((N : ℂ) / 2) *
          (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * ((N : ℂ) / 2) + 1)) := by
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
  exact sublatticeSpinSquaredS_mulVec_sublatticeLadderIterateDownS A k.val

/-- **Lower bound on the A-symmetric subspace dimension**:
`|A|·N + 1 ≤ finrank((Ŝ_A)²-eigenspace at s_A(s_A+1))`. -/
theorem sublatticeMaxCasimirEigenspace_finrank_ge (A : Λ → Bool) :
    (Finset.univ.filter (fun x : Λ => A x = true)).card * N + 1 ≤
      Module.finrank ℂ
        (Module.End.eigenspace (sublatticeSpinSquaredS N A).mulVecLin
          (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * ((N : ℂ) / 2) *
            (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * ((N : ℂ) / 2) + 1))) := by
  set E := Module.End.eigenspace (sublatticeSpinSquaredS N A).mulVecLin
    (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * ((N : ℂ) / 2) *
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * ((N : ℂ) / 2) + 1)) with hE
  let f : Fin ((Finset.univ.filter (fun x : Λ => A x = true)).card * N + 1) → E :=
    fun k => ⟨sublatticeLadderIterateDownFin A N k,
      sublatticeLadderIterateDownFin_mem_maxCasimirEigenspace A k⟩
  have hLI : LinearIndependent ℂ f := by
    have h := sublatticeLadderIterateDownFin_linearIndependent (Λ := Λ) (N := N) A
    exact (LinearIndependent.of_comp E.subtype) (by simpa [f] using h)
  have := hLI.fintype_card_le_finrank
  simpa using this

end LatticeSystem.Quantum
