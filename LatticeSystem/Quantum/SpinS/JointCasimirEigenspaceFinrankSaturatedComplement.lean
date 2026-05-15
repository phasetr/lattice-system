import LatticeSystem.Quantum.SpinS.JointCasimirEigenspaceFinrankSaturated

/-!
# Complement saturated joint Casimir eigenspace finrank: `|Λ|·N + 1`

PR #2927 gave `finrank (jointSublatticeCasimirEigenspace A N) =
|Λ|·N + 1` at `|¬A| = 0`. The complement mirror at `|A| = 0`:

  `finrank (jointSublatticeCasimirEigenspace (fun x => ! A x) N)
     = |Λ|·N + 1`   at `|A| = 0`,

since `|¬¬A| = |A| = 0` reduces to the original case applied to `¬A`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Complement saturated joint Casimir finrank**: at `|A| = 0`,
`finrank (jointSublatticeCasimirEigenspace (fun x => ! A x) N) = |Λ|·N + 1`. -/
theorem jointSublatticeCasimirEigenspace_complement_finrank_eq_succ_card_mul_N_of_cardA_zero
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    Module.finrank ℂ
        (jointSublatticeCasimirEigenspace (Λ := Λ) (fun x => ! A x) N) =
      Fintype.card Λ * N + 1 := by
  apply jointSublatticeCasimirEigenspace_finrank_eq_succ_card_mul_N_of_cardNotA_zero
    (fun x => ! A x) N
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  rw [hfilter_eq]
  exact h

end LatticeSystem.Quantum
