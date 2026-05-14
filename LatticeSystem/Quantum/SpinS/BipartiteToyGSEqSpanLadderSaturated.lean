import LatticeSystem.Quantum.SpinS.BipartiteToyGSEqSaturatedJointZero

/-!
# Predicted GS at saturated case = span of ladder iterates

Composition of PR #2796 (`predicted GS = saturatedFerromagnetJointEigenspace
0 N` at the saturated case) with PR #2768
(`saturatedFerromagnetJointEigenspace J N = Submodule.span ℂ
(Set.range (ladderIterateUp V N))` for any `J`) gives:

  `bipartiteToyGroundStateSubspacePredicted A N
     = Submodule.span ℂ (Set.range (ladderIterateUp Λ N))`

when `|¬A| = 0`. This is the **concrete basis identification** of
the saturated-case predicted GS subspace: it is precisely the
linear span of the `(2 m_max + 1)` ladder iterates
`{(Ŝ^-_tot)^k · |σ_⊤⟩ : k ∈ Fin (|V|·N + 1)}`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **Predicted GS at saturated case = span of ladder iterates**:
when `|¬A| = 0`,
`bipartiteToyGroundStateSubspacePredicted A N =
Submodule.span ℂ (Set.range (ladderIterateUp Λ N))`. -/
theorem bipartiteToyGroundStateSubspacePredicted_eq_span_ladderIterateUp_of_cardNotA_zero
    [Nonempty Λ] (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N =
      Submodule.span ℂ (Set.range (ladderIterateUp Λ N)) := by
  rw [bipartiteToyGroundStateSubspacePredicted_eq_saturatedFerromagnetJointEigenspace_zero_of_cardNotA_zero
        A h,
      saturatedFerromagnetJointEigenspace_eq_span_ladderIterateUp]

end LatticeSystem.Quantum
