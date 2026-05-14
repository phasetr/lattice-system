import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy

/-!
# Predicted GS ⊆ `(Ŝ_tot)²` eigenspace at target (any `A`, `N`)

By definition (PR #2778), the predicted GS subspace is the meet
of three Casimir eigenspaces:
`(Ŝ_tot)²` at `(s_A − s_B)(s_A − s_B + 1)`, `(Ŝ_A)²` at
`s_A(s_A+1)`, `(Ŝ_¬A)²` at `s_B(s_B+1)`. So trivially:

  `bipartiteToyGroundStateSubspacePredicted A N
     ⊆ Module.End.eigenspace (Ŝ_tot)².mulVecLin
         ((s_A − s_B)(s_A − s_B + 1))`

for any `A` and `N`. This packages the `(Ŝ_tot)²` eigenspace
component of the predicted GS definition as a standalone
inclusion. Works for ANY orientation (no saturation hypothesis).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **Predicted GS ⊆ (Ŝ_tot)² eigenspace at target**: definitional
projection onto the first joint Casimir component. -/
theorem bipartiteToyGroundStateSubspacePredicted_le_totalSpinSSquaredEigenspace
    (A : Λ → Bool) (N : ℕ) :
    bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N ≤
      Module.End.eigenspace (totalSpinSSquared Λ N).mulVecLin
        ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) + 1)) := by
  intro v hv
  obtain ⟨⟨h_tot, _⟩, _⟩ := hv
  exact h_tot

set_option linter.style.longLine false in
/-- **Predicted GS ⊆ (Ŝ_A)² eigenspace at target**. -/
theorem bipartiteToyGroundStateSubspacePredicted_le_sublatticeSpinSquaredSEigenspace
    (A : Λ → Bool) (N : ℕ) :
    bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N ≤
      Module.End.eigenspace (sublatticeSpinSquaredS N A).mulVecLin
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2) *
          ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)) := by
  intro v hv
  obtain ⟨⟨_, h_A⟩, _⟩ := hv
  exact h_A

set_option linter.style.longLine false in
/-- **Predicted GS ⊆ (Ŝ_¬A)² eigenspace at target**. -/
theorem bipartiteToyGroundStateSubspacePredicted_le_sublatticeSpinSquaredS_complementEigenspace
    (A : Λ → Bool) (N : ℕ) :
    bipartiteToyGroundStateSubspacePredicted (Λ := Λ) A N ≤
      Module.End.eigenspace
        (sublatticeSpinSquaredS N (fun x => ! A x)).mulVecLin
        (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2) *
          ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)) := by
  intro v hv
  obtain ⟨_, h_B⟩ := hv
  exact h_B

end LatticeSystem.Quantum
