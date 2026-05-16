import LatticeSystem.Quantum.SpinS.NeelToyComplementExpectation
import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelExpectations

/-!
# Sublattice-swap symmetry: `⟨Néel(A)|Ĥ_toy|Néel(A)⟩ = ⟨Néel(¬A)|Ĥ_toy|Néel(¬A)⟩`

Both Néel states (canonical orientation `A` and complement orientation
`¬A`) have the same toy-Hamiltonian expectation `−|A|·|¬A|·N²/2`,
reflecting the sublattice-swap symmetry of `bipartiteToyMinEnergyPredictedSymm`
(PR #2781 / #1093):

  `⟨Φ_Néel(A)|Ĥ_toy|Φ_Néel(A)⟩
    = ⟨Φ_Néel(¬A)|Ĥ_toy|Φ_Néel(¬A)⟩`

unconditionally. The toy-Hamiltonian doesn't care which sublattice is
labelled "A": the expectation depends only on the symmetric product
`|A|·|¬A|`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **Sublattice-swap symmetry of Néel-state toy-Hamiltonian
expectation**. Both orientations give the same value. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_eq_complement_orientation
    (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N)) =
      dotProduct (star (neelStateOfS (fun x => ! A x) N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS (fun x => ! A x) N)) := by
  rw [neelStateOfS_heisenbergToyHamiltonianS_expectation,
      neelStateOfS_complement_heisenbergToyHamiltonianS_expectation]

end LatticeSystem.Quantum
