import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeel

/-!
# Complement-Néel toy-Hamiltonian expectation

The Néel state on the **complement** sublattice `¬A` has the same
toy-Hamiltonian expectation as the original Néel state:

  `⟨Φ_Néel(¬A) | Ĥ_toy_S(A) | Φ_Néel(¬A)⟩ = −|A|·|¬A|·N²/2`.

This is the sublattice-swap symmetry of the toy-Hamiltonian
expectation: the toy Hamiltonian is invariant under `A ↔ ¬A`
(via `heisenbergToyHamiltonianS_eq_two_sublatticeSpinSDot` +
`sublatticeSpinSDot_complement_comm`), and the complement Néel
state's basis-state configuration has the opposite spin pattern
but produces the same per-bond contribution `m_x · m_y = -N²/4`.

This completes the pair of Néel-orientation expectations: both
`Φ_Néel(A)` (PR #1093) and `Φ_Néel(¬A)` (this PR) sit at the same
toy-Hamiltonian expectation, demonstrating the sublattice-swap
symmetry that underlies the choice-of-orientation freedom in
Tasaki §2.5 Theorem 2.3 (`Φ_Néel(A)` for `|A| ≥ |¬A|`,
`Φ_Néel(¬A)` for `|¬A| ≥ |A|`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Diagonal matrix entry of `Ĥ_toy_S(A)` at the complement Néel
configuration**:
`(Ĥ_toy_S(A)) (neelConfigOfS ¬A N) (neelConfigOfS ¬A N) = −|A|·|¬A|·N²/2`.

Same value as the original-orientation diagonal
(`heisenbergToyHamiltonianS_apply_diag_neel`, PR #1070): the per-
pair contribution `m_x · m_y = -N²/4` only depends on the
antiparallel-on-bipartite-bonds structure, which holds in both
orientations. -/
theorem heisenbergToyHamiltonianS_apply_diag_neel_complement
    (A : Λ → Bool) (N : ℕ) :
    (heisenbergToyHamiltonianS (Λ := Λ) A N)
        (neelConfigOfS (fun x => ! A x) N)
        (neelConfigOfS (fun x => ! A x) N) =
      -(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          ((N : ℂ) * (N : ℂ)) / 2) := by
  -- H_toy_S A is sublattice-swap invariant; reuse the same
  -- per-pair argument as PR #1070 with the complement orientation.
  -- The cleanest route: relate to H_toy_S (¬A) via swap invariance,
  -- and apply PR #1070's diagonal formula.
  have h_complement_complement : (fun x : Λ => ! (! A x)) = A := by
    funext x; rcases A x <;> simp
  have h_swap : heisenbergToyHamiltonianS (Λ := Λ) A N =
      heisenbergToyHamiltonianS (Λ := Λ) (fun x => ! A x) N := by
    rw [heisenbergToyHamiltonianS_eq_two_sublatticeSpinSDot,
        heisenbergToyHamiltonianS_eq_two_sublatticeSpinSDot]
    rw [h_complement_complement]
    rw [sublatticeSpinSDot_complement_comm]
  rw [h_swap]
  -- Now goal: (H_toy_S (¬A)) (neelConfigOfS ¬A N) (neelConfigOfS ¬A N) = ...
  have hcalc := heisenbergToyHamiltonianS_apply_diag_neel
    (Λ := Λ) (fun x => ! A x) N
  rw [hcalc]
  -- The RHS has the cardinality of {x : !(!A x) = true};
  -- reduce ¬¬A to A at the filter level.
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  rw [hfilter_eq]
  ring

/-- **Complement-Néel toy-Hamiltonian expectation**:
`⟨Φ_Néel(¬A) | Ĥ_toy_S(A) | Φ_Néel(¬A)⟩ = −|A|·|¬A|·N²/2`.

Combines `basisVecS_expectation_eq_diagonal` with the complement-
orientation diagonal entry above. -/
theorem neelStateOfS_complement_heisenbergToyHamiltonianS_expectation
    (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS (fun x => ! A x) N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS (fun x => ! A x) N)) =
      -(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          ((N : ℂ) * (N : ℂ)) / 2) := by
  unfold neelStateOfS
  rw [basisVecS_expectation_eq_diagonal]
  exact heisenbergToyHamiltonianS_apply_diag_neel_complement A N

end LatticeSystem.Quantum
