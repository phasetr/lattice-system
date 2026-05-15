import LatticeSystem.Quantum.SpinS.CardBothZeroIffEmpty

/-!
# At least one sublattice has positive cardinality on a non-empty lattice

For a non-empty lattice `Λ`, at least one sublattice is non-empty:

  `Nonempty Λ → 0 < |A| ∨ 0 < |¬A|`.

Direct corollary of PR #2872.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool)

/-- **At least one sublattice is non-empty on a non-empty lattice**:
`0 < |A| ∨ 0 < |¬A|`. -/
theorem cardA_pos_or_cardNotA_pos_of_nonempty [Nonempty Λ] :
    0 < (Finset.univ.filter (fun x : Λ => A x = true)).card ∨
      0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  have hcard_pos : 0 < Fintype.card Λ := Fintype.card_pos
  have hne : (((Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∧
       (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) → False) := by
    intro hboth
    have h := (cardA_and_cardNotA_zero_iff_card_eq_zero (Λ := Λ) A).mp hboth
    omega
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hAc⟩ := hcon
  apply hne
  refine ⟨?_, ?_⟩
  · omega
  · omega

end LatticeSystem.Quantum
