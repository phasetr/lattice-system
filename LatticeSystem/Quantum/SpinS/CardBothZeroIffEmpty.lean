import LatticeSystem.Quantum.SpinS.CardSumEqFintype

/-!
# Both saturated edges simultaneously ⇔ empty lattice

The trivial bipartition `|A| = 0 = |¬A|` happens iff the
underlying lattice is empty:

  `(|A| = 0 ∧ |¬A| = 0) ↔ Fintype.card Λ = 0`.

Direct corollary of PR #2870 (`cardA_add_cardNotA_eq_card`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool)

/-- **Both saturated edges ⇔ empty lattice**:
`(|A| = 0 ∧ |¬A| = 0) ↔ Fintype.card Λ = 0`. -/
theorem cardA_and_cardNotA_zero_iff_card_eq_zero :
    ((Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∧
       (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) ↔
      Fintype.card Λ = 0 := by
  constructor
  · rintro ⟨hA, hAc⟩
    have := cardA_add_cardNotA_eq_card (Λ := Λ) A
    omega
  · intro h
    have := cardA_add_cardNotA_eq_card (Λ := Λ) A
    omega

end LatticeSystem.Quantum
