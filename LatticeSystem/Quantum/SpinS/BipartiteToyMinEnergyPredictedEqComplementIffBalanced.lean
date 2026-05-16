import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyComplement

/-!
# `predicted_min_energy A = predicted_min_energy (¬A) ↔ |A| = |¬A|` at `N ≥ 1`

The gap identity (existing `_sub_complement`):
`predicted_min_energy A − predicted_min_energy (¬A) = (|A| − |¬A|)·N`.

At `N ≥ 1`, this difference is zero iff `|A| = |¬A|`. Hence

  `predicted_min_energy A = predicted_min_energy (¬A) ↔ |A| = |¬A|`
  at `N ≥ 1`.

The two orientations give the same predicted min energy **iff**
balanced sublattices. Direct from the gap identity + `N ≥ 1` cancellation.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Iff**: `predicted_min_energy A = predicted_min_energy (¬A) ↔
balanced` at `N ≥ 1`. -/
theorem bipartiteToyMinEnergyPredicted_eq_complement_iff_card_eq
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    bipartiteToyMinEnergyPredicted (Λ := Λ) A N =
        bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card =
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  rw [show (bipartiteToyMinEnergyPredicted (Λ := Λ) A N =
        bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N) ↔
        bipartiteToyMinEnergyPredicted (Λ := Λ) A N -
          bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N = 0 from
        sub_eq_zero.symm,
      bipartiteToyMinEnergyPredicted_sub_complement A N]
  -- `(|A| - |¬A|) · N = 0 ↔ |A| = |¬A|` at `N ≥ 1`.
  have hN_ne : (N : ℂ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp hN
  rw [mul_eq_zero]
  constructor
  · rintro (heq | hN0)
    · have : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) =
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) := by
        linear_combination heq
      exact_mod_cast this
    · exact absurd hN0 hN_ne
  · intro h
    left
    have : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) =
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) := by
      exact_mod_cast h
    linear_combination this

end LatticeSystem.Quantum
