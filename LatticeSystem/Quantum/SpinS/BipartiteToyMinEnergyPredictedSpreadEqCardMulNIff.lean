import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedSpreadLtCardMulNIff

/-!
# `spread = |Λ|·N ↔ saturated edge` at `N ≥ 1`

PR #3071: `spread < |Λ|·N ↔ |A| ≥ 1 ∧ |¬A| ≥ 1` at `N ≥ 1`.
PR #3028: `spread ≤ |Λ|·N` unconditionally.

Contraposing #3071 (and using `spread ≤ |Λ|·N`):

  `spread = |Λ|·N ↔ |A| = 0 ∨ |¬A| = 0` at `N ≥ 1`.

The orientation-spread saturates the maximum `|Λ|·N` exactly at the
saturated edge (one of the sublattices is empty).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **spread = `|Λ|·N` iff saturated edge** at `N ≥ 1`. Equality version
of PR #3071 (strict iff non-degenerate). -/
theorem bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_eq_card_mul_N_iff_saturated
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
      min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
        (Fintype.card Λ : ℝ) * (N : ℝ) ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 := by
  have hle := bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_le_card_mul_N
    (Λ := Λ) A N
  have hlt_iff := bipartiteToyMinEnergyPredicted_max_sub_min_complement_re_lt_card_mul_N_iff_nondegenerate
    (Λ := Λ) A N hN
  constructor
  · intro heq
    by_contra hne
    push Not at hne
    obtain ⟨hA_ne, hAc_ne⟩ := hne
    have hA_pos : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card :=
      Nat.pos_of_ne_zero hA_ne
    have hAc_pos : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card :=
      Nat.pos_of_ne_zero hAc_ne
    have hlt := hlt_iff.mpr ⟨hA_pos, hAc_pos⟩
    linarith
  · intro hor
    have hnot_both : ¬ (0 < (Finset.univ.filter (fun x : Λ => A x = true)).card ∧
        0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) := by
      intro ⟨hA, hAc⟩
      rcases hor with h | h
      · exact (Nat.pos_iff_ne_zero.mp hA) h
      · exact (Nat.pos_iff_ne_zero.mp hAc) h
    have hnot_lt : ¬ max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
        min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re <
          (Fintype.card Λ : ℝ) * (N : ℝ) := by
      intro hlt
      exact hnot_both (hlt_iff.mp hlt)
    linarith

end LatticeSystem.Quantum
