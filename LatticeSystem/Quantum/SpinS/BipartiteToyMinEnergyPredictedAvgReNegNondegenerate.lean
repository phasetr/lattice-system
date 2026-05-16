import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyStrictNeg

/-!
# `avg < 0` at non-degenerate (`|A| ≥ 1, |¬A| ≥ 1, N ≥ 1`)

PR #2817: `(pmA).re < 0` at non-degenerate. Applying to both
orientations (note `|¬A| ≥ 1` and `|¬(¬A)| = |A| ≥ 1` swap roles):

  `0 < |A|, 0 < |¬A|, 0 < N
    → ((predicted_min A).re + (predicted_min ¬A).re) / 2 < 0`.

Both orientations are strictly negative, so their arithmetic mean
is too. Strict version of PR #3042 (`avg ≤ 0` unconditional).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`avg < 0` at non-degenerate**: both orientations strictly
negative (PR #2817), so average is too. Strict version of PR #3042. -/
theorem bipartiteToyMinEnergyPredicted_avg_complement_re_neg_of_nondegenerate
    (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N) :
    ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 < 0 := by
  -- Apply PR #2817 to both A and ¬A. For ¬A: cardinalities are swapped, both still positive.
  have hA_neg :=
    bipartiteToyMinEnergyPredicted_re_neg_of_nondegenerate (Λ := Λ) A N hA hAc hN
  -- For the complement orientation, the filter cardinalities of ¬A swap roles.
  have hcardA_notA : (Finset.univ.filter (fun x : Λ => (fun y => ! A y) x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := rfl
  have hcardAc_notA : (Finset.univ.filter (fun x : Λ => (! ((fun y => ! A y) x)) = true)).card =
      (Finset.univ.filter (fun x : Λ => A x = true)).card := by
    congr 1
    ext x
    simp [Finset.mem_filter]
  have hpos_notA : 0 < (Finset.univ.filter (fun x : Λ => (fun y => ! A y) x = true)).card := by
    rw [hcardA_notA]; exact hAc
  have hpos_notAc : 0 < (Finset.univ.filter (fun x : Λ => (! ((fun y => ! A y) x)) = true)).card := by
    rw [hcardAc_notA]; exact hA
  have hB_neg :=
    bipartiteToyMinEnergyPredicted_re_neg_of_nondegenerate (Λ := Λ) (fun x => ! A x) N
      hpos_notA hpos_notAc hN
  linarith

end LatticeSystem.Quantum
