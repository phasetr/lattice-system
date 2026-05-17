import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelAllAlignedOrtho

/-!
# iff: `0 < (⟨Φ_↑⟩ − ⟨Φ_Néel⟩).re ↔ 0 < |A| ∧ 0 < |¬A| ∧ 0 < N`

iff form of `heisenbergToyHamiltonianS_variational_gap`. The variational
spin gap between all-up and Néel state expectations is strictly positive
exactly when the orientation pair is non-degenerate.

  `0 < (⟨Φ_↑|Ĥ_toy|Φ_↑⟩ − ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩).re
   ↔ 0 < |A| ∧ 0 < |¬A| ∧ 0 < N`.

The gap formula gives `(|A| · |¬A| · N²).re`, which is strictly
positive iff all three factors are positive.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`0 < (⟨Φ_↑⟩ − ⟨Φ_Néel⟩).re iff non-deg`**. iff form of the
existing variational gap formula. -/
theorem heisenbergToyHamiltonianS_variational_gap_re_pos_iff_nondeg
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    0 < (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re ↔
      0 < (Finset.univ.filter (fun x : Λ => A x = true)).card ∧
      0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∧
      0 < N := by
  rw [heisenbergToyHamiltonianS_variational_gap]
  -- Gap = |A|·|¬A|·N² as complex; take .re.
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re,
    Complex.natCast_im, mul_zero, zero_mul, add_zero, sub_zero]
  -- Goal: 0 < |A|·|¬A|·N²
  constructor
  · intro hpos
    -- product > 0 → all factors > 0.
    have hA_nn : (0 : ℝ) ≤
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := Nat.cast_nonneg _
    have hNotA_nn : (0 : ℝ) ≤
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := Nat.cast_nonneg _
    have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    have hN_pos : (0 : ℝ) < (N : ℝ) := by
      by_contra hz
      push Not at hz
      have hN_zero : (N : ℝ) = 0 := le_antisymm hz hN_nn
      rw [hN_zero] at hpos
      simp at hpos
    have hA_pos : (0 : ℝ) <
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by
      by_contra hz
      push Not at hz
      have hA_zero : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) = 0 :=
        le_antisymm hz hA_nn
      rw [hA_zero] at hpos
      simp at hpos
    have hNotA_pos : (0 : ℝ) <
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
      by_contra hz
      push Not at hz
      have hNotA_zero : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 :=
        le_antisymm hz hNotA_nn
      rw [hNotA_zero] at hpos
      simp at hpos
    refine ⟨?_, ?_, ?_⟩
    · exact_mod_cast hA_pos
    · exact_mod_cast hNotA_pos
    · exact_mod_cast hN_pos
  · intro ⟨hA, hNotA, hN⟩
    have hA_re : (0 : ℝ) <
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := by
      exact_mod_cast hA
    have hNotA_re : (0 : ℝ) <
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
      exact_mod_cast hNotA
    have hN_re : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hNN : (0 : ℝ) < (N : ℝ) * (N : ℝ) := mul_pos hN_re hN_re
    have hA_NotA : (0 : ℝ) <
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
      mul_pos hA_re hNotA_re
    exact mul_pos hA_NotA hNN

end LatticeSystem.Quantum
