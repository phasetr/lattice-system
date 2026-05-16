import LatticeSystem.Quantum.SpinS.NeelStateOfSPredictedSymmGap

/-!
# `⟨Néel⟩.re = (predictedSymm A).re ↔ |A| = 0 ∨ |¬A| = 0 ∨ N = 0` unconditionally

The complex-level gap identity gives
`⟨Néel⟩ − predictedSymm = (Nat.min |A| |¬A| : ℂ) · N`. Taking `.re`:

  `⟨Néel⟩.re − (predictedSymm A).re = min(|A|, |¬A|) · N`,

which vanishes iff `min(|A|, |¬A|) = 0 ∨ N = 0`, iff `|A| = 0 ∨
|¬A| = 0 ∨ N = 0`.

  `⟨Néel⟩.re = (predictedSymm A).re ↔ |A| = 0 ∨ |¬A| = 0 ∨ N = 0`.

Unconditional version of PR #3064 (which required `N ≥ 1`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **⟨Néel⟩.re = predictedSymm.re iff degenerate** unconditionally. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_eq_predictedSymm_re_iff_uncond
    (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re =
        (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 ∨
        N = 0 := by
  have hgap_eq := neelStateOfS_heisenbergToyHamiltonianS_expectation_sub_predictedSymm
    (Λ := Λ) (A := A) (N := N)
  -- Take .re of hgap_eq:
  have hre_sub : (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re -
      (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re =
      ((Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
          (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) * (N : ℝ) := by
    have := congrArg Complex.re hgap_eq
    rw [Complex.sub_re, Complex.mul_re] at this
    simp only [Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero] at this
    exact this
  -- min(|A|, |¬A|) · N = 0 ↔ min = 0 ∨ N = 0 ↔ |A| = 0 ∨ |¬A| = 0 ∨ N = 0.
  constructor
  · intro heq
    have hgap_zero : ((Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) * (N : ℝ) = 0 := by
      linarith
    rcases mul_eq_zero.mp hgap_zero with hmin | hN
    · -- min(|A|, |¬A|) : ℕ → ℝ cast = 0 → min = 0 → |A| = 0 ∨ |¬A| = 0.
      have hmin_nat : Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
          (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 := by exact_mod_cast hmin
      rcases Nat.min_eq_zero_iff.mp hmin_nat with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by exact_mod_cast hN))
  · intro hor
    have hgap_zero : ((Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) * (N : ℝ) = 0 := by
      rcases hor with hA | hAc | hN_zero
      · have : Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
            (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 := by
          rw [hA]; simp
        have hre : ((Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
            (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) = 0 := by
          exact_mod_cast this
        rw [hre]; ring
      · have : Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
            (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 := by
          rw [hAc]; simp
        have hre : ((Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
            (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) = 0 := by
          exact_mod_cast this
        rw [hre]; ring
      · have hN_re : (N : ℝ) = 0 := by exact_mod_cast hN_zero
        rw [hN_re]; ring
    linarith

end LatticeSystem.Quantum
