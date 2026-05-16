import LatticeSystem.Quantum.SpinS.NeelStateOfSPredictedSymmGap

/-!
# Unconditional `(predictedSymm A).re ≤ ⟨Néel⟩.re`

PR (existing): `⟨Néel⟩ − predictedSymm = min(|A|, |¬A|)·N` at the
complex level.

Taking `.re`:

  `⟨Néel⟩.re − (predictedSymm A).re = min(|A|, |¬A|)·N ≥ 0`,

so unconditionally:

  `(predictedSymm A).re ≤ ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re`.

This is the foundational fact for Tasaki §2.5 Theorem 2.3: the Néel
state's energy is always at least the symmetric predicted minimum.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **Unconditional `(predictedSymm A).re ≤ ⟨Néel⟩.re`**: foundational
fact for Tasaki §2.5 Theorem 2.3. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_ge_predictedSymm_re
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re ≤
      (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re := by
  have hgap := neelStateOfS_heisenbergToyHamiltonianS_expectation_sub_predictedSymm
    (Λ := Λ) (A := A) (N := N)
  -- hgap (in ℂ): ⟨Néel⟩ - predictedSymm = (Nat.min |A| |¬A| : ℂ) * N
  have hre : ((dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))) -
      bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re =
      ((Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
          (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) * (N : ℂ)).re := by
    rw [hgap]
  rw [Complex.sub_re] at hre
  -- Compute (Nat.min · N : ℂ).re
  have hprod_re : ((Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) * (N : ℂ)).re =
      ((Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
          (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) * (N : ℝ) := by
    rw [Complex.mul_re]
    simp [Complex.natCast_re, Complex.natCast_im]
  rw [hprod_re] at hre
  -- hre: ⟨Néel⟩.re - predictedSymm.re = min · N ≥ 0.
  have hmin_nn : (0 : ℝ) ≤
      ((Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
          (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) := by positivity
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hgap_nn : (0 : ℝ) ≤
      ((Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
          (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) * (N : ℝ) :=
    mul_nonneg hmin_nn hN_nn
  linarith

end LatticeSystem.Quantum
