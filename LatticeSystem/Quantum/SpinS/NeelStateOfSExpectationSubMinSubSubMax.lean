import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubMinComplement
import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubMaxComplement

/-!
# Difference identity: `(⟨Néel⟩ − min) − (⟨Néel⟩ − max) = (max − min)·N`

Existing (PR #3052): `⟨Néel⟩.re − min(...) = max(|A|, |¬A|)·N`.
Existing (PR #3129): `⟨Néel⟩.re − max(...) = min(|A|, |¬A|)·N`.

Subtracting:

  `(⟨Néel⟩.re − min(...)) − (⟨Néel⟩.re − max(...))
    = (max(|A|, |¬A|) − min(|A|, |¬A|)) · N
    = ||A| − |¬A|| · N
    = 2 · ‖biw‖`

unconditionally, where the last equality uses `max − min = |x − y|`
and the orientation imbalance-weight norm
`‖biw‖ = ||A| − |¬A||·N/2`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **Difference of the two gaps equals `(max − min)·N`** unconditionally:

  `(⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re − min(...)) − (⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re − max(...))
    = (max(|A|, |¬A|) − min(|A|, |¬A|)) · N`. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_min_sub_sub_max_complement_re_eq
    (A : Λ → Bool) (N : ℕ) :
    ((dotProduct (star (neelStateOfS A N))
          ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
            (neelStateOfS A N))).re -
        min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) -
      ((dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re -
          max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
              (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) =
      (max ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) -
        min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) *
        (N : ℝ) := by
  rw [neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_min_complement_re_eq,
      neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_max_complement_re_eq]
  ring

end LatticeSystem.Quantum
