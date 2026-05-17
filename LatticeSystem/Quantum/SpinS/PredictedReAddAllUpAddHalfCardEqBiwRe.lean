import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubCanonicalEqHalfCardSubBiwRe
import LatticeSystem.Quantum.SpinS.AllAlignedExpectationEqNegNeel

/-!
# `(pmA).re + ⟨Φ_↑⟩.re + |Λ|·N/2 = biw.re` unconditionally

Combines PR #3171 (`⟨Néel⟩.re − (pmA).re = |Λ|·N/2 − biw.re`) with
PR #3199 (`⟨Φ_↑⟩.re = −⟨Φ_Néel⟩.re`):

  `(predicted_min A).re + ⟨Φ_↑|Ĥ_toy|Φ_↑⟩.re + |Λ|·N/2 = biw.re`

unconditionally. Symmetric chain: `(pmA).re = -⟨Φ_↑⟩.re - |Λ|·N/2 + biw.re`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`(pmA).re + ⟨Φ_↑⟩.re + |Λ|·N/2 = biw.re`** unconditionally. -/
theorem bipartiteToyMinEnergyPredicted_re_add_all_up_add_half_card_eq_biw_re
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1))))).re +
        (Fintype.card Λ : ℝ) * (N : ℝ) / 2 =
      (bipartiteImbalanceWeight (Λ := Λ) A N).re := by
  have h1 := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_canonical_predicted_re_eq_half_card_sub_biw_re
    (Λ := Λ) (A := A) (N := N)
  have h2 := heisenbergToyHamiltonianS_allAligned_zero_expectation_re_eq_neg_neel_expectation_re
    (Λ := Λ) (A := A) (N := N)
  linarith

end LatticeSystem.Quantum
