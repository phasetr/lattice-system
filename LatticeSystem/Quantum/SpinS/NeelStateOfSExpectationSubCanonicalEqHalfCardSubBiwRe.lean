import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubCanonicalPredicted
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# `⟨Néel⟩.re − (pmA).re = |Λ|·N/2 − biw.re` unconditionally

biw-form of the existing `⟨Néel⟩.re − (pmA).re = |¬A|·N` identity.

  `⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re − (predicted_min A).re = |Λ|·N/2 − biw.re`

unconditionally, where `biw.re = (|A| − |¬A|)·N/2`. The arithmetic:
`|¬A|·N = (|Λ| − |A| + |¬A| − |¬A|)·N/2 + |¬A|·N = |Λ|·N/2 − (|A| − |¬A|)·N/2
 = |Λ|·N/2 − biw.re`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`⟨Néel⟩.re − (pmA).re = |Λ|·N/2 − biw.re`** unconditionally. biw-form of the existing `|¬A|·N` identity. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_canonical_predicted_re_eq_half_card_sub_biw_re
    (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re -
          (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re =
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 -
        (bipartiteImbalanceWeight (Λ := Λ) A N).re := by
  rw [neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_canonical_predicted_re_eq]
  rw [bipartiteImbalanceWeight_re_eq]
  -- Goal: |¬A|·N = |Λ|·N/2 - (|A|-|¬A|)·N/2
  -- Use |A| + |¬A| = |Λ|.
  have hsum : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
      (Fintype.card Λ : ℝ) := by
    classical
    have hN' : (Finset.univ.filter (fun x : Λ => A x = true)).card +
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = Fintype.card Λ := by
      rw [← Finset.card_union_of_disjoint, ← Finset.card_univ]
      · congr 1
        ext x
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        cases A x <;> simp
      · rw [Finset.disjoint_filter]
        intro x _ hx
        simp [hx]
    exact_mod_cast hN'
  -- Goal: |¬A|·N = |Λ|·N/2 − (|A|−|¬A|)·N/2.
  -- Substitute |Λ| via hsum.
  rw [show (Fintype.card Λ : ℝ) =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) from hsum.symm]
  ring

end LatticeSystem.Quantum
