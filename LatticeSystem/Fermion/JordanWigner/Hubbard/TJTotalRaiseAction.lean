import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorRaise

/-!
# Tasaki 11.5: the total raising operator on a sector basis state (Prop 11.24 E3b PR5b)

The total raising operator acts on a t-J sector basis state by raising each down-spin in turn:
`Ŝ⁺_tot |Φ_s⟩ = Σ_{x : s x = ↓} |Φ_{s with x ↦ ↑}⟩`.  This is the sign-free expansion (every term
has coefficient `+1`, from `fermionSiteSpinPlus_mulVec_tJConfigOf_of_down`) underlying the
positivity of the iterated raising (lifting the Perron–Frobenius vector to a highest weight).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **The total raising operator on a sector basis state.**  `Ŝ⁺_tot |Φ_s⟩` is the sign-free sum of
the basis states obtained by raising each down-spin of `s` to `↑`. -/
theorem fermionTotalSpinPlus_mulVec_tJConfigOf (N : ℕ) (s : Fin (N + 1) → Fin 3) :
    (fermionTotalSpinPlus N).mulVec (basisVec (tJConfigOf N s)) =
      ∑ x ∈ Finset.univ.filter (fun x => s x = 2),
        basisVec (tJConfigOf N (Function.update s x 1)) := by
  rw [fermionTotalSpinPlus_eq_sum_siteSpinPlus, Matrix.sum_mulVec, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : s x = 2
  · rw [if_pos h, fermionSiteSpinPlus_mulVec_tJConfigOf_of_down N s x h]
  · rw [if_neg h, fermionSiteSpinPlus_mulVec_tJConfigOf_of_not_down N s x h]

end LatticeSystem.Fermion
