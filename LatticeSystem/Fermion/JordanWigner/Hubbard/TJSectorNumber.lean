import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorSpin
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiHopAction

/-!
# Tasaki 11.5: the electron-number eigenvalue of the t-J sector basis (Prop 11.24 PR3b)

The t-J basis state `basisVec (tJConfigOf s)` is an `N̂`-eigenvector with eigenvalue the number of
occupied sites `#{i | s i = up} + #{i | s i = down}` (each occupied site has one electron).  With
the `S^z = 1/2` eigenvalue (`TJSectorSpin.lean`), a site state with `#up + #down = Ne` and
`#up = #down + 1` lands in the `N̂ = Ne`, `S^z_tot = 1/2` sector of Proposition 11.24.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), 11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- `N̂` acts on `basisVec (tJConfigOf s)` with eigenvalue `#{s = up} + #{s = down}` (the electron
number): each occupied site contributes one electron. -/
theorem fermionTotalNumber_mulVec_tJConfigOf (N : ℕ) (s : Fin (N + 1) → Fin 3) :
    (fermionTotalNumber (2 * N + 1)).mulVec (basisVec (tJConfigOf N s))
      = (((Finset.univ.filter (fun k => s k = 1)).card : ℂ) +
          ((Finset.univ.filter (fun k => s k = 2)).card : ℂ))
        • basisVec (tJConfigOf N s) := by
  rw [fermionTotalNumber_mulVec_basisVec]
  congr 1
  rw [sum_spinful_reindex N (fun k => ((tJConfigOf N s k).val : ℂ))]
  have : ∀ t : Fin (N + 1), (∑ r : Fin 2, ((tJConfigOf N s (spinfulIndex N t r)).val : ℂ))
      = ((tJConfigOf N s (spinfulIndex N t 0)).val : ℂ) +
        ((tJConfigOf N s (spinfulIndex N t 1)).val : ℂ) := fun t => Fin.sum_univ_two _
  rw [Finset.sum_congr rfl (fun t _ => this t), Finset.sum_add_distrib, ← Nat.cast_sum,
    ← Nat.cast_sum, tJConfigOf_up_count, tJConfigOf_down_count]

/-- **`N̂ = Ne` on the sector basis**: if a site state has `Ne` occupied sites (`#up + #down = Ne`),
the basis state lies in the `Ne`-electron sector. -/
theorem fermionTotalNumber_mulVec_tJConfigOf_eq (N : ℕ) (s : Fin (N + 1) → Fin 3) (Ne : ℕ)
    (h : (Finset.univ.filter (fun k => s k = 1)).card +
        (Finset.univ.filter (fun k => s k = 2)).card = Ne) :
    (fermionTotalNumber (2 * N + 1)).mulVec (basisVec (tJConfigOf N s))
      = (Ne : ℂ) • basisVec (tJConfigOf N s) := by
  rw [fermionTotalNumber_mulVec_tJConfigOf, ← Nat.cast_add, h]

end LatticeSystem.Fermion
