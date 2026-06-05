import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorHopConfig
import LatticeSystem.Fermion.JordanWigner.Hubbard.FermionSiteSpin

/-!
# Tasaki 11.5: the exchange spin-flip on the t-J sector basis (Prop 11.24 PR-B1)

The exchange term `Ŝ_x·Ŝ_y` of the t-J Hamiltonian has the ladder part `½(Ŝ⁺_xŜ⁻_y + Ŝ⁻_xŜ⁺_y)`.
The off-diagonal piece `Ŝ⁺_i Ŝ⁻_j = ĉ†_{i↑}ĉ_{i↓}ĉ†_{j↓}ĉ_{j↑}` swaps the spins of an antiparallel
nearest-neighbour pair: acting on `|Φ_s⟩` with `s i = ↓`, `s j = ↑` (`i ≠ j`) it produces
`|Φ_{tJSpinSwap s i j}⟩` with **net Jordan–Wigner sign `+1`** — the two same-site
creation/annihilation pairs `(j↑,j↓)` and `(i↓,i↑)` each cancel (equal string exponents at adjacent
modes), with no dependence on the electrons between `i` and `j`.

This file builds the configuration-level identity; the operator action and the `+1` sign follow.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- The spin-swap move on site-states: exchange the entries at sites `i` and `j`. -/
def tJSpinSwap (s : Fin (N + 1) → Fin 3) (i j : Fin (N + 1)) : Fin (N + 1) → Fin 3 :=
  fun k => if k = i then s j else if k = j then s i else s k

/-- An antiparallel pair (`s i = ↓`, `s j = ↑`) sits at distinct sites. -/
theorem tJ_spinSwap_ne (s : Fin (N + 1) → Fin 3) (i j : Fin (N + 1)) (hi : s i = 2)
    (hj : s j = 1) : i ≠ j := by
  rintro rfl; rw [hi] at hj; exact absurd hj (by decide)

/-- **Exchange config identity**: for `s i = ↓`, `s j = ↑`, the spinful occupation of
`tJSpinSwap s i j` is `tJConfigOf s` with the four orbitals `(j↑,j↓,i↓,i↑)` updated to
`(0,1,0,1)` — i.e. `i` becomes ↑ and `j` becomes ↓. -/
theorem tJConfigOf_tJSpinSwap (N : ℕ) (s : Fin (N + 1) → Fin 3) (i j : Fin (N + 1))
    (hi : s i = 2) (hj : s j = 1) :
    Function.update (Function.update (Function.update (Function.update (tJConfigOf N s)
        (spinfulIndex N j 0) 0) (spinfulIndex N j 1) 1) (spinfulIndex N i 1) 0)
        (spinfulIndex N i 0) 1
      = tJConfigOf N (tJSpinSwap s i j) := by
  have hij : i ≠ j := tJ_spinSwap_ne s i j hi hj
  funext k
  obtain ⟨t, r, rfl⟩ := exists_spinfulIndex N k
  simp only [Function.update_apply, spinfulIndex_eq_iff]
  rcases (show r = 0 ∨ r = 1 from tJ_fin2_eq r) with rfl | rfl <;>
    rcases eq_or_ne t i with rfl | hti <;> rcases eq_or_ne t j with rfl | htj <;>
    simp_all [tJConfigOf_apply_up, tJConfigOf_apply_down, tJSpinSwap]

end LatticeSystem.Fermion
