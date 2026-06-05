import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorHop

/-!
# Tasaki 11.5: the hop config identity for the t-J sector basis (Prop 11.24 PR3c-2)

The spinful occupation `tJConfigOf s` of the hopped site-state `tJSiteHop s a b` equals the original
configuration updated by the single-electron hop `mode (a,σ) ↦ 0`, `mode (b,σ) ↦ 1`.  This is the
configuration-level identity underlying the hop matrix element `⟨Φ_{tJSiteHop s a b} | ĉ†_{bσ}ĉ_{aσ}
| Φ_s⟩`: applying `ĉ†_{bσ}ĉ_{aσ}` to `basisVec (tJConfigOf s)` produces (up to the Jordan–Wigner
sign) exactly `basisVec (tJConfigOf (tJSiteHop s a b))`.

Both the up-hop (`σ = ↑`, source `s a = ↑`) and the down-hop (`σ = ↓`, source `s a = ↓`) are
covered; in each case the target site must be empty (`s b = 0`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

variable {N : ℕ}

/-- An up-occupied source and an empty target sit at distinct sites. -/
private theorem tJ_hop_ne_up (s : Fin (N + 1) → Fin 3) (a b : Fin (N + 1)) (ha : s a = 1)
    (hb : s b = 0) : a ≠ b := by
  rintro rfl; rw [ha] at hb; exact absurd hb (by decide)

/-- A down-occupied source and an empty target sit at distinct sites. -/
private theorem tJ_hop_ne_down (s : Fin (N + 1) → Fin 3) (a b : Fin (N + 1)) (ha : s a = 2)
    (hb : s b = 0) : a ≠ b := by
  rintro rfl; rw [ha] at hb; exact absurd hb (by decide)

/-- A spin label is `0` or `1` (the two-element dichotomy used throughout the t-J sector files). -/
theorem tJ_fin2_eq (r : Fin 2) : r = 0 ∨ r = 1 := by
  rcases eq_or_ne r 0 with h | h
  · exact Or.inl h
  · refine Or.inr (Fin.ext ?_)
    have h0 : r.val ≠ 0 := fun hh => h (Fin.ext hh)
    have := r.isLt; omega

/-- **Up-hop config identity**: when site `a` is ↑ and site `b` is empty, the spinful occupation of
`tJSiteHop s a b` is `tJConfigOf s` with the up-orbital of `a` emptied and the up-orbital of `b`
filled.  The down-orbitals are untouched. -/
theorem tJConfigOf_tJSiteHop_up (N : ℕ) (s : Fin (N + 1) → Fin 3) (a b : Fin (N + 1))
    (ha : s a = 1) (hb : s b = 0) :
    Function.update (Function.update (tJConfigOf N s) (spinfulIndex N a 0) 0)
        (spinfulIndex N b 0) 1
      = tJConfigOf N (tJSiteHop s a b) := by
  have hab : a ≠ b := tJ_hop_ne_up s a b ha hb
  funext k
  obtain ⟨i, r, rfl⟩ := exists_spinfulIndex N k
  simp only [Function.update_apply, spinfulIndex_eq_iff]
  rcases tJ_fin2_eq r with rfl | rfl <;> rcases eq_or_ne i a with rfl | hia <;>
    rcases eq_or_ne i b with rfl | hib <;>
    simp_all [tJConfigOf_apply_up, tJConfigOf_apply_down, tJSiteHop]

/-- **Down-hop config identity**: when site `a` is ↓ and site `b` is empty, the spinful occupation
of `tJSiteHop s a b` is `tJConfigOf s` with the down-orbital of `a` emptied and the down-orbital of
`b` filled.  The up-orbitals are untouched. -/
theorem tJConfigOf_tJSiteHop_down (N : ℕ) (s : Fin (N + 1) → Fin 3) (a b : Fin (N + 1))
    (ha : s a = 2) (hb : s b = 0) :
    Function.update (Function.update (tJConfigOf N s) (spinfulIndex N a 1) 0)
        (spinfulIndex N b 1) 1
      = tJConfigOf N (tJSiteHop s a b) := by
  have hab : a ≠ b := tJ_hop_ne_down s a b ha hb
  funext k
  obtain ⟨i, r, rfl⟩ := exists_spinfulIndex N k
  simp only [Function.update_apply, spinfulIndex_eq_iff]
  rcases tJ_fin2_eq r with rfl | rfl <;> rcases eq_or_ne i a with rfl | hia <;>
    rcases eq_or_ne i b with rfl | hib <;>
    simp_all [tJConfigOf_apply_up, tJConfigOf_apply_down, tJSiteHop]

end LatticeSystem.Fermion
