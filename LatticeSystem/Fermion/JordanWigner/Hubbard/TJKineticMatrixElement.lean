import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorHopWrap

/-!
# Tasaki 11.5: the forward hop matrix elements on the sector basis (Prop 11.24 PR-B4)

The per-term hopping matrix element `⟨Φ_{s'} | ĉ†_{bσ}ĉ_{aσ} | Φ_s⟩` for a *forward* allowed
nearest-neighbour or wrap hop equals `1` exactly when `s'` is the hopped site-state
`tJSiteHop s a b`, and `0` otherwise.  This combines the sign-free hop actions
(`tJ_uphop_nn_mulVec`,
the wrap variants) with the orthonormality of the sector basis (`tJConfigOf_basisVec_inner`); it is
the off-diagonal `−τ` kinetic entry of the t-J effective matrix.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **Forward NN up-hop matrix element.**  For `b.val = a.val + 1`, `s a = ↑`, `s b = empty`,
`⟨Φ_{s'} | ĉ†_{b↑}ĉ_{a↑} | Φ_s⟩ = [s' = tJSiteHop s a b]`. -/
theorem tJ_uphop_nn_matrixElement (N : ℕ) (s s' : Fin (N + 1) → Fin 3) (a b : Fin (N + 1))
    (hb : b.val = a.val + 1) (ha : s a = 1) (hsb : s b = 0) :
    (∑ w, basisVec (tJConfigOf N s') w *
        ((fermionMultiCreation (2 * N + 1) (spinfulIndex N b 0) *
            fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N a 0)).mulVec
            (basisVec (tJConfigOf N s))) w)
      = if s' = tJSiteHop s a b then 1 else 0 := by
  rw [tJ_uphop_nn_mulVec N s a b hb ha hsb]
  exact tJConfigOf_basisVec_inner N s' (tJSiteHop s a b)

/-- **Forward NN down-hop matrix element.** -/
theorem tJ_downhop_nn_matrixElement (N : ℕ) (s s' : Fin (N + 1) → Fin 3) (a b : Fin (N + 1))
    (hb : b.val = a.val + 1) (ha : s a = 2) (hsb : s b = 0) :
    (∑ w, basisVec (tJConfigOf N s') w *
        ((fermionMultiCreation (2 * N + 1) (spinfulIndex N b 1) *
            fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N a 1)).mulVec
            (basisVec (tJConfigOf N s))) w)
      = if s' = tJSiteHop s a b then 1 else 0 := by
  rw [tJ_downhop_nn_mulVec N s a b hb ha hsb]
  exact tJConfigOf_basisVec_inner N s' (tJSiteHop s a b)

/-- **Forward wrap up-hop matrix element** (cycle bond `{0, N}`, odd `Ne`). -/
theorem tJ_uphop_wrap_matrixElement (N : ℕ) (s s' : Fin (N + 1) → Fin 3) (a b : Fin (N + 1))
    (hpos : 0 < N) (ha0 : a.val = 0) (hbN : b.val = N) (ha : s a = 1) (hsb : s b = 0)
    (Ne : ℕ) (hNe : (Finset.univ.filter (fun k => s k = 1)).card
        + (Finset.univ.filter (fun k => s k = 2)).card = Ne) (hodd : Odd Ne) :
    (∑ w, basisVec (tJConfigOf N s') w *
        ((fermionMultiCreation (2 * N + 1) (spinfulIndex N b 0) *
            fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N a 0)).mulVec
            (basisVec (tJConfigOf N s))) w)
      = if s' = tJSiteHop s a b then 1 else 0 := by
  rw [tJ_uphop_wrap_mulVec N s a b hpos ha0 hbN ha hsb Ne hNe hodd]
  exact tJConfigOf_basisVec_inner N s' (tJSiteHop s a b)

/-- **Forward wrap down-hop matrix element** (cycle bond `{0, N}`, odd `Ne`). -/
theorem tJ_downhop_wrap_matrixElement (N : ℕ) (s s' : Fin (N + 1) → Fin 3) (a b : Fin (N + 1))
    (hpos : 0 < N) (ha0 : a.val = 0) (hbN : b.val = N) (ha : s a = 2) (hsb : s b = 0)
    (Ne : ℕ) (hNe : (Finset.univ.filter (fun k => s k = 1)).card
        + (Finset.univ.filter (fun k => s k = 2)).card = Ne) (hodd : Odd Ne) :
    (∑ w, basisVec (tJConfigOf N s') w *
        ((fermionMultiCreation (2 * N + 1) (spinfulIndex N b 1) *
            fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N a 1)).mulVec
            (basisVec (tJConfigOf N s))) w)
      = if s' = tJSiteHop s a b then 1 else 0 := by
  rw [tJ_downhop_wrap_mulVec N s a b hpos ha0 hbN ha hsb Ne hNe hodd]
  exact tJConfigOf_basisVec_inner N s' (tJSiteHop s a b)

end LatticeSystem.Fermion
