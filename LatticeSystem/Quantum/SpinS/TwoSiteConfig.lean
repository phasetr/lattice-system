import Mathlib.Data.Complex.Basic

/-!
# Two-site configuration gluing

The reduction of a two-site interaction term on a many-body system to a local `(N+1)² × (N+1)²`
problem proceeds by freezing the configuration of every spectator site and letting the two
distinguished sites vary.  This module holds the two elementary combinatorial ingredients of that
change of variables, shared by the ring (`Fin L`) and the general-graph formalizations:

* `glueTwoSitesS x y a τ` — overwrite a spectator configuration `τ` with the two-site
  configuration `a` on the sites `x, y`;
* `twoSiteSliceS x y Φ τ` — the resulting two-site coefficient slice `a ↦ Φ (glueTwoSitesS x y a τ)`
  of a many-body coefficient vector `Φ`.

Both are pure configuration combinatorics: no finiteness of the vertex type is required, so the
module is a leaf depending only on `ℂ`.  The specializations to a periodic chain bond
(`glueBond` / `bondSlice`, on the bond `{x, ringSucc x}`) live in
`LatticeSystem.Quantum.SpinS.AKLTBondProjection`, and the fibrewise action of a block-embedded
two-site matrix on these slices is proved in `LatticeSystem.Quantum.SpinS.TwoSiteSliceS`.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [DecidableEq Λ]

/-- Replace the values at two sites by a prescribed two-site
configuration, leaving every spectator value unchanged. -/
def glueTwoSitesS {N : ℕ} (x y : Λ)
    (a : Fin 2 → Fin (N + 1)) (τ : Λ → Fin (N + 1)) :
    Λ → Fin (N + 1) :=
  fun k => if k = x then a 0 else if k = y then a 1 else τ k

/-- The two-site coefficient slice obtained by fixing the spectator
configuration `τ`. -/
def twoSiteSliceS {N : ℕ} (x y : Λ)
    (Φ : (Λ → Fin (N + 1)) → ℂ) (τ : Λ → Fin (N + 1)) :
    (Fin 2 → Fin (N + 1)) → ℂ :=
  fun a => Φ (glueTwoSitesS x y a τ)

/-- Gluing a configuration `q` with the two values it already takes on the sites `x, y` returns `q`
itself.  No distinctness hypothesis `x ≠ y` is needed: on the degenerate site `x = y` the first
branch wins and `a 0 = q x` still closes the goal. -/
theorem glueTwoSitesS_eq_self {N : ℕ} {x y : Λ} {a : Fin 2 → Fin (N + 1)}
    (q : Λ → Fin (N + 1)) (h0 : a 0 = q x) (h1 : a 1 = q y) :
    glueTwoSitesS x y a q = q := by
  funext k
  by_cases hkx : k = x
  · subst hkx
    rw [glueTwoSitesS, if_pos rfl, h0]
  · by_cases hky : k = y
    · subst hky
      rw [glueTwoSitesS, if_neg hkx, if_pos rfl, h1]
    · rw [glueTwoSitesS, if_neg hkx, if_neg hky]

end LatticeSystem.Quantum
