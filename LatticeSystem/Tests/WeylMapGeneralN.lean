import LatticeSystem.Math.MvPolynomial.WeylSpinMap
import LatticeSystem.Math.MvPolynomial.WeightedHomogeneousLayer

/-!
# `N = 2` convergence regression gate for the general-`N` Weyl map

`LatticeSystem.Math.weylMap` and its supporting declarations (`mdSite`, `md`, `cgSite`, `cgNorm`,
`weylMono`) are being generalized from the hard-wired spin-`1` case (site-state type `Fin 3`) to a
general spin-`S` case with `N = 2S` (site-state type `Fin (N + 1)`), per Issue #5292 PR-1 (design:
`.self-local/reports/design-5292-pr1-weylmap-generalization-round1-20260819.md`). This file is the
regression gate that certifies the generalization does not silently change the pre-PR spin-`1`
statements when `N` is instantiated to `2`.

Four groups:

1. **Type/statement convergence** — the pre-PR `Fin 3` statements, discharged by *bare term
   application* of the general-`N` declaration (no tactic). A tactic proof (e.g. `simp`) would hide
   a coercion/defeq mismatch; term-mode application only typechecks if the general statement is
   *definitionally* the old one after `N := 2` unification.
2. **`cgSite` value convergence** — pins the load-bearing `cgSite (N := 2) 1 = √2` Clebsch–Gordan
   weight explicitly. Group 1 alone would still pass even if `cgSite` silently computed the wrong
   values, as long as the values it produced still made every other lemma provable; this group
   catches that.
3. **`mdSite` shape convergence** — restates the old matrix-literal definition of `mdSite` as a
   theorem to hold, so the exponent-`Finsupp` shape at each of the three `Fin 3` states is pinned
   independently of the closed-form definition.
4. **Non-degeneracy control** — one example at `N = 4` (`Fin 5`), so a "generalization" that
   silently ignores `N` (e.g. one that always behaves as if `N = 2`) fails this file even though it
   would pass groups 1-3.

No production code is written here. This file must FAIL TO COMPILE until `weylMap` and its
supporting declarations gain the implicit `{N : ℕ}` parameter (`weylMap_isHomogeneous`,
`weylMapWeight_apply`, and the rest of §2/§3 of the design note).
-/

open MvPolynomial LatticeSystem.Math

namespace LatticeSystem.Tests.WeylMapGeneralN

variable {L : ℕ}

/-! ## Group 1: type/statement convergence at `N = 2` -/

/-- `mdSite_degree` at `N = 2` (inferred from `k : Fin 3`) reproduces the pre-PR statement
`(mdSite x k).degree = 2` verbatim. -/
example (x : Fin L) (k : Fin 3) : (mdSite x k).degree = 2 :=
  mdSite_degree x k

/-- `md_degree` at `N = 2` reproduces the pre-PR statement `(md σ).degree = 2 * L` verbatim. -/
example (σ : Fin L → Fin 3) : (md σ).degree = 2 * L :=
  md_degree σ

/-- `md_apply_fst` at `N = 2` reproduces the pre-PR statement `(md σ) (i, 0) = 2 - σ i` verbatim. -/
example (σ : Fin L → Fin 3) (i : Fin L) : (md σ) (i, 0) = 2 - (σ i : ℕ) :=
  md_apply_fst σ i

/-- `weylMap_coeff` at `N = 2` reproduces the pre-PR statement verbatim. -/
example (Φ : (Fin L → Fin 3) → ℂ) (τ : Fin L → Fin 3) :
    (weylMap Φ).coeff (md τ) = Φ τ * cgNorm τ :=
  weylMap_coeff Φ τ

/-- `weylMap_injective` at `N = 2` reproduces the pre-PR statement verbatim. -/
example : Function.Injective (weylMap : ((Fin L → Fin 3) → ℂ) →ₗ[ℂ] _) :=
  weylMap_injective

/-- `weylMap_isHomogeneous` at `N = 2` reproduces the pre-PR statement `IsHomogeneous (2 * L)`
verbatim. -/
example (Φ : (Fin L → Fin 3) → ℂ) : (weylMap Φ).IsHomogeneous (2 * L) :=
  weylMap_isHomogeneous Φ

/-- `weylMap_isWeightedHomogeneous` at `N = 2` reproduces the pre-PR statement `∑ x, single x 2`
verbatim. -/
example (Φ : (Fin L → Fin 3) → ℂ) :
    (weylMap Φ).IsWeightedHomogeneous (siteWeight (L := L)) (∑ x : Fin L, Finsupp.single x 2) :=
  weylMap_isWeightedHomogeneous Φ

/-- `weylMapWeight_apply` has no `Fin (N + 1)`-typed subterm to infer `N` from, so after
generalization it takes `N` as an explicit first argument; `weylMapWeight_apply 2 y` reproduces the
pre-PR statement `∑ x, single x 2 $ y = 2` verbatim. -/
example (y : Fin L) : (∑ x : Fin L, Finsupp.single x 2 : Fin L →₀ ℕ) y = 2 :=
  weylMapWeight_apply 2 y

/-! ## Group 2: `cgSite` value convergence at `N = 2` -/

/-- The `N = 2, k = 0` Clebsch–Gordan weight is `1`. -/
example : cgSite (N := 2) 0 = (1 : ℂ) := by
  norm_num [cgSite]

/-- The `N = 2, k = 1` (middle) Clebsch–Gordan weight is `√2`; this is the load-bearing value the
module header calls essential (it is what makes a bond singlet divisible by the bond factor). A
`cgSite` implementation that ignores `N` and always returns `binom(N, k)` instead of
`√(binom(N, k))`, or that returns the wrong middle value, still passes Group 1 but fails here. -/
example : cgSite (N := 2) 1 = (Real.sqrt 2 : ℂ) := by
  norm_num [cgSite]

/-- The `N = 2, k = 2` Clebsch–Gordan weight is `1`. -/
example : cgSite (N := 2) 2 = (1 : ℂ) := by
  norm_num [cgSite]

/-! ## Group 3: `mdSite` shape convergence at `N = 2` -/

/-- The general-`N` `mdSite` reproduces the pre-PR matrix-literal shape at `N = 2`: the three
`Fin 3` site states map to `u_x^2`, `u_x v_x`, `v_x^2` respectively. -/
theorem mdSite_eq_matrixLiteral (x : Fin L) (k : Fin 3) :
    mdSite (N := 2) x k =
      ![Finsupp.single (x, 0) 2,
        Finsupp.single (x, 0) 1 + Finsupp.single (x, 1) 1,
        Finsupp.single (x, 1) 2] k := by
  fin_cases k <;> simp [mdSite]

/-! ## Group 4: non-degeneracy control (`N = 4`) -/

/-- At `N = 4` the site-state type is `Fin 5` and `k = 0` still contributes the full degree-`N`
monomial `u_x^N`; this fails for any "generalization" that silently keeps behaving as `N = 2`. -/
example (x : Fin L) : mdSite (N := 4) x 0 = Finsupp.single (x, 0) 4 := by
  simp [mdSite]

/-- At `N = 4` the middle-ish Clebsch–Gordan weight `cgSite 2 = √(binom(4,2)) = √6`, distinct from
the `N = 2` value `√2`; this fails for any "generalization" that silently keeps behaving as
`N = 2`. -/
example : cgSite (N := 4) 2 = (Real.sqrt 6 : ℂ) := by
  norm_num [cgSite, Nat.choose]

end LatticeSystem.Tests.WeylMapGeneralN
