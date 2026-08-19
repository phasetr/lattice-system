import LatticeSystem.Quantum.SpinS.GeneralSCasimirDescent
import LatticeSystem.Quantum.SpinS.AKLTUniqueness.LocalBondDivisibility
import LatticeSystem.Math.MvPolynomial.BondFactorDerivation
import LatticeSystem.Math.MvPolynomial.WeightedHomogeneousLayer

/-!
# Signature and numeric regression pins for the Casimir-descent layer (PR-3c)

`GeneralSCasimirDescent` is the polynomial-algebra engine behind the local kernel statement
`f2_pow_dvd_weylMap_of_localCasimirPenalty` of `GeneralSOpenChainBondTerm`: a composite of
`c·(−) − f₂·Ω(−)` steps is `∏ c_i · (−) mod f₂`, and the Casimir-penalty scalar family is invariant
under the level shift that division by `f₂` induces.  This file pins the exact signatures of its
eight public declarations (both `def`s and all six `theorem`s) by bare term application — no tactic
hides an argument-order or coercion mismatch — together with fully concrete numeric instances at
small `m`/`S` that a later refactor of the definitions cannot silently change.

No production code is written here.
-/

open MvPolynomial LatticeSystem.Math LatticeSystem.Quantum
open LatticeSystem.Quantum.AKLTUniqueness

namespace LatticeSystem.Tests.GeneralSCasimirDescent

/-! ## Group 1: signature pins for the eight public declarations -/

/-- `casimirDescentStep : ℂ → MvPolynomial (Fin 2 × Fin 2) ℂ → MvPolynomial (Fin 2 × Fin 2) ℂ`. -/
noncomputable example (c : ℂ) (p : MvPolynomial (Fin 2 × Fin 2) ℂ) :
    MvPolynomial (Fin 2 × Fin 2) ℂ :=
  casimirDescentStep c p

/-- `casimirPenaltyScalars : ℕ → ℕ → List ℂ`. -/
noncomputable example (m S : ℕ) : List ℂ :=
  casimirPenaltyScalars m S

/-- `casimirDescentStep` preserves `siteWeight`-homogeneity of bidegree `(m + 1, m + 1)`. -/
example {m : ℕ} (c : ℂ) {p : MvPolynomial (Fin 2 × Fin 2) ℂ}
    (hp : p.IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 (m + 1) + Finsupp.single 1 (m + 1))) :
    (casimirDescentStep c p).IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 (m + 1) + Finsupp.single 1 (m + 1)) :=
  casimirDescentStep_isWeightedHomogeneous c hp

/-- The level shift: `A_{c + (2m+2)}(f₂ q) = f₂ · A_c(q)` for `q` of bidegree `(m, m)`. -/
example {m : ℕ} (c : ℂ) {q : MvPolynomial (Fin 2 × Fin 2) ℂ}
    (hq : q.IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 m + Finsupp.single 1 m)) :
    casimirDescentStep (c + (2 * m + 2 : ℕ)) (f2 * q) = f2 * casimirDescentStep c q :=
  casimirDescentStep_bondFactor_mul c hq

/-- The level shift, folded over a whole scalar list. -/
example {m : ℕ} (hm : m ≠ 0) (cs : List ℂ) {q : MvPolynomial (Fin 2 × Fin 2) ℂ}
    (hq : q.IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 m + Finsupp.single 1 m)) :
    List.foldr casimirDescentStep (f2 * q) (cs.map (· + (2 * m + 2 : ℕ)))
      = f2 * List.foldr casimirDescentStep q cs :=
  casimirDescentFold_bondFactor_mul hm cs hq

/-- A nonzero-scalar-product fold vanishing at `p` forces `f₂ ∣ p`. -/
example {cs : List ℂ} (hcs : cs.prod ≠ 0) {p : MvPolynomial (Fin 2 × Fin 2) ℂ}
    (h : List.foldr casimirDescentStep p cs = 0) :
    f2 ∣ p :=
  bondFactor_dvd_of_casimirDescentFold_eq_zero hcs h

/-- The Casimir-penalty scalar family has nonzero product below the top level `S < m`. -/
example {m S : ℕ} (h : S < m) : (casimirPenaltyScalars m S).prod ≠ 0 :=
  casimirPenaltyScalars_prod_ne_zero h

/-- **Headline.** A `k`-step Casimir-penalty descent vanishing on `p` (homogeneous of bidegree
`(S + k, S + k)`) forces `f₂^k ∣ p`. -/
example {S : ℕ} (hS : S ≠ 0) (k : ℕ) {p : MvPolynomial (Fin 2 × Fin 2) ℂ}
    (hp : p.IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 (S + k) + Finsupp.single 1 (S + k)))
    (h : List.foldr casimirDescentStep p (casimirPenaltyScalars (S + k) S) = 0) :
    f2 ^ k ∣ p :=
  bondFactor_pow_dvd_of_casimirDescentFold hS k hp h

/-! ## Group 2: `S = 0` degenerate instance -/

/-- **`S = 0` degenerate instance.** `casimirPenaltyScalars m 0` is the singleton list of the
top-Casimir eigenvalue gap `m(m+1)`; there is no side condition to check here since `f₂^0 = 1`
divides every polynomial unconditionally, so this pins only the shape of the singleton list. -/
example (m : ℕ) : casimirPenaltyScalars m 0 = [(m : ℂ) * (m + 1)] := by
  simp [casimirPenaltyScalars, List.ofFn_succ]

/-! ## Group 3: numeric instances at `m = 1`, `S = 1` and the negative control -/

/-- `casimirPenaltyScalars 1 1 = [2, 0]`: `j = 0` gives `1·2 − 0·1 = 2`, `j = 1` gives
`1·2 − 1·2 = 0`. -/
example : casimirPenaltyScalars 1 1 = [(2 : ℂ), 0] := by
  norm_num [casimirPenaltyScalars, List.ofFn_succ]

/-- **Negative control.** At `m = S = 1` the scalar list contains `0`
(`casimirPenaltyScalars_prod_ne_zero` needs the strict inequality `S < m`), pinning that the descent
cannot be pushed one level past `f₂^S`. -/
example : (casimirPenaltyScalars 1 1).prod = (0 : ℂ) := by
  norm_num [casimirPenaltyScalars, List.ofFn_succ]

/-- `casimirPenaltyScalars 2 1 = [6, 4]`: `j = 0` gives `2·3 − 0·1 = 6`, `j = 1` gives
`2·3 − 1·2 = 4`. This is the `S < m` level directly above the negative control. -/
example : casimirPenaltyScalars 2 1 = [(6 : ℂ), 4] := by
  norm_num [casimirPenaltyScalars, List.ofFn_succ]

/-- The scalar product at `m = 2, S = 1` is nonzero (`24`), the numeric witness for
`casimirPenaltyScalars_prod_ne_zero` at `S = 1 < m = 2`. -/
example : (casimirPenaltyScalars 2 1).prod = (24 : ℂ) := by
  norm_num [casimirPenaltyScalars, List.ofFn_succ]

/-- **Level-shift numeric instance.** `casimirPenaltyScalars 2 1` is exactly `casimirPenaltyScalars
1 1` shifted by `2·1 + 2 = 4`: the concrete `m = 1` case of the scalar-family invariance
(`casimirPenaltyScalars_succ`) that drives `casimirDescentFold_bondFactor_mul`. -/
example : casimirPenaltyScalars 2 1 = (casimirPenaltyScalars 1 1).map (· + 4) := by
  norm_num [casimirPenaltyScalars, List.ofFn_succ]

/-! ## Group 4: numeric descent-step instances -/

/-- **Singlet sanity check.** `casimirDescentStep 2 f₂ = 2 • f₂ − f₂ · Ω f₂ = 2f₂ − 2f₂ = 0`
(`bondOmega_bondFactor_self : Ω f₂ = 2`), the same `J = 0` computation recorded in
`GeneralSWeylCasimir.weylMap_mulVec_bondCasimirS`'s doc comment. Catches a sign slip in
`casimirDescentStep` (pitfall 5 of the design report). -/
example : casimirDescentStep (2 : ℂ) f2 = 0 := by
  have h : bondOmega ((0 : Fin 2), (0 : Fin 2)) (1, 1) (0, 1) (1, 0) f2 = 2 := by
    rw [f2]
    exact bondOmega_bondFactor_self (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  rw [casimirDescentStep, h, smul_eq_C_mul, map_ofNat]
  ring

/-- **Concrete level-shift instance at `m = 1`.** Instantiating `casimirDescentStep_bondFactor_mul`
at `c = 2`, `m = 1`, `q = f₂` (bidegree `(1, 1)`, shift `2·1 + 2 = 4`, so the scalar is
`2 + 4 = 6`): `A₆(f₂ · f₂) = f₂ · A₂(f₂)`, which by the singlet sanity check above is
`f₂ · 0 = 0`. -/
example : casimirDescentStep (6 : ℂ) (f2 * f2) = f2 * casimirDescentStep (2 : ℂ) f2 := by
  have hq : (f2 : MvPolynomial (Fin 2 × Fin 2) ℂ).IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 1 + Finsupp.single 1 1) := by
    rw [f2]
    exact bondFactor_isWeightedHomogeneous _ _ _ _ _ rfl
  have h := casimirDescentStep_bondFactor_mul (m := 1) (2 : ℂ) hq
  norm_num at h
  exact h

end LatticeSystem.Tests.GeneralSCasimirDescent
