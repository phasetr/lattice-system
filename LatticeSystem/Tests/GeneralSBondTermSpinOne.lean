import LatticeSystem.Quantum.SpinS.GeneralSOpenChainBondTerm
import LatticeSystem.Quantum.SpinS.AKLTOpenChain
import LatticeSystem.Quantum.SpinS.AKLTKnabe.BondProjectionAlgebraD6b
import LatticeSystem.Quantum.SpinS.AKLTUniqueness.LocalBondDivisibility

/-!
# `S = 1` convergence + capstone-shape regression gate for the general-`S` AKLT bond term

The general-`S` open-chain bond term `bondCasimirPenaltyS` and its divisibility capstone
(`LatticeSystem.Quantum.GeneralSOpenChainBondTerm`) must reduce, at `S = 1`, to the spin-one AKLT
chain that the rest of the tree already owns.  This file pins that convergence together with the
weight values and the shape of the capstone, so that a later change to the general-`S` definitions
cannot silently move the `S = 1` model or the root set of the penalty polynomial.  No production
code is written here.

Five groups, mirroring the general-`N` Weyl-map gate `WeylMapGeneralN.lean`:

1. **Type/statement convergence at `S = 1`** — the design's #5292 acceptance criterion, discharged
   by *bare term application* (no tactic) so a `2 * 1` vs `2` coercion/defeq mismatch surfaces here.
2. **Weight-value pinning** — `casimirPenaltyWeight` at concrete `(S, J)`, catching a silently wrong
   weight that Group 1 alone would not detect.
3. **Root-set pinning at `S = 2`** — `casimirPenaltyWeight S J = 0 ↔ J ≤ S`; catches the
   `∏_{j<S}` vs `∏_{j≤S}` off-by-one that would silently produce the §7.3.2 top-spin family instead.
4. **Non-degeneracy control** — the same `J = 2` weight differs between `S = 1` (nonzero, `24`) and
   `S = 2` (zero), so a definition that silently ignores `S` fails here.
5. **Divisibility capstone shape** — `prod_fBond_pow_dvd_weylMap_of_annihilated` applied at its
   stated general signature, and `onEmbS_list_prod` referenced from the shared embedding module
   `AKLTExactCertificateSector234Sequential` rather than from any `N`-specific consumer, which is
   what lets the general-`S` module reduce a bond term to `onEmbS` without importing the `N = 3`
   certificate tables.
-/

open MvPolynomial LatticeSystem.Math LatticeSystem.Quantum LatticeSystem.Quantum.AKLTUniqueness
open LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential

namespace LatticeSystem.Tests.GeneralSBondTermSpinOne

variable {L : ℕ}

/-! ## Group 1: type/statement convergence at `S = 1` -/

/-- `bondCasimirPenaltyS x y 1 = 24 • bondSpin2ProjectionS x y` (the `S = 1` back-compatibility
identity). Bare term application: a `2 * 1` vs `2` defeq mismatch in `ManyBodyOpS (Fin L) (2 * 1)`
vs `ManyBodyOpS (Fin L) 2` must be resolved by the source theorem itself, not hidden by a tactic
here. -/
example (x y : Fin L) :
    bondCasimirPenaltyS x y 1 = (24 : ℂ) • bondSpin2ProjectionS x y :=
  bondCasimirPenaltyS_one x y

/-- `openAKLTHamiltonianGeneralS L 1 = 24 • openProjHamiltonianS L`. -/
example (L : ℕ) :
    openAKLTHamiltonianGeneralS L 1 = (24 : ℂ) • openProjHamiltonianS L :=
  openAKLTHamiltonianGeneralS_one L

/-! ## Group 2: weight-value pinning -/

/-- `casimirPenaltyWeight 1 0 = 0` (`J = 0 ≤ S = 1`). -/
example : casimirPenaltyWeight 1 0 = 0 :=
  casimirPenaltyWeight_eq_zero (le_refl 0 |>.trans (Nat.zero_le 1))

/-- `casimirPenaltyWeight 1 1 = 0` (`J = 1 ≤ S = 1`). -/
example : casimirPenaltyWeight 1 1 = 0 :=
  casimirPenaltyWeight_eq_zero (le_refl 1)

/-- `casimirPenaltyWeight 1 2 = 24 = (2·3 − 0)(2·3 − 2) = 6 · 4`: the `S = 1` weight that,
combined with `bondCasimirPenaltyS_one`, must be the same `24` appearing in Group 1. -/
example : casimirPenaltyWeight 1 2 = 24 := by
  norm_num [casimirPenaltyWeight, Finset.prod_range_succ]

/-- `casimirPenaltyWeight 2 3 = (12)(12 − 2)(12 − 6) = 720`. -/
example : casimirPenaltyWeight 2 3 = 720 := by
  norm_num [casimirPenaltyWeight, Finset.prod_range_succ]

/-- `0 < casimirPenaltyWeight 2 3` through `casimirPenaltyWeight_pos`: the penalty on the total
spins `J > S` is strictly positive. Pinning the numeric value alone does not record that sign
condition, which is what makes the bond term a positive-weight member of Tasaki's family. -/
example : 0 < casimirPenaltyWeight 2 3 :=
  casimirPenaltyWeight_pos (by norm_num)

/-! ## Group 3: root-set pinning at `S = 2` -/

/-- `casimirPenaltyWeight 2 J = 0 ↔ J ≤ 2` for every `J ≤ 4`: the single most likely error
(`∏_{j < S}` instead of `∏_{j ≤ S}`) would give the wrong root set here. -/
example (J : ℕ) (hJ : J ≤ 4) : casimirPenaltyWeight 2 J = 0 ↔ J ≤ 2 := by
  interval_cases J <;> norm_num [casimirPenaltyWeight, Finset.prod_range_succ]

/-! ## Group 4: non-degeneracy control -/

/-- At `J = 2` the weight is nonzero for `S = 1` (`24`, Group 2) but zero for `S = 2`
(`J ≤ S`); a definition that silently ignores `S` cannot satisfy both. -/
example : casimirPenaltyWeight 2 2 = 0 :=
  casimirPenaltyWeight_eq_zero (le_refl 2)

/-! ## Group 5: divisibility capstone shape -/

/-- **Capstone shape.** `prod_fBond_pow_dvd_weylMap_of_annihilated`, applied at its stated general
signature: a state `Φ` annihilated by every open-bond Casimir penalty, together with the local
kernel hypothesis `hloc`, forces the prime-power product `∏ f_x ^ S` to divide `weylMap Φ`. -/
example (hL : 2 ≤ L) (S : ℕ) (Φ : (Fin L → Fin (2 * S + 1)) → ℂ)
    (hloc : ∀ φ : (Fin 2 → Fin (2 * S + 1)) → ℂ,
        (localCasimirPenalty S).mulVec φ = 0 → f2 ^ S ∣ weylMap (L := 2) φ)
    (hΦ : ∀ x ∈ openBonds L, (bondCasimirPenaltyS x (ringSucc x) S).mulVec Φ = 0) :
    (∏ x ∈ openBonds L, fBond x ^ S) ∣ weylMap Φ :=
  prod_fBond_pow_dvd_weylMap_of_annihilated hL S Φ hloc hΦ

/-- **`onEmbS_list_prod` module-boundary regression.** The block-embedding-of-a-list-product lemma
lives in `AKLTExactCertificateSector234Sequential` alongside `onEmbS_posSemidef` and is not
`private`, so every spin can reduce an ordered product of local bond factors to `onEmbS` without
importing an `N`-specific certificate table. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {m N : ℕ}
    (ι : Fin m → Λ) (hι : Function.Injective ι)
    (l : List (Matrix (Fin m → Fin (N + 1)) (Fin m → Fin (N + 1)) ℂ)) :
    onEmbS ι l.prod = (l.map fun A => onEmbS ι A).prod :=
  onEmbS_list_prod ι hι l

end LatticeSystem.Tests.GeneralSBondTermSpinOne
