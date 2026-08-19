import LatticeSystem.Quantum.SpinS.GeneralSOpenChainBondTerm
import LatticeSystem.Quantum.SpinS.AKLTOpenChain
import LatticeSystem.Quantum.SpinS.AKLTKnabe.SiteBlockEmbeddingD5b
import LatticeSystem.Quantum.SpinS.AKLTUniqueness.LocalBondDivisibility

/-!
# `S = 1` convergence + capstone regression gate for the general-`S` AKLT bond term

The general-`S` open-chain bond term `bondCasimirPenaltyS` and its divisibility capstone
(`LatticeSystem.Quantum.GeneralSOpenChainBondTerm`) must reduce, at `S = 1`, to the spin-one AKLT
chain that the rest of the tree already owns.  This file pins that convergence together with the
weight values and the capstone, so that a later change to the general-`S` definitions cannot
silently move the `S = 1` model or the root set of the weight function.  No production code is
written here.

The operator `bondCasimirPenaltyS` and the scalar weight function `casimirPenaltyWeight` are linked
by no theorem in the tree (that link is the spectral decomposition of `Ĉ`, which is not proved), so
the groups below are pinned separately and a group about one of them constrains the other in no way.

Five groups, mirroring the general-`N` Weyl-map gate `WeylMapGeneralN.lean`:

1. **Type/statement convergence at `S = 1`** — discharged by *bare term application* (no tactic),
   so a `2 * 1` vs `2` coercion/defeq mismatch surfaces here instead of being hidden by a tactic.
2. **Weight-value pinning** — `casimirPenaltyWeight` at concrete `(S, J)`, catching a silently wrong
   weight that Group 1 alone would not detect.
3. **Root-set pinning of the weight function at `S = 2`** — `casimirPenaltyWeight S J = 0 ↔ J ≤ S`;
   catches a `∏_{j<S}` vs `∏_{j≤S}` off-by-one *inside `casimirPenaltyWeight`*.  The index range of
   the operator `bondCasimirPenaltyS` is a separate piece of data and is not seen here.
4. **Non-degeneracy control** — the same `J = 2` weight differs between `S = 1` (nonzero, `24`) and
   `S = 2` (zero), so a weight definition that silently ignores `S` fails here.
5. **Divisibility capstone: shape and `S = 1` signature pin** —
   `prod_fBond_pow_dvd_weylMap_of_annihilated` applied at its stated general signature (the local
   kernel is discharged in-line by `f2_pow_dvd_weylMap_of_localCasimirPenalty`, so it is not a
   hypothesis of the capstone), then the `S = 1` local-kernel statement derived a second time
   through the pre-existing spin-one bespoke route (`bondCasimirPenaltyS_one`,
   `bondLocal_ker_eq_vbsBondSubspace`, `f2_dvd_weylMap_of_mem_vbsBondSubspace`).  Both routes prove
   the *same* proposition, so what is pinned is the signature — that the general-`S` theorem still
   instantiates verbatim to the bespoke spin-one statement — and not a numeric value: the sign of
   the Casimir-descent scalars (design pitfall 5: the scalars are `N(N+1) − j(j+1)`, not `j(j+1)`)
   is pinned in `Tests/GeneralSCasimirDescent.lean`, Groups 3–4
   (`casimirPenaltyScalars 2 1 = [6, 4]`, `casimirDescentStep 2 f₂ = 0`).  Plus `onEmbS_list_prod`
   referenced from the shared embedding module `SiteBlockEmbeddingD5b` rather than from any
   `N`-specific consumer, which is what lets the general-`S` module reduce a bond term to `onEmbS`
   without importing the `N = 3` certificate tables.
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

/-- `casimirPenaltyWeight 1 2 = 24 = (2·3 − 0)(2·3 − 2) = 6 · 4`: the `S = 1` weight, numerically
the same `24` that `bondCasimirPenaltyS_one` carries in Group 1.  The two are pinned separately;
no theorem identifies the weight function with that operator factor. -/
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

/-! ## Group 3: root-set pinning of the weight function at `S = 2` -/

/-- `casimirPenaltyWeight 2 J = 0 ↔ J ≤ 2` for every `J ≤ 4`: an `∏_{j < S}` instead of
`∏_{j ≤ S}` in `casimirPenaltyWeight` gives the wrong root set here.  What is fixed is the root set
of the weight function only; the operator `bondCasimirPenaltyS` carries its own index range and is
untouched by this example. -/
example (J : ℕ) (hJ : J ≤ 4) : casimirPenaltyWeight 2 J = 0 ↔ J ≤ 2 := by
  interval_cases J <;> norm_num [casimirPenaltyWeight, Finset.prod_range_succ]

/-! ## Group 4: non-degeneracy control -/

/-- At `J = 2` the weight is nonzero for `S = 1` (`24`, Group 2) but zero for `S = 2`
(`J ≤ S`); a weight definition that silently ignores `S` cannot satisfy both. -/
example : casimirPenaltyWeight 2 2 = 0 :=
  casimirPenaltyWeight_eq_zero (le_refl 2)

/-! ## Group 5: divisibility capstone, shape and `S = 1` oracle -/

/-- **Capstone shape.** `prod_fBond_pow_dvd_weylMap_of_annihilated` at its general signature: the
local kernel statement is discharged in-line by `f2_pow_dvd_weylMap_of_localCasimirPenalty` and is
not a hypothesis here, so a state `Φ` annihilated by every open-bond Casimir penalty alone forces
the prime-power product `∏ f_x ^ S` to divide `weylMap Φ`. -/
example (hL : 2 ≤ L) (S : ℕ) (Φ : (Fin L → Fin (2 * S + 1)) → ℂ)
    (hΦ : ∀ x ∈ openBonds L, (bondCasimirPenaltyS x (ringSucc x) S).mulVec Φ = 0) :
    (∏ x ∈ openBonds L, fBond x ^ S) ∣ weylMap Φ :=
  prod_fBond_pow_dvd_weylMap_of_annihilated hL S Φ hΦ

/-- **`S = 1` oracle, general-`S` route.** The same capstone shape as above, instantiated at
`S = 1`; the local kernel is discharged for every `S`, not just `S = 1`, by
`f2_pow_dvd_weylMap_of_localCasimirPenalty` inside `prod_fBond_pow_dvd_weylMap_of_annihilated`
itself. -/
example {L : ℕ} (hL : 2 ≤ L) (Φ : (Fin L → Fin 3) → ℂ)
    (hΦ : ∀ x ∈ openBonds L, (bondCasimirPenaltyS x (ringSucc x) 1).mulVec Φ = 0) :
    (∏ x ∈ openBonds L, fBond x ^ 1) ∣ weylMap Φ :=
  prod_fBond_pow_dvd_weylMap_of_annihilated hL 1 Φ hΦ

/-- **`S = 1` oracle, independent spin-one cross-check.** The same local-kernel discharge at
`S = 1`, derived independently from the pre-existing spin-one tree
(`bondCasimirPenaltyS_one`, `bondLocal_ker_eq_vbsBondSubspace`,
`f2_dvd_weylMap_of_mem_vbsBondSubspace`) rather than from
`f2_pow_dvd_weylMap_of_localCasimirPenalty`.  Kept beside the general route as the only independent
check available (the `S = 3/2` tables are a different model and must not be used). -/
example (φ : (Fin 2 → Fin 3) → ℂ) (hφ : (localCasimirPenalty 1).mulVec φ = 0) :
    f2 ^ 1 ∣ weylMap (L := 2) φ := by
  rw [pow_one]
  refine f2_dvd_weylMap_of_mem_vbsBondSubspace _ ?_
  rw [← bondLocal_ker_eq_vbsBondSubspace]
  have hz : (bondSpin2ProjectionS (0 : Fin 2) 1).mulVec φ = 0 := by
    have h24 : localCasimirPenalty 1 = (24 : ℂ) • bondSpin2ProjectionS (0 : Fin 2) 1 :=
      bondCasimirPenaltyS_one 0 1
    rw [h24, Matrix.smul_mulVec] at hφ
    exact (smul_eq_zero.mp hφ).resolve_left (by norm_num)
  simpa [LinearMap.mem_ker] using hz

/-! ## Group 6 (PR-4a, `#5292`): the local kernel becomes an iff

`localCasimirPenalty_mulVec_eq_zero_iff_f2_pow_dvd` does not exist yet on this branch (it *replaces*
`f2_pow_dvd_weylMap_of_localCasimirPenalty`, design report §2.2); every example below is expected to
fail to elaborate until PR-4a lands. -/

/-- **Signature pin at `S = 1`, `⊆` direction (`.mp`).** The general-`S` local-kernel iff
`localCasimirPenalty_mulVec_eq_zero_iff_f2_pow_dvd`, instantiated at `S = 1` and read via `.mp`,
states verbatim what the bespoke spin-one derivation above proves; being the same proposition, the
two cannot disagree.  What this pins is the signature — a general-`S` statement that no longer
instantiates to the spin-one one fails to elaborate here.  The sign of the Casimir-descent scalars
(`N(N+1) − j(j+1)`, not `j(j+1)`) is pinned numerically in `Tests/GeneralSCasimirDescent.lean`,
Groups 3–4. -/
example (φ : (Fin 2 → Fin 3) → ℂ) (hφ : (localCasimirPenalty 1).mulVec φ = 0) :
    f2 ^ 1 ∣ weylMap (L := 2) φ :=
  (localCasimirPenalty_mulVec_eq_zero_iff_f2_pow_dvd 1 φ).mp hφ

/-- **New-direction oracle (`⊇`, `.mpr`), independent cross-check.** Each of the four VBS bond
generators `vbsBondVec σ σ'` independently satisfies both sides of the `S = 1` iff by pre-existing
routes with *no* dependency on the new lemma: `f₂ ∣ weylMap (vbsBondVec σ σ')`
(`f2_dvd_weylMap_vbsBondVec`) and `(localCasimirPenalty 1).mulVec (vbsBondVec σ σ') = 0`
(`bondCasimirPenaltyS_one` + `bondLocal_mulVec_vbsBondVec`).  This is the trip-wire for the newly
proved `⊇` direction: the `S = 3/2` tables are a different model and must not be used. -/
example (σ σ' : Fin 2) :
    (localCasimirPenalty 1).mulVec (vbsBondVec σ σ') = 0 := by
  have h24 : localCasimirPenalty 1 = (24 : ℂ) • bondSpin2ProjectionS (0 : Fin 2) 1 :=
    bondCasimirPenaltyS_one 0 1
  rw [h24, Matrix.smul_mulVec, bondLocal_mulVec_vbsBondVec, smul_zero]

/-- **The same target, derived from the new `.mpr` direction.** Consistency check: applying
`localCasimirPenalty_mulVec_eq_zero_iff_f2_pow_dvd` at `S = 1` to the independently-known
`f2_dvd_weylMap_vbsBondVec` must produce the *same* conclusion as the independent derivation
directly above. -/
example (σ σ' : Fin 2) :
    (localCasimirPenalty 1).mulVec (vbsBondVec σ σ') = 0 :=
  (localCasimirPenalty_mulVec_eq_zero_iff_f2_pow_dvd 1 (vbsBondVec σ σ')).mpr
    (by rw [pow_one]; exact f2_dvd_weylMap_vbsBondVec σ σ')

/-- **`onEmbS_list_prod` module-boundary regression.** The block-embedding-of-a-list-product lemma
lives in the shared embedding module `SiteBlockEmbeddingD5b` alongside the `onEmbS` ring-transport
lemmas it is proved from, and is not `private`, so every spin can reduce an ordered product of
local bond factors to `onEmbS` without importing an `N`-specific certificate table. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {m N : ℕ}
    (ι : Fin m → Λ) (hι : Function.Injective ι)
    (l : List (Matrix (Fin m → Fin (N + 1)) (Fin m → Fin (N + 1)) ℂ)) :
    onEmbS ι l.prod = (l.map fun A => onEmbS ι A).prod :=
  onEmbS_list_prod ι hι l

end LatticeSystem.Tests.GeneralSBondTermSpinOne
