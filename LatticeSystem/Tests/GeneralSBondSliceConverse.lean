import LatticeSystem.Quantum.SpinS.AKLTUniqueness.BondDivisibilityBridge
import LatticeSystem.Quantum.SpinS.GeneralSOpenChainBondTerm
import LatticeSystem.Math.MvPolynomial.WeightedHomogeneousLayer

/-!
# TDD Red — the Weyl preimage and the global-to-local bond-divisibility bridge (PR-6a, #5292)

**Red-phase specification tests**, per the design report
`.self-local/reports/design-5292-pr6-finrank-lower-bound-round1-20260820.md` §3 and §7 (PR-6a test
points). These tests pin the acceptance criteria of the four PR-6a declarations *before* they exist
on `main`; the file is expected to fail to build (`sorry`s are build errors under this repo's
`warningAsError` policy) until PR-6a lands the production declarations. No production logic is
written here.

## Declarations under test (not yet on `main`)

* `LatticeSystem.Math.weylPreimage {L N} (p : MvPolynomial (Fin L × Fin 2) ℂ) :
    (Fin L → Fin (N + 1)) → ℂ`
* `LatticeSystem.Math.weylMap_weylPreimage {L N} {p}
    (hp : p.IsWeightedHomogeneous siteWeight (∑ x, single x N)) : weylMap (weylPreimage p) = p`
* `LatticeSystem.Quantum.AKLTUniqueness.f2_pow_dvd_weylMap_bondSlice_of_fBond_pow_dvd
    {N} (hL : 1 < L) (x : Fin L) (S) (Φ) (h : fBond x ^ S ∣ weylMap Φ) (r) :
      f2 ^ S ∣ weylMap (L := 2) (bondSlice x Φ r)`
* `LatticeSystem.Quantum.bondCasimirPenaltyS_mulVec_eq_zero_iff_fBond_pow_dvd
    {L} (hL : 1 < L) (x) (S) (Φ) :
      (bondCasimirPenaltyS x (ringSucc x) S).mulVec Φ = 0 ↔ fBond x ^ S ∣ weylMap Φ`

## `weylPreimage` placeholder

`weylPreimage` does not exist on `main` yet, but its type is needed to state the round-trip and
negative-control tests (test points 2–3 of the design report §7). `weylPreimagePlaceholder` below is
a **type-only stand-in**: its body is `sorry`, never the design report's formula
(`p.coeff (md τ) / cgNorm τ`), so this file never duplicates the production definition it is
specifying. It must be deleted (together with the tests that use it) once PR-6a lands the real
`LatticeSystem.Math.weylPreimage` and this file is updated to reference it directly.
-/

open MvPolynomial LatticeSystem.Math LatticeSystem.Quantum LatticeSystem.Quantum.AKLTUniqueness

namespace LatticeSystem.Tests.GeneralSBondSliceConverse

variable {L : ℕ}

/-! ## `weylPreimage` placeholder (type-only, `sorry` body; see module doc) -/

/-- Type-only stand-in for the not-yet-existing `LatticeSystem.Math.weylPreimage`. Its body is
`sorry`, not the production formula, so this is a signature fixture and not production logic. -/
private noncomputable def weylPreimagePlaceholder {L N : ℕ}
    (p : MvPolynomial (Fin L × Fin 2) ℂ) : (Fin L → Fin (N + 1)) → ℂ :=
  sorry

/-! ## Test point 2: round-trip oracle at `L = 2`, `N = 2` -/

/-- **Round-trip oracle.** `weylMap (weylPreimage (f2 ^ 2)) = f2 ^ 2`: `f2 ^ 2` has per-site
degree `(2, 2)` at `N = 2`, so `weylMap_weylPreimage`'s homogeneity hypothesis is met and the
preimage really is a two-sided inverse on this input. Pins that `weylPreimage` recovers exactly the
polynomial it was built from, not merely something in its fiber. -/
theorem weylMap_weylPreimage_f2_sq :
    weylMap (weylPreimagePlaceholder (N := 2) (f2 ^ 2)) = f2 ^ 2 := by
  sorry

/-! ## Test point 3: negative control — the homogeneity hypothesis is load-bearing -/

/-- **Negative control.** At `N = 2`, `p = X ((0 : Fin 2), 0) ^ 2` has per-site degree `(2, 0)`,
*not* `(2, 2)`, so `weylMap_weylPreimage`'s hypothesis fails and the round-trip must break: `p` is
not weight-homogeneous of the degree `weylPreimage` is built to recover. Mirrors
`GradedPolynomialLayerNegativeControl`; catches an unconditional (hypothesis-free) `weylPreimage`
round-trip theorem, which would be false. -/
theorem weylMap_weylPreimage_ne_of_not_homogeneous :
    weylMap (weylPreimagePlaceholder (N := 2)
        ((X ((0 : Fin 2), (0 : Fin 2)) : MvPolynomial (Fin 2 × Fin 2) ℂ) ^ 2))
      ≠ (X ((0 : Fin 2), (0 : Fin 2)) : MvPolynomial (Fin 2 × Fin 2) ℂ) ^ 2 := by
  sorry

/-! ## Test points 1 / 4 / 5: the global-to-local bridge and the packaged bond-kernel iff -/

/-- **Signature pin — the crux.** `f2_pow_dvd_weylMap_bondSlice_of_fBond_pow_dvd`: if the global
bond factor `fBond x` to the power `S` divides the Weyl image of `Φ`, then the local bond factor
`f2` to the same power `S` divides the Weyl image of *every* bond slice of `Φ` at `x`. The converse
of the already-merged `fBond_pow_dvd_weylMap_of_local`. -/
theorem f2_pow_dvd_weylMap_bondSlice_of_fBond_pow_dvd_sig {N : ℕ} (hL : 1 < L) (x : Fin L)
    (S : ℕ) (Φ : (Fin L → Fin (N + 1)) → ℂ) (h : fBond x ^ S ∣ weylMap Φ)
    (r : Fin L → Fin (N + 1)) :
    f2 ^ S ∣ weylMap (L := 2) (bondSlice x Φ r) := by
  sorry

/-- **Direction consistency.** Composing the new converse with the already-merged forward bridge
`fBond_pow_dvd_weylMap_of_local` must return the original hypothesis: for `Φ` with
`fBond x ^ S ∣ weylMap Φ`, going local (the new lemma) and then back global (the merged one)
reproduces `fBond x ^ S ∣ weylMap Φ`. Pins that both directions agree on the same `f2` / `fBond` /
`bondEmb` convention — a `u ↔ v` drift in the new lemma would still typecheck but break this. -/
theorem fBond_pow_dvd_weylMap_round_trip {N : ℕ} (hL : 1 < L) (x : Fin L) (S : ℕ)
    (Φ : (Fin L → Fin (N + 1)) → ℂ) (h : fBond x ^ S ∣ weylMap Φ) :
    fBond x ^ S ∣ weylMap Φ :=
  fBond_pow_dvd_weylMap_of_local x hL S Φ
    (fun r => f2_pow_dvd_weylMap_bondSlice_of_fBond_pow_dvd_sig hL x S Φ h r)

/-- **Signature pin — the packaged bond-kernel iff.**
`bondCasimirPenaltyS_mulVec_eq_zero_iff_fBond_pow_dvd`: the bond term's kernel is exactly the
`fBond x ^ S`-divisible Weyl images, both directions. -/
theorem bondCasimirPenaltyS_mulVec_eq_zero_iff_fBond_pow_dvd_sig {L : ℕ} (hL : 1 < L) (x : Fin L)
    (S : ℕ) (Φ : (Fin L → Fin (2 * S + 1)) → ℂ) :
    (bondCasimirPenaltyS x (ringSucc x) S).mulVec Φ = 0 ↔ fBond x ^ S ∣ weylMap Φ := by
  sorry

/-- **`S = 1` control.** Instantiating the packaged iff at `S = 1` and rewriting through the
pre-existing `bondCasimirPenaltyS_one` reproduces annihilation by `bondSpin2ProjectionS`: a state's
Weyl image is divisible by `fBond x` exactly when the spin-two bond projection annihilates it (up to
the harmless positive factor `24`). Cross-checks the new `⟸` half against the merged spin-one
bespoke route, the same role Group 6 of `Tests/GeneralSBondTermSpinOne.lean` plays for the local
(two-site) iff. -/
theorem bondCasimirPenaltyS_mulVec_eq_zero_iff_fBond_pow_dvd_S_one {L : ℕ} (hL : 1 < L) (x : Fin L)
    (Φ : (Fin L → Fin 3) → ℂ) :
    (bondSpin2ProjectionS x (ringSucc x)).mulVec Φ = 0 ↔ fBond x ^ 1 ∣ weylMap Φ := by
  rw [← bondCasimirPenaltyS_mulVec_eq_zero_iff_fBond_pow_dvd_sig hL x 1 Φ,
    bondCasimirPenaltyS_one x (ringSucc x), Matrix.smul_mulVec, smul_eq_zero]
  constructor
  · intro h
    exact Or.inr h
  · rintro (h | h)
    · exact absurd h (by norm_num)
    · exact h

end LatticeSystem.Tests.GeneralSBondSliceConverse
