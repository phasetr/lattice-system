import LatticeSystem.Quantum.SpinS.AKLTUniqueness.BondDivisibilityBridge
import LatticeSystem.Quantum.SpinS.GeneralSOpenChainBondTerm
import LatticeSystem.Math.MvPolynomial.WeightedHomogeneousLayer

/-!
# The Weyl preimage and the global-to-local bond-divisibility bridge

Regression tests for the two facts that turn a *polynomial* into a *state* and a *global*
divisibility statement into a *slicewise* one:

* `weylPreimage` / `weylMap_weylPreimage` — the Weyl map inverts on its per-site graded piece, so a
  polynomial with the per-site degrees of a Weyl image is the image of an explicit state.
* `f2_pow_dvd_weylMap_bondSlice_of_fBond_pow_dvd` and the packaged bond-kernel iff
  `bondCasimirPenaltyS_mulVec_eq_zero_iff_fBond_pow_dvd` — divisibility of the chain Weyl image by
  `f_x ^ S` restricts to every two-site bond slice, so the bond term's kernel *is* the
  `f_x ^ S`-divisible Weyl images.

Pinned here: the round trip on a genuine graded input, the negative control showing that the
homogeneity hypothesis is load-bearing, composability of the two directions of the bridge (the
converse's conclusion is the forward bridge's premise), and the `S = 1` specialization against the
bespoke spin-one bond projection.
-/

open MvPolynomial LatticeSystem.Math LatticeSystem.Quantum LatticeSystem.Quantum.AKLTUniqueness

namespace LatticeSystem.Tests.GeneralSBondSliceConverse

variable {L : ℕ}

/-! ## The Weyl preimage round trip -/

/-- **Round-trip oracle.** `weylMap (weylPreimage (f₂ ^ 2)) = f₂ ^ 2`: `f₂ ^ 2` has per-site degree
`(2, 2)` at `N = 2`, so `weylMap_weylPreimage`'s homogeneity hypothesis is met and the preimage
really is a two-sided inverse on this input. Pins that `weylPreimage` recovers exactly the
polynomial it was built from, not merely something in its fiber. -/
theorem weylMap_weylPreimage_f2_sq :
    weylMap (weylPreimage (N := 2) (f2 ^ 2)) = f2 ^ 2 := by
  refine weylMap_weylPreimage ?_
  have hf2 := bondFactor_isWeightedHomogeneous (siteWeight (L := 2))
    ((0 : Fin 2), (0 : Fin 2)) (1, 1) (0, 1) (1, 0) rfl
  have hdeg : (∑ x : Fin 2, Finsupp.single x 2 : Fin 2 →₀ ℕ)
      = 2 • (siteWeight ((0 : Fin 2), (0 : Fin 2)) + siteWeight ((1 : Fin 2), (1 : Fin 2))) := by
    rw [Fin.sum_univ_two, smul_add, siteWeight, siteWeight, Finsupp.smul_single,
      Finsupp.smul_single, smul_eq_mul]
  rw [hdeg]
  exact hf2.pow 2

/-- **Negative control.** At `N = 2`, `p = X ((0 : Fin 2), 0) ^ 2` has per-site degree `(2, 0)`,
*not* `(2, 2)`, so `weylMap_weylPreimage`'s hypothesis fails and the round trip must break: no Weyl
monomial has the multidegree of `p` (they all have total degree `4`), the preimage is the zero state
and its Weyl image is `0 ≠ p`. Catches an unconditional (hypothesis-free) round-trip theorem, which
would be false; mirrors `GradedPolynomialLayerNegativeControl`. -/
theorem weylMap_weylPreimage_ne_of_not_homogeneous :
    weylMap (weylPreimage (N := 2)
        ((X ((0 : Fin 2), (0 : Fin 2)) : MvPolynomial (Fin 2 × Fin 2) ℂ) ^ 2))
      ≠ (X ((0 : Fin 2), (0 : Fin 2)) : MvPolynomial (Fin 2 × Fin 2) ℂ) ^ 2 := by
  have hzero : weylPreimage (N := 2)
      ((X ((0 : Fin 2), (0 : Fin 2)) : MvPolynomial (Fin 2 × Fin 2) ℂ) ^ 2) = 0 := by
    funext τ
    have hne : Finsupp.single ((0 : Fin 2), (0 : Fin 2)) 2 ≠ md τ := by
      intro h
      have hdeg := md_degree τ
      rw [← h, Finsupp.degree_single] at hdeg
      norm_num at hdeg
    simp [weylPreimage, X_pow_eq_monomial, coeff_monomial, hne]
  rw [hzero, map_zero]
  exact fun h => pow_ne_zero 2 (X_ne_zero ((0 : Fin 2), (0 : Fin 2))) h.symm

/-! ## The global-to-local bridge and the packaged bond-kernel iff -/

/-- **Signature pin — the crux.** `f2_pow_dvd_weylMap_bondSlice_of_fBond_pow_dvd`: if the global
bond factor `fBond x` to the power `S` divides the Weyl image of `Φ`, then the local bond factor
`f2` to the same power `S` divides the Weyl image of *every* bond slice of `Φ` at `x`. The converse
of `fBond_pow_dvd_weylMap_of_local`. -/
theorem f2_pow_dvd_weylMap_bondSlice_of_fBond_pow_dvd_sig {N : ℕ} (hL : 1 < L) (x : Fin L)
    (S : ℕ) (Φ : (Fin L → Fin (N + 1)) → ℂ) (h : fBond x ^ S ∣ weylMap Φ)
    (r : Fin L → Fin (N + 1)) :
    f2 ^ S ∣ weylMap (L := 2) (bondSlice x Φ r) :=
  f2_pow_dvd_weylMap_bondSlice_of_fBond_pow_dvd hL x S Φ h r

/-- **API consistency.** Composing the converse with the forward bridge
`fBond_pow_dvd_weylMap_of_local` returns the original hypothesis: for `Φ` with
`fBond x ^ S ∣ weylMap Φ`, going local (the converse) and then back global (the forward bridge)
reproduces `fBond x ^ S ∣ weylMap Φ`. Pins that the two statements stay composable — the converse's
conclusion is exactly the premise the forward bridge consumes, so a statement-level drift of either
(a different slice, exponent or bond-factor argument) breaks this. It does *not* probe the shared
`f2` / `fBond` / `bondEmb` definitions, which both directions inherit from the same source. -/
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
    (bondCasimirPenaltyS x (ringSucc x) S).mulVec Φ = 0 ↔ fBond x ^ S ∣ weylMap Φ :=
  bondCasimirPenaltyS_mulVec_eq_zero_iff_fBond_pow_dvd hL x S Φ

/-- **`S = 1` control.** Instantiating the packaged iff at `S = 1` and rewriting through
`bondCasimirPenaltyS_one` reproduces annihilation by `bondSpin2ProjectionS`: a state's Weyl image is
divisible by `fBond x` exactly when the spin-two bond projection annihilates it (up to the harmless
positive factor `24`). Cross-checks the `⟸` half against the spin-one bespoke route, the same role
Group 6 of `Tests/GeneralSBondTermSpinOne.lean` plays for the local (two-site) iff. -/
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
