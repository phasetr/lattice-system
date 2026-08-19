import LatticeSystem.Quantum.SpinS.GeneralSWeylLadder

/-!
# Regression tests for the per-site Weyl transport layer

`LatticeSystem.Quantum.SpinS.GeneralSWeylLadder` claims that `weylMap` intertwines each single-site
spin-`S` operator (`spinSOpPlus`, `spinSOpMinus`, `spinSOp3`) embedded at site `x` (`onSiteS x _`)
with a differential operator in the two Weyl variables of that site, for any chain length `L` and
any `x : Fin L`.

Four groups, in backward-chaining order (boundaries and the Clebsch–Gordan-critical instance
first):

1. **Boundary regression** — `j = 0` for `Ŝ^+` and `j = N` for `Ŝ^-` both vanish, but for
   *different* reasons (empty `Finset.sum` fiber vs. vanishing `pderiv` coefficient); these are
   where silent `simp` failure would live.
2. **Clebsch–Gordan regression (highest value)** — `N = 2`, lowering `Ŝ^-` at site `0` applied to
   the top state `u₀²u₁²` (`weylMono ![0, 0]`) must land at `2·u₀v₀u₁²`, not `√2·u₀v₀u₁²`; the
   latter is what a *unit*-weight Clebsch–Gordan normalization would (wrongly) give, so this test
   pins the `cgSite` weights, not merely the shape of the identity.
3. **`N = 1` closed form** — the raising ladder sum at `j = 1` reproduces `v_x ↦ u_x` exactly.
4. **Signature pins** — bare term-level type checks of the three global transports at a fixed `N`,
   so a signature drift is caught independently of the proof content.
-/

open MvPolynomial LatticeSystem.Math LatticeSystem.Quantum

namespace LatticeSystem.Tests.GeneralSWeylLadder

variable {L N : ℕ}

/-! ## Group 1: ladder boundary regression -/

/-- Raising at the top site-state `j = 0` (`m = N/2`, already maximal): the ladder-sum column is
`0`, and via the differential-operator side it is `0` because `weylSiteMono x 0` carries no `v_x`
dependence (its `pderiv (x,1)` vanishes), *not* because the sum over `k` is empty by inspection. -/
theorem weylSiteMono_spinSOpPlus_sum_top (x : Fin L) :
    ∑ k : Fin (N + 1), spinSOpPlus N k 0 • weylSiteMono x k = 0 := by
  rw [weylSiteMono_spinSOpPlus_sum]
  simp [weylSiteMono, mdSite_apply_snd]

/-- Lowering at the bottom site-state `j = N` (`m = -N/2`, already minimal): the ladder-sum column
is `0`, via the differential-operator side because `weylSiteMono x N` carries no `u_x` dependence
(its `pderiv (x,0)` vanishes). -/
theorem weylSiteMono_spinSOpMinus_sum_bottom (x : Fin L) :
    ∑ k : Fin (N + 1), spinSOpMinus N k (⟨N, N.lt_succ_self⟩ : Fin (N + 1)) • weylSiteMono x k
      = 0 := by
  rw [weylSiteMono_spinSOpMinus_sum]
  simp [weylSiteMono, mdSite_apply_self]

/-! ## Group 2: `N = 2` Clebsch–Gordan regression (the highest-value single test) -/

/-- At `N = 2, L = 2`: lowering `Ŝ^-` at site `0`, applied to the top-weight config
`![0, 0] : Fin 2 → Fin 3` (Weyl image `weylMono ![0,0] = u₀²u₁²`), lands the many-body state at
`√2 • ![1, 0]` (index raised `0 ↦ 1` at site `0`, `Ŝ^-`'s matrix weight `√((2-0)(0+1)) = √2`); its
Weyl image is `√2 · weylMono ![1,0] = √2 · √2 · u₀v₀u₁² = 2 · u₀v₀u₁²`.  A Weyl map with *unit*
Clebsch–Gordan weights (`cgSite ≡ 1` instead of `√(binom N k)`) would instead give `√2 · u₀v₀u₁²`
here, so this pins the exact CG normalization, not merely the shape of the transport. -/
theorem weylMap_mulVec_onSiteS_spinSOpMinus_N2_top (φ : (Fin 2 → Fin 3) → ℂ)
    (hφ : φ = Pi.single (![0, 0] : Fin 2 → Fin 3) 1) :
    weylMap ((onSiteS (0 : Fin 2) (spinSOpMinus 2)).mulVec φ)
      = (2 : ℂ) • (X ((0 : Fin 2), (0 : Fin 2)) * X ((0 : Fin 2), 1) * X ((1 : Fin 2), 0) ^ 2) := by
  have hmd : md (![0, 0] : Fin 2 → Fin 3)
      = Finsupp.single ((0 : Fin 2), (0 : Fin 2)) 2
        + Finsupp.single ((1 : Fin 2), (0 : Fin 2)) 2 := by
    simp [md, mdSite, Fin.sum_univ_two]
  have hcg : cgNorm (![0, 0] : Fin 2 → Fin 3) = 1 := by
    simp [cgNorm, cgSite, Fin.prod_univ_two]
  have hw : weylMap φ
      = X ((0 : Fin 2), (0 : Fin 2)) ^ 2 * X ((1 : Fin 2), (0 : Fin 2)) ^ 2 := by
    simp only [hφ, weylMap, Fintype.linearCombination_apply_single, one_smul, weylMono, hmd, hcg]
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]
  have hd : pderiv ((0 : Fin 2), (0 : Fin 2))
      (X ((1 : Fin 2), (0 : Fin 2)) : MvPolynomial (Fin 2 × Fin 2) ℂ) = 0 :=
    pderiv_X_of_ne (by decide)
  rw [weylMap_mulVec_onSiteS_spinSOpMinus, hw]
  simp only [pderiv_mul, pderiv_pow, pderiv_X_self, hd, smul_eq_C_mul, map_ofNat]
  ring

/-! ## Group 3: `N = 1` closed form -/

/-- At `N = 1`: raising `Ŝ^+` at the bottom state `j = 1` (`v_x`) reproduces `v_x ↦ u_x` exactly
(`spinSOpPlus 1 0 1 = 1`, the trivial spin-`1/2` matrix element). -/
theorem weylSiteMono_spinSOpPlus_sum_N1_bottom (x : Fin L) :
    ∑ k : Fin 2, spinSOpPlus 1 k 1 • weylSiteMono x k = weylSiteMono x (0 : Fin 2) := by
  have h1 : weylSiteMono (N := 1) x (1 : Fin 2) = X ((x, 1) : Fin L × Fin 2) := by
    rw [weylSiteMono, X, mdSite, cgSite]
    norm_num
  have h0 : weylSiteMono (N := 1) x (0 : Fin 2) = X ((x, 0) : Fin L × Fin 2) := by
    rw [weylSiteMono, X, mdSite, cgSite]
    norm_num
  rw [weylSiteMono_spinSOpPlus_sum, h1, h0, pderiv_X_self, mul_one]

/-! ## Group 4: signature pins of the three global transports, `N = 2` -/

/-- Signature pin: `weylMap_mulVec_onSiteS_spinSOpPlus` at `N = 2` has the exact type
`weylMap ((onSiteS x (spinSOpPlus 2)).mulVec φ) = X (x,0) * pderiv (x,1) (weylMap φ)`. -/
example (x : Fin L) (φ : (Fin L → Fin 3) → ℂ) :
    weylMap ((onSiteS x (spinSOpPlus 2)).mulVec φ) = X (x, 0) * pderiv (x, 1) (weylMap φ) :=
  weylMap_mulVec_onSiteS_spinSOpPlus x φ

/-- Signature pin: `weylMap_mulVec_onSiteS_spinSOpMinus` at `N = 2`. -/
example (x : Fin L) (φ : (Fin L → Fin 3) → ℂ) :
    weylMap ((onSiteS x (spinSOpMinus 2)).mulVec φ) = X (x, 1) * pderiv (x, 0) (weylMap φ) :=
  weylMap_mulVec_onSiteS_spinSOpMinus x φ

/-- Signature pin: `weylMap_mulVec_onSiteS_spinSOp3` at `N = 2`. -/
example (x : Fin L) (φ : (Fin L → Fin 3) → ℂ) :
    weylMap ((onSiteS x (spinSOp3 2)).mulVec φ)
      = (1 / 2 : ℂ) • (X (x, 0) * pderiv (x, 0) (weylMap φ)
          - X (x, 1) * pderiv (x, 1) (weylMap φ)) :=
  weylMap_mulVec_onSiteS_spinSOp3 x φ

end LatticeSystem.Tests.GeneralSWeylLadder
