import LatticeSystem.Quantum.SpinS.GeneralSWeylCasimir

/-!
# Regression tests for the Weyl transport of the two-site Casimir

`LatticeSystem.Quantum.SpinS.GeneralSWeylCasimir` claims that the bond Casimir
`Ĉ = (Ŝ₀ + Ŝ₁)²` of two spin-`S` sites acts, under `weylMap`, as `N(N+1) − f₂ Ω` (`N = 2S`).

Three groups, in backward-chaining order:

1. **The two `N = 1` (spin-½) eigenvalues** — the highest-value tests.  The triplet basis vector
   `|↑↑⟩` is `Ω`-annihilated and must come back with `J(J+1) = 2`, while the singlet
   `|↑↓⟩ − |↓↑⟩` (Weyl image `f₂`, with `Ω f₂ = 2`) must come back with `0`.  Together they pin
   *both* the additive constant `N(N+1)` and the sign of the `f₂ Ω` term: flipping the sign, or
   shifting the constant, breaks the singlet test.
2. **Scalar sanity** — the arithmetic core `2·(N/2)(N/2+1) + N²/2 = N(N+1)` on its own, so a
   miscomputed constant is localised independently of the operator content.
3. **Signature pin** — a bare term-level type check, catching signature drift independently of the
   proof.
-/

open MvPolynomial LatticeSystem.Math LatticeSystem.Quantum LatticeSystem.Quantum.AKLTUniqueness

namespace LatticeSystem.Tests.GeneralSWeylCasimir

/-! ## Group 1: the two `N = 1` bond eigenvalues -/

/-- At `N = 1` the Weyl image of the aligned basis vector `|↑↑⟩` is the monomial `u₀u₁`. -/
private theorem weylMap_N1_up_up (φ : (Fin 2 → Fin 2) → ℂ)
    (hφ : φ = Pi.single (![0, 0] : Fin 2 → Fin 2) 1) :
    weylMap φ = X ((0 : Fin 2), (0 : Fin 2)) * X ((1 : Fin 2), (0 : Fin 2)) := by
  have hmd : md (![0, 0] : Fin 2 → Fin 2)
      = Finsupp.single ((0 : Fin 2), (0 : Fin 2)) 1
        + Finsupp.single ((1 : Fin 2), (0 : Fin 2)) 1 := by
    simp [md, mdSite, Fin.sum_univ_two]
  have hcg : cgNorm (![0, 0] : Fin 2 → Fin 2) = 1 := by
    simp [cgNorm, cgSite, Fin.prod_univ_two]
  rw [hφ]
  simp only [weylMap, Fintype.linearCombination_apply_single, one_smul, weylMono, hmd, hcg]
  rw [X, X, monomial_mul, one_mul]

/-- **Top-spin eigenvalue.**  At `N = 1` (two spin-½ sites) the aligned state `|↑↑⟩` has bond spin
`J = 1`, so `Ĉ` acts on it by `J(J+1) = 2`.  On the Weyl side its image `u₀u₁` is annihilated by
`Ω = ∂_{u₀}∂_{v₁} − ∂_{v₀}∂_{u₁}` (no `v` variable occurs), so the whole eigenvalue must come from
the constant `N(N+1) = 2`. -/
theorem weylMap_mulVec_bondCasimirS_N1_triplet (φ : (Fin 2 → Fin 2) → ℂ)
    (hφ : φ = Pi.single (![0, 0] : Fin 2 → Fin 2) 1) :
    weylMap ((bondCasimirS (0 : Fin 2) 1 1).mulVec φ)
      = (2 : ℂ) • (X ((0 : Fin 2), (0 : Fin 2)) * X ((1 : Fin 2), (0 : Fin 2))) := by
  have hw := weylMap_N1_up_up φ hφ
  have hzero : bondOmega ((0 : Fin 2), (0 : Fin 2)) (1, 1) (0, 1) (1, 0)
      (X ((0 : Fin 2), (0 : Fin 2)) * X ((1 : Fin 2), (0 : Fin 2))) = 0 := by
    rw [bondOmega_apply]
    simp [Prod.ext_iff]
  rw [weylMap_mulVec_bondCasimirS, hw, hzero, mul_zero, sub_zero]
  norm_num

/-- At `N = 1` the Weyl image of the singlet `|↑↓⟩ − |↓↑⟩` is exactly the bond factor `f₂`. -/
private theorem weylMap_N1_singlet (φ : (Fin 2 → Fin 2) → ℂ)
    (hφ : φ = Pi.single (![0, 1] : Fin 2 → Fin 2) 1 - Pi.single (![1, 0] : Fin 2 → Fin 2) 1) :
    weylMap φ = f2 := by
  have hmd₁ : md (![0, 1] : Fin 2 → Fin 2)
      = Finsupp.single ((0 : Fin 2), (0 : Fin 2)) 1
        + Finsupp.single ((1 : Fin 2), (1 : Fin 2)) 1 := by
    simp [md, mdSite, Fin.sum_univ_two]
  have hmd₂ : md (![1, 0] : Fin 2 → Fin 2)
      = Finsupp.single ((0 : Fin 2), (1 : Fin 2)) 1
        + Finsupp.single ((1 : Fin 2), (0 : Fin 2)) 1 := by
    simp [md, mdSite, Fin.sum_univ_two]
  have hcg₁ : cgNorm (![0, 1] : Fin 2 → Fin 2) = 1 := by
    simp [cgNorm, cgSite, Fin.prod_univ_two]
  have hcg₂ : cgNorm (![1, 0] : Fin 2 → Fin 2) = 1 := by
    simp [cgNorm, cgSite, Fin.prod_univ_two]
  rw [hφ, map_sub]
  simp only [weylMap, Fintype.linearCombination_apply_single, one_smul, weylMono, hmd₁, hmd₂,
    hcg₁, hcg₂]
  rw [f2, bondFactor, X, X, monomial_mul, one_mul, X, X, monomial_mul, one_mul]

/-- **Singlet eigenvalue.**  At `N = 1` the singlet `|↑↓⟩ − |↓↑⟩` has bond spin `J = 0`, so `Ĉ`
annihilates it.  Its Weyl image is `f₂` itself, on which `Ω f₂ = 2` (`bondOmega_bondFactor_self`),
so the identity returns `2·f₂ − f₂·2 = 0`: the constant `N(N+1) = 2` and the coefficient *and sign*
of the `f₂ Ω` term have to match exactly, which makes this the sharpest of the tests. -/
theorem weylMap_mulVec_bondCasimirS_N1_singlet (φ : (Fin 2 → Fin 2) → ℂ)
    (hφ : φ = Pi.single (![0, 1] : Fin 2 → Fin 2) 1 - Pi.single (![1, 0] : Fin 2 → Fin 2) 1) :
    weylMap ((bondCasimirS (0 : Fin 2) 1 1).mulVec φ) = 0 := by
  have hw := weylMap_N1_singlet φ hφ
  have hconst : ((1 : ℕ) : ℂ) * (((1 : ℕ) : ℂ) + 1) = 2 := by norm_num
  rw [weylMap_mulVec_bondCasimirS, hw, f2,
    bondOmega_bondFactor_self (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hconst, smul_eq_C_mul, map_ofNat]
  ring

/-! ## Group 2: the scalar core -/

/-- Scalar sanity: the two contributions to the Casimir constant — the on-site part
`2·S(S+1) = 2·(N/2)(N/2+1)` and the Euler part `N²/2` from `¼(a₀+b₀)(a₁+b₁)` — add up to the
top-spin eigenvalue `N(N+1)`. -/
example (N : ℕ) :
    2 * (((N : ℂ) / 2) * ((N : ℂ) / 2 + 1)) + (N : ℂ) * (N : ℂ) / 2 = (N : ℂ) * (N + 1) := by
  ring

/-! ## Group 3: signature pin -/

/-- Signature pin: `weylMap_mulVec_bondCasimirS` has the exact type
`weylMap (Ĉ *ᵥ φ) = N(N+1) • weylMap φ − f₂ · Ω (weylMap φ)`. -/
example (N : ℕ) (φ : (Fin 2 → Fin (N + 1)) → ℂ) :
    weylMap ((bondCasimirS (0 : Fin 2) 1 N).mulVec φ)
      = ((N : ℂ) * (N + 1)) • weylMap φ
        - f2 * bondOmega ((0 : Fin 2), (0 : Fin 2)) (1, 1) (0, 1) (1, 0) (weylMap φ) :=
  weylMap_mulVec_bondCasimirS N φ

end LatticeSystem.Tests.GeneralSWeylCasimir
