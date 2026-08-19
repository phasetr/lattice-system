import LatticeSystem.Quantum.SpinS.GeneralAKLT
import LatticeSystem.Quantum.SpinS.GeneralSWeylLadder
import LatticeSystem.Quantum.SpinS.AKLTUniqueness.LocalBondDivisibility
import LatticeSystem.Math.MvPolynomial.BondFactorDerivation

/-!
# Weyl transport of the two-site Casimir

For two spin-`S` sites (`N = 2S`) the bond Casimir `Ĉ = (Ŝ₀ + Ŝ₁)² = 2S(S+1) + 2 Ŝ₀·Ŝ₁`
(`bondCasimirS`) becomes, under the Weyl (Schwinger-boson) map `weylMap`, the second-order
differential operator

  `Ĉ ↦ N(N+1) − f₂ Ω`,  `f₂ = u₀v₁ − v₀u₁`,  `Ω = ∂_{u₀}∂_{v₁} − ∂_{v₀}∂_{u₁}`.

This is the identity that turns the spectral condition "the bond carries total spin `J`", i.e. the
eigenvalue `J(J+1)` of `Ĉ`, into an *algebraic* condition on the Weyl image, since the commutator
layer (`bondOmega_bond_mul_of_isWeightedHomogeneous`) records how multiplication by `f₂` shifts
`Ω`, and hence the Casimir value, with no spectral theory involved.

Two ingredients meet here, and nothing else is needed:

* the per-site transports of `Ŝ^+`, `Ŝ^-`, `Ŝ^{(3)}` (`GeneralSWeylLadder`), composed by
  `Matrix.mulVec_mulVec` so that each two-site product of the ladder decomposition
  `Ŝ₀·Ŝ₁ = ½(Ŝ₀^+Ŝ₁^- + Ŝ₀^-Ŝ₁^+) + Ŝ₀^{(3)}Ŝ₁^{(3)}` transports to a composition of two per-site
  differential operators;
* the derivation layer (`BondFactorDerivation`): the universal distribution
  `f₂ Ω = a₀b₁ + b₀a₁ − (u₀∂_{v₀})(v₁∂_{u₁}) − (v₀∂_{u₀})(u₁∂_{v₁})` recognises the transported
  ladder terms, and the per-site Euler identity collapses the leftover
  `¼(a₀+b₀)(a₁+b₁)` to the scalar `N²/4` because a Weyl image has degree exactly `N` in each site's
  own pair of variables.

The constant is then forced: `2·(N/2)(N/2+1) + N²/2 = N(N+1)`, the top-spin (`J = N`) eigenvalue,
which is the value `Ω`-annihilated polynomials must carry.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.1.3 "The Uniqueness of the Ground State", pp. 186–188, eqs. (7.1.22)–(7.1.25); polynomial
representation due to Arovas–Auerbach–Haldane [10]; proof due to Kennedy–Lieb–Tasaki [41].
-/

open MvPolynomial LatticeSystem.Math LatticeSystem.Quantum.AKLTUniqueness

namespace LatticeSystem.Quantum

variable {L N : ℕ}

/-- Additivity of a per-variable Euler operator `X i ∂_i`: it fuses the two halves of an inner
per-site Euler identity that sit under an outer Euler operator. -/
private theorem mul_pderiv_add (i : Fin L × Fin 2) (p q : MvPolynomial (Fin L × Fin 2) ℂ) :
    X i * pderiv i p + X i * pderiv i q = X i * pderiv i (p + q) := by
  rw [map_add, mul_add]

/-- Homogeneity of a per-variable Euler operator `X i ∂_i`: it pulls a scalar out, which is what
lets the inner site's Euler eigenvalue pass through the outer site's operator. -/
private theorem mul_pderiv_smul (i : Fin L × Fin 2) (r : ℂ) (p : MvPolynomial (Fin L × Fin 2) ℂ) :
    X i * pderiv i (r • p) = r • (X i * pderiv i p) := by
  rw [Derivation.map_smul, mul_smul_comm]

/-- **Euler identity on a Weyl image.**  A Weyl image carries degree exactly `N = 2S` in the two
variables of every site (`weylMap_isWeightedHomogeneous`), so the per-site Euler operator
`u_x∂_{u_x} + v_x∂_{v_x}` acts on it as the scalar `N`.  This is the only place where the spin
enters the Casimir eigenvalue. -/
private theorem weylMap_site_euler (x : Fin L) (φ : (Fin L → Fin (N + 1)) → ℂ) :
    X ((x, 0) : Fin L × Fin 2) * pderiv (x, 0) (weylMap φ)
        + X ((x, 1) : Fin L × Fin 2) * pderiv (x, 1) (weylMap φ)
      = (N : ℂ) • weylMap φ := by
  rw [site_euler (weylMap_isWeightedHomogeneous φ), weylMapWeight_apply]
  exact (Nat.cast_smul_eq_nsmul ℂ N _).symm

/-- **The two-site Casimir intertwiner.**  Under the Weyl map the bond Casimir
`Ĉ = (Ŝ₀ + Ŝ₁)²` of two spin-`S` sites (`N = 2S`) acts as `N(N+1) − f₂ Ω`, with `f₂` the bond factor
`u₀v₁ − v₀u₁` and `Ω = ∂_{u₀}∂_{v₁} − ∂_{v₀}∂_{u₁}` its bond derivation (Tasaki §7.1.3,
eqs. (7.1.22)–(7.1.25)).

Both extreme cases are visible in the identity itself: a polynomial in the kernel of `Ω` carries the
top eigenvalue `J(J+1) = N(N+1)`, i.e. total spin `J = N`; on `f₂` itself (the two-site singlet at
`N = 1`) the identity returns `2·f₂ − f₂·(Ω f₂) = 2f₂ − 2f₂ = 0`, i.e. `J = 0`.

Proof: transport the ladder decomposition
`Ŝ₀·Ŝ₁ = ½(Ŝ₀^+Ŝ₁^- + Ŝ₀^-Ŝ₁^+) + Ŝ₀^{(3)}Ŝ₁^{(3)}` site by site (each two-site product becoming a
composition of two per-site operators via `Matrix.mulVec_mulVec`), match the four ladder terms
against `bondFactor_mul_bondOmega_two_site`, and collapse the surviving
`¼(a₀+b₀)(a₁+b₁)` by the per-site Euler identity. -/
theorem weylMap_mulVec_bondCasimirS (N : ℕ) (φ : (Fin 2 → Fin (N + 1)) → ℂ) :
    weylMap ((bondCasimirS (0 : Fin 2) 1 N).mulVec φ)
      = ((N : ℂ) * (N + 1)) • weylMap φ
        - f2 * bondOmega ((0 : Fin 2), (0 : Fin 2)) (1, 1) (0, 1) (1, 0) (weylMap φ) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hPM : weylMap ((onSiteS (0 : Fin 2) (spinSOpPlus N) * onSiteS 1 (spinSOpMinus N)).mulVec φ)
      = X ((0 : Fin 2), (0 : Fin 2)) * pderiv (0, 1)
          (X ((1 : Fin 2), (1 : Fin 2)) * pderiv (1, 0) (weylMap φ)) := by
    rw [← Matrix.mulVec_mulVec, weylMap_mulVec_onSiteS_spinSOpPlus,
      weylMap_mulVec_onSiteS_spinSOpMinus]
  have hMP : weylMap ((onSiteS (0 : Fin 2) (spinSOpMinus N) * onSiteS 1 (spinSOpPlus N)).mulVec φ)
      = X ((0 : Fin 2), (1 : Fin 2)) * pderiv (0, 0)
          (X ((1 : Fin 2), (0 : Fin 2)) * pderiv (1, 1) (weylMap φ)) := by
    rw [← Matrix.mulVec_mulVec, weylMap_mulVec_onSiteS_spinSOpMinus,
      weylMap_mulVec_onSiteS_spinSOpPlus]
  have hTT : weylMap ((onSiteS (0 : Fin 2) (spinSOp3 N) * onSiteS 1 (spinSOp3 N)).mulVec φ)
      = (1 / 4 : ℂ) • (X ((0 : Fin 2), (0 : Fin 2)) * pderiv (0, 0)
              (X ((1 : Fin 2), (0 : Fin 2)) * pderiv (1, 0) (weylMap φ))
            - X ((0 : Fin 2), (0 : Fin 2)) * pderiv (0, 0)
              (X ((1 : Fin 2), (1 : Fin 2)) * pderiv (1, 1) (weylMap φ))
            - X ((0 : Fin 2), (1 : Fin 2)) * pderiv (0, 1)
              (X ((1 : Fin 2), (0 : Fin 2)) * pderiv (1, 0) (weylMap φ))
            + X ((0 : Fin 2), (1 : Fin 2)) * pderiv (0, 1)
              (X ((1 : Fin 2), (1 : Fin 2)) * pderiv (1, 1) (weylMap φ))) := by
    rw [← Matrix.mulVec_mulVec, weylMap_mulVec_onSiteS_spinSOp3, weylMap_mulVec_onSiteS_spinSOp3]
    simp only [Derivation.map_smul, map_sub, mul_smul_comm, mul_sub]
    module
  have heuler : X ((0 : Fin 2), (0 : Fin 2)) * pderiv (0, 0)
              (X ((1 : Fin 2), (0 : Fin 2)) * pderiv (1, 0) (weylMap φ))
            + X ((0 : Fin 2), (0 : Fin 2)) * pderiv (0, 0)
              (X ((1 : Fin 2), (1 : Fin 2)) * pderiv (1, 1) (weylMap φ))
            + X ((0 : Fin 2), (1 : Fin 2)) * pderiv (0, 1)
              (X ((1 : Fin 2), (0 : Fin 2)) * pderiv (1, 0) (weylMap φ))
            + X ((0 : Fin 2), (1 : Fin 2)) * pderiv (0, 1)
              (X ((1 : Fin 2), (1 : Fin 2)) * pderiv (1, 1) (weylMap φ))
        = ((N : ℂ) * N) • weylMap φ := by
    rw [add_assoc, mul_pderiv_add, mul_pderiv_add, weylMap_site_euler (1 : Fin 2) φ,
      mul_pderiv_smul, mul_pderiv_smul, ← smul_add, weylMap_site_euler (0 : Fin 2) φ, smul_smul]
  rw [bondCasimirS, spinSDot_eq_plus_minus]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, map_add, map_smul]
  rw [hPM, hMP, hTT, f2, bondFactor_mul_bondOmega_two_site h01]
  linear_combination (norm := module) (1 / 2 : ℂ) • heuler

end LatticeSystem.Quantum
