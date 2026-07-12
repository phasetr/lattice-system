import LatticeSystem.Quantum.SpinS.AndersonTowerOrderSqMoment
import LatticeSystem.Quantum.SpinS.AndersonTowerTanakaCapstone

/-!
# Tasaki §4.2.2 Proposition 4.10 (L5-a): the `ô²`-collapse identity (4.2.60)

The purely algebraic collapse identity (Tasaki eq. (4.2.60)) for the squared-order operator
`B := ô² = orderSqOp`.  Writing `R_k := orderSqMoment d L N Φ k = ⟨Φ, Bᵏ Φ⟩` for the `ô²`-moments,
`Φ̂ := unitNormalize Φ`, and `B^j Φ` for the `j`-th tower term, the two unit-normalized vectors
`unitNormalize (Bʲ Φ)` and `Φ̂` differ in squared `L²`-norm by

`‖ unitNormalize (Bʲ Φ) − Φ̂ ‖² = 2 ( 1 − R_j / (√R_{2j} · √R_0) )`.

This is unconditional (no Conjecture 4.12, no isotropy `L4b`, no long-range-order input): it is the
sesquilinear expansion `‖û − v̂‖² = 2 − 2 Re⟨û, v̂⟩` of two unit vectors, combined with the two
Hermitian facts `‖Bʲ Φ‖² = ⟨Φ, B^{2j} Φ⟩ = R_{2j}` (`hermitian_pow_dotProduct_split`) and
`⟨Bʲ Φ, Φ⟩ = ⟨Φ, Bʲ Φ⟩ = R_j` (both real, `B` Hermitian).  The hypothesis `0 < R_{2j}` (supplied
downstream by the long-range-order lower bound `orderSqMoment_ge`) and `Φ ≠ 0` (giving `0 < R_0`)
make both unit normalizations well-defined.

The collapse of the right-hand side `R_j / (√R_{2j} √R_0) → 1` as `L ↑ ∞` (the moment ratio going to
`(m*)²`) and its assembly into the sphere-average constant predicate are the sequel arcs `L5-b` /
`PR-6`; this file supplies only the algebraic identity they consume.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, Proposition 4.10, eq. (4.2.60), p. 108.
-/

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

/-- **The `ô²`-collapse identity** (Tasaki eq. (4.2.60)): for the squared-order operator
`B := ô² = orderSqOp` on the hypercubic torus, with moments `R_k := orderSqMoment d L N Φ k`,

`vecNormSqRe (unitNormalize (Bʲ Φ) − unitNormalize Φ) = 2 (1 − R_j / (√R_{2j} · √R_0))`.

Purely algebraic and unconditional: the sesquilinear expansion `‖û − v̂‖² = 2 − 2 Re⟨û, v̂⟩` of the
two unit vectors `û = unitNormalize (Bʲ Φ)`, `v̂ = unitNormalize Φ`, using `B` Hermitian to read
`‖Bʲ Φ‖² = R_{2j}` and `⟨Bʲ Φ, Φ⟩ = ⟨Φ, Bʲ Φ⟩ = R_j` (real).  The hypotheses `0 < R_{2j}` and
`Φ ≠ 0` make both normalizations well-defined.  Specialized to `orderSqOp` (its only consumer, the
Proposition 4.10 sphere-average assembly PR-6); no generic `IsHermitian`/`PosSemidef` lift. -/
theorem orderSq_collapse_vecNormSqRe (d L N j : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (hΦ : Φ ≠ 0)
    (hpos : 0 < orderSqMoment d L N Φ (2 * j)) :
    vecNormSqRe (unitNormalize ((orderSqOp (torusParitySublattice d L) N ^ j).mulVec Φ)
        - unitNormalize Φ)
      = 2 * (1 - orderSqMoment d L N Φ j
          / (Real.sqrt (orderSqMoment d L N Φ (2 * j)) * Real.sqrt (orderSqMoment d L N Φ 0))) := by
  classical
  set B := orderSqOp (torusParitySublattice d L) N with hBdef
  set u := (B ^ j).mulVec Φ with hudef
  set R2j := orderSqMoment d L N Φ (2 * j) with hR2jdef
  set Rj := orderSqMoment d L N Φ j with hRjdef
  set R0 := orderSqMoment d L N Φ 0 with hR0def
  have hH : B.IsHermitian := orderSqOp_torus_isHermitian d L N
  -- `‖Bʲ Φ‖² = R_{2j}` (Hermitian split `⟨Bʲ Φ, Bʲ Φ⟩ = ⟨Φ, B^{2j} Φ⟩`).
  have hvsu : vecNormSqRe u = R2j := by
    rw [vecNormSqRe, hudef, hermitian_pow_dotProduct_split hH j j Φ,
      orderSq_dotProduct_eq_orderSqMoment, Complex.ofReal_re, hR2jdef, two_mul]
  -- `‖Φ‖² = R_0` (the zeroth moment is the plain squared norm).
  have hvsv : vecNormSqRe Φ = R0 := by
    rw [vecNormSqRe, hR0def, orderSqMoment, pow_zero, Matrix.one_mulVec]
  -- Positivity of both normalization denominators.
  have hΦpos : 0 < vecNormSqRe Φ := by
    rw [vecNormSqRe]; exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hΦ)).1
  have hupos : 0 < vecNormSqRe u := by rw [hvsu]; exact hpos
  -- `⟨Φ, Bʲ Φ⟩ = R_j` and `⟨Bʲ Φ, Φ⟩ = R_j` (both real, `B` Hermitian).
  have hstarΦu : star Φ ⬝ᵥ u = (Rj : ℂ) := by
    rw [hudef, hRjdef]; exact orderSq_dotProduct_eq_orderSqMoment d L N Φ j
  have hstaruΦ : star u ⬝ᵥ Φ = (Rj : ℂ) := by
    have h := hermitian_pow_dotProduct_split hH j 0 Φ
    rw [pow_zero, Matrix.one_mulVec, add_zero] at h
    rw [hudef, h, ← hudef]; exact hstarΦu
  -- Unit-normalized rewrites, exposing the real inverse-norm scalars.
  have hUu : unitNormalize u = ((Real.sqrt R2j : ℝ) : ℂ)⁻¹ • u := by rw [unitNormalize, hvsu]
  have hUv : unitNormalize Φ = ((Real.sqrt R0 : ℝ) : ℂ)⁻¹ • Φ := by rw [unitNormalize, hvsv]
  -- Sesquilinear expansion of `⟨û − v̂, û − v̂⟩` into `2 − 2·(√R_{2j}⁻¹ √R_0⁻¹ R_j)`.
  have huu : star (unitNormalize u) ⬝ᵥ unitNormalize u = 1 :=
    unitNormalize_dotProduct_self u hupos
  have hvv : star (unitNormalize Φ) ⬝ᵥ unitNormalize Φ = 1 :=
    unitNormalize_dotProduct_self Φ hΦpos
  have huv : star (unitNormalize u) ⬝ᵥ unitNormalize Φ
      = ((Real.sqrt R2j : ℝ) : ℂ)⁻¹ * ((Real.sqrt R0 : ℝ) : ℂ)⁻¹ * (Rj : ℂ) := by
    rw [hUu, hUv, star_smul_dotProduct_smul, hstaruΦ, Complex.star_def, map_inv₀,
      Complex.conj_ofReal]
  have hvu : star (unitNormalize Φ) ⬝ᵥ unitNormalize u
      = ((Real.sqrt R2j : ℝ) : ℂ)⁻¹ * ((Real.sqrt R0 : ℝ) : ℂ)⁻¹ * (Rj : ℂ) := by
    rw [hUu, hUv, star_smul_dotProduct_smul, hstarΦu, Complex.star_def, map_inv₀,
      Complex.conj_ofReal]
    ring
  have key : star (unitNormalize u - unitNormalize Φ) ⬝ᵥ (unitNormalize u - unitNormalize Φ)
      = 2 - 2 * (((Real.sqrt R2j : ℝ) : ℂ)⁻¹ * ((Real.sqrt R0 : ℝ) : ℂ)⁻¹ * (Rj : ℂ)) := by
    rw [star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, huu, hvv, huv, hvu]
    ring
  -- Take real parts: the right-hand side is (a cast of) a real number.
  have hcast : (2 : ℂ) - 2 * (((Real.sqrt R2j : ℝ) : ℂ)⁻¹ * ((Real.sqrt R0 : ℝ) : ℂ)⁻¹ * (Rj : ℂ))
      = ((2 * (1 - Rj / (Real.sqrt R2j * Real.sqrt R0)) : ℝ) : ℂ) := by
    push_cast; ring
  rw [vecNormSqRe, key, hcast, Complex.ofReal_re]

end LatticeSystem.Quantum
