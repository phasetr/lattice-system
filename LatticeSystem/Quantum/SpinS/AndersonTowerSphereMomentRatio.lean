import LatticeSystem.Quantum.SpinS.AndersonTowerPinch
import LatticeSystem.Quantum.SpinS.AndersonTowerOrderSqMoment

/-!
# Tasaki §4.2.2 Proposition 4.10 (PR-4b): the sphere-average relative-close estimate

This module converts the pinch scalar band identity (`cartWord_sphereAverage_pinch`, PR-3.3b) from
an *absolute* remainder into a *relative* one by dividing through the `ô²`-moment lower bound
(`orderSqMoment_ge`, PR-4a).  The pinch gives, on the hypercubic torus `Λ = HypercubicTorus d L`
with `V = L^d`,

`|⟨Φ, (∫_{S²} (Ô_L^n)^{2m} dσ) Φ⟩.re − (4π/(2m+1)) R_m| ≤ cartPinchPoly m · (V·N)^{2m−2} · R_0`,

while the long-range-order moment bound gives `R_0 ≤ R_m / (q₀ V²)^m`.  Substituting the latter into
the former and cancelling the volume exponent `V^{2m−2} / V^{2m} = 1/V²` collapses the absolute
remainder to a relative one of size `C(m, N, d, q₀) / V²`:

`|⟨Φ, (∫_{S²} (Ô_L^n)^{2m} dσ) Φ⟩.re − (4π/(2m+1)) R_m|
    ≤ (cartPinchPoly m · N^{2m−2} / (q₀^m · V²)) · R_m`.

Here `R_k := orderSqMoment d L N Φ k = ⟨Φ, (ô²)^k Φ⟩.re`.  Only this finite relative inequality is
established; its `L ↑ ∞` limit (`Tendsto` of the ratio to `4π/(2m+1)`), the isotropy factor `3`, the
`Φ`-collapse and Conjecture 4.12 are the sequel PR-5/PR-6.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, Proposition 4.10, eqs. (4.2.58)–(4.2.59), p. 108.
-/

namespace LatticeSystem.Quantum

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius

/-- **Proposition 4.10 sphere-average relative-close estimate** (PR-4b tip; Tasaki §4.2.2,
eqs. (4.2.58)/(4.2.59), p. 108).  On the hypercubic torus `Λ = HypercubicTorus d L` (`V = L^d`), for
a total-spin singlet `Φ ≠ 0` (annihilated by the `Ŝ³` and `Ŝ¹` generators) satisfying the long-range
order hypothesis `q₀ ≤ ⟨(ô^{(3)})²⟩ / (‖Φ‖² V²)` with `0 < q₀`, the `2m`-th sphere average of the
direction order operator agrees with the rotationally invariant main part `(4π/(2m+1)) R_m` up to a
*relative* error `(cartPinchPoly m · N^{2m−2} / (q₀^m · V²)) R_m`, i.e. `O(1/V²)` for fixed `m`:

`|⟨Φ, (∫_{S²} (Ô_L^n)^{2m} dσ) Φ⟩.re − (4π/(2m+1)) R_m|
    ≤ (cartPinchPoly m · N^{2m−2} / (q₀^m · V²)) · R_m`,

where `R_m = orderSqMoment d L N Φ m = ⟨Φ, (ô²)^m Φ⟩.re`.  The pinch absolute remainder
`cartPinchPoly m · (V·N)^{2m−2} · R_0` is divided by the moment lower bound
`R_0 ≤ R_m / (q₀ V²)^m`, and the volume exponent cancels as `V^{2m−2} / V^{2m} = 1/V²` (for `m = 0`
the pinch prefactor `cartPinchPoly 0 = 0` makes both sides vanish). -/
theorem sphereAverage_orderSqMoment_relative_close (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (hΦ : Φ ≠ 0)
    (h3 : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (h1 : (totalSpinSOp1 (HypercubicTorus d L) N).mulVec Φ = 0)
    {q₀ : ℝ} (hq₀ : 0 < q₀)
    (hlro : q₀ ≤ (star Φ ⬝ᵥ (staggeredOrderOpS (torusParitySublattice d L) N
        * staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ).re
        / ((star Φ ⬝ᵥ Φ).re * ((L : ℝ) ^ d) ^ 2)) (m : ℕ) :
    |(star Φ ⬝ᵥ (∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
          (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) (torusParitySublattice d L) N)
            ^ (2 * m) ∂volume.toSphere).mulVec Φ).re
        - 4 * Real.pi / (2 * m + 1) * orderSqMoment d L N Φ m|
      ≤ (cartPinchPoly m * (N : ℝ) ^ (2 * m - 2) / (q₀ ^ m * ((L : ℝ) ^ d) ^ 2))
          * orderSqMoment d L N Φ m := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hcard : (Fintype.card (HypercubicTorus d L) : ℝ) = (L : ℝ) ^ d := by
    rw [card_hypercubicTorus]; push_cast; ring
  have hR0 : orderSqMoment d L N Φ 0 = (star Φ ⬝ᵥ Φ).re := by
    simp only [orderSqMoment, pow_zero, Matrix.one_mulVec]
  have hPnn : 0 ≤ cartPinchPoly m := by
    rw [cartPinchPoly]
    refine mul_nonneg (mul_nonneg (add_nonneg ?_ (by positivity)) (by positivity)) (by positivity)
    exact Finset.sum_nonneg (fun f _ => sphereMonomialMoment_nonneg _)
  -- The pinch scalar band identity, specialised to the torus with `V = L^d`.
  have hpinch := cartWord_sphereAverage_pinch (torusParitySublattice d L) hN Φ h3 h1 m
  rw [hcard] at hpinch
  -- Relative-close arithmetic: the pinch remainder is bounded by the relative one.
  have harith : cartPinchPoly m * ((L : ℝ) ^ d * (N : ℝ)) ^ (2 * m - 2) * (star Φ ⬝ᵥ Φ).re
      ≤ (cartPinchPoly m * (N : ℝ) ^ (2 * m - 2) / (q₀ ^ m * ((L : ℝ) ^ d) ^ 2))
          * orderSqMoment d L N Φ m := by
    rcases m with _ | n
    · simp [cartPinchPoly]
    · have hmom := orderSqMoment_ge d L N Φ hΦ (le_of_lt hq₀) hlro (n + 1)
      rw [hR0] at hmom
      have he : 2 * (n + 1) - 2 = 2 * n := by omega
      rw [he, mul_pow, div_mul_eq_mul_div,
        le_div_iff₀ (by positivity : (0 : ℝ) < q₀ ^ (n + 1) * ((L : ℝ) ^ d) ^ 2)]
      have hab : 0 ≤ cartPinchPoly (n + 1) * (N : ℝ) ^ (2 * n) := mul_nonneg hPnn (by positivity)
      calc cartPinchPoly (n + 1) * (((L : ℝ) ^ d) ^ (2 * n) * (N : ℝ) ^ (2 * n))
              * (star Φ ⬝ᵥ Φ).re * (q₀ ^ (n + 1) * ((L : ℝ) ^ d) ^ 2)
          = (cartPinchPoly (n + 1) * (N : ℝ) ^ (2 * n))
              * ((q₀ * ((L : ℝ) ^ d) ^ 2) ^ (n + 1) * (star Φ ⬝ᵥ Φ).re) := by ring
        _ ≤ (cartPinchPoly (n + 1) * (N : ℝ) ^ (2 * n)) * orderSqMoment d L N Φ (n + 1) :=
            mul_le_mul_of_nonneg_left hmom hab
        _ = cartPinchPoly (n + 1) * (N : ℝ) ^ (2 * n) * orderSqMoment d L N Φ (n + 1) := by ring
  exact le_trans hpinch harith

end LatticeSystem.Quantum
