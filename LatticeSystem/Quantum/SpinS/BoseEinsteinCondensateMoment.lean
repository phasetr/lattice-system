import LatticeSystem.Quantum.SpinS.BoseEinsteinCondensateAlgebra

/-!
# Tasaki §5.3 Theorem 5.2 (BEC low-lying tower states): U(1) planar moment base entry (PR-2)

This file supplies the **crux** of the Bose–Einstein-condensation tower discharge
(`tasaki_5_2_bec_tower`, Tasaki §5.3, eq. (5.3.4)): the `U(1)`-planar base entry of the
`p̂`-moment recursion, driven **directly by the two XY-plane ODLRO hypotheses** (α = 1, 2) rather
than by the `SU(2)` singlet/isotropy mechanism of the Anderson-tower Theorem 4.6.

The Anderson-tower base entry `phatMoment_one_ge_of_lro`
(`AndersonTowerEnergyBoundSU2.lean`) derives `2 q₀ m₀ ≤ m₁` from a **single** long-range-order
axis together with the `Ŝ³`/`Ŝ¹`-singlet isotropy relations
`⟨(Ô^{(1)})²⟩ = ⟨(Ô^{(2)})²⟩ = ⟨(Ô^{(3)})²⟩`.  The chemical-potential XY ground state `Φ_GS` of
Theorem 5.2 is an `Ŝ³`-sector eigenstate but is **not** a `Ŝ¹`-singlet, so that isotropy is
unavailable.  Instead the BEC hypotheses (bundled in `IsBECTowerConstants`) supply **both** planar
axes `α = 1, 2` directly:
`q₀ m₀ V² ≤ ⟨(Ô^{(1)})²⟩` and `q₀ m₀ V² ≤ ⟨(Ô^{(2)})²⟩` (`V = L^d`).  Summing the two and using
`p̂ = V⁻² ((Ô^{(1)})² + (Ô^{(2)})²)` (`staggeredPhatS_eq_cartesian_sq`) yields the identical base
ratio `2 q₀ m₀ ≤ m₁` with **no** appeal to isotropy — the same `2 q₀` constant, mathematically
simpler.

The downstream moment recursion `2 q₀ mₙ ≤ mₙ₊₁` and its geometric iterate
`(2 q₀)ⁿ m₀ ≤ mₙ` are **not re-proved here**: the singlet-free processed form
`phatMoment_succ_ratio` (`AndersonTowerEnergyBoundSU2.lean`) already takes the base entry as a
hypothesis, so the base entry proved here feeds it directly (no duplication).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §5.3, Theorem 5.2, eqs. (5.2.5)/(5.3.4), pp. 139–141 (Koma–Tasaki [21]); the `p̂`-moment
kernel is eq. (4.2.31)/(4.2.37), pp. 105–106.
-/

namespace LatticeSystem.Quantum

open Matrix

/-- **U(1) planar base entry** `2 q₀ m₀ ≤ m₁` for the BEC tower moment recursion (Tasaki §5.3,
eq. (5.2.5) → eq. (4.2.37) base).  From the two XY-plane ODLRO hypotheses (`α = 1, 2`,
`q₀ ≤ ⟨(Ô^{(α)})²⟩ / (‖Φ‖² (L^d)²)`) alone, the first `p̂`-moment obeys
`2 q₀ ‖Φ‖² ≤ ⟨Φ, p̂ Φ⟩`.  Since `p̂ = V⁻² ((Ô^{(1)})² + (Ô^{(2)})²)`
(`staggeredPhatS_eq_cartesian_sq`, `V = L^d`), summing the two planar bounds gives
`⟨p̂⟩ = V⁻² (⟨(Ô^{(1)})²⟩ + ⟨(Ô^{(2)})²⟩) ≥ 2 q₀ ‖Φ‖²`.
Unlike the `SU(2)` version `phatMoment_one_ge_of_lro` this uses **no** singlet/isotropy relation —
both planar axes are supplied by the hypotheses — so it applies to the chemical-potential XY ground
state, which is not a `Ŝ¹`-singlet.  Combined with the singlet-free processed recursion
`phatMoment_succ_ratio` it yields the full geometric moment lower bound of the BEC tower. -/
theorem phatMoment_one_ge_of_planar_lro (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (q₀ : ℝ) (hm0 : 0 < (star Φ ⬝ᵥ Φ).re) (hL : (0 : ℝ) < (L : ℝ) ^ d)
    (hlro : ∀ α : Fin 3, α ≠ 2 →
      q₀ ≤ expectationRatioRe
        ((staggeredOrderOpAxisS α (torusParitySublattice d L) N) ^ 2) Φ / ((L : ℝ) ^ d) ^ 2) :
    2 * q₀ * (star Φ ⬝ᵥ Φ).re ≤ phatMoment d L N Φ 1 := by
  set V2 : ℝ := ((L : ℝ) ^ d) ^ 2 with hV2def
  have hV2 : 0 < V2 := pow_pos hL 2
  have hcast : (((L : ℂ) ^ d) ^ 2)⁻¹ = ((V2⁻¹ : ℝ) : ℂ) := by
    rw [hV2def]; push_cast; ring
  -- m₁ = V⁻² (⟨(Ô^{(1)})²⟩.re + ⟨(Ô^{(2)})²⟩.re)
  have hm1 : phatMoment d L N Φ 1
      = V2⁻¹ * ((star Φ ⬝ᵥ (staggeredOrderOp1S (torusParitySublattice d L) N
            * staggeredOrderOp1S (torusParitySublattice d L) N).mulVec Φ).re
          + (star Φ ⬝ᵥ (staggeredOrderOp2S (torusParitySublattice d L) N
            * staggeredOrderOp2S (torusParitySublattice d L) N).mulVec Φ).re) := by
    rw [phatMoment, pow_one, staggeredPhatS_dotProduct_cartesian, hcast, Complex.re_ofReal_mul,
      Complex.add_re]
  -- The two planar ODLRO hypotheses reduce to `q₀ (m₀ V²) ≤ ⟨(Ô^{(α)})²⟩.re` for `α = 1, 2`.
  have e0 : staggeredOrderOpAxisS (0 : Fin 3) (torusParitySublattice d L) N
      = staggeredOrderOp1S (torusParitySublattice d L) N := rfl
  have e1 : staggeredOrderOpAxisS (1 : Fin 3) (torusParitySublattice d L) N
      = staggeredOrderOp2S (torusParitySublattice d L) N := rfl
  have h0 := hlro 0 (by decide)
  have h1 := hlro 1 (by decide)
  rw [e0] at h0
  rw [e1] at h1
  simp only [expectationRatioRe, pow_two] at h0 h1
  rw [div_div, le_div_iff₀ (mul_pos hm0 hV2)] at h0 h1
  -- Sum the two planar bounds and rescale by `V⁻² > 0`.
  rw [hm1]
  have hsum : 2 * (q₀ * ((star Φ ⬝ᵥ Φ).re * V2))
      ≤ (star Φ ⬝ᵥ (staggeredOrderOp1S (torusParitySublattice d L) N
            * staggeredOrderOp1S (torusParitySublattice d L) N).mulVec Φ).re
          + (star Φ ⬝ᵥ (staggeredOrderOp2S (torusParitySublattice d L) N
            * staggeredOrderOp2S (torusParitySublattice d L) N).mulVec Φ).re := by
    linarith
  have key : 2 * q₀ * (star Φ ⬝ᵥ Φ).re
      = V2⁻¹ * (2 * (q₀ * ((star Φ ⬝ᵥ Φ).re * V2))) := by
    field_simp
  rw [key]
  exact mul_le_mul_of_nonneg_left hsum (le_of_lt (inv_pos.mpr hV2))

end LatticeSystem.Quantum
