import LatticeSystem.Quantum.SpinS.AKLTStringOrderCovariance
import LatticeSystem.Quantum.SpinS.AKLT

/-!
# Tasaki §7.2.2: exponential decay of the AKLT two-point correlation

This module discharges the **correlation-function conjunct** of the AKLT main
theorem (Tasaki Theorem 7.1, eq. (7.1.2), the last of the theorem's four
assertions).  For the explicit valence-bond-solid state `Φ_VBS` on the spin-one
ring `Fin (n + 1)` and any two fixed sites `x, y` with `|x − y| ≥ 1`,

`⟨Φ_VBS, Ŝ_x · Ŝ_y Φ_VBS⟩ / ⟨Φ_VBS, Φ_VBS⟩ → 4 (−3)^{−|x − y|}` as `L = n + 1 ↑ ∞`,

stated in the sound eventual-`ε` form used in the `aklt_theorem_7_1` theorem
(`AKLTTheorem71.lean`).

The proof combines the plain (no interior string phase) axis-three transfer
computation (`AKLTStringOrderTransfer`, eqs. (7.2.31)–(7.2.33)) with the
single-site rotation covariance of the VBS state (`AKLTStringOrderCovariance`,
eq. (7.2.34)), which turns the full inner product `Ŝ_x · Ŝ_y` into three times
its axis-three component.

This discharges conjunct 6 as a standalone theorem; this result now forms part of the theorem
`aklt_theorem_7_1` (in `AKLTTheorem71.lean`), which bundles this correlation result together with
existence, gap, and uniqueness.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer, 2020, §7.2.2, eqs. (7.2.26)–(7.2.34), pp. 197–200.
-/

namespace LatticeSystem.Quantum

open Matrix LatticeSystem.Quantum.AKLTStringOrder

/-- The real Rayleigh expectation is additive over a finite sum of operators
(the numerator is additive and the denominator is shared). -/
theorem expectationRatioRe_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (O : κ → Matrix ι ι ℂ) (w : ι → ℂ) :
    expectationRatioRe (∑ k, O k) w = ∑ k, expectationRatioRe (O k) w := by
  unfold expectationRatioRe
  rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum, Finset.sum_div]

/-- The two-site dot product decomposes as the sum over the three axes of the
products of the corresponding site components. -/
theorem spinSDot_eq_sum_component {L : ℕ} (x y : Fin L) :
    spinSDot x y 2 =
      ∑ α : Fin 3, spinSSiteComponentS α x * spinSSiteComponentS α y := by
  rw [Fin.sum_univ_three, spinSDot_def]
  rfl

/-- **Tasaki Theorem 7.1, correlation conjunct (§7.2.2, eq. (7.1.2)), for `x < y`.**
The finite-volume VBS Rayleigh quotient of `Ŝ_x · Ŝ_y` converges to
`4 (−3)^{−(y − x)}` as the ring length `L = n + 1 ↑ ∞`. -/
private theorem aklt_correlation_decay_lt (x y : ℕ) (hxy : x < y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n →
      |expectationRatioRe (spinSDot (chainSite n x) (chainSite n y) 2)
          (akltVBSState (n + 1))
        - (4 : ℝ) * (-3 : ℝ) ^ (-(Nat.dist x y : ℤ))| < ε := by
  have hr : Nat.dist x y = y - x := Nat.dist_eq_sub_of_le (le_of_lt hxy)
  obtain ⟨L₀, _hL₀2, hLmain⟩ :=
    Internal.plainAxis3Epsilon x y hxy (ε / 3) (by positivity)
  -- The thermodynamic value `3 · (−(4/9)(−1/3)^{y-x-1}) = 4 (−3)^{−(y−x)}`.
  have hV : (3 : ℝ) * (-(4 / 9 : ℝ) * (-1 / 3 : ℝ) ^ (y - x - 1)) =
      4 * (-3 : ℝ) ^ (-(Nat.dist x y : ℤ)) := by
    have hbridge : (-3 : ℝ) ^ (-(Nat.dist x y : ℤ)) = (-1 / 3 : ℝ) ^ (Nat.dist x y) := by
      rw [zpow_neg, zpow_natCast, ← inv_pow]; norm_num
    have hpow : (-1 / 3 : ℝ) ^ (Nat.dist x y) =
        (-1 / 3 : ℝ) ^ (y - x - 1) * (-1 / 3) := by
      rw [hr]
      conv_lhs => rw [show y - x = (y - x - 1) + 1 by omega]
      rw [pow_succ]
    rw [hbridge, hpow]; ring
  refine ⟨max L₀ y, fun n hn => ?_⟩
  have hnL0 : L₀ ≤ n := le_trans (le_max_left L₀ y) hn
  have hny : y ≤ n := le_trans (le_max_right L₀ y) hn
  have hxn : x < n + 1 := by omega
  have hyn : y < n + 1 := by omega
  have hxfval : (chainSite n x).val = x := by
    unfold chainSite; simp [Nat.mod_eq_of_lt hxn]
  have hyfval : (chainSite n y).val = y := by
    unfold chainSite; simp [Nat.mod_eq_of_lt hyn]
  -- Split the dot product into three axis components and reduce each to axis three.
  rw [spinSDot_eq_sum_component, expectationRatioRe_sum, Fin.sum_univ_three]
  rw [Internal.spinComponentCorrelation_akltVBSState_eq_three
        (0 : Fin 3) (n + 1) (chainSite n x) (chainSite n y),
    Internal.spinComponentCorrelation_akltVBSState_eq_three
        (1 : Fin 3) (n + 1) (chainSite n x) (chainSite n y),
    Internal.spinComponentCorrelation_akltVBSState_eq_three
        (2 : Fin 3) (n + 1) (chainSite n x) (chainSite n y)]
  rw [show spinSSiteComponentS (2 : Fin 3) (chainSite n x) =
        spinSSiteOp3 (chainSite n x) 2 from rfl,
    show spinSSiteComponentS (2 : Fin 3) (chainSite n y) =
        spinSSiteOp3 (chainSite n y) 2 from rfl]
  -- Now the sum is `3 ·` the axis-three correlation.
  have hclose := hLmain (n + 1) (by omega) (chainSite n x) (chainSite n y) hxfval hyfval
  set c := expectationRatioRe
    (spinSSiteOp3 (chainSite n x) 2 * spinSSiteOp3 (chainSite n y) 2)
    (akltVBSState (n + 1)) with hc
  have hsum3 : c + c + c = 3 * c := by ring
  rw [hsum3, ← hV, ← mul_sub, abs_mul, show |(3 : ℝ)| = 3 by norm_num]
  linarith [hclose]

/-- **Tasaki Theorem 7.1, correlation-function conjunct (§7.2.2, eq. (7.1.2)).**
For the explicit spin-one AKLT valence-bond-solid state on the ring `Fin (n + 1)`
and any two fixed sites `x, y` with `|x − y| ≥ 1`, the ground-state Rayleigh
quotient of `Ŝ_x · Ŝ_y` decays with alternating sign to `4 (−3)^{−|x − y|}` as
the ring length `L = n + 1 ↑ ∞` (sound eventual-`ε` form).  This is the sixth and
last assertion of the AKLT main theorem, discharged here as a standalone theorem
that is now composed together with the other conjuncts in the `aklt_theorem_7_1`
theorem in `AKLTTheorem71.lean`. -/
theorem aklt_correlation_decay :
    ∀ (x y : ℕ), 1 ≤ Nat.dist x y → ∀ ε : ℝ, 0 < ε → ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n →
      |expectationRatioRe (spinSDot (chainSite n x) (chainSite n y) 2)
          (akltVBSState (n + 1))
        - (4 : ℝ) * (-3 : ℝ) ^ (-(Nat.dist x y : ℤ))| < ε := by
  intro x y hdist ε hε
  have hne : x ≠ y := by rintro rfl; simp [Nat.dist_self] at hdist
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · exact aklt_correlation_decay_lt x y hxy ε hε
  · obtain ⟨n₁, hn₁⟩ := aklt_correlation_decay_lt y x hyx ε hε
    refine ⟨n₁, fun n hn => ?_⟩
    have h := hn₁ n hn
    rwa [spinSDot_comm (chainSite n y) (chainSite n x), Nat.dist_comm y x] at h

end LatticeSystem.Quantum
