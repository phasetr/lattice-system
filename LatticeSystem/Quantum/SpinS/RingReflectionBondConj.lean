/-
The right-half gauge fixes the non-crossing bonds
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 26).

The right-half DLS/Marshall gauge leaves every non-crossing bond invariant: a left bond (both sites
in the left half) is untouched, and a right bond (both sites gauged) is fixed because the
`Ŝ^1`/`Ŝ^3` sign flips cancel in the product while `Ŝ^2` is unchanged.  Only the two crossing bonds
(one endpoint on each side) acquire the DLS sign flip.  This file proves the two invariance lemmas
`rightGauge_conj_spinSDot_left` and `rightGauge_conj_spinSDot_right`.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionGaugeConj
import LatticeSystem.Quantum.SpinS.MultiSiteDot

namespace LatticeSystem.Quantum

open Matrix

namespace AxisTwoPiRotS

variable (G : AxisTwoPiRotS N) (n : ℕ)

/-- Conjugating a single-site operator at a **left** site (`z < n`) by the right-half gauge is the
identity. -/
theorem rightGauge_conj_onSiteS_left {z : Fin (2 * n)} (hz : (z : ℕ) < n)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    G.rightGauge n * onSiteS z A * G.rightGaugeInv n = onSiteS z A := by
  rw [rightGauge_conj_onSiteS, if_neg (by omega)]

/-- Conjugating a single-site operator at a **right** site (`n ≤ z`) by the right-half gauge applies
`U · A · U⁻¹`. -/
theorem rightGauge_conj_onSiteS_right {z : Fin (2 * n)} (hz : n ≤ (z : ℕ))
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    G.rightGauge n * onSiteS z A * G.rightGaugeInv n = onSiteS z (G.U * A * G.Uinv) := by
  rw [rightGauge_conj_onSiteS, if_pos hz]

/-- The gauge fixes a **left bond** (both sites in the left half). -/
theorem rightGauge_conj_spinSDot_left {x y : Fin (2 * n)} (hx : (x : ℕ) < n) (hy : (y : ℕ) < n) :
    G.rightGauge n * spinSDot x y N * G.rightGaugeInv n = spinSDot x y N := by
  rw [spinSDot_def]
  simp only [rightGauge_conj_add, rightGauge_conj_mul, G.rightGauge_conj_onSiteS_left n hx,
    G.rightGauge_conj_onSiteS_left n hy]

/-- The gauge fixes a **right bond** (both sites gauged: the `Ŝ^1`/`Ŝ^3` sign flips cancel). -/
theorem rightGauge_conj_spinSDot_right {x y : Fin (2 * n)} (hx : n ≤ (x : ℕ)) (hy : n ≤ (y : ℕ)) :
    G.rightGauge n * spinSDot x y N * G.rightGaugeInv n = spinSDot x y N := by
  rw [spinSDot_def]
  simp only [rightGauge_conj_add, rightGauge_conj_mul, G.rightGauge_conj_onSiteS_right n hx,
    G.rightGauge_conj_onSiteS_right n hy, G.conj_spinSOp1, G.conj_spinSOp2, G.conj_spinSOp3,
    onSiteS_neg, neg_mul_neg]

end AxisTwoPiRotS

end LatticeSystem.Quantum
