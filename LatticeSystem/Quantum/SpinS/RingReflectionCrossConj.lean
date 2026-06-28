/-
The right-half gauge turns a crossing bond into the gauged crossing interaction
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 27).

A crossing bond joins a left site `x < n` to its reflection `r x ≥ n`.  Conjugating it by the
right-half gauge leaves the left endpoint untouched and gauges the right endpoint, flipping signs
of the `Ŝ^1` and `Ŝ^3` contributions: `rightGauge · (Ŝ_x · Ŝ_{r x}) · rightGaugeInv =
−crossBondInteractionS x`.  Both crossing bonds of the ring (`(n−1, n)` and `(2n−1, 0)`) are of this
form, so this single lemma covers both.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionBondConj
import LatticeSystem.Quantum.SpinS.RingReflectionRPDecomposition

namespace LatticeSystem.Quantum

open Matrix

namespace AxisTwoPiRotS

variable (G : AxisTwoPiRotS N) (n : ℕ)

/-- **The gauge image of a crossing bond is the negated gauged crossing interaction.**  For a left
site `x < n` (whose reflection `r x` is a right site), conjugating the crossing bond `Ŝ_x · Ŝ_{r x}`
by the right-half gauge gives `−crossBondInteractionS x`. -/
theorem rightGauge_conj_crossBond {x : Fin (2 * n)} (hx : (x : ℕ) < n) :
    G.rightGauge n * spinSDot x (ringReflect n x) N * G.rightGaugeInv n
      = -crossBondInteractionS x N := by
  have hrx : n ≤ (ringReflect n x : ℕ) := by rw [ringReflect_val]; omega
  rw [spinSDot_def]
  simp only [rightGauge_conj_add, rightGauge_conj_mul, G.rightGauge_conj_onSiteS_left n hx,
    G.rightGauge_conj_onSiteS_right n hrx, G.conj_spinSOp1, G.conj_spinSOp2, G.conj_spinSOp3,
    onSiteS_neg, mul_neg]
  rw [crossBondInteractionS_eq]
  abel

end AxisTwoPiRotS

end LatticeSystem.Quantum
