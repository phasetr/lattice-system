import LatticeSystem.Quantum.SpinS.MultiSite
import LatticeSystem.Quantum.SpinS.CyclicCommutator
import LatticeSystem.Quantum.SpinS.CyclicCommutator23
import LatticeSystem.Quantum.SpinS.CyclicCommutator31

/-!
# Multi-site spin-`S` same-site commutators
(Tasaki §2.5 Phase B-β β-3k)

Lifts the single-site SU(2) cyclic commutators (Issue #458 β-20/21/22)

  `[Ŝ^{(1)}, Ŝ^{(2)}] = i Ŝ^{(3)}`,
  `[Ŝ^{(2)}, Ŝ^{(3)}] = i Ŝ^{(1)}`,
  `[Ŝ^{(3)}, Ŝ^{(1)}] = i Ŝ^{(2)}`,

to the multi-site Hilbert space at a single site `x : Λ`:

  `[Ŝ_x^{(1)}, Ŝ_x^{(2)}] = i Ŝ_x^{(3)}`, etc.

Also exposes the general "same-site lifting" identity

  `[onSiteS i A, onSiteS i B] = onSiteS i [A, B]`,

which is an immediate corollary of `onSiteS_mul_onSiteS_same` (β-3d).
This is the diagonal (`x = y`) case of Tasaki eq. (2.2.6) for general spin.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- Same-site commutator: `[onSiteS i A, onSiteS i B] = onSiteS i [A, B]`. -/
theorem onSiteS_commutator_same (i : Λ)
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A * onSiteS i B - onSiteS i B * onSiteS i A : ManyBodyOpS Λ N) =
      onSiteS i (A * B - B * A) := by
  rw [onSiteS_mul_onSiteS_same, onSiteS_mul_onSiteS_same, ← onSiteS_sub]

/-- Same-site SU(2) cyclic commutator at axis `(1, 2) → 3`. -/
theorem spinSOp1_onSiteS_commutator_spinSOp2_onSiteS (x : Λ) :
    (onSiteS x (spinSOp1 N) * onSiteS x (spinSOp2 N)
        - onSiteS x (spinSOp2 N) * onSiteS x (spinSOp1 N) :
        ManyBodyOpS Λ N) =
      Complex.I • onSiteS x (spinSOp3 N) := by
  rw [onSiteS_commutator_same, spinSOp1_commutator_spinSOp2, onSiteS_smul]

/-- Same-site SU(2) cyclic commutator at axis `(2, 3) → 1`. -/
theorem spinSOp2_onSiteS_commutator_spinSOp3_onSiteS (x : Λ) :
    (onSiteS x (spinSOp2 N) * onSiteS x (spinSOp3 N)
        - onSiteS x (spinSOp3 N) * onSiteS x (spinSOp2 N) :
        ManyBodyOpS Λ N) =
      Complex.I • onSiteS x (spinSOp1 N) := by
  rw [onSiteS_commutator_same, spinSOp2_commutator_spinSOp3, onSiteS_smul]

/-- Same-site SU(2) cyclic commutator at axis `(3, 1) → 2`. -/
theorem spinSOp3_onSiteS_commutator_spinSOp1_onSiteS (x : Λ) :
    (onSiteS x (spinSOp3 N) * onSiteS x (spinSOp1 N)
        - onSiteS x (spinSOp1 N) * onSiteS x (spinSOp3 N) :
        ManyBodyOpS Λ N) =
      Complex.I • onSiteS x (spinSOp2 N) := by
  rw [onSiteS_commutator_same, spinSOp3_commutator_spinSOp1, onSiteS_smul]

end LatticeSystem.Quantum
