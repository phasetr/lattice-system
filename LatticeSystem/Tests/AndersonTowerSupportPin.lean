import LatticeSystem.Quantum.SpinS.AndersonTowerSameSignDecay
import LatticeSystem.Quantum.SpinS.OperatorSupport

/-!
# Signature pin: the §4.2.2 local-decay stack's `SupportedOnS` support contract

Repository-internal regression guard, **not** a Tasaki result and carrying no book citation. The
§4.2.2 local-decay stack (`Quantum/SpinS/AndersonTowerLocalDecay.lean`,
`Quantum/SpinS/AndersonTowerSameSignDecay.lean`) states its per-operator support hypotheses and
conclusions against the operator-support predicate of `Quantum/SpinS/OperatorSupport.lean`
(`SupportedOnS`). This file pins four of those statements verbatim: the definition-file conclusion
side (`bondDoubleComm_supportedOnS`), the hypothesis-and-conclusion side
(`orderComm_supportedOnS`), the cross-module interface consumed by the Bose–Einstein-condensate
numerator and the ring-ball locality bridge (`iterOrderComm_norm_le_of_localSum`), and the
same-sign-decay boundary (`spinSDot_staggeredLowering_commutator_supportedOnS`).

Reference: no textbook citation (repository-internal regression guard; see
`Quantum/SpinS/OperatorSupport.lean` and `Quantum/SpinS/AndersonTowerLocalDecay.lean`).
-/

namespace LatticeSystem.Tests.AndersonTowerSupportPin

open Matrix LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {d L N : ℕ}

/-- **Signature pin (P1).** The bond–order double commutator `[Ŝ_x·Ŝ_y, d̂]` is supported on the
bond `{x, y}`, stated against `SupportedOnS`. -/
example [NeZero L] (x y : HypercubicTorus d L) (hxy : x ≠ y) :
    SupportedOnS ({x, y} : Finset (HypercubicTorus d L)) (bondDoubleComm d L N x y) :=
  bondDoubleComm_supportedOnS x y hxy

/-- **Signature pin (P2).** The order-density commutator preserves support, both the hypothesis
and the conclusion stated against `SupportedOnS`. -/
example [NeZero L] {S : Finset (HypercubicTorus d L)} {G : ManyBodyOpS (HypercubicTorus d L) N}
    (hG : SupportedOnS S G) (b : Bool) :
    SupportedOnS S (orderComm b G) :=
  orderComm_supportedOnS hG b

/-- **Signature pin (P3, cross-module interface).** The quasi-local-sum norm bound for iterated
order-density commutators, with its per-term support hypothesis stated against `SupportedOnS`.
This is the contract the Bose–Einstein-condensate numerator and the ring-ball locality bridge
consume. -/
example [NeZero L] {ι : Type*} (hN : 1 ≤ N) (u : List Bool) (s : Finset ι) (c : ι → ℂ)
    (G : ι → ManyBodyOpS (HypercubicTorus d L) N) (S : ι → Finset (HypercubicTorus d L))
    (smax : ℕ) (hsup : ∀ i ∈ s, SupportedOnS (S i) (G i))
    (hcard : ∀ i ∈ s, (S i).card ≤ smax) :
    manyBodyOperatorNormS (iterOrderComm u (∑ i ∈ s, c i • G i))
      ≤ (2 * (smax : ℝ) * (N : ℝ) / (L : ℝ) ^ d) ^ u.length
        * ∑ i ∈ s, ‖c i‖ * manyBodyOperatorNormS (G i) :=
  iterOrderComm_norm_le_of_localSum hN u s c G S smax hsup hcard

/-- **Signature pin (P4, same-sign-decay boundary).** The bond–order lowering commutator
`[Ŝ_x·Ŝ_y, Ô⁻]` is supported on the bond `{x, y}`, stated against `SupportedOnS`. -/
example (A : Λ → Bool) (x y : Λ) (hxy : x ≠ y) :
    SupportedOnS ({x, y} : Finset Λ)
      (spinSDot x y N * staggeredLoweringOpS A N - staggeredLoweringOpS A N * spinSDot x y N) :=
  spinSDot_staggeredLowering_commutator_supportedOnS A x y hxy

end LatticeSystem.Tests.AndersonTowerSupportPin
