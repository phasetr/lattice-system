import LatticeSystem.Quantum.SpinS.MultiSiteCommutator
import LatticeSystem.Quantum.SpinS.TotalSpin
import LatticeSystem.Quantum.SpinS.Cartan3

/-!
# Multi-site Cartan ⁺⁻ relation: `[Ŝ^+_{tot}, Ŝ^-_{tot}] = 2 · Ŝ^z_{tot}`

The third multi-site Cartan relation, completing the SU(2) algebra
of total operators
`{Ŝ^z_{tot}, Ŝ^+_{tot}, Ŝ^-_{tot}}`. The other two
(`[Ŝ^z_{tot}, Ŝ^∓_{tot}] = ∓Ŝ^∓_{tot}`) are in `AllAlignedState.lean`
(PR #883).

Proof template (mirroring PR #883's `totalSpinSOp3_commutator_totalSpinSOpMinus`):

1. Distribute outer sums:
   `(Σ_x Ŝ^+_x)(Σ_y Ŝ^-_y) − (Σ_y Ŝ^-_y)(Σ_x Ŝ^+_x)
     = Σ_x [Ŝ^+_x, Σ_y Ŝ^-_y]`.
2. Apply `onSiteS_commutator_totalOnSiteS`: cross-site terms vanish
   (off-site operators commute), on-site reduces to `onSiteS x [Ŝ^+, Ŝ^-]`.
3. Single-site Cartan ⁺⁻ (`spinSOpPlus_commutator_spinSOpMinus`):
   `[Ŝ^+, Ŝ^-] = 2 · Ŝ^z`.
4. Linearity of `onSiteS` in the matrix argument:
   `Σ_x onSiteS x (2 • Ŝ^z) = 2 • Σ_x onSiteS x Ŝ^z = 2 • Ŝ^z_{tot}`.

This is the operator-algebraic input for the standard SU(2)
Casimir-rearrangement
`Ŝ^+_{tot} Ŝ^-_{tot} = (Ŝ_{tot})^2 − (Ŝ^z_{tot})^2 + Ŝ^z_{tot}`,
deferred to a future textbook unit.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Multi-site Cartan ⁺⁻ relation**:
`[Ŝ^+_{tot}, Ŝ^-_{tot}] = 2 · Ŝ^z_{tot}`.

Lifts the single-site Cartan
`spinSOpPlus_commutator_spinSOpMinus : [Ŝ^+, Ŝ^-] = 2 · Ŝ^z` to
multi-site via `onSiteS_commutator_totalOnSiteS` summed over `x : V`. -/
theorem totalSpinSOpPlus_commutator_totalSpinSOpMinus :
    (totalSpinSOpPlus V N : ManyBodyOpS V N) * totalSpinSOpMinus V N -
      totalSpinSOpMinus V N * totalSpinSOpPlus V N =
      (2 : ℂ) • totalSpinSOp3 V N := by
  unfold totalSpinSOpPlus totalSpinSOpMinus totalSpinSOp3
  rw [Finset.sum_mul]
  rw [show ((∑ x : V, onSiteS x (spinSOpPlus N) *
            (∑ y : V, onSiteS y (spinSOpMinus N)) :
            ManyBodyOpS V N) -
          (∑ y : V, onSiteS y (spinSOpMinus N)) *
            (∑ x : V, onSiteS x (spinSOpPlus N))) =
        ∑ x : V, ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N) *
            (∑ y : V, onSiteS y (spinSOpMinus N)) -
          (∑ y : V, onSiteS y (spinSOpMinus N)) *
            onSiteS x (spinSOpPlus N)) from by
    rw [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]]
  rw [show (∑ x : V, ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N) *
            (∑ y : V, onSiteS y (spinSOpMinus N)) -
          (∑ y : V, onSiteS y (spinSOpMinus N)) *
            onSiteS x (spinSOpPlus N))) =
        ∑ x : V, (onSiteS x ((2 : ℂ) • spinSOp3 N) : ManyBodyOpS V N) from by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [onSiteS_commutator_totalOnSiteS x (spinSOpPlus N) (spinSOpMinus N),
      spinSOpPlus_commutator_spinSOpMinus]]
  rw [show (∑ x : V, (onSiteS x ((2 : ℂ) • spinSOp3 N) : ManyBodyOpS V N)) =
        (2 : ℂ) • ∑ x : V, (onSiteS x (spinSOp3 N) : ManyBodyOpS V N) from by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [onSiteS_smul]]

/-- The reverse Cartan ⁻⁺ relation (corollary):
`[Ŝ^-_{tot}, Ŝ^+_{tot}] = −2 · Ŝ^z_{tot}`. -/
theorem totalSpinSOpMinus_commutator_totalSpinSOpPlus :
    (totalSpinSOpMinus V N : ManyBodyOpS V N) * totalSpinSOpPlus V N -
      totalSpinSOpPlus V N * totalSpinSOpMinus V N =
      -((2 : ℂ) • totalSpinSOp3 V N) := by
  have h := totalSpinSOpPlus_commutator_totalSpinSOpMinus (V := V) (N := N)
  rw [show (totalSpinSOpMinus V N : ManyBodyOpS V N) * totalSpinSOpPlus V N -
      totalSpinSOpPlus V N * totalSpinSOpMinus V N =
    -(totalSpinSOpPlus V N * totalSpinSOpMinus V N -
      totalSpinSOpMinus V N * totalSpinSOpPlus V N) from by abel]
  rw [h]

end LatticeSystem.Quantum
