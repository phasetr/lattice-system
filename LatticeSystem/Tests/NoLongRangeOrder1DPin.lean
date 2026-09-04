import LatticeSystem.Quantum.SpinS.CartesianAxis
import LatticeSystem.Quantum.SpinS.NoLongRangeOrder1D

/-!
# Signature pin: `no_long_range_order_1d` and its all-axes su(2) bridge (Corollary 4.3)

`no_long_range_order_1d` is written out here in full, independently of the conditional route
`no_long_range_order_1d_of_theorem_4_2` it is derived from.  The theorem's own `ε`–`δ` statement is
what consumers see, so it is fixed on its own: an added hypothesis, an altered quantifier order or
`Even L` drift breaks this file even when the unproved input its proof consumes is exchanged for
another one — as it was when the susceptibility route was replaced by Tasaki's own contraposition
from Theorem 4.2.  It also pins the two su(2) bridge lemmas (L2, L3) that Tasaki's own fourth
sentence ("the same bound holds for α = 1 or 2 because the unique ground state is SU(2) invariant")
supplies: without them the capstone only carries Tasaki's α = 3 instance.
-/

namespace LatticeSystem.Tests.NoLongRangeOrder1DPin

open Matrix LatticeSystem.Quantum

/-- **Signature pin: `no_long_range_order_1d`, strengthened to all three Cartesian axes.** Written
out independently of the conditional reduction it is derived from, so the theorem's own public
statement — carrying Tasaki's fourth sentence closing (4.1.11) over `α = 1, 2, 3` via SU(2)
invariance, not just his third sentence's `α = 3` instance — is pinned regardless of how its proof
(or the axiom it rests on) changes. -/
example (N : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → Even L →
      ∀ Φ : (Fin L → Fin (N + 1)) → ℂ,
        star Φ ⬝ᵥ Φ = 1 →
        (∃ E₀ : ℂ, (staggeredFieldChainHamiltonianS L 0 N).mulVec Φ = E₀ • Φ ∧
          (∀ E : ℂ, ∀ Ψ : (Fin L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
            (staggeredFieldChainHamiltonianS L 0 N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) ∧
          Φ ≠ 0) →
        ∀ α : Fin 3,
          |(star Φ ⬝ᵥ ((stagOpVec (ringStaggeredSublattice L) N α *
              stagOpVec (ringStaggeredSublattice L) N α).mulVec Φ)).re / ((L : ℝ) ^ 2)| < ε :=
  no_long_range_order_1d N

/-- **Signature pin: `totalSpinSOpVec_mulVec_eq_zero_of_unique_ground` (L2, the su(2) bridge).**
On a `finrank ≤ 1` eigenspace of `H`, if all three total-spin generators commute with `H`, then all
three annihilate the unit ground state `Φ` — the operator form of "the unique ground state is SU(2)
invariant". -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ} (H : ManyBodyOpS Λ N) (μ : ℂ)
    (huniq : Module.finrank ℂ ↥(Module.End.eigenspace (Matrix.toLin' H) μ) ≤ 1)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (hΦne : Φ ≠ 0) (hΦ : H.mulVec Φ = μ • Φ)
    (hc1 : H * totalSpinSOp1 Λ N = totalSpinSOp1 Λ N * H)
    (hc2 : H * totalSpinSOp2 Λ N = totalSpinSOp2 Λ N * H)
    (hc3 : H * totalSpinSOp3 Λ N = totalSpinSOp3 Λ N * H) (α : Fin 3) :
    (totalSpinSOpVec Λ N α).mulVec Φ = 0 :=
  totalSpinSOpVec_mulVec_eq_zero_of_unique_ground H μ huniq hΦne hΦ hc1 hc2 hc3 α

/-- **Signature pin: `afmRing_groundState_totalSpin_annihilate` (L3, the ring specialisation).**
Every unit ground state `Φ` of the zero-field antiferromagnetic-ring Hamiltonian at an even length
`L ≥ 2` is annihilated by all three total-spin generators, i.e. is SU(2) invariant. -/
example (L N : ℕ) (hLeven : Even L) (hL2 : 2 ≤ L) (hN : 1 ≤ N)
    {Φ : (Fin L → Fin (N + 1)) → ℂ} (hΦnorm : star Φ ⬝ᵥ Φ = 1)
    (hΦgs : ∃ E₀ : ℂ, (staggeredFieldChainHamiltonianS L 0 N).mulVec Φ = E₀ • Φ ∧
      (∀ E : ℂ, ∀ Ψ : (Fin L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
        (staggeredFieldChainHamiltonianS L 0 N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) ∧ Φ ≠ 0)
    (α : Fin 3) : (totalSpinSOpVec (Fin L) N α).mulVec Φ = 0 :=
  afmRing_groundState_totalSpin_annihilate L N hLeven hL2 hN hΦnorm hΦgs α

end LatticeSystem.Tests.NoLongRangeOrder1DPin
