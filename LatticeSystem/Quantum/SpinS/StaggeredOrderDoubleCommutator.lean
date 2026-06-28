/-
The staggered order double commutator as a double site sum
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

Applying the order-operator commutator distribution twice expands the f-sum-rule double commutator
`[Ô, [Ĥ, Ô]]` into a double sum over site pairs:
`[Ô, [Ĥ, Ô]] = Σ_x Σ_z ε_x ε_z [Ŝ_x^{(3)}, [Ĥ, Ŝ_z^{(3)}]]`.  Each summand is the single-site double
commutator, which vanishes unless `x` and `z` are adjacent, so the apparent `O(L²)` sum collapses to
`O(L)` — the bounded oscillator strength of the Falk–Bruch bound.
-/
import LatticeSystem.Quantum.SpinS.StaggeredOrderCommutator

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The reversed order-operator commutator distribution: `[C, Ô] = Σ_x ε_x [C, Ŝ_x^{(3)}]`. -/
theorem staggeredOrderOpS_commutator' (A : Λ → Bool) (N : ℕ) (C : ManyBodyOpS Λ N) :
    C * staggeredOrderOpS A N - staggeredOrderOpS A N * C
      = ∑ x : Λ, (if A x then (1 : ℂ) else -1)
          • (C * spinSSiteOp3 x N - spinSSiteOp3 x N * C) := by
  rw [staggeredOrderOpS, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [mul_smul_comm, smul_mul_assoc, smul_sub]

/-- **The staggered order double commutator as a double site sum**:
`[Ô, [Ĥ, Ô]] = Σ_x Σ_z ε_x ε_z [Ŝ_x^{(3)}, [Ĥ, Ŝ_z^{(3)}]]`. -/
theorem staggeredOrderOpS_double_commutator (A : Λ → Bool) (N : ℕ) (H : ManyBodyOpS Λ N) :
    staggeredOrderOpS A N * (H * staggeredOrderOpS A N - staggeredOrderOpS A N * H)
        - (H * staggeredOrderOpS A N - staggeredOrderOpS A N * H) * staggeredOrderOpS A N
      = ∑ x : Λ, ∑ z : Λ,
          ((if A x then (1 : ℂ) else -1) * (if A z then (1 : ℂ) else -1))
            • (spinSSiteOp3 x N * (H * spinSSiteOp3 z N - spinSSiteOp3 z N * H)
                - (H * spinSSiteOp3 z N - spinSSiteOp3 z N * H) * spinSSiteOp3 x N) := by
  -- inner commutator `[H, Ô]` as a single sum over `z`
  rw [staggeredOrderOpS_commutator' A N H]
  -- outer distribution over `x`
  rw [staggeredOrderOpS_commutator A N
    (∑ z : Λ, (if A z then (1 : ℂ) else -1) • (H * spinSSiteOp3 z N - spinSSiteOp3 z N * H))]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  -- distribute `[Ŝ_x^{(3)}, ·]` over the inner sum
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, smul_smul]

end LatticeSystem.Quantum
