/-
The staggered order operator commutator distributes over sites
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

The commutator of the staggered order operator `Ô = Σ_x ε_x Ŝ_x^{(3)}` with any operator `C`
distributes over the sites: `[Ô, C] = Σ_x ε_x [Ŝ_x^{(3)}, C]`.  Applied twice (to `C = [Ĥ, Ô]`
and to `Ô` inside) this expands the double commutator `[Ô, [Ĥ, Ô]]` into a double site sum, whose
terms vanish unless the two sites are adjacent — reducing the naive `O(L²)` count to `O(L)`.
-/
import LatticeSystem.Quantum.SpinS.DysonLiebSimon

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **The staggered order operator commutator distributes over sites**:
`[Ô, C] = Σ_x ε_x [Ŝ_x^{(3)}, C]`. -/
theorem staggeredOrderOpS_commutator (A : Λ → Bool) (N : ℕ) (C : ManyBodyOpS Λ N) :
    staggeredOrderOpS A N * C - C * staggeredOrderOpS A N
      = ∑ x : Λ, (if A x then (1 : ℂ) else -1)
          • (spinSSiteOp3 x N * C - C * spinSSiteOp3 x N) := by
  rw [staggeredOrderOpS, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [smul_mul_assoc, mul_smul_comm, smul_sub]

end LatticeSystem.Quantum
