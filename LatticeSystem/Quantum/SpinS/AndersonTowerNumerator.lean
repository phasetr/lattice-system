/-
Tasaki §4.2.2 Theorem 4.6 (Anderson tower), Tier 4 — the numerator estimate.

The ★ variational bound (`tower_numerator_double_commutator_le`) reduces the trial-state energy gap to
`⟨Φ, [(ô⁻)^M, [Ĥ, (ô⁺)^M]] Φ⟩`.  This file expands that double commutator via `commutator_pow_eq_sum`
and prepares to feed the pieces to Lemma R2: the `d̂ = [ô⁺, [Ĥ, ô⁻]]` terms (first sum, `O(M²/V)`) and
the `[ô⁺, ô⁻]` terms (second/third sums, `O(M⁴/V²)`).
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerLocalDecay
import LatticeSystem.Quantum.SpinS.AndersonTowerAssembly

namespace LatticeSystem.Quantum

open Matrix

variable {d L N : ℕ}

/-- **Commutator-power expansion of `[Ĥ, (ô⁺)^M]`.**  The inner commutator of the numerator splits
into a telescoping sum of single `[Ĥ, ô⁺]` insertions between powers of the order density. -/
theorem heisenberg_orderDensityPow_commutator_eq (d L N M : ℕ) [NeZero L] :
    heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true ^ M
        - staggeredOrderDensityOpS d L N true ^ M
          * heisenbergHamiltonianS (torusNNCoupling d L) N
      = ∑ j ∈ Finset.range M, staggeredOrderDensityOpS d L N true ^ j
          * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true * heisenbergHamiltonianS (torusNNCoupling d L) N)
          * staggeredOrderDensityOpS d L N true ^ (M - 1 - j) :=
  commutator_pow_eq_sum _ _ M

/-- **The numerator double commutator as a single sum over insertion positions.**  Substituting the
commutator-power expansion of `[Ĥ, (ô⁺)^M]` into the ★-variational numerator gives a sum over `j` of
the `(ô⁻)^M`-commutators of the position-`j` `[Ĥ, ô⁺]` insertions. -/
theorem numerator_eq_sum_j (d L N M : ℕ) [NeZero L] :
    staggeredOrderDensityOpS d L N false ^ M
        * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true ^ M
          - staggeredOrderDensityOpS d L N true ^ M
            * heisenbergHamiltonianS (torusNNCoupling d L) N)
      - (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true ^ M
          - staggeredOrderDensityOpS d L N true ^ M
            * heisenbergHamiltonianS (torusNNCoupling d L) N)
        * staggeredOrderDensityOpS d L N false ^ M
      = ∑ j ∈ Finset.range M,
          (staggeredOrderDensityOpS d L N false ^ M
              * (staggeredOrderDensityOpS d L N true ^ j
                * (heisenbergHamiltonianS (torusNNCoupling d L) N
                    * staggeredOrderDensityOpS d L N true
                  - staggeredOrderDensityOpS d L N true
                    * heisenbergHamiltonianS (torusNNCoupling d L) N)
                * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
            - (staggeredOrderDensityOpS d L N true ^ j
                * (heisenbergHamiltonianS (torusNNCoupling d L) N
                    * staggeredOrderDensityOpS d L N true
                  - staggeredOrderDensityOpS d L N true
                    * heisenbergHamiltonianS (torusNNCoupling d L) N)
                * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
              * staggeredOrderDensityOpS d L N false ^ M) := by
  rw [heisenberg_orderDensityPow_commutator_eq, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib]

end LatticeSystem.Quantum
