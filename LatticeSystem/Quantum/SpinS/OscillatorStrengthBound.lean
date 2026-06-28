/-
The f-sum-rule oscillator strength is `O(L)`
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

The f-sum-rule oscillator strength of the staggered order parameter grows only linearly in the ring
length: `|⟨Φ, [Ô, [Ĥ, Ô]] Φ⟩.re| ≤ 12 N³ · L` in any normalized state.  Its double site sum has at
most three nonzero summands per `x` (the off-pair vanishing), each bounded by `4 N³` (the uniform
two-site double-commutator norm).  This is the `O(L)` numerator of the Falk–Bruch bound.
-/
import LatticeSystem.Quantum.SpinS.OscillatorStrengthForm
import LatticeSystem.Quantum.SpinS.PairCommutatorNorm
import LatticeSystem.Quantum.SpinS.PairCommutatorVanish
import LatticeSystem.Quantum.SpinS.ExpectationNormBound

namespace LatticeSystem.Quantum

open Matrix

/-- **The oscillator strength is `O(L)`**: in a normalized state `Φ`,
`|⟨Φ, [Ô, [Ĥ, Ô]] Φ⟩.re| ≤ 12 N³ · L`. -/
theorem oscillatorStrength_abs_le (L N : ℕ) (hL : 2 ≤ L) (hN : 1 ≤ N)
    {Φ : (Fin L → Fin (N + 1)) → ℂ} (hΦ : star Φ ⬝ᵥ Φ = 1) :
    haveI : NeZero L := ⟨by omega⟩
    |(star Φ ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N
          * (heisenbergHamiltonianS (ringCoupling L) N
              * staggeredOrderOpS (ringStaggeredSublattice L) N
            - staggeredOrderOpS (ringStaggeredSublattice L) N
              * heisenbergHamiltonianS (ringCoupling L) N)
        - (heisenbergHamiltonianS (ringCoupling L) N
              * staggeredOrderOpS (ringStaggeredSublattice L) N
            - staggeredOrderOpS (ringStaggeredSublattice L) N
              * heisenbergHamiltonianS (ringCoupling L) N)
          * staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ).re|
      ≤ 12 * (N : ℝ) ^ 3 * (L : ℝ) := by
  haveI : NeZero L := ⟨by omega⟩
  classical
  rw [staggeredOrderOpS_double_commutator_dotProduct (ringStaggeredSublattice L) N
    (heisenbergHamiltonianS (ringCoupling L) N) Φ]
  simp only [spinSSiteOp3_def, Complex.re_sum]
  rw [show 12 * (N : ℝ) ^ 3 * (L : ℝ) = ∑ _x : Fin L, 12 * (N : ℝ) ^ 3 by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun x _ => ?_))
  -- per-`x` inner bound: at most three nonzero `z`, each `≤ 4 N³`
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  set S : Finset (Fin L) := {x, finRotate L x, (finRotate L).symm x} with hS
  have hterm : ∀ z : Fin L,
      |(((if ringStaggeredSublattice L x then (1 : ℂ) else -1)
          * (if ringStaggeredSublattice L z then (1 : ℂ) else -1))
        • (star Φ ⬝ᵥ (onSiteS x (spinSOp3 N)
            * (heisenbergHamiltonianS (ringCoupling L) N * onSiteS z (spinSOp3 N)
              - onSiteS z (spinSOp3 N) * heisenbergHamiltonianS (ringCoupling L) N)
          - (heisenbergHamiltonianS (ringCoupling L) N * onSiteS z (spinSOp3 N)
              - onSiteS z (spinSOp3 N) * heisenbergHamiltonianS (ringCoupling L) N)
            * onSiteS x (spinSOp3 N)).mulVec Φ)).re|
      ≤ (if z ∈ S then 4 * (N : ℝ) ^ 3 else 0) := by
    intro z
    by_cases hz : z ∈ S
    · rw [if_pos hz]
      have hnorm : |(star Φ ⬝ᵥ (onSiteS x (spinSOp3 N)
            * (heisenbergHamiltonianS (ringCoupling L) N * onSiteS z (spinSOp3 N)
              - onSiteS z (spinSOp3 N) * heisenbergHamiltonianS (ringCoupling L) N)
          - (heisenbergHamiltonianS (ringCoupling L) N * onSiteS z (spinSOp3 N)
              - onSiteS z (spinSOp3 N) * heisenbergHamiltonianS (ringCoupling L) N)
            * onSiteS x (spinSOp3 N)).mulVec Φ).re| ≤ 4 * (N : ℝ) ^ 3 :=
        le_trans (expectation_abs_le_manyBodyOperatorNormS _ hΦ)
          (pair_double_commutator_norm_le L N hL hN x z)
      have hsg : (if ringStaggeredSublattice L x then (1 : ℂ) else -1)
          * (if ringStaggeredSublattice L z then (1 : ℂ) else -1) = 1
          ∨ (if ringStaggeredSublattice L x then (1 : ℂ) else -1)
            * (if ringStaggeredSublattice L z then (1 : ℂ) else -1) = -1 := by
        by_cases hx : ringStaggeredSublattice L x <;> by_cases hz' : ringStaggeredSublattice L z <;>
          simp [hx, hz']
      rcases hsg with hc | hc
      · rw [hc, one_smul]; exact hnorm
      · rw [hc, neg_one_smul, Complex.neg_re, abs_neg]; exact hnorm
    · rw [if_neg hz]
      have hzero : (onSiteS x (spinSOp3 N)
            * (heisenbergHamiltonianS (ringCoupling L) N * onSiteS z (spinSOp3 N)
              - onSiteS z (spinSOp3 N) * heisenbergHamiltonianS (ringCoupling L) N)
          - (heisenbergHamiltonianS (ringCoupling L) N * onSiteS z (spinSOp3 N)
              - onSiteS z (spinSOp3 N) * heisenbergHamiltonianS (ringCoupling L) N)
            * onSiteS x (spinSOp3 N)) = 0 := by
        refine pair_double_commutator_eq_zero_of_ne L N hL z x ?_ ?_ ?_
        · exact fun h => hz (by rw [hS, ← h]; exact Finset.mem_insert_self _ _)
        · exact fun h => hz (by
            have hzx : z = (finRotate L).symm x := by rw [h, Equiv.symm_apply_apply]
            rw [hS, hzx]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
        · exact fun h => hz (by
            have hzx : z = finRotate L x := by rw [h, Equiv.apply_symm_apply]
            rw [hS, hzx]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      rw [hzero, Matrix.zero_mulVec, dotProduct_zero, smul_zero, Complex.zero_re, abs_zero]
  refine le_trans (Finset.sum_le_sum (fun z _ => hterm z)) ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hcard : (S.card : ℝ) ≤ 3 := by
    have h1 := Finset.card_insert_le x ({finRotate L x, (finRotate L).symm x} : Finset (Fin L))
    have h2 := Finset.card_insert_le (finRotate L x) ({(finRotate L).symm x} : Finset (Fin L))
    rw [Finset.card_singleton] at h2
    have h3 : S.card ≤ 3 := by rw [hS]; omega
    exact_mod_cast h3
  calc (S.card : ℝ) * (4 * (N : ℝ) ^ 3) ≤ 3 * (4 * (N : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 12 * (N : ℝ) ^ 3 := by ring

end LatticeSystem.Quantum
