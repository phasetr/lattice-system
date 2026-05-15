import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmReal
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero
import LatticeSystem.Quantum.SpinS.CardSumEqFintype

/-!
# Bridge identity: symm-energy real part via imbalance-weight squared

Using
`bipartiteToyMinEnergyPredictedSymm A N
   = -|A|·|¬A|·N²/2 - min(|A|, |¬A|)·N`
together with the algebraic identity
`4·|A|·|¬A| = (|A|+|¬A|)² - (|A|-|¬A|)² = |Λ|² - (|A|-|¬A|)²`,
and the real-part formula
`(bipartiteImbalanceWeight A N).re = (|A| - |¬A|)·N/2`,
we get a clean bridge

  `8·((bipartiteToyMinEnergyPredictedSymm A N).re
       + min(|A|, |¬A|)·N)
     + |Λ|²·N²
     = 4·((bipartiteImbalanceWeight A N).re)²`.

This identity is fundamental for Tasaki §2.5 Theorem 2.3 (γ-4):
it makes the energy depend on the lattice cardinality and the
single number `||A| − |¬A||·N/2` (the predicted spin magnitude).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Bridge identity between `bipartiteToyMinEnergyPredictedSymm`
real part and `(bipartiteImbalanceWeight A N).re`**:

`8·(symm.re + min(|A|, |¬A|)·N) + |Λ|²·N² = 4·(biw.re)²`.

Useful for Tasaki §2.5 Theorem 2.3 (γ-4): the predicted minimum
energy and the predicted spin magnitude are linked by a simple
quadratic constraint involving only the lattice cardinality. -/
theorem bipartiteToyMinEnergyPredictedSymm_re_via_imbalance_sq :
    ((bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re +
        min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
          (N : ℝ)) * 8 +
      (Fintype.card Λ : ℝ) * (Fintype.card Λ : ℝ) * ((N : ℝ) * (N : ℝ)) =
      4 *
        ((bipartiteImbalanceWeight (Λ := Λ) A N).re *
          (bipartiteImbalanceWeight (Λ := Λ) A N).re) := by
  rw [bipartiteToyMinEnergyPredictedSymm_re_eq,
      bipartiteImbalanceWeight_re_eq]
  have hsum := cardA_add_cardNotA_eq_card (Λ := Λ) A
  have hsum_real :
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
        (Fintype.card Λ : ℝ) := by exact_mod_cast hsum
  have hL_sq :
      (Fintype.card Λ : ℝ) * (Fintype.card Λ : ℝ) =
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) *
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) := by
    rw [hsum_real]
  rw [hL_sq]
  ring

end LatticeSystem.Quantum
