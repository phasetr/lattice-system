import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightAbs
import LatticeSystem.Quantum.SpinS.CardSumEqFintype

/-!
# Identity: `min(|A|, |¬A|)·N = |Λ|·N/2 − ‖biw‖`

The minor sublattice count `min(|A|, |¬A|)`, the lattice
cardinality `|Λ|`, and the imbalance norm `‖biw‖` satisfy the
linear identity

  `min(|A|, |¬A|)·N = |Λ|·N/2 − ‖bipartiteImbalanceWeight A N‖`.

Proof:
- From PR #2870, `|A| + |¬A| = |Λ|`, so
  `max(|A|, |¬A|) − min(|A|, |¬A|) = ||A| − |¬A||` and
  `max + min = |Λ|`. Hence `2·min = |Λ| − ||A| − |¬A||`.
- From PR #2826, `‖biw‖ = ||A| − |¬A||·N/2`.
- Combining: `min·N = (|Λ| − ||A|−|¬A||)·N/2
                     = |Λ|·N/2 − ‖biw‖`.

This converts every formula involving `min(|A|, |¬A|)·N` into a
formula involving `‖biw‖` and `|Λ|·N/2`, enabling cleaner forms of
the Tasaki §2.5 Theorem 2.3 (γ-4) energy bounds.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Linear identity bridging `min·N`, `|Λ|·N/2`, and `‖biw‖`**:
`min(|A|, |¬A|)·N = |Λ|·N/2 − ‖bipartiteImbalanceWeight A N‖`. -/
theorem min_cardA_cardNotA_mul_N_eq_half_card_times_N_sub_imbalance_norm :
    min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
      (N : ℝ) =
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 -
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
  rw [bipartiteImbalanceWeight_norm_eq]
  have hsum := cardA_add_cardNotA_eq_card (Λ := Λ) A
  have hsum_real :
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
        (Fintype.card Λ : ℝ) := by exact_mod_cast hsum
  set a : ℝ := ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
  set b : ℝ := ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)
  -- 2·min(a, b) = (a+b) - |a − b|.
  have hmin :
      min a b = ((a + b) - |a - b|) / 2 := by
    rcases le_total a b with hab | hba
    · rw [min_eq_left hab, abs_of_nonpos (sub_nonpos.mpr hab)]
      ring
    · rw [min_eq_right hba, abs_of_nonneg (sub_nonneg.mpr hba)]
      ring
  rw [hmin, hsum_real]
  ring

end LatticeSystem.Quantum
