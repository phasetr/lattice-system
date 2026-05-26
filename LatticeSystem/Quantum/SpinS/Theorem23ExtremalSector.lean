import LatticeSystem.Quantum.SpinS.Theorem23Sectors
import Mathlib.Data.Complex.Basic

/-!
# The extremal magnetization sector realizes the predicted total spin

Issue #3674 (the abstract variational lower bound completing the toy-ground-state
predicted-Casimir witness; Issue #3658 PR 4 / #3542).

The left endpoint `M = min(|A|, |¬A|)·N` of the predicted ground-state sector
interval (`tasaki23GroundStateSectors`) is the **extremal** magnetization sector:
its `Ŝ_tot^(3)` magnetization eigenvalue `|V|·N/2 − M` equals the predicted total
spin `S_tot = |s_A − s_B|`.  This supplies the extremal-sector hypothesis `hM` of
the toy total-Casimir pin (`tasaki23_total_casimir_re_eq_predicted_of_bounds`,
#3676): a sector-`M` vector has magnetization equal to the predicted total spin.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- **Extremal sector realizes the predicted total spin**: for the left-endpoint
sector `M = min(|A|, |¬A|)·N`, the magnetization eigenvalue `|V|·N/2 − M` has real
part equal to `tasaki23PredictedTotalSpin A N = |s_A − s_B|`. -/
theorem tasaki23_extremal_sector_magnetization_re_eq_predicted (A : V → Bool) (N : ℕ) :
    (((Fintype.card V : ℂ) * (N : ℂ) / 2) -
        ((min (Finset.univ.filter (fun x : V => A x = true)).card
            (Finset.univ.filter (fun x : V => (! A x) = true)).card * N : ℕ) : ℂ)).re =
      tasaki23PredictedTotalSpin (V := V) A N := by
  -- abbreviations
  obtain ⟨cA, hcA⟩ : ∃ n, (Finset.univ.filter (fun x : V => A x = true)).card = n := ⟨_, rfl⟩
  obtain ⟨cB, hcB⟩ : ∃ n, (Finset.univ.filter (fun x : V => (! A x) = true)).card = n := ⟨_, rfl⟩
  rw [hcA, hcB]
  -- |V| = cA + cB.
  have hcard : Fintype.card V = cA + cB := by
    rw [← hcA, ← hcB]; exact (tasaki23_card_filter_A_add_card_notA A).symm
  -- Compute the real part.
  have hre : (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((min cA cB * N : ℕ) : ℂ)).re =
      (Fintype.card V : ℝ) * (N : ℝ) / 2 - ((min cA cB * N : ℕ) : ℝ) := by
    simp [Complex.sub_re, Complex.mul_re]
  rw [hre, tasaki23PredictedTotalSpin_eq_sector_half_width, hcA, hcB, hcard]
  -- max ≥ min so the ℕ subtraction is exact.
  have hmm : min cA cB ≤ max cA cB := min_le_max
  have hcast : ((max cA cB * N - min cA cB * N : ℕ) : ℝ) =
      (max cA cB : ℝ) * (N : ℝ) - (min cA cB : ℝ) * (N : ℝ) := by
    have hle : (min cA cB * N) ≤ (max cA cB * N) := Nat.mul_le_mul_right N hmm
    push_cast [Nat.cast_sub hle]
    ring
  rw [hcast]
  push_cast
  have hsum : max (cA : ℝ) (cB : ℝ) + min (cA : ℝ) (cB : ℝ) = (cA : ℝ) + (cB : ℝ) :=
    max_add_min _ _
  nlinarith [hsum]

end LatticeSystem.Quantum
