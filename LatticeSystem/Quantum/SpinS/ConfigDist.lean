import LatticeSystem.Quantum.SpinS.RaiseLower
import Mathlib.Data.Nat.Dist

/-!
# Spin-`S` configuration distance
(Tasaki §2.5 Phase B-γ γ-3 connectivity prep)

The configuration distance `configDistS σ σ' := ∑_x |σ x − σ' x|`
(natural-number absolute difference) measures how far apart two
spin-`S` configurations are. It is the spin-`S` generalisation of the
Hamming distance used in the spin-`1/2` connectivity argument
(`LatticeSystem/Quantum/MarshallLiebMattis/EqMagnetizationReachable.lean`).

Key properties:
- `configDistS_eq_zero_iff`: distance zero iff configurations are equal.
- `configDistS_comm`: symmetry.

These are stepping stones for the irreducibility argument: starting
from two equal-magnetization configurations of positive distance, find
sites `x, y` where `σ x > σ' x` and `σ y < σ' y`, transport one unit
to reduce the distance, and iterate.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The configuration distance: sum of natural-number absolute
differences of `σ x` and `σ' x` over all sites. -/
def configDistS (σ σ' : V → Fin (N + 1)) : ℕ :=
  ∑ x : V, Nat.dist (σ x).val (σ' x).val

omit [DecidableEq V] in
/-- Definitional unfolding of `configDistS`. -/
theorem configDistS_def (σ σ' : V → Fin (N + 1)) :
    configDistS σ σ' = ∑ x : V, Nat.dist (σ x).val (σ' x).val := rfl

omit [DecidableEq V] in
/-- Configuration distance is zero iff the two configurations agree
everywhere. -/
theorem configDistS_eq_zero_iff (σ σ' : V → Fin (N + 1)) :
    configDistS σ σ' = 0 ↔ σ = σ' := by
  unfold configDistS
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h
    funext x
    have hx := h x (Finset.mem_univ x)
    apply Fin.ext
    exact Nat.eq_of_dist_eq_zero hx
  · intro h x _
    rw [h]
    exact Nat.dist_self _

omit [DecidableEq V] in
/-- `configDistS` is symmetric. -/
theorem configDistS_comm (σ σ' : V → Fin (N + 1)) :
    configDistS σ σ' = configDistS σ' σ := by
  unfold configDistS
  refine Finset.sum_congr rfl (fun x _ => ?_)
  exact Nat.dist_comm _ _

omit [DecidableEq V] in
/-- Configuration distance with itself is zero. -/
@[simp]
theorem configDistS_self (σ : V → Fin (N + 1)) : configDistS σ σ = 0 := by
  rw [configDistS_eq_zero_iff]

omit [DecidableEq V] in
/-- Two configurations differ iff their `configDistS` is positive. -/
theorem configDistS_pos_iff (σ σ' : V → Fin (N + 1)) :
    0 < configDistS σ σ' ↔ σ ≠ σ' := by
  rw [Nat.pos_iff_ne_zero, ne_eq, configDistS_eq_zero_iff]

/-! ## Existence of over/under sites for equal-magnetization pairs -/

omit [DecidableEq V] in
/-- For two distinct configurations with equal magnetization sums,
there exists a site where `σ` exceeds `σ'` and another where `σ`
falls below `σ'`. This is the input to the iteration argument that
reduces `configDistS` step by step toward zero. -/
theorem exists_over_under_of_eq_magSumS
    {σ σ' : V → Fin (N + 1)}
    (hne : σ ≠ σ') (hmag : magSumS σ = magSumS σ') :
    (∃ x : V, (σ' x).val < (σ x).val) ∧
      ∃ y : V, (σ y).val < (σ' y).val := by
  -- Witness of disagreement.
  obtain ⟨z, hz⟩ := Function.ne_iff.mp hne
  -- WLOG σ z ≠ σ' z, so either σ z > σ' z or σ z < σ' z.
  have hzord : (σ z).val < (σ' z).val ∨ (σ' z).val < (σ z).val := by
    rcases Nat.lt_or_ge (σ z).val (σ' z).val with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      rcases Nat.lt_or_ge (σ' z).val (σ z).val with h' | h'
      · exact h'
      · -- (σ z).val ≥ (σ' z).val and (σ z).val ≤ (σ' z).val: equal.
        exfalso; apply hz; apply Fin.ext; omega
  -- From the magnetization equality, ∑ over = ∑ under (positive integer sums).
  -- If only over (no under), sum-σ > sum-σ', contradiction.
  -- If only under (no over), sum-σ < sum-σ', contradiction.
  refine ⟨?_, ?_⟩
  · -- Show ∃ x, (σ' x).val < (σ x).val.
    by_contra h_no_over
    push Not at h_no_over
    -- h_no_over : ∀ x, (σ x).val ≤ (σ' x).val.
    have hzlt : (σ z).val < (σ' z).val := by
      rcases hzord with hlt | hgt
      · exact hlt
      · exact (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (h_no_over z) hgt)).elim
    have hsum_lt : magSumS σ < magSumS σ' := by
      unfold magSumS
      apply Finset.sum_lt_sum (fun x _ => h_no_over x) ⟨z, Finset.mem_univ z, hzlt⟩
    omega
  · -- Show ∃ y, (σ y).val < (σ' y).val.
    by_contra h_no_under
    push Not at h_no_under
    -- h_no_under : ∀ y, (σ' y).val ≤ (σ y).val.
    have hzgt : (σ' z).val < (σ z).val := by
      rcases hzord with hlt | hgt
      · exact (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (h_no_under z) hlt)).elim
      · exact hgt
    have hsum_gt : magSumS σ' < magSumS σ := by
      unfold magSumS
      apply Finset.sum_lt_sum (fun x _ => h_no_under x) ⟨z, Finset.mem_univ z, hzgt⟩
    omega

end LatticeSystem.Quantum
