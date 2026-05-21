import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Tasaki §2.5 Theorem 2.3 — predicted spin and sector interval

This file contains the combinatorial sector API used by
`Theorem23.lean`: the predicted total spin/Casimir values, the
admissible `magSumS` interval, and its basic endpoint/cardinality
facts.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 predicted total-spin magnitude**
`S_tot = ||A| − |¬A|| · (N/2)` (the real-valued half-integer
prediction). -/
noncomputable def tasaki23PredictedTotalSpin (A : V → Bool) (N : ℕ) : ℝ :=
  |((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) -
    ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ)| *
    ((N : ℝ) / 2)

/-- **Tasaki §2.5 Theorem 2.3 predicted total-Casimir value**:
`S_tot * (S_tot + 1)` for the predicted total spin. -/
noncomputable def tasaki23PredictedCasimirValue (A : V → Bool) (N : ℕ) : ℝ :=
  tasaki23PredictedTotalSpin (V := V) A N *
    (tasaki23PredictedTotalSpin (V := V) A N + 1)

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 sublattice-cardinality partition**:
the `A` and `¬A` Boolean fibers partition the finite vertex set. -/
theorem tasaki23_card_filter_A_add_card_notA (A : V → Bool) :
    (Finset.univ.filter (fun x : V => A x = true)).card +
      (Finset.univ.filter (fun x : V => (! A x) = true)).card =
        Fintype.card V := by
  classical
  have hfilter_eq :
      Finset.univ.filter (fun x : V => (! A x) = true) =
        Finset.univ.filter (fun x : V => ¬ A x = true) := by
    congr 1
    funext x
    by_cases hA : A x = true
    · simp [hA]
    · simp [hA]
  rw [hfilter_eq, ← Finset.card_univ]
  exact Finset.card_filter_add_card_filter_not (fun x : V => A x = true)

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 predicted spin as half-width**:
the predicted total spin is half the width of the admissible
`magSumS` interval. -/
theorem tasaki23PredictedTotalSpin_eq_sector_half_width (A : V → Bool) (N : ℕ) :
    tasaki23PredictedTotalSpin (V := V) A N =
      (((max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N) -
        (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N) :
        ℕ) : ℝ) / 2 := by
  let cA := (Finset.univ.filter (fun x : V => A x = true)).card
  let cB := (Finset.univ.filter (fun x : V => (! A x) = true)).card
  change |(cA : ℝ) - (cB : ℝ)| * ((N : ℝ) / 2) =
    (((max cA cB * N - min cA cB * N : ℕ) : ℝ) / 2)
  rcases le_total cA cB with h | h
  · have hmin : min cA cB = cA := min_eq_left h
    have hmax : max cA cB = cB := max_eq_right h
    have hle_real : (cA : ℝ) ≤ (cB : ℝ) := by exact_mod_cast h
    have hnonpos : (cA : ℝ) - (cB : ℝ) ≤ 0 := by nlinarith
    rw [hmin, hmax, ← Nat.sub_mul]
    rw [abs_of_nonpos hnonpos]
    have hsub_cast : ((cB - cA : ℕ) : ℝ) = (cB : ℝ) - (cA : ℝ) := by
      have hsub_add : ((cB - cA : ℕ) : ℝ) + (cA : ℝ) = (cB : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel h
      nlinarith
    rw [Nat.cast_mul, hsub_cast]
    ring
  · have hmin : min cA cB = cB := min_eq_right h
    have hmax : max cA cB = cA := max_eq_left h
    have hle_real : (cB : ℝ) ≤ (cA : ℝ) := by exact_mod_cast h
    have hnonneg : 0 ≤ (cA : ℝ) - (cB : ℝ) := by nlinarith
    rw [hmin, hmax, ← Nat.sub_mul]
    rw [abs_of_nonneg hnonneg]
    have hsub_cast : ((cA - cB : ℕ) : ℝ) = (cA : ℝ) - (cB : ℝ) := by
      have hsub_add : ((cA - cB : ℕ) : ℝ) + (cB : ℝ) = (cA : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel h
      nlinarith
    rw [Nat.cast_mul, hsub_cast]
    ring

/-- **Tasaki §2.5 Theorem 2.3 predicted spectral degeneracy**
`2 S_tot + 1 = ||A| − |¬A|| · N + 1` (integer-valued). -/
def tasaki23PredictedDegeneracy (A : V → Bool) (N : ℕ) : ℕ :=
  (Int.natAbs (((Finset.univ.filter (fun x : V => A x = true)).card : ℤ) -
    ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℤ))) * N + 1

/-- **Tasaki §2.5 Theorem 2.3 admissible magnetization sectors**:
the set of `magSumS` values `M` whose centered magnetization
`m = M − |V|·N/2` satisfies `m ∈ {−S_tot, …, S_tot}`. In `magSumS`
(non-negative integer) units this is the closed integer interval
`[min(|A|, |¬A|) · N, max(|A|, |¬A|) · N]`, of cardinality
`2 S_tot + 1 = ||A| − |¬A|| · N + 1` (= `tasaki23PredictedDegeneracy`). -/
def tasaki23GroundStateSectors (A : V → Bool) (N : ℕ) : Finset ℕ :=
  let cA := (Finset.univ.filter (fun x : V => A x = true)).card
  let cB := (Finset.univ.filter (fun x : V => (! A x) = true)).card
  Finset.Icc (min cA cB * N) (max cA cB * N)

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 admissible-sector membership**:
membership in `tasaki23GroundStateSectors A N` is exactly the closed
integer interval between `min(|A|, |¬A|)·N` and `max(|A|, |¬A|)·N`. -/
theorem tasaki23GroundStateSectors_mem_iff (A : V → Bool) (N M : ℕ) :
    M ∈ tasaki23GroundStateSectors (V := V) A N ↔
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N ≤ M ∧
        M ≤ max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N := by
  simp [tasaki23GroundStateSectors]

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 left endpoint sector**:
the lower endpoint `min(|A|, |¬A|)·N` belongs to the admissible
sector interval. -/
theorem tasaki23GroundStateSectors_left_mem (A : V → Bool) (N : ℕ) :
    min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N ∈
      tasaki23GroundStateSectors (V := V) A N := by
  rw [tasaki23GroundStateSectors_mem_iff]
  exact ⟨le_rfl, Nat.mul_le_mul_right N min_le_max⟩

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 right endpoint sector**:
the upper endpoint `max(|A|, |¬A|)·N` belongs to the admissible
sector interval. -/
theorem tasaki23GroundStateSectors_right_mem (A : V → Bool) (N : ℕ) :
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N ∈
      tasaki23GroundStateSectors (V := V) A N := by
  rw [tasaki23GroundStateSectors_mem_iff]
  exact ⟨Nat.mul_le_mul_right N min_le_max, le_rfl⟩

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 successor sector closure**:
inside the admissible interval, any non-right-endpoint sector has its
successor in the same interval. This is the combinatorial form needed
to apply the lowering-direction adjacent-sector ladder step. -/
theorem tasaki23GroundStateSectors_succ_mem_of_mem_of_lt_right (A : V → Bool) (N : ℕ)
    {M : ℕ}
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N := by
  rw [tasaki23GroundStateSectors_mem_iff] at hM ⊢
  omega

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 predecessor sector closure**:
inside the admissible interval, any non-left-endpoint sector has its
predecessor in the same interval. This is the combinatorial form needed
to apply the raising-direction adjacent-sector ladder step. -/
theorem tasaki23GroundStateSectors_pred_mem_of_left_lt_of_mem (A : V → Bool) (N : ℕ)
    {M : ℕ}
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N < M)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N) :
    M - 1 ∈ tasaki23GroundStateSectors (V := V) A N := by
  rw [tasaki23GroundStateSectors_mem_iff] at hM ⊢
  omega

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 admissible-sector physical range**:
every admissible sector lies within the full spin-`S` magnetization
range `0 ≤ M ≤ |V| * N`.  This is the upper-bound half needed to
replace interval-specific non-emptiness callbacks by a canonical
physical-range non-emptiness callback for `magConfigS`. -/
theorem tasaki23GroundStateSectors_le_card_mul (A : V → Bool) (N : ℕ) {M : ℕ}
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N) :
    M ≤ Fintype.card V * N := by
  let cA := (Finset.univ.filter (fun x : V => A x = true)).card
  let cB := (Finset.univ.filter (fun x : V => (! A x) = true)).card
  have hbounds := (tasaki23GroundStateSectors_mem_iff (V := V) A N M).mp hM
  have hmax_le_sum : max cA cB ≤ cA + cB := by
    exact max_le (Nat.le_add_right cA cB) (Nat.le_add_left cB cA)
  have hright_le_total : max cA cB * N ≤ (cA + cB) * N :=
    Nat.mul_le_mul_right N hmax_le_sum
  have hcard_sum : cA + cB = Fintype.card V := by
    simpa [cA, cB] using tasaki23_card_filter_A_add_card_notA (V := V) A
  calc
    M ≤ max cA cB * N := by
      simpa [cA, cB] using hbounds.2
    _ ≤ (cA + cB) * N := hright_le_total
    _ = Fintype.card V * N := by rw [hcard_sum]

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 admissible-sector cardinality**:
the interval of ground-state magnetization sectors has the predicted
degeneracy `||A| - |¬A||·N + 1 = 2 S_tot + 1`. -/
theorem tasaki23GroundStateSectors_card (A : V → Bool) (N : ℕ) :
    (tasaki23GroundStateSectors (V := V) A N).card =
      tasaki23PredictedDegeneracy (V := V) A N := by
  let cA := (Finset.univ.filter (fun x : V => A x = true)).card
  let cB := (Finset.univ.filter (fun x : V => (! A x) = true)).card
  change (Finset.Icc (min cA cB * N) (max cA cB * N)).card =
    Int.natAbs ((cA : ℤ) - (cB : ℤ)) * N + 1
  rcases le_total cA cB with h | h
  · have hmin : min cA cB = cA := min_eq_left h
    have hmax : max cA cB = cB := max_eq_right h
    have habs : Int.natAbs ((cA : ℤ) - (cB : ℤ)) = cB - cA := by
      omega
    rw [hmin, hmax, Nat.card_Icc, habs]
    have hmul : cA * N ≤ cB * N := Nat.mul_le_mul_right N h
    have hcard : cB * N + 1 - cA * N = (cB * N - cA * N) + 1 := by
      omega
    rw [hcard, ← Nat.sub_mul]
  · have hmin : min cA cB = cB := min_eq_right h
    have hmax : max cA cB = cA := max_eq_left h
    have habs : Int.natAbs ((cA : ℤ) - (cB : ℤ)) = cA - cB := by
      omega
    rw [hmin, hmax, Nat.card_Icc, habs]
    have hmul : cB * N ≤ cA * N := Nat.mul_le_mul_right N h
    have hcard : cA * N + 1 - cB * N = (cA * N - cB * N) + 1 := by
      omega
    rw [hcard, ← Nat.sub_mul]

end LatticeSystem.Quantum
