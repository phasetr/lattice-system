import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy
import LatticeSystem.Quantum.SpinS.SublatticeSpin
import LatticeSystem.Quantum.SpinS.SublatticeSpinDot
import LatticeSystem.Quantum.SpinS.TotalSquared

/-!
# Sublattice spin operators equal the total spin in the saturated edge case

When `|¬A| = 0` (i.e. all sites are in `A`), the complement
sublattice `¬A` is empty and its spin operators all vanish.
Consequently:

  * `Ŝ_{¬A}^{(α)} = 0` for `α ∈ {1, 2, 3}` (empty-sum identity).
  * `Ŝ_{¬A}² = 0` (zero operator).
  * `Ŝ_A^{(α)} = Ŝ_{tot}^{(α)}` for each axis (via the decomposition
    `totalSpinSOp_α = sublatticeSpinSOp_α A + sublatticeSpinSOp_α (¬A)`).
  * `Ŝ_A² = Ŝ_{tot}²` as operators.

This file packages these identities and uses them to derive the
**eigenspace bridge**:

  `eigenspace((Ŝ_tot)²)_{s_A(s_A+1)} ≤
     bipartiteToyGroundStateSubspacePredicted A N`

for `|¬A| = 0`. This gives a dimension lower bound on the
predicted GS subspace at the saturated edge case: it contains the
entire `(Ŝ_tot)²`-eigenspace at the maximum eigenvalue, which by
PR #2768's identification with the saturated-ferromagnet joint
eigenspace has dimension at least `(2 s_A + 1)` (the predicted
Theorem 2.3 degeneracy).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Empty-sublattice spin-`α` operator vanishes**: when
`card {x | A x = true} = 0`, `Ŝ_A^(α) = 0`. -/
theorem sublatticeSpinSOp1_eq_zero_of_card_zero
    (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    (sublatticeSpinSOp1 N A : ManyBodyOpS Λ N) = 0 := by
  unfold sublatticeSpinSOp1
  have hall : ∀ x : Λ, ¬ (A x = true) := by
    intro x hAx
    have : x ∈ Finset.univ.filter (fun x : Λ => A x = true) := by
      simp [hAx]
    have : (Finset.univ.filter (fun x : Λ => A x = true)).card ≠ 0 :=
      Finset.card_ne_zero_of_mem this
    exact this h
  refine Finset.sum_eq_zero (fun x _ => ?_)
  rw [if_neg (hall x)]

theorem sublatticeSpinSOp2_eq_zero_of_card_zero
    (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    (sublatticeSpinSOp2 N A : ManyBodyOpS Λ N) = 0 := by
  unfold sublatticeSpinSOp2
  have hall : ∀ x : Λ, ¬ (A x = true) := by
    intro x hAx
    have : x ∈ Finset.univ.filter (fun x : Λ => A x = true) := by
      simp [hAx]
    have : (Finset.univ.filter (fun x : Λ => A x = true)).card ≠ 0 :=
      Finset.card_ne_zero_of_mem this
    exact this h
  refine Finset.sum_eq_zero (fun x _ => ?_)
  rw [if_neg (hall x)]

theorem sublatticeSpinSOp3_eq_zero_of_card_zero
    (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    (sublatticeSpinSOp3 N A : ManyBodyOpS Λ N) = 0 := by
  unfold sublatticeSpinSOp3
  have hall : ∀ x : Λ, ¬ (A x = true) := by
    intro x hAx
    have : x ∈ Finset.univ.filter (fun x : Λ => A x = true) := by
      simp [hAx]
    have : (Finset.univ.filter (fun x : Λ => A x = true)).card ≠ 0 :=
      Finset.card_ne_zero_of_mem this
    exact this h
  refine Finset.sum_eq_zero (fun x _ => ?_)
  rw [if_neg (hall x)]

/-- **Empty-sublattice spin squared vanishes**:
`Ŝ_A² = 0` when `card A = 0`. -/
theorem sublatticeSpinSquaredS_eq_zero_of_card_zero
    (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    (sublatticeSpinSquaredS N A : ManyBodyOpS Λ N) = 0 := by
  unfold sublatticeSpinSquaredS
  rw [sublatticeSpinSOp1_eq_zero_of_card_zero A h,
      sublatticeSpinSOp2_eq_zero_of_card_zero A h,
      sublatticeSpinSOp3_eq_zero_of_card_zero A h]
  simp

/-- **Sublattice spin axis 1 = total spin axis 1 when `|¬A| = 0`**:
in the saturated case, the `A`-sublattice spin-1 operator coincides
with the total spin-1 operator. -/
theorem sublatticeSpinSOp1_eq_totalSpinSOp1_of_cardNotA_zero
    (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    (sublatticeSpinSOp1 N A : ManyBodyOpS Λ N) = totalSpinSOp1 Λ N := by
  rw [totalSpinSOp1_eq_sublattice_sum (Λ := Λ) (N := N) A,
      sublatticeSpinSOp1_eq_zero_of_card_zero (fun x => ! A x) h]
  simp

theorem sublatticeSpinSOp2_eq_totalSpinSOp2_of_cardNotA_zero
    (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    (sublatticeSpinSOp2 N A : ManyBodyOpS Λ N) = totalSpinSOp2 Λ N := by
  rw [totalSpinSOp2_eq_sublattice_sum (Λ := Λ) (N := N) A,
      sublatticeSpinSOp2_eq_zero_of_card_zero (fun x => ! A x) h]
  simp

theorem sublatticeSpinSOp3_eq_totalSpinSOp3_of_cardNotA_zero
    (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    (sublatticeSpinSOp3 N A : ManyBodyOpS Λ N) = totalSpinSOp3 Λ N := by
  rw [totalSpinSOp3_eq_sublattice_sum (Λ := Λ) (N := N) A,
      sublatticeSpinSOp3_eq_zero_of_card_zero (fun x => ! A x) h]
  simp

/-- **`Ŝ_A² = Ŝ_{tot}²` when `|¬A| = 0`**: in the saturated case,
the `A`-sublattice Casimir coincides with the total Casimir. -/
theorem sublatticeSpinSquaredS_eq_totalSpinSSquared_of_cardNotA_zero
    (A : Λ → Bool)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    (sublatticeSpinSquaredS N A : ManyBodyOpS Λ N) = totalSpinSSquared Λ N := by
  unfold sublatticeSpinSquaredS totalSpinSSquared
  rw [sublatticeSpinSOp1_eq_totalSpinSOp1_of_cardNotA_zero A h,
      sublatticeSpinSOp2_eq_totalSpinSOp2_of_cardNotA_zero A h,
      sublatticeSpinSOp3_eq_totalSpinSOp3_of_cardNotA_zero A h]

end LatticeSystem.Quantum
