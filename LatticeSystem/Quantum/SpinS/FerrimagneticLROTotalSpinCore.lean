import LatticeSystem.Quantum.SpinS.Theorem23StructuralPFSectorCasimir
import LatticeSystem.Quantum.SpinS.MagConfig

/-!
# Ferrimagnetic LRO total spin: centered sector admissibility (foundation)

Foundational layer extracted from `FerrimagneticLROTotalSpin.lean` for build speed.  This file
proves that the centered magnetization sector is admissible.

The centered ground state with the predicted total-spin Casimir value is kept in the capstone module
`FerrimagneticLROTotalSpin.lean`.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The centered magnetization sector is admissible -/

omit [DecidableEq V] in
/-- **The centered magnetization sector lies in the Theorem 2.3 admissible interval.**

If the `magSumS` value `M0` is the center of the spectrum (centered magnetization `0`, i.e.
`|V| · N / 2 − M0 = 0` over `ℂ`), then `M0 ∈ tasaki23GroundStateSectors A N`, because
`2 · M0 = |V| · N = (|A| + |¬A|) · N` forces `min(|A|, |¬A|) · N ≤ M0 ≤ max(|A|, |¬A|) · N`. -/
theorem tasaki23GroundStateSectors_center_mem (A : V → Bool) (N M0 : ℕ)
    (hM0_center : ((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M0 : ℂ) = 0) :
    M0 ∈ tasaki23GroundStateSectors (V := V) A N := by
  classical
  set cA := (Finset.univ.filter (fun x : V => A x = true)).card with hcA
  set cB := (Finset.univ.filter (fun x : V => (! A x) = true)).card with hcB
  -- Turn the centering equation over `ℂ` into the integer identity `2 * M0 = (cA + cB) * N`.
  have hM0_two : 2 * M0 = (cA + cB) * N := by
    have hcard : cA + cB = Fintype.card V := tasaki23_card_filter_A_add_card_notA A
    have h := sub_eq_zero.mp hM0_center
    have hcast : (Fintype.card V : ℂ) * (N : ℂ) = 2 * (M0 : ℂ) := by
      have h2 : (Fintype.card V : ℂ) * (N : ℂ) / 2 * 2 = (M0 : ℂ) * 2 := by
        rw [h]
      rw [div_mul_cancel₀] at h2
      · linear_combination h2
      · norm_num
    have hcast' : ((2 * M0 : ℕ) : ℂ) = (((cA + cB) * N : ℕ) : ℂ) := by
      push_cast [hcard]
      linear_combination -hcast
    exact_mod_cast hcast'
  rw [tasaki23GroundStateSectors_mem_iff]
  rw [← hcA, ← hcB]
  refine ⟨?_, ?_⟩
  · -- `min cA cB * N ≤ M0` from `2 * min cA cB ≤ cA + cB` and `2 * M0 = (cA + cB) * N`.
    have hmin : 2 * (min cA cB * N) ≤ 2 * M0 := by
      rw [hM0_two]
      calc 2 * (min cA cB * N) = (2 * min cA cB) * N := by ring
        _ ≤ (cA + cB) * N := by
              apply Nat.mul_le_mul_right
              have := min_le_left cA cB
              have := min_le_right cA cB
              omega
    omega
  · -- `M0 ≤ max cA cB * N` from `cA + cB ≤ 2 * max cA cB`.
    have hmax : 2 * M0 ≤ 2 * (max cA cB * N) := by
      rw [hM0_two]
      calc (cA + cB) * N ≤ (2 * max cA cB) * N := by
              apply Nat.mul_le_mul_right
              have := le_max_left cA cB
              have := le_max_right cA cB
              omega
        _ = 2 * (max cA cB * N) := by ring
    omega

end LatticeSystem.Quantum
