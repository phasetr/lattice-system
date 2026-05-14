import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyProperties

/-!
# Strict negativity of the predicted toy-H minimum energy
(non-degenerate case)

PR #2791 proved
`(bipartiteToyMinEnergyPredicted A N).re ≤ 0`.

In the non-degenerate case (`|A| ≥ 1`, `|¬A| ≥ 1`, `N ≥ 1`), the
real part is **strictly negative**:

  `(bipartiteToyMinEnergyPredicted A N).re < 0`.

Reflects that for a bipartite system with both sublattices
non-empty and at least one quantum (`N ≥ 1`), the
antiferromagnetic toy Hamiltonian has strictly negative
ground-state energy — consistent with the Tasaki §2.5
Theorem 2.3 prediction.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] {N : ℕ}

omit [Fintype Λ] in
/-- **Strict negativity of the predicted min energy** (non-
degenerate case): `(bipartiteToyMinEnergyPredicted A N).re < 0`
when both sublattices are non-empty and `N ≥ 1`. -/
theorem bipartiteToyMinEnergyPredicted_re_neg_of_nondegenerate
    [Fintype Λ] (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re < 0 := by
  rw [bipartiteToyMinEnergyPredicted_eq_simplified]
  have hreal :
      -(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          ((N : ℂ) * (N : ℂ)) / 2) -
        (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          (N : ℂ)) =
      ((-(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
            ((N : ℝ) * (N : ℝ)) / 2) -
          (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
            (N : ℝ))) : ℝ) := by
    push_cast; ring
  rw [hreal, Complex.ofReal_re]
  have h_card_A_pos : 0 < ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) :=
    by exact_mod_cast hA
  have h_card_notA_pos : 0 < ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
    by exact_mod_cast hAc
  have h_N_pos : 0 < (N : ℝ) := by exact_mod_cast hN
  nlinarith [mul_pos h_card_A_pos h_card_notA_pos,
    mul_pos (mul_pos h_card_A_pos h_card_notA_pos)
      (mul_pos h_N_pos h_N_pos),
    mul_pos h_card_notA_pos h_N_pos]

end LatticeSystem.Quantum
