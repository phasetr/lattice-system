import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyProperties

/-!
# Non-positivity of the predicted toy-Hamiltonian minimum energy

The simplified form of `bipartiteToyMinEnergyPredicted A N`
(PR #2779) is `-|A|·|¬A|·N²/2 - |¬A|·N`. Both terms are non-
positive real numbers, so the predicted minimum is itself non-
positive:

  `(bipartiteToyMinEnergyPredicted A N).re ≤ 0`.

Sanity-check theorem: the toy-Hamiltonian ground-state energy
prediction is consistent with antiferromagnetism (negative energy
contribution from each cross-bond).

Edge cases:
  * `|¬A| = 0` (saturated): predicted min = 0 (PR #2779).
  * `|A| = |¬A|` (balanced): predicted min = `-2 s_A(s_A+1)`
    (PR #2779), strictly negative for `s_A ≥ 1`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] {N : ℕ}

omit [Fintype Λ] in
/-- **Non-positivity of `bipartiteToyMinEnergyPredicted` (real part)**:
the predicted minimum toy-Hamiltonian energy has non-positive
real part for any bipartite sublattice `A` and any `N`. -/
theorem bipartiteToyMinEnergyPredicted_re_nonpos
    [Fintype Λ] (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re ≤ 0 := by
  rw [bipartiteToyMinEnergyPredicted_eq_simplified]
  -- The expression is purely real, so equate to a real number and
  -- apply real-valued arithmetic.
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
  have h_card_A_nn : 0 ≤ ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) :=
    Nat.cast_nonneg _
  have h_card_notA_nn : 0 ≤ ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
    Nat.cast_nonneg _
  have h_N_nn : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg h_card_A_nn h_card_notA_nn,
    mul_nonneg (mul_nonneg h_card_A_nn h_card_notA_nn)
      (mul_nonneg h_N_nn h_N_nn),
    mul_nonneg h_card_notA_nn h_N_nn]

end LatticeSystem.Quantum
