import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy

/-!
# Signed difference `(predicted_min A).re − (predicted_min ¬A).re = (|A| − |¬A|)·N`

The signed-difference formula gives:
- `(predicted_min A).re = −|A|·|¬A|·N²/2 − |¬A|·N`.
- `(predicted_min ¬A).re = −|A|·|¬A|·N²/2 − |A|·N`.

Subtracting (the quadratic terms cancel):

  `(predicted_min A).re − (predicted_min ¬A).re = (|A| − |¬A|)·N`

unconditionally.

The sign of this difference equals the sign of `|A| − |¬A|` (at
`N ≥ 1`): positive at proper orientation (`|¬A| < |A|`), zero at
balanced, negative at complement orientation (`|A| < |¬A|`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Signed difference**: `(predicted_min A).re − (predicted_min ¬A).re
= (|A| − |¬A|)·N` unconditionally. -/
theorem bipartiteToyMinEnergyPredicted_re_sub_complement_re_eq
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re -
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) *
        (N : ℝ) := by
  rw [bipartiteToyMinEnergyPredicted_eq_simplified A N,
      bipartiteToyMinEnergyPredicted_eq_simplified (fun x => ! A x) N]
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  rw [hfilter_eq]
  simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im, Complex.div_ofNat_re,
    mul_zero, zero_mul, sub_zero]
  ring

end LatticeSystem.Quantum
