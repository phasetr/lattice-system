import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelExpectations
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy

/-!
# Néel expectation vs complement-orientation predicted min: gap = `|A|·N`

Mirror of PR #3053. By the same algebra applied to the complement
orientation `¬A`:

  `⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re − (predicted_min ¬A).re = |A|·N`

unconditionally. The two bridges together give:
- Néel − pmA   = `|¬A|·N` (PR #3053).
- Néel − pm¬A = `|A|·N`  (this PR).
Their sum = `|Λ|·N` matches `2 · (|Λ|·N/2) = 2·(avg-gap)` (PR #3051).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **Néel expectation sits `|A|·N` above the complement-orientation
predicted min energy** (mirror of PR #3053). -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_complement_predicted_re_eq
    (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re -
      (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) * (N : ℝ) := by
  rw [neelStateOfS_heisenbergToyHamiltonianS_expectation,
      bipartiteToyMinEnergyPredicted_eq_simplified (fun x => ! A x) N]
  -- Replace card {¬¬A} with card {A}.
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  rw [hfilter_eq]
  simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im, Complex.div_ofNat_re,
    mul_zero, zero_mul, sub_zero, add_zero]
  ring

end LatticeSystem.Quantum
