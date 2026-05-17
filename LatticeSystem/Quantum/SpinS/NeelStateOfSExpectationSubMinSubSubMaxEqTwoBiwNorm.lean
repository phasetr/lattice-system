import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubMinComplement
import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubMaxComplement
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightAbs

/-!
# `(⟨Néel⟩.re − min) − (⟨Néel⟩.re − max) = 2 · ‖biw‖` unconditionally

biw-norm form of PR #3132 (`(Néel − min) − (Néel − max) = (max − min)·N`).
The difference of the two operator-algebraic gaps equals twice the
imbalance-weight norm `‖biw‖ = ||A|−|¬A||·N/2`:

  `(⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re − min(...)) − (⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re − max(...))
    = 2 · ‖biw‖`

unconditionally. From PR #3052 (Néel − min = max·N) and PR #3129
(Néel − max = min·N), the difference is `(max − min)·N = ||A|−|¬A||·N
= 2·‖biw‖`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`(⟨Néel⟩.re − min) − (⟨Néel⟩.re − max) = 2 · ‖biw‖`** unconditionally. biw-norm of PR #3132. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_min_sub_sub_max_complement_re_eq_two_biw_norm
    (A : Λ → Bool) (N : ℕ) :
    ((dotProduct (star (neelStateOfS A N))
          ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
            (neelStateOfS A N))).re -
        min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
            (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) -
      ((dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re -
          max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
              (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) =
      2 * ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
  rw [neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_min_complement_re_eq,
      neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_max_complement_re_eq]
  -- Goal: max·N − min·N = 2·‖biw‖.
  rw [bipartiteImbalanceWeight_norm_eq]
  -- ‖biw‖ = ||A| − |¬A||·N/2.
  have h := max_sub_min_eq_abs ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
    ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)
  -- h: max - min = |y - x|. Want: max - min = |x - y|. Use abs_sub_comm.
  have h' : max ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) -
      min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
      |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| := by
    rw [h, abs_sub_comm]
  have hN : (max ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) -
      min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) * (N : ℝ) =
      |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| * (N : ℝ) := by
    rw [h']
  linarith

end LatticeSystem.Quantum
