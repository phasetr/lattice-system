import LatticeSystem.Quantum.SpinS.ConfigCombinatorics
import LatticeSystem.Quantum.SpinS.Magnetization
import LatticeSystem.Quantum.SpinS.MultiSiteDotOffDiag
import LatticeSystem.Quantum.SpinS.MultiSiteDot
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Matrix-level content of the spin-`S` raise/lower step
(Tasaki §2.5 Phase B-γ γ-3 connectivity infrastructure)

For the general spin-`S` Marshall–Lieb–Mattis theorem (Tasaki Theorem 2.2),
the irreducibility step requires showing that any two configurations with
the same magnetization are connected by a sequence of "raise/lower" moves
across `G`-adjacent vertex pairs — the spin-`S` analogue of the
spin-`1/2` `SwapStep` / `SwapReachable` infrastructure (see
`LatticeSystem/Quantum/MarshallLiebMattis/Connectivity.lean`).

The step relation `RaiseLowerStepS` and its reflexive transitive closure
`RaiseLowerReachableS` are purely combinatorial and live in
`LatticeSystem/Quantum/SpinS/ConfigCombinatorics.lean`.  This module adds
the matrix-level content of those moves:

* reachability preserves the `Ŝ_tot^{(3)}` eigenvalue `magEigenvalueS`;

* a raise/lower move along a `G`-edge is exactly a configuration pattern
  with a strictly real-positive `Ŝ_x · Ŝ_y` matrix element, hence a
  non-zero off-diagonal entry of the Heisenberg bond term.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Magnetization conservation -/

omit [DecidableEq V] in
/-- A `RaiseLowerReachableS` preserves the magnetization eigenvalue:
`magEigenvalueS σ' = magEigenvalueS σ`. -/
theorem magEigenvalueS_eq_of_raiseLowerReachableS {G : SimpleGraph V}
    {σ σ' : V → Fin (N + 1)} (h : RaiseLowerReachableS G σ σ') :
    magEigenvalueS σ' = magEigenvalueS σ := by
  classical
  unfold magEigenvalueS
  rw [magSumS_eq_of_raiseLowerReachableS h]

/-! ## Connection to spinSDot non-zero entries -/

/-- For a `RaiseLowerStepS G σ σ'` along an edge `(x, y)`, the
two-site dot-product matrix element `(spinSDot x y N) σ' σ` is
strictly real-positive (hence non-zero).  This bridges the
combinatorial connectivity (raise/lower steps) to the matrix-level
non-zero entries needed for the irreducibility argument. -/
theorem spinSDot_apply_re_pos_of_raiseLowerStepS_witness
    {G : SimpleGraph V} {σ σ' : V → Fin (N + 1)}
    {x y : V} (hadj : G.Adj x y)
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    0 < ((spinSDot x y N : ManyBodyOpS V N) σ' σ).re := by
  have hxy : x ≠ y := fun heq => G.loopless.irrefl _ (heq ▸ hadj)
  rcases hsh with ⟨hxr, hyl⟩ | ⟨hxl, hyr⟩
  · -- raise at x, lower at y: use spinSDot_apply_eq_lowering_raising_explicit.
    rw [spinSDot_apply_eq_lowering_raising_explicit hxy N hagree hxr hyl]
    -- The result is (1/2) · √_x · √_y · ofReal projection.
    -- Re of ((1/2) * (real * real)) = (1/2) * (real * real). Both √'s positive.
    rw [show ((1 / 2 : ℂ) *
            (((Real.sqrt (((N : ℝ) - (σ x).val) * ((σ x).val + 1)) : ℝ) : ℂ) *
              ((Real.sqrt (((σ y).val : ℝ) *
                ((N : ℝ) - (σ y).val + 1)) : ℝ) : ℂ))).re =
          (1 / 2 : ℝ) *
            (Real.sqrt (((N : ℝ) - (σ x).val) * ((σ x).val + 1)) *
              Real.sqrt (((σ y).val : ℝ) *
                ((N : ℝ) - (σ y).val + 1))) from by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]]
    -- Need positivity of both sqrt terms.
    -- σ' x = σ x + 1 ⟹ σ x < N (strict). And σ x + 1 ≥ 1. So sqrt is positive.
    have hxlt : (σ x).val < N := by
      have := (σ' x).isLt; omega
    have hsqx : 0 < Real.sqrt (((N : ℝ) - (σ x).val) * ((σ x).val + 1)) := by
      apply Real.sqrt_pos.mpr
      apply mul_pos
      · have : ((σ x).val : ℝ) < (N : ℝ) := by exact_mod_cast hxlt
        linarith
      · have : (0 : ℝ) ≤ (σ x).val := by positivity
        linarith
    -- σ' y = σ y - 1 ⟹ σ y > 0. And N - σ y ≥ 0 (since σ y ≤ N).
    have hygt : 0 < (σ y).val := by
      have hsy_le := (σ y).isLt; omega
    have hsqy : 0 < Real.sqrt (((σ y).val : ℝ) *
        ((N : ℝ) - (σ y).val + 1)) := by
      apply Real.sqrt_pos.mpr
      apply mul_pos
      · exact_mod_cast hygt
      · have : (σ y).val ≤ N := by have := (σ y).isLt; omega
        have : ((σ y).val : ℝ) ≤ (N : ℝ) := by exact_mod_cast this
        linarith
    have h12 : (0 : ℝ) < 1 / 2 := by norm_num
    positivity
  · -- lower at x, raise at y: use spinSDot_apply_eq_raising_lowering_explicit.
    rw [spinSDot_apply_eq_raising_lowering_explicit hxy N hagree hxl hyr]
    rw [show ((1 / 2 : ℂ) *
            (((Real.sqrt (((σ x).val : ℝ) *
              ((N : ℝ) - (σ x).val + 1)) : ℝ) : ℂ) *
              ((Real.sqrt (((N : ℝ) - (σ y).val) *
                ((σ y).val + 1)) : ℝ) : ℂ))).re =
          (1 / 2 : ℝ) *
            (Real.sqrt (((σ x).val : ℝ) *
              ((N : ℝ) - (σ x).val + 1)) *
              Real.sqrt (((N : ℝ) - (σ y).val) *
                ((σ y).val + 1))) from by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]]
    have hxgt : 0 < (σ x).val := by
      have := (σ' x).isLt; omega
    have hsqx : 0 < Real.sqrt (((σ x).val : ℝ) *
        ((N : ℝ) - (σ x).val + 1)) := by
      apply Real.sqrt_pos.mpr
      apply mul_pos
      · exact_mod_cast hxgt
      · have : (σ x).val ≤ N := by have := (σ x).isLt; omega
        have : ((σ x).val : ℝ) ≤ (N : ℝ) := by exact_mod_cast this
        linarith
    have hylt : (σ y).val < N := by
      have := (σ' y).isLt; omega
    have hsqy : 0 < Real.sqrt (((N : ℝ) - (σ y).val) * ((σ y).val + 1)) := by
      apply Real.sqrt_pos.mpr
      apply mul_pos
      · have : ((σ y).val : ℝ) < (N : ℝ) := by exact_mod_cast hylt
        linarith
      · have : (0 : ℝ) ≤ (σ y).val := by positivity
        linarith
    have h12 : (0 : ℝ) < 1 / 2 := by norm_num
    positivity

/-- Convenience form: the matrix element is non-zero. -/
theorem spinSDot_apply_ne_zero_of_raiseLowerStepS_witness
    {G : SimpleGraph V} {σ σ' : V → Fin (N + 1)}
    {x y : V} (hadj : G.Adj x y)
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (spinSDot x y N : ManyBodyOpS V N) σ' σ ≠ 0 := by
  intro heq
  have hpos := spinSDot_apply_re_pos_of_raiseLowerStepS_witness hadj hsh hagree
  rw [heq] at hpos
  simp at hpos

end LatticeSystem.Quantum
