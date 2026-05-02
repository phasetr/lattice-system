import LatticeSystem.Quantum.SpinS.Magnetization
import LatticeSystem.Quantum.SpinS.MultiSiteDot
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Spin-`S` raising/lowering step relation
(Tasaki §2.5 Phase B-γ γ-3 connectivity infrastructure)

For the general spin-`S` Marshall–Lieb–Mattis theorem (Tasaki Theorem 2.2),
the irreducibility step requires showing that any two configurations with
the same magnetization are connected by a sequence of "raise/lower" moves
across `G`-adjacent vertex pairs — the spin-`S` analogue of the
spin-`1/2` `SwapStep` / `SwapReachable` infrastructure (see
`LatticeSystem/Quantum/MarshallLiebMattis/Connectivity.lean`).

This module records the basic single-step relation:

* `RaiseLowerStepS G σ σ'` — `σ'` differs from `σ` only at two
  `G`-adjacent vertices `x, y`, with one site raised by `1` and the
  other lowered by `1` (the only off-diagonal pattern that yields a
  non-zero `Ŝ_x · Ŝ_y` matrix element on a raising/lowering pair).

* `RaiseLowerReachableS G` — its reflexive transitive closure.

The walk-based reachability lemma (analogue of
`swapReachable_of_walk_of_ne` in the `S = 1/2` case) is deferred to
a follow-up PR.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- One-step raise/lower relation along a `G`-edge: `σ'` is obtained
from `σ` by either
- raising at `x` (so `σ' x = σ x + 1`) and lowering at `y` (so
  `σ' y = σ y − 1`),
- or vice versa (lowering at `x` and raising at `y`).

The pair `(x, y)` must be `G`-adjacent and σ' agrees with σ off
`{x, y}`.  This corresponds exactly to the configuration patterns where
`(Ŝ_x · Ŝ_y) σ' σ ≠ 0` for the raising/lowering ladder terms (the
off-diagonal entries of the Heisenberg Hamiltonian on a `G`-bond). -/
def RaiseLowerStepS (G : SimpleGraph V)
    (σ σ' : V → Fin (N + 1)) : Prop :=
  ∃ x y : V, G.Adj x y ∧
    (((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val)) ∧
    ∀ k, k ≠ x → k ≠ y → σ' k = σ k

/-- Reflexive transitive closure of `RaiseLowerStepS G`: the smallest
relation containing `RaiseLowerStepS G` that is reflexive and
transitive. -/
def RaiseLowerReachableS (G : SimpleGraph V) :
    (V → Fin (N + 1)) → (V → Fin (N + 1)) → Prop :=
  Relation.ReflTransGen (RaiseLowerStepS G)

omit [Fintype V] [DecidableEq V] in
/-- Reflexivity of `RaiseLowerReachableS`. -/
theorem RaiseLowerReachableS.refl (G : SimpleGraph V)
    (σ : V → Fin (N + 1)) :
    RaiseLowerReachableS G σ σ :=
  Relation.ReflTransGen.refl

omit [Fintype V] [DecidableEq V] in
/-- A single `RaiseLowerStepS` is a `RaiseLowerReachableS`. -/
theorem RaiseLowerReachableS.single {G : SimpleGraph V}
    {σ σ' : V → Fin (N + 1)} (h : RaiseLowerStepS G σ σ') :
    RaiseLowerReachableS G σ σ' :=
  Relation.ReflTransGen.single h

omit [Fintype V] [DecidableEq V] in
/-- Transitivity of `RaiseLowerReachableS`. -/
theorem RaiseLowerReachableS.trans {G : SimpleGraph V}
    {σ τ σ' : V → Fin (N + 1)}
    (h₁ : RaiseLowerReachableS G σ τ)
    (h₂ : RaiseLowerReachableS G τ σ') :
    RaiseLowerReachableS G σ σ' :=
  Relation.ReflTransGen.trans h₁ h₂

omit [Fintype V] [DecidableEq V] in
/-- Tail extension: `RaiseLowerReachableS` extended by a single
`RaiseLowerStepS`. -/
theorem RaiseLowerReachableS.tail' {G : SimpleGraph V}
    {σ τ σ' : V → Fin (N + 1)}
    (h₁ : RaiseLowerReachableS G σ τ)
    (h₂ : RaiseLowerStepS G τ σ') :
    RaiseLowerReachableS G σ σ' :=
  Relation.ReflTransGen.tail h₁ h₂

/-! ## Magnetization conservation -/

/-- A `RaiseLowerStepS` preserves the magnetization sum:
`magSumS σ' = magSumS σ`. The raise at one site (+1) is exactly
compensated by the lower at the other (−1). -/
theorem magSumS_eq_of_raiseLowerStepS {G : SimpleGraph V}
    {σ σ' : V → Fin (N + 1)} (h : RaiseLowerStepS G σ σ') :
    magSumS σ' = magSumS σ := by
  classical
  obtain ⟨x, y, _hadj, hsh, hagree⟩ := h
  have hxy : x ≠ y := by
    rcases hsh with ⟨hxr, hyl⟩ | ⟨hxl, hyr⟩
    · -- σ' x = σ x + 1, σ' y + 1 = σ y. Suppose x = y, then σ' x = σ x + 1
      -- AND σ' x + 1 = σ x. Contradiction.
      intro heq
      subst heq
      omega
    · intro heq
      subst heq
      omega
  unfold magSumS
  -- Split sum over {x, y} ∪ rest. Off-{x, y}-agree gives equal rest sums.
  have hsplit : ∀ τ : V → Fin (N + 1),
      (∑ k : V, (τ k).val) =
        (∑ k ∈ ((Finset.univ : Finset V) \ ({x, y} : Finset V)),
            (τ k).val) + ((τ x).val + (τ y).val) := by
    intro τ
    rw [← Finset.sum_sdiff (Finset.subset_univ ({x, y} : Finset V))]
    congr 1
    rw [Finset.sum_insert (Finset.notMem_singleton.mpr hxy),
      Finset.sum_singleton]
  rw [hsplit σ', hsplit σ]
  have hrest :
      ∑ k ∈ (Finset.univ : Finset V) \ ({x, y} : Finset V),
        (σ' k).val =
      ∑ k ∈ (Finset.univ : Finset V) \ ({x, y} : Finset V),
        (σ k).val := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
      not_or, Finset.mem_univ, true_and] at hk
    rw [hagree k hk.1 hk.2]
  rw [hrest]
  rcases hsh with ⟨hxr, hyl⟩ | ⟨hxl, hyr⟩
  · omega
  · omega

/-- A `RaiseLowerReachableS` preserves the magnetization sum:
iterated application of `magSumS_eq_of_raiseLowerStepS`. -/
theorem magSumS_eq_of_raiseLowerReachableS {G : SimpleGraph V}
    {σ σ' : V → Fin (N + 1)} (h : RaiseLowerReachableS G σ σ') :
    magSumS σ' = magSumS σ := by
  induction h with
  | refl => rfl
  | tail _hτ hτσ' ih => rw [magSumS_eq_of_raiseLowerStepS hτσ', ih]

/-- A `RaiseLowerReachableS` preserves the magnetization eigenvalue:
`magEigenvalueS σ' = magEigenvalueS σ`. -/
theorem magEigenvalueS_eq_of_raiseLowerReachableS {G : SimpleGraph V}
    {σ σ' : V → Fin (N + 1)} (h : RaiseLowerReachableS G σ σ') :
    magEigenvalueS σ' = magEigenvalueS σ := by
  unfold magEigenvalueS
  rw [magSumS_eq_of_raiseLowerReachableS h]

/-! ## Single-edge raise/lower step constructions -/

/-- The configuration obtained from `σ` by lowering at `x` (subtracting
1) and raising at `y` (adding 1). Well-defined Fin values when
`(σ y).val < (σ x).val ≤ N` (so the lowered `x` value `≥ 0` and the
raised `y` value `≤ N`). -/
noncomputable def raiseLowerSwapS {N : ℕ}
    (σ : V → Fin (N + 1)) (x y : V)
    (hxy_strict : (σ y).val < (σ x).val) : V → Fin (N + 1) :=
  Function.update (Function.update σ x
    ⟨(σ x).val - 1, by have := (σ x).isLt; omega⟩) y
    ⟨(σ y).val + 1, by have := (σ y).isLt; omega⟩

omit [Fintype V] in
/-- `raiseLowerSwapS σ x y` at site `x` equals `σ x − 1` (when `x ≠ y`). -/
theorem raiseLowerSwapS_apply_x {x y : V} (hxy : x ≠ y)
    {σ : V → Fin (N + 1)} (hxy_strict : (σ y).val < (σ x).val) :
    (raiseLowerSwapS σ x y hxy_strict x).val = (σ x).val - 1 := by
  unfold raiseLowerSwapS
  rw [Function.update_of_ne hxy, Function.update_self]

omit [Fintype V] in
/-- `raiseLowerSwapS σ x y` at site `y` equals `σ y + 1`. -/
theorem raiseLowerSwapS_apply_y {x y : V}
    {σ : V → Fin (N + 1)} (hxy_strict : (σ y).val < (σ x).val) :
    (raiseLowerSwapS σ x y hxy_strict y).val = (σ y).val + 1 := by
  unfold raiseLowerSwapS
  rw [Function.update_self]

omit [Fintype V] in
/-- `raiseLowerSwapS σ x y` agrees with `σ` off `{x, y}`. -/
theorem raiseLowerSwapS_apply_off {x y : V}
    {σ : V → Fin (N + 1)} (hxy_strict : (σ y).val < (σ x).val)
    {z : V} (hzx : z ≠ x) (hzy : z ≠ y) :
    raiseLowerSwapS σ x y hxy_strict z = σ z := by
  unfold raiseLowerSwapS
  rw [Function.update_of_ne hzy, Function.update_of_ne hzx]

omit [Fintype V] in
/-- For an adjacent pair `(x, y)` with `σ y < σ x`, the
`raiseLowerSwapS` lowering at `x` and raising at `y` is a
`RaiseLowerStepS`. -/
theorem raiseLowerStepS_of_adj_of_lt {G : SimpleGraph V}
    {x y : V} (hadj : G.Adj x y)
    {σ : V → Fin (N + 1)} (hxy_strict : (σ y).val < (σ x).val) :
    RaiseLowerStepS G σ (raiseLowerSwapS σ x y hxy_strict) := by
  have hxy : x ≠ y := fun heq => G.loopless.irrefl _ (heq ▸ hadj)
  refine ⟨x, y, hadj, Or.inr ⟨?_, ?_⟩, ?_⟩
  · -- (σ' x).val + 1 = (σ x).val
    rw [raiseLowerSwapS_apply_x hxy hxy_strict]
    omega
  · -- (σ y).val + 1 = (σ' y).val
    rw [raiseLowerSwapS_apply_y hxy_strict]
  · intro k hkx hky
    exact raiseLowerSwapS_apply_off hxy_strict hkx hky

/-! ## Symmetry of the step relation -/

omit [Fintype V] [DecidableEq V] in
/-- `RaiseLowerStepS` is symmetric: if `σ ↦ σ'` is a raise/lower step,
then `σ' ↦ σ` is also a raise/lower step (along the same edge,
swapping the raise/lower roles). -/
theorem RaiseLowerStepS.symm {G : SimpleGraph V}
    {σ σ' : V → Fin (N + 1)} (h : RaiseLowerStepS G σ σ') :
    RaiseLowerStepS G σ' σ := by
  obtain ⟨x, y, hadj, hsh, hagree⟩ := h
  refine ⟨x, y, hadj, ?_, fun k hkx hky => (hagree k hkx hky).symm⟩
  rcases hsh with ⟨hxr, hyl⟩ | ⟨hxl, hyr⟩
  · -- Original σ → σ' was "raise x, lower y". Reverse σ' → σ is "lower x, raise y".
    -- Lower x from σ' to σ: (σ x).val + 1 = (σ' x).val ✓ matches hxr.
    -- Raise y from σ' to σ: (σ' y).val + 1 = (σ y).val ✓ matches hyl.
    exact Or.inr ⟨hxr, hyl⟩
  · -- Original σ → σ' was "lower x, raise y". Reverse σ' → σ is "raise x, lower y".
    -- Raise x from σ' to σ: (σ' x).val + 1 = (σ x).val ✓ matches hxl.
    -- Lower y from σ' to σ: (σ y).val + 1 = (σ' y).val ✓ matches hyr.
    exact Or.inl ⟨hxl, hyr⟩

omit [Fintype V] [DecidableEq V] in
/-- `RaiseLowerReachableS` is symmetric: if `σ` reaches `σ'`, then
`σ'` reaches `σ`. (Iterates `RaiseLowerStepS.symm` along the chain.) -/
theorem RaiseLowerReachableS.symm {G : SimpleGraph V}
    {σ σ' : V → Fin (N + 1)} (h : RaiseLowerReachableS G σ σ') :
    RaiseLowerReachableS G σ' σ := by
  induction h with
  | refl => exact RaiseLowerReachableS.refl G _
  | tail _h₁ h₂ ih =>
    exact (RaiseLowerReachableS.single h₂.symm).trans ih

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
