import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Logic.Relation

/-!
# Configuration combinatorics for spin-`S` systems

Matrix-free layer underlying the spin-`S` connectivity arguments.  A
configuration of a spin-`S` system (`N = 2S`) on a site type `Λ` is a map
`σ : Λ → Fin (N + 1)`, and the only data used by the connectivity
arguments are its magnetization index sum and the raise/lower moves along
the edges of a graph:

* `magSumS σ = ∑_x (σ x).val` — the combinatorial magnetization quantum
  number.  For spin-1/2 (`N = 1`) it is the down-spin count.
* `RaiseLowerStepS G σ σ'` — `σ'` differs from `σ` only at two
  `G`-adjacent sites, one raised by `1` and the other lowered by `1`.
* `RaiseLowerReachableS G` — its reflexive transitive closure, together
  with symmetry and conservation of `magSumS`.

This module depends on `Mathlib` alone, so that the configuration-distance
and reachability development resting on it stays independent of the
spin-`S` matrix layer.  The matrix-level counterparts — the eigenvalue
`magEigenvalueS`, the magnetization subspaces, and the `spinSDot` matrix
entries realised by a raise/lower step — live in
`LatticeSystem/Quantum/SpinS/Magnetization.lean` and
`LatticeSystem/Quantum/SpinS/RaiseLower.lean`.
-/

namespace LatticeSystem.Quantum

section MagSum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The magnetization-index sum of a spin-`S` configuration. -/
def magSumS (σ : Λ → Fin (N + 1)) : ℕ :=
  ∑ x : Λ, (σ x).val

omit [DecidableEq Λ] in
/-- Definitional unfolding of `magSumS`. -/
theorem magSumS_def (σ : Λ → Fin (N + 1)) :
    magSumS σ = ∑ x : Λ, (σ x).val := rfl

omit [DecidableEq Λ] in
/-- `magSumS σ ≤ |Λ| · N`. -/
theorem magSumS_le (σ : Λ → Fin (N + 1)) :
    magSumS σ ≤ Fintype.card Λ * N := by
  unfold magSumS
  calc ∑ x : Λ, (σ x).val
      ≤ ∑ _ : Λ, N := by
        refine Finset.sum_le_sum ?_
        intro x _
        have := (σ x).isLt
        omega
    _ = Fintype.card Λ * N := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

omit [DecidableEq Λ] in
/-- `magSumS σ = |Λ| · N` iff `σ x = Fin.last N` for every `x : Λ`
(the lowest-weight all-`Fin.last N` config achieves the maximum). -/
theorem magSumS_eq_max_iff (σ : Λ → Fin (N + 1)) :
    magSumS σ = Fintype.card Λ * N ↔ ∀ x : Λ, σ x = Fin.last N := by
  unfold magSumS
  constructor
  · intro h x
    -- If `magSumS σ = |Λ| · N`, then each `(σ x).val = N` (max).
    have hle : ∀ y ∈ (Finset.univ : Finset Λ), (σ y).val ≤ N :=
      fun y _ => by have := (σ y).isLt; omega
    have hsum_eq : ∀ y ∈ (Finset.univ : Finset Λ), (σ y).val = N := by
      apply (Finset.sum_eq_sum_iff_of_le hle).mp
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      exact h
    apply Fin.ext
    rw [hsum_eq x (Finset.mem_univ x)]
    rfl
  · intro h
    have heq : ∀ x : Λ, (σ x).val = N := fun x => by rw [h x]; rfl
    rw [Finset.sum_congr rfl (fun x _ => heq x)]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

omit [DecidableEq Λ] in
/-- `magSumS` of a constant configuration `(fun _ => s)` is `|Λ| · s.val`. -/
theorem magSumS_const (s : Fin (N + 1)) :
    magSumS (fun _ : Λ => s) = Fintype.card Λ * s.val := by
  unfold magSumS
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

omit [DecidableEq Λ] in
/-- `magSumS (fun _ => 0) = 0`. -/
theorem magSumS_const_zero :
    magSumS (fun _ : Λ => (0 : Fin (N + 1))) = 0 := by
  rw [magSumS_const]
  simp

end MagSum

section RaiseLowerStep

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

omit [DecidableEq V] in
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

omit [DecidableEq V] in
/-- A `RaiseLowerReachableS` preserves the magnetization sum:
iterated application of `magSumS_eq_of_raiseLowerStepS`. -/
theorem magSumS_eq_of_raiseLowerReachableS {G : SimpleGraph V}
    {σ σ' : V → Fin (N + 1)} (h : RaiseLowerReachableS G σ σ') :
    magSumS σ' = magSumS σ := by
  induction h with
  | refl => rfl
  | tail _hτ hτσ' ih => rw [magSumS_eq_of_raiseLowerStepS hτσ', ih]

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

end RaiseLowerStep

end LatticeSystem.Quantum
