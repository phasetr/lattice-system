import LatticeSystem.Quantum.MarshallLiebMattis.MarshallSignTrick
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option linter.unusedSectionVars false

/-!
# Connectivity of magnetization-zero configurations
(Tasaki §2.5, p. 41–42, "Property (iii)" in the proof of Theorem 2.2)

The third property needed in Tasaki's Perron–Frobenius proof of the
Marshall–Lieb–Mattis theorem (Theorem 2.2, §2.5 p. 39) is

  **(iii)** any two configurations `σ ≠ σ'` with the same total
  magnetization are connected by a sequence of nonvanishing matrix
  elements of `⟨Ψ̃^σ|Ĥ|Ψ̃^σ'⟩`, in the Perron–Frobenius sense.

For the spin-1/2 antiferromagnetic Heisenberg Hamiltonian on a
**connected** graph `G : SimpleGraph Λ`, this reduces to the purely
graph-theoretic statement that the relation **"σ ↦ basisSwap σ x y for
some `G`-edge `(x, y)` with antiparallel σ_x ≠ σ_y"** has reflexive
transitive closure that contains every pair `(σ, σ')` with equal
magnetization.

This module formalises the combinatorial content of Property (iii):

* `SwapStep G σ σ'` — `σ'` is obtained from `σ` by swapping
  antiparallel spins along a single `G`-edge.
* `SwapReachable G` — the reflexive transitive closure of `SwapStep G`.
* `swapReachable_of_walk_of_ne` — for any `G`-walk from `x` to `y`
  with `σ x ≠ σ y`, `SwapReachable G σ (basisSwap σ x y)`. The proof
  follows Tasaki p. 41 by induction on the walk, decomposing into
  three single-edge swaps with case analysis on `σ z` at the
  intermediate vertex.

Key applications (used in PR α-5 to invoke Perron–Frobenius):

* For any `σ, σ'` with `σ x ≠ σ y` and `G.Reachable x y`, we have
  `SwapReachable G σ (basisSwap σ x y)`. Combined with iteration on
  the magnetization-difference Σ_x |σ_x − σ'_x|, this gives
  irreducibility of the dressed Heisenberg matrix on the
  magnetisation-`M` subspace.

References:

- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5, pp. 41–42 (Property (iii) — "Proof of
  Property (iii)" in the proof of Theorem 2.2).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Single-step swap relation -/

/-- One-step swap relation along a `G`-edge: `σ' = basisSwap σ x y`
for some `G`-adjacent `(x, y)` with `σ x ≠ σ y`. -/
def SwapStep (G : SimpleGraph Λ) (σ σ' : Λ → Fin 2) : Prop :=
  ∃ x y : Λ, G.Adj x y ∧ σ x ≠ σ y ∧ σ' = basisSwap σ x y

/-- Reflexive transitive closure of `SwapStep G`: the smallest
relation containing `SwapStep G` that is reflexive and transitive. -/
def SwapReachable (G : SimpleGraph Λ) : (Λ → Fin 2) → (Λ → Fin 2) → Prop :=
  Relation.ReflTransGen (SwapStep G)

theorem SwapReachable.refl (G : SimpleGraph Λ) (σ : Λ → Fin 2) :
    SwapReachable G σ σ :=
  Relation.ReflTransGen.refl

theorem SwapReachable.single (G : SimpleGraph Λ) {σ σ' : Λ → Fin 2}
    (h : SwapStep G σ σ') : SwapReachable G σ σ' :=
  Relation.ReflTransGen.single h

theorem SwapReachable.trans {G : SimpleGraph Λ} {σ τ σ' : Λ → Fin 2}
    (h₁ : SwapReachable G σ τ) (h₂ : SwapReachable G τ σ') :
    SwapReachable G σ σ' :=
  Relation.ReflTransGen.trans h₁ h₂

theorem SwapReachable.tail' {G : SimpleGraph Λ} {σ τ σ' : Λ → Fin 2}
    (h₁ : SwapReachable G σ τ) (h₂ : SwapStep G τ σ') :
    SwapReachable G σ σ' :=
  Relation.ReflTransGen.tail h₁ h₂

/-- Single-edge case: a direct `SwapStep` is a `SwapReachable`. -/
theorem SwapReachable.of_step {G : SimpleGraph Λ}
    {σ σ' : Λ → Fin 2} (h : SwapStep G σ σ') :
    SwapReachable G σ σ' :=
  SwapReachable.single G h

/-! ## Walk-based connectivity -/

/-- Helper: `basisSwap` agrees with the underlying configuration off
`{x, y}`. -/
private theorem basisSwap_off_xy {x y : Λ} (σ : Λ → Fin 2)
    {z : Λ} (hzx : z ≠ x) (hzy : z ≠ y) :
    basisSwap σ x y z = σ z := by
  unfold basisSwap
  rw [Function.update_of_ne hzy, Function.update_of_ne hzx]

/-- Helper: `basisSwap σ x y` at site `x` equals `σ y`. -/
private theorem basisSwap_at_x {x y : Λ} (hxy : x ≠ y) (σ : Λ → Fin 2) :
    basisSwap σ x y x = σ y := by
  unfold basisSwap
  rw [Function.update_of_ne hxy, Function.update_self]

/-- Helper: `basisSwap σ x y` at site `y` equals `σ x`. -/
private theorem basisSwap_at_y {x y : Λ} (σ : Λ → Fin 2) :
    basisSwap σ x y y = σ x := by
  unfold basisSwap
  rw [Function.update_self]

/-- For Fin 2, `s ≠ t` and `s ≠ u` implies `t = u`. -/
private theorem fin2_eq_of_both_ne {s t u : Fin 2} (h₁ : s ≠ t) (h₂ : s ≠ u) :
    t = u := by
  fin_cases s <;> fin_cases t <;> fin_cases u <;>
    first | rfl | (exact absurd rfl h₁) | (exact absurd rfl h₂)

/-- **Key lemma (Tasaki p. 41).** If `G.Walk x y` exists and
`σ x ≠ σ y`, then `σ` and `basisSwap σ x y` are `SwapReachable`.

Proof: induction on the walk `x → ... → y`. The base case `nil` has
`x = y` contradicting `σ x ≠ σ y`. For the cons case `x → v → y'`
(walk of positive length):

* If `v = y'` (walk has length 1): direct single-edge swap step.
* Otherwise, two cases on `σ v`:
  - **Case A** `σ v ≠ σ x` (so `σ v = σ y`): swap along the edge
    `(x, v)` first, then apply the induction hypothesis on the
    remaining walk `v → y'`.
  - **Case B** `σ v = σ x`: apply the induction hypothesis on the
    walk `v → y'` first, then swap along the edge `(x, v)`. -/
theorem swapReachable_of_walk_of_ne
    {G : SimpleGraph Λ} {x y : Λ} (w : G.Walk x y)
    {σ : Λ → Fin 2} (h : σ x ≠ σ y) :
    SwapReachable G σ (basisSwap σ x y) := by
  induction w generalizing σ with
  | nil =>
    -- x = y, contradicting h
    exact absurd rfl h
  | @cons u v y' hadj p ih =>
    -- u → v → ... → y'.  hadj : G.Adj u v.  p : G.Walk v y'.
    -- ih : ∀ σ', σ' v ≠ σ' y' → SwapReachable G σ' (basisSwap σ' v y')
    -- Goal: SwapReachable G σ (basisSwap σ u y') given σ u ≠ σ y'.
    have huv : u ≠ v := fun heq => G.loopless.irrefl _ (heq ▸ hadj)
    by_cases hvy : v = y'
    · -- Walk has length 1: direct swap along (u, v) = (u, y').
      subst hvy
      exact SwapReachable.of_step ⟨u, v, hadj, h, rfl⟩
    · -- Walk has length ≥ 2: case analysis on σ v.
      by_cases hsuv : σ v = σ u
      · -- Case B: σ v = σ u. So σ v ≠ σ y'.
        have hvy_ne : σ v ≠ σ y' := hsuv ▸ h
        -- Step 1: IH on σ along walk p, swapping (v, y').
        have hreach1 : SwapReachable G σ (basisSwap σ v y') := ih hvy_ne
        -- Let σ₁ := basisSwap σ v y'.
        have huy : u ≠ y' := fun heq => h (heq ▸ rfl)
        have hσ₁_u : (basisSwap σ v y') u = σ u :=
          basisSwap_off_xy σ huv huy
        have hσ₁_v : (basisSwap σ v y') v = σ y' := basisSwap_at_x hvy σ
        have hσ₁_y : (basisSwap σ v y') y' = σ v := basisSwap_at_y σ
        have hσ₁_ne : (basisSwap σ v y') u ≠ (basisSwap σ v y') v := by
          rw [hσ₁_u, hσ₁_v]; exact h
        have hreach2 : SwapStep G (basisSwap σ v y')
            (basisSwap (basisSwap σ v y') u v) :=
          ⟨u, v, hadj, hσ₁_ne, rfl⟩
        have hcomb : SwapReachable G σ (basisSwap (basisSwap σ v y') u v) :=
          hreach1.tail hreach2
        -- Show basisSwap σ₁ u v = basisSwap σ u y'.
        have hgoal :
            basisSwap (basisSwap σ v y') u v = basisSwap σ u y' := by
          funext z
          by_cases hzu : z = u
          · rw [hzu]
            rw [basisSwap_at_x huv (basisSwap σ v y'), hσ₁_v]
            rw [basisSwap_at_x huy σ]
          · by_cases hzv : z = v
            · rw [hzv]
              rw [basisSwap_at_y (basisSwap σ v y'), hσ₁_u]
              rw [basisSwap_off_xy σ (Ne.symm huv) hvy]
              exact hsuv.symm
            · by_cases hzy' : z = y'
              · rw [hzy']
                rw [basisSwap_off_xy (basisSwap σ v y')
                      (Ne.symm huy) (Ne.symm hvy)]
                rw [hσ₁_y, basisSwap_at_y σ, hsuv]
              · rw [basisSwap_off_xy (basisSwap σ v y') hzu hzv]
                rw [basisSwap_off_xy σ hzu hzy']
                rw [basisSwap_off_xy σ hzv hzy']
        rw [← hgoal]; exact hcomb
      · -- Case A: σ v ≠ σ u. So σ v = σ y' (Fin 2 has only 2 values).
        have hvy_eq : σ v = σ y' := fin2_eq_of_both_ne (Ne.symm hsuv) h
        -- Step 1: swap (u, v) on σ. σ u ≠ σ v (= σ y').
        have huv_ne_σ : σ u ≠ σ v := by
          intro heq; exact hsuv heq.symm
        have hstep1 : SwapStep G σ (basisSwap σ u v) :=
          ⟨u, v, hadj, huv_ne_σ, rfl⟩
        -- Let σ₁ := basisSwap σ u v.
        have huy : u ≠ y' := fun heq => h (heq ▸ rfl)
        have hσ₁_v : (basisSwap σ u v) v = σ u := basisSwap_at_y σ
        have hσ₁_y : (basisSwap σ u v) y' = σ y' :=
          basisSwap_off_xy σ (Ne.symm huy) (Ne.symm hvy)
        have hσ₁_u : (basisSwap σ u v) u = σ v := basisSwap_at_x huv σ
        have hσ₁_ne : (basisSwap σ u v) v ≠ (basisSwap σ u v) y' := by
          rw [hσ₁_v, hσ₁_y]; exact h
        have hreach2 : SwapReachable G (basisSwap σ u v)
            (basisSwap (basisSwap σ u v) v y') := ih hσ₁_ne
        have hcomb : SwapReachable G σ
            (basisSwap (basisSwap σ u v) v y') :=
          (SwapReachable.of_step hstep1).trans hreach2
        -- Show basisSwap σ₁ v y' = basisSwap σ u y'.
        have hgoal :
            basisSwap (basisSwap σ u v) v y' = basisSwap σ u y' := by
          funext z
          by_cases hzv : z = v
          · rw [hzv]
            rw [basisSwap_at_x hvy (basisSwap σ u v), hσ₁_y]
            rw [basisSwap_off_xy σ (Ne.symm huv) hvy]
            exact hvy_eq.symm
          · by_cases hzy' : z = y'
            · rw [hzy']
              rw [basisSwap_at_y (basisSwap σ u v), hσ₁_v]
              rw [basisSwap_at_y σ]
            · by_cases hzu : z = u
              · rw [hzu]
                rw [basisSwap_off_xy (basisSwap σ u v) huv huy]
                rw [hσ₁_u, basisSwap_at_x huy σ, hvy_eq]
              · rw [basisSwap_off_xy (basisSwap σ u v) hzv hzy']
                rw [basisSwap_off_xy σ hzu hzy']
                rw [basisSwap_off_xy σ hzu hzv]
        rw [← hgoal]; exact hcomb

/-- **Property (iii) ingredient.** For a connected graph `G`, any
two distinct vertices `x, y ∈ Λ` with `σ x ≠ σ y` admit a swap
chain reaching `basisSwap σ x y`. -/
theorem swapReachable_of_reachable_of_ne
    {G : SimpleGraph Λ} {x y : Λ} (hxy_reach : G.Reachable x y)
    {σ : Λ → Fin 2} (h : σ x ≠ σ y) :
    SwapReachable G σ (basisSwap σ x y) := by
  obtain ⟨w⟩ := hxy_reach
  exact swapReachable_of_walk_of_ne w h

/-- For a preconnected graph, the swap-reachability holds for any
`x, y` with `σ x ≠ σ y`. -/
theorem swapReachable_of_preconnected_of_ne
    {G : SimpleGraph Λ} (hG : G.Preconnected)
    (x y : Λ) {σ : Λ → Fin 2} (h : σ x ≠ σ y) :
    SwapReachable G σ (basisSwap σ x y) :=
  swapReachable_of_reachable_of_ne (hG x y) h

end LatticeSystem.Quantum
