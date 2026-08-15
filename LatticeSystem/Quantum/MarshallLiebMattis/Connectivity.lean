import LatticeSystem.Quantum.MarshallLiebMattis.MarshallSignTrick
import LatticeSystem.Quantum.SpinS.ConnectedRaiseLower
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

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
* `swapStep_of_raiseLowerStepS` — a spin-`S` raise/lower step at `N = 1`
  is a bond swap, the bridge through which the spin-`1/2` reachability
  results are obtained from the spin-`S` development.
* `transportOne_eq_basisSwap` — the configuration-level half of that
  bridge: at `N = 1` the single-quantum transport is the bond swap.
* `swapReachable_of_walk_of_ne` — for any `G`-walk from `x` to `y`
  with `σ x ≠ σ y`, `SwapReachable G σ (basisSwap σ x y)`. This is
  Tasaki p. 41, read off the spin-`S` walk transport
  `raiseLowerReachableS_transportOne_of_walk` at `N = 1`: the bond swap
  moves the single quantum sitting at the endpoint with value `1` to the
  endpoint with value `0`, and Tasaki's three-edge decomposition at an
  intermediate vertex is the `N = 1` case of the overflow-free routing
  performed there.

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

omit [Fintype Λ] in
theorem SwapReachable.refl (G : SimpleGraph Λ) (σ : Λ → Fin 2) :
    SwapReachable G σ σ :=
  Relation.ReflTransGen.refl

omit [Fintype Λ] in
theorem SwapReachable.single (G : SimpleGraph Λ) {σ σ' : Λ → Fin 2}
    (h : SwapStep G σ σ') : SwapReachable G σ σ' :=
  Relation.ReflTransGen.single h

omit [Fintype Λ] in
theorem SwapReachable.trans {G : SimpleGraph Λ} {σ τ σ' : Λ → Fin 2}
    (h₁ : SwapReachable G σ τ) (h₂ : SwapReachable G τ σ') :
    SwapReachable G σ σ' :=
  Relation.ReflTransGen.trans h₁ h₂

omit [Fintype Λ] in
theorem SwapReachable.tail' {G : SimpleGraph Λ} {σ τ σ' : Λ → Fin 2}
    (h₁ : SwapReachable G σ τ) (h₂ : SwapStep G τ σ') :
    SwapReachable G σ σ' :=
  Relation.ReflTransGen.tail h₁ h₂

omit [Fintype Λ] in
/-- Single-edge case: a direct `SwapStep` is a `SwapReachable`. -/
theorem SwapReachable.of_step {G : SimpleGraph Λ}
    {σ σ' : Λ → Fin 2} (h : SwapStep G σ σ') :
    SwapReachable G σ σ' :=
  SwapReachable.single G h

/-! ## Bridges from the spin-`S` development at `N = 1` -/

omit [Fintype Λ] in
/-- At `N = 1` a spin-`S` raise/lower step along a `G`-edge is a bond swap:
raising one endpoint and lowering the other within `Fin 2` forces the two
endpoint values to be `0` and `1` in some order, so the resulting
configuration is `basisSwap σ x y`. This is the specialisation that lets the
spin-`1/2` reachability statements be read off the spin-`S` development. -/
theorem swapStep_of_raiseLowerStepS {G : SimpleGraph Λ} {σ σ' : Λ → Fin 2}
    (h : RaiseLowerStepS (N := 1) G σ σ') : SwapStep G σ σ' := by
  obtain ⟨x, y, hadj, hstep, hoff⟩ := h
  have hxy : x ≠ y := fun heq => G.loopless.irrefl _ (heq ▸ hadj)
  have hx := (σ x).isLt
  have hy := (σ y).isLt
  have hx' := (σ' x).isLt
  have hy' := (σ' y).isLt
  refine ⟨x, y, hadj, ?_, ?_⟩
  · intro heq
    have hval : (σ x).val = (σ y).val := by rw [heq]
    rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · funext z
    by_cases hzx : z = x
    · subst hzx
      unfold basisSwap
      rw [Function.update_of_ne hxy, Function.update_self]
      apply Fin.ext
      rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · by_cases hzy : z = y
      · subst hzy
        unfold basisSwap
        rw [Function.update_self]
        apply Fin.ext
        rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      · rw [hoff z hzx hzy]
        unfold basisSwap
        rw [Function.update_of_ne hzy, Function.update_of_ne hzx]

omit [Fintype Λ] in
/-- At `N = 1` the single-quantum transport `transportOne σ x y` (lower `x`,
raise `y`) is the bond swap `basisSwap σ x y`, under the endpoint values
`σ x = 1` and `σ y = 0` that make the transport possible. Together with
`swapStep_of_raiseLowerStepS` this identifies the spin-`S` transport moves at
`N = 1` with the spin-`1/2` bond swaps, configuration by configuration. -/
theorem transportOne_eq_basisSwap {σ : Λ → Fin 2} {x y : Λ} (hxy : x ≠ y)
    (hx : σ x = 1) (hy : σ y = 0) :
    transportOne (N := 1) σ x y = basisSwap σ x y := by
  have hyroom : (σ y).val < 1 := by rw [hy]; decide
  funext z
  apply Fin.ext
  by_cases hzx : z = x
  · subst hzx
    rw [transportOne_apply_x hxy]
    unfold basisSwap
    rw [Function.update_of_ne hxy, Function.update_self, hx, hy]
    decide
  · by_cases hzy : z = y
    · subst hzy
      rw [transportOne_apply_y hyroom]
      unfold basisSwap
      rw [Function.update_self, hx, hy]
      decide
    · rw [transportOne_apply_off hzx hzy]
      unfold basisSwap
      rw [Function.update_of_ne hzy, Function.update_of_ne hzx]

/-! ## Walk-based connectivity -/

omit [Fintype Λ] in
/-- **Key lemma (Tasaki p. 41).** If `G.Walk x y` exists and
`σ x ≠ σ y`, then `σ` and `basisSwap σ x y` are `SwapReachable`.

Proof: the two endpoint values are `0` and `1` in one of the two orders, so
the bond swap transports the single quantum sitting at the endpoint with
value `1` to the endpoint with value `0` (`transportOne_eq_basisSwap`). The
spin-`S` walk transport `raiseLowerReachableS_transportOne_of_walk` at
`N = 1`, run along `w` or along its reverse according to that order, yields a
chain of raise/lower steps, each of which is a bond swap
(`swapStep_of_raiseLowerStepS`). Tasaki's decomposition into three
single-edge swaps at an intermediate vertex is the `N = 1` case of the
overflow-free routing performed inside that transport. -/
theorem swapReachable_of_walk_of_ne
    {G : SimpleGraph Λ} {x y : Λ} (w : G.Walk x y)
    {σ : Λ → Fin 2} (h : σ x ≠ σ y) :
    SwapReachable G σ (basisSwap σ x y) := by
  have hxy : x ≠ y := fun heq => h (by rw [heq])
  have hvals : ∀ s : Fin 2, s = 0 ∨ s = 1 := by decide
  rcases hvals (σ x) with hx0 | hx1
  · -- `σ x = 0`, `σ y = 1`: transport the quantum from `y` to `x`.
    have hy1 : σ y = 1 := by
      rcases hvals (σ y) with hy0 | hy1
      · exact absurd (hx0.trans hy0.symm) h
      · exact hy1
    have hreach := raiseLowerReachableS_transportOne_of_walk (N := 1)
      w.reverse (σ := σ) hxy.symm (by rw [hy1]; decide) (by rw [hx0]; decide)
    rw [transportOne_eq_basisSwap hxy.symm hy1 hx0,
      ← basisSwap_comm σ x y] at hreach
    exact Relation.ReflTransGen.mono
      (fun _ _ hstep => swapStep_of_raiseLowerStepS hstep) hreach
  · -- `σ x = 1`, `σ y = 0`: transport the quantum from `x` to `y`.
    have hy0 : σ y = 0 := by
      rcases hvals (σ y) with hy0 | hy1
      · exact hy0
      · exact absurd (hx1.trans hy1.symm) h
    have hreach := raiseLowerReachableS_transportOne_of_walk (N := 1)
      w (σ := σ) hxy (by rw [hx1]; decide) (by rw [hy0]; decide)
    rw [transportOne_eq_basisSwap hxy hx1 hy0] at hreach
    exact Relation.ReflTransGen.mono
      (fun _ _ hstep => swapStep_of_raiseLowerStepS hstep) hreach

omit [Fintype Λ] in
/-- **Property (iii) ingredient.** For a connected graph `G`, any
two distinct vertices `x, y ∈ Λ` with `σ x ≠ σ y` admit a swap
chain reaching `basisSwap σ x y`. -/
theorem swapReachable_of_reachable_of_ne
    {G : SimpleGraph Λ} {x y : Λ} (hxy_reach : G.Reachable x y)
    {σ : Λ → Fin 2} (h : σ x ≠ σ y) :
    SwapReachable G σ (basisSwap σ x y) := by
  obtain ⟨w⟩ := hxy_reach
  exact swapReachable_of_walk_of_ne w h

omit [Fintype Λ] in
/-- For a preconnected graph, the swap-reachability holds for any
`x, y` with `σ x ≠ σ y`. -/
theorem swapReachable_of_preconnected_of_ne
    {G : SimpleGraph Λ} (hG : G.Preconnected)
    (x y : Λ) {σ : Λ → Fin 2} (h : σ x ≠ σ y) :
    SwapReachable G σ (basisSwap σ x y) :=
  swapReachable_of_reachable_of_ne (hG x y) h

end LatticeSystem.Quantum
