import LatticeSystem.Quantum.MarshallLiebMattis.SpinDotSwapEntry

set_option linter.unusedSectionVars false

/-!
# Off-bond non-equality for `basisSwap`-related configurations

This module proves the key combinatorial helper for analyzing the
Heisenberg matrix entry `(heisenbergHamiltonian J) σ (basisSwap σ x y)`:

  **Lemma.** For `x ≠ y`, `σ_x ≠ σ_y`, and any `u ≠ v` with
  `{u, v} ≠ {x, y}` (as unordered pairs), we have
  `basisSwap (basisSwap σ x y) u v ≠ σ`.

Geometric content: `σ` and `σ' = basisSwap σ x y` differ at exactly
the two sites `x` and `y` (since `σ_x ≠ σ_y`). For
`basisSwap σ' u v` to equal `σ`, the swap of `σ'` at `(u, v)` must
match the swap of `σ` at `(x, y)`. This forces the difference sets
to coincide, i.e., `{u, v} = {x, y}`.

This is the building block for the off-bond vanishing argument
needed in subsequent PRs to compute the explicit Heisenberg matrix
entry value `(J x y + J y x) / 2` and ultimately conclude
Perron–Frobenius irreducibility of the dressed matrix on `H_0`.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5, p. 41.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- For `σ' = basisSwap σ x y` (with `x ≠ y`, `σ_x ≠ σ_y`) and any
`u ≠ v`, if `{u, v} ≠ {x, y}` (encoded as the negation of "ordered
match" with both orientations), then `basisSwap σ' u v ≠ σ`.

**Proof.** Suppose for contradiction `σ = basisSwap σ' u v`. Then
`σ` and `σ'` differ exactly at the swap sites of the antiparallel
pair, which (after some analysis) forces `{u, v} = {x, y}`.

Site analysis: at site `x`, `σ x ≠ σ' x` (since `σ' x = σ y ≠ σ x`).
For `σ = basisSwap σ' u v`, we have `σ z = (basisSwap σ' u v) z`,
which equals `σ' z` for `z ∉ {u, v}`. So if `x ∉ {u, v}`, then
`σ x = σ' x`, contradicting `σ x ≠ σ' x`. Hence `x ∈ {u, v}`.
Similarly `y ∈ {u, v}`. With `x ≠ y` and `u ≠ v`, this forces
`{u, v} = {x, y}` (as either `(u, v) = (x, y)` or `(u, v) = (y, x)`),
contradicting the bond hypothesis. -/
theorem basisSwap_basisSwap_ne_self_of_ne_bond
    {x y u v : Λ} (hxy : x ≠ y)
    {σ : Λ → Fin 2} (h : σ x ≠ σ y)
    (hbond : ¬ ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) :
    basisSwap (basisSwap σ x y) u v ≠ σ := by
  intro heq
  -- Site x: σ x ≠ σ' x (= (basisSwap σ x y) x = σ y), so x ∈ {u, v}.
  have hσ'_x : (basisSwap σ x y) x = σ y := by
    unfold basisSwap
    rw [Function.update_of_ne hxy, Function.update_self]
  have hx_diff : (basisSwap σ x y) x ≠ σ x := by rw [hσ'_x]; exact h.symm
  have hxuv : x = u ∨ x = v := by
    by_contra hxnotuv
    push Not at hxnotuv
    -- x ∉ {u, v}, so basisSwap (basisSwap σ x y) u v at x = (basisSwap σ x y) at x.
    have hbsx : basisSwap (basisSwap σ x y) u v x = (basisSwap σ x y) x := by
      unfold basisSwap
      rw [Function.update_of_ne hxnotuv.2, Function.update_of_ne hxnotuv.1]
    have := congrFun heq x
    rw [hbsx] at this
    exact hx_diff this
  -- Site y: similarly y ∈ {u, v}.
  have hσ'_y : (basisSwap σ x y) y = σ x := by
    unfold basisSwap; rw [Function.update_self]
  have hy_diff : (basisSwap σ x y) y ≠ σ y := by rw [hσ'_y]; exact h
  have hyuv : y = u ∨ y = v := by
    by_contra hynotuv
    push Not at hynotuv
    have hbsy : basisSwap (basisSwap σ x y) u v y = (basisSwap σ x y) y := by
      unfold basisSwap
      rw [Function.update_of_ne hynotuv.2, Function.update_of_ne hynotuv.1]
    have := congrFun heq y
    rw [hbsy] at this
    exact hy_diff this
  -- Now {x, y} ⊆ {u, v} with x ≠ y, u ≠ v ⇒ {u, v} = {x, y}.
  rcases hxuv with hxu | hxv
  · -- x = u
    rcases hyuv with hyu | hyv
    · exact hxy (hxu.trans hyu.symm)
    · -- (u, v) = (x, y)
      apply hbond; left; exact ⟨hxu.symm, hyv.symm⟩
  · -- x = v
    rcases hyuv with hyu | hyv
    · -- (u, v) = (y, x)
      apply hbond; right; exact ⟨hyu.symm, hxv.symm⟩
    · exact hxy (hxv.trans hyv.symm)

end LatticeSystem.Quantum
