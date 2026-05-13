import LatticeSystem.Quantum.SpinS.SaturatedLadderJointEigenspace

/-!
# The saturated-ferromagnet ladder span has dimension `2m_max + 1`

For `[Nonempty V]`, the linear span of the ladder family
`ladderIterateUp : Fin (|V|·N + 1) → ((V → Fin (N+1)) → ℂ)` has
`Module.finrank ℂ` exactly `|V|·N + 1 = 2m_max + 1`. Furthermore,
this span is contained in the joint
`(H, (Ŝ_{tot})²)`-eigenspace at the saturated-ferromagnet
eigenvalues.

The dimension equality combines linear independence (PR #896) with
mathlib's `finrank_span_eq_card`. The containment in the joint
eigenspace combines the per-element membership (PR #903) with
`Submodule.span_le`.

This identifies the saturated-ferromagnet ground-state ladder span
as a concrete `(2m_max + 1)`-dimensional subspace of the joint
Heisenberg + Casimir eigenspace, the spin-`S` analog of Tasaki
§2.4 (2.4.10) and §2.4 final structural identification.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

open Submodule

/-- **Span dimension equality**: for `[Nonempty V]`, the linear
span of the saturated-ferromagnet ladder family has
`Module.finrank ℂ = |V|·N + 1 = 2m_max + 1`.

Direct application of `finrank_span_eq_card` to the LI family
`ladderIterateUp` (PR #896). -/
theorem ladderIterateUp_span_finrank_eq_succ_card_mul_N [Nonempty V] :
    Module.finrank ℂ
        (Submodule.span ℂ (Set.range (ladderIterateUp V N))) =
      Fintype.card V * N + 1 := by
  have h := finrank_span_eq_card
    (R := ℂ)
    (b := ladderIterateUp V N)
    ladderIterateUp_linearIndependent
  simpa using h

/-- The saturated-ferromagnet ladder span is contained in the
joint `(H, (Ŝ_{tot})²)`-eigenspace at the saturated-ferromagnet
eigenvalues. Combines per-element membership (PR #903) with
`Submodule.span_le`. -/
theorem ladderIterateUp_span_le_saturatedFerromagnetJointEigenspace
    [Nonempty V] (J : V → V → ℂ) :
    Submodule.span ℂ (Set.range (ladderIterateUp V N)) ≤
      saturatedFerromagnetJointEigenspace (V := V) J N := by
  apply Submodule.span_le.mpr
  rintro v ⟨k, rfl⟩
  exact ladderIterateUp_mem_saturatedFerromagnetJointEigenspace J k

/-- **`Module.finrank ℂ (saturatedFerromagnetJointEigenspace J N) =
|V|·N + 1`** — the operator-level dimension formula for the
saturated-ferromagnet ground-state subspace in Tasaki §2.4
Theorem 2.1.

Direct corollary of the Theorem 2.1 closure (PR #2768): the joint
eigenspace equals the linear span of the ladder iterates, whose
finrank is `|V|·N + 1 = 2m_max + 1` (this file). -/
theorem saturatedFerromagnetJointEigenspace_finrank_eq
    [Nonempty V] (J : V → V → ℂ) :
    Module.finrank ℂ
      (saturatedFerromagnetJointEigenspace (V := V) J N) =
        Fintype.card V * N + 1 := by
  rw [saturatedFerromagnetJointEigenspace_eq_span_ladderIterateUp J]
  exact ladderIterateUp_span_finrank_eq_succ_card_mul_N

end LatticeSystem.Quantum
