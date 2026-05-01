import LatticeSystem.Quantum.SpinS.Magnetization

/-!
# Spin-`S` Marshall sign on a bipartite sublattice
(Tasaki §2.5 Phase B-β β-4h)

For a vertex type `V`, a sublattice-`A` indicator `A : V → Bool`, and
a spin-`S` configuration `σ : V → Fin (N + 1)`, the Marshall sign is

  `marshallSignS A σ := ∏_{x ∈ A} (-1)^(σ x).val
                     = (-1)^(Σ_{x ∈ A} (σ x).val)`.

Generalises the spin-1/2 `marshallSignOf` (`Quantum/NeelState/MarshallSign.lean`).

For the spin-1/2 case `N = 1`, `(σ x).val ∈ {0, 1}` so
`Σ_{x ∈ A} (σ x).val = |{x ∈ A : σ x = 1}|`
recovers the standard "down-spin count on sublattice A" sign.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] {N : ℕ}

/-- The spin-`S` Marshall sign on sublattice indicator `A`. -/
noncomputable def marshallSignS (A : V → Bool) (σ : V → Fin (N + 1)) : ℂ :=
  ∏ x : V, if A x then ((-1 : ℂ) ^ (σ x).val) else 1

/-- All-`s = 0` Marshall sign is `+1` on any sublattice. -/
theorem marshallSignS_const_zero (A : V → Bool) :
    marshallSignS A (fun _ : V => (0 : Fin (N + 1))) = 1 := by
  unfold marshallSignS
  apply Finset.prod_eq_one
  intro x _
  by_cases hAx : A x
  · simp [hAx]
  · simp [hAx]

end LatticeSystem.Quantum
