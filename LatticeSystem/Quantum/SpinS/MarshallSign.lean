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

/-! ## Marshall-dressed basis -/

/-- The Marshall-dressed basis vector at `σ`:

  `marshallDressedBasisS A σ := marshallSignS A σ • basisVecS σ`.

This is the orthonormal basis used in the Marshall–Lieb–Mattis
machinery: by absorbing the Marshall sign into the basis vector, the
Heisenberg matrix elements become *real and non-positive*
off-diagonal in this rotated basis (Marshall sign trick), enabling
the Perron–Frobenius argument.

Generalises the spin-1/2 `marshallDressedBasis`
(`Quantum/MarshallDressedBasis.lean`) to arbitrary spin. -/
noncomputable def marshallDressedBasisS [DecidableEq V]
    (A : V → Bool) (σ : V → Fin (N + 1)) : (V → Fin (N + 1)) → ℂ :=
  marshallSignS A σ • basisVecS σ

/-- Component formula: `marshallDressedBasisS A σ τ` is
`marshallSignS A σ` if `τ = σ`, else `0`. -/
theorem marshallDressedBasisS_apply [DecidableEq V]
    (A : V → Bool) (σ τ : V → Fin (N + 1)) :
    marshallDressedBasisS A σ τ =
      if τ = σ then marshallSignS A σ else 0 := by
  unfold marshallDressedBasisS basisVecS
  rw [Pi.smul_apply, smul_eq_mul]
  by_cases h : τ = σ
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

/-- Diagonal component: `marshallDressedBasisS A σ σ = marshallSignS A σ`. -/
@[simp]
theorem marshallDressedBasisS_self [DecidableEq V]
    (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallDressedBasisS A σ σ = marshallSignS A σ := by
  rw [marshallDressedBasisS_apply, if_pos rfl]

/-- Off-diagonal component: zero for `τ ≠ σ`. -/
theorem marshallDressedBasisS_of_ne [DecidableEq V]
    (A : V → Bool) {σ τ : V → Fin (N + 1)} (hne : τ ≠ σ) :
    marshallDressedBasisS A σ τ = 0 := by
  rw [marshallDressedBasisS_apply, if_neg hne]

end LatticeSystem.Quantum
