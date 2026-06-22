import LatticeSystem.Quantum.NeelState.MarshallSign
import LatticeSystem.Quantum.MagnetizationSubspaceCore

/-!
# Marshall-dressed standard basis on a bipartite graph (Tasaki §2.5 eq. (2.5.8))

For a finite vertex type `V`, a sublattice indicator
`A : V → Bool`, and a spin-1/2 configuration `σ : V → Fin 2`,
the **Marshall-dressed standard basis state** is

  `|Ψ̃^σ⟩ := marshallSignOf A σ • |σ⟩`,

where `|σ⟩ = basisVec σ` is the standard computational basis
state and `marshallSignOf A σ = ∏_{x ∈ A} (-1)^(σ_x)` is the
Marshall sign on `A` (Tasaki §2.5, p. 41, eq. (2.5.8)).  This
change of basis underlies the Marshall–Lieb–Mattis theorem: in
the dressed basis the spin-1/2 antiferromagnetic Heisenberg
Hamiltonian on a bipartite graph has all off-diagonal matrix
elements `≤ 0`, which is the input to the Perron–Frobenius
argument that proves uniqueness of the ground state.

This file provides the basic structural lemmas:

* `marshallDressedBasis_apply`, `_self`, `_of_ne` — explicit
  pointwise evaluation rules.
* `marshallSignOf_sq_eq_one` — `(marshallSignOf A σ)² = 1`,
  i.e. the dressing sign squares to `1` (each factor is `±1`).
* `marshallDressedBasis_inner` — orthonormality of the dressed
  basis under the real bilinear pairing `Σ_τ Ψ̃^σ τ · Ψ̃^σ' τ`.
* `marshallDressedBasis_mem_magnetizationSubspace` — the dressed
  basis state lies in the same magnetization-`M` subspace `H_M`
  as the underlying `basisVec σ`, since the dressing is a
  scalar multiplication and `H_M` is a `ℂ`-submodule (Tasaki
  eq. (2.2.10)).

References:

- H. Tasaki, *Physics and Mathematics of Quantum Many-Body
  Systems*, Springer 2020, §2.5, p. 41, eq. (2.5.8).
- W. Marshall, Proc. R. Soc. A **232**, 48 (1955).
- E.H. Lieb, D. Mattis, J. Math. Phys. **3**, 749 (1962).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Definition and pointwise rules -/

/-- The **Marshall-dressed standard basis state** on a bipartite
vertex type `V` with sublattice indicator `A : V → Bool`:

  `|Ψ̃^σ⟩ := marshallSignOf A σ • basisVec σ`,

where `marshallSignOf A σ = ∏_{x : V}, A x ? (-1)^(σ x) : 1` is
the Marshall sign on `A` (Tasaki §2.5, p. 41, eq. (2.5.8)).

The dressing produces a basis in which the spin-1/2
antiferromagnetic Heisenberg Hamiltonian on a connected
bipartite graph has all off-diagonal matrix elements `≤ 0`
(established in subsequent files).  This is the
Marshall sign trick at the heart of the Marshall–Lieb–Mattis
theorem. -/
noncomputable def marshallDressedBasis (A : V → Bool)
    (σ : V → Fin 2) : (V → Fin 2) → ℂ :=
  marshallSignOf A σ • basisVec σ

omit [DecidableEq V] in
/-- Explicit pointwise form: `|Ψ̃^σ⟩ τ = marshallSignOf A σ · basisVec σ τ`. -/
theorem marshallDressedBasis_apply (A : V → Bool)
    (σ τ : V → Fin 2) :
    marshallDressedBasis A σ τ =
      marshallSignOf A σ * basisVec σ τ := by
  unfold marshallDressedBasis
  simp [Pi.smul_apply, smul_eq_mul]

omit [DecidableEq V] in
/-- Diagonal value of the dressed basis state at its own
configuration: `|Ψ̃^σ⟩ σ = marshallSignOf A σ`.

Follows from `basisVec σ σ = 1` and the definition. -/
@[simp]
theorem marshallDressedBasis_self (A : V → Bool) (σ : V → Fin 2) :
    marshallDressedBasis A σ σ = marshallSignOf A σ := by
  rw [marshallDressedBasis_apply, basisVec_self, mul_one]

omit [DecidableEq V] in
/-- Off-diagonal value: the dressed basis state at `σ` vanishes
on every configuration `τ ≠ σ`.

Follows from `basisVec σ τ = 0` for `τ ≠ σ` and the definition. -/
theorem marshallDressedBasis_of_ne (A : V → Bool)
    {σ τ : V → Fin 2} (h : τ ≠ σ) :
    marshallDressedBasis A σ τ = 0 := by
  rw [marshallDressedBasis_apply, basisVec_of_ne h, mul_zero]

/-! ## Marshall sign squares to one -/

omit [DecidableEq V] in
/-- Each factor of `marshallSignOf` is `±1`, so the Marshall sign
itself squares to `1`: `(marshallSignOf A σ)² = 1`. -/
theorem marshallSignOf_sq_eq_one (A : V → Bool) (σ : V → Fin 2) :
    marshallSignOf A σ * marshallSignOf A σ = 1 := by
  unfold marshallSignOf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun x _ => ?_
  by_cases hA : A x = true
  · rw [if_pos hA]
    -- `(-1)^k · (-1)^k = 1` for `k = 0` or `1` (the only values of `σ x : Fin 2`).
    have hk : (σ x : ℕ) = 0 ∨ (σ x : ℕ) = 1 := by
      rcases (σ x) with ⟨k, hk⟩
      omega
    rcases hk with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
  · rw [if_neg hA]; ring

/-! ## Orthonormality (real bilinear pairing) -/

/-- Orthonormality of the Marshall-dressed basis under the real
bilinear pairing:

  `Σ_τ |Ψ̃^σ⟩ τ · |Ψ̃^ρ⟩ τ = if ρ = σ then 1 else 0`.

Follows from orthonormality of the standard basis (Tasaki
eq. (2.2.1) `S = 1/2` form) together with
`(marshallSignOf A σ)² = 1`.  No complex conjugation appears
because the Marshall sign and the standard basis values are all
real. -/
theorem marshallDressedBasis_inner (A : V → Bool) (σ ρ : V → Fin 2) :
    ∑ τ : V → Fin 2,
        marshallDressedBasis A σ τ * marshallDressedBasis A ρ τ =
      if ρ = σ then 1 else 0 := by
  simp only [marshallDressedBasis_apply]
  -- Σ_τ (s σ * b σ τ) * (s ρ * b ρ τ) = s σ * s ρ * Σ_τ b σ τ * b ρ τ.
  rw [show (∑ τ : V → Fin 2,
        marshallSignOf A σ * basisVec σ τ *
          (marshallSignOf A ρ * basisVec ρ τ)) =
      marshallSignOf A σ * marshallSignOf A ρ *
        ∑ τ : V → Fin 2, basisVec σ τ * basisVec ρ τ from ?_,
      basisVec_inner]
  · split_ifs with hρσ
    · -- ρ = σ, so the sign factors collapse.
      subst hρσ
      rw [marshallSignOf_sq_eq_one, mul_one]
    · rw [mul_zero]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro τ _
    ring

/-! ## Membership in the magnetization subspace -/

/-- The Marshall-dressed basis state `|Ψ̃^σ⟩` lies in the same
magnetization-`M` subspace `H_M` as the underlying `basisVec σ`,
namely `M = (magnetization σ : ℂ) / 2` (Tasaki eq. (2.2.10)).

The dressing is a scalar multiplication, and `magnetizationSubspace`
is a `ℂ`-submodule, so it is closed under scalar multiples. -/
theorem marshallDressedBasis_mem_magnetizationSubspace
    (A : V → Bool) (σ : V → Fin 2) :
    marshallDressedBasis A σ ∈
      magnetizationSubspace V ((magnetization V σ : ℂ) / 2) := by
  unfold marshallDressedBasis
  exact Submodule.smul_mem _ _ (basisVec_mem_magnetizationSubspace V σ)

/-- The Marshall-dressed basis state of a magnetization-zero
configuration lies in `H_0`, the zero-magnetization subspace.

Specialisation of `marshallDressedBasis_mem_magnetizationSubspace`
when `Σ_x σ_x = 0`. -/
theorem marshallDressedBasis_mem_magnetizationSubspace_zero
    (A : V → Bool) {σ : V → Fin 2} (hσ : magnetization V σ = 0) :
    marshallDressedBasis A σ ∈ magnetizationSubspace V 0 := by
  have h := marshallDressedBasis_mem_magnetizationSubspace A σ
  rw [hσ] at h
  simpa using h

end LatticeSystem.Quantum
