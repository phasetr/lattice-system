/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MarshallLiebMattis.H0ShiftedReachable
import LatticeSystem.Quantum.MarshallLiebMattis.EqMagnetizationReachable
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

/-!
# Irreducibility of `B = c · I − M` on `H_0`

This module establishes the key Perron–Frobenius input:

  `(dressedHeisenbergShifted A J c).IsIrreducible`

for the spin-1/2 antiferromagnetic Heisenberg Hamiltonian on a
**connected** bipartite graph `G : SimpleGraph Λ` with positive
real symmetric coupling supported on `G`-edges, and a shift
constant `c` strictly larger than every diagonal entry of the
dressed matrix `M`.

The proof uses the iff
`Matrix.isIrreducible_iff_exists_pow_pos` (under non-negativity):

  `B.IsIrreducible ↔ ∀ σ τ, ∃ k > 0, 0 < (B^k) σ τ`.

Two cases:

* `σ = τ`: take `k = 1`; positivity is `0 < B σ σ = c − M σ σ`,
  which holds when `c > M σ σ` (strict shift hypothesis).
* `σ ≠ τ`: by PR α-5c's `swapReachable_of_eq_magnetization`,
  `σ.val` and `τ.val` are connected by a SwapReachable chain
  (since both have magnetisation `0`); by PR α-5m
  (`dressedHeisenbergShifted_pow_pos_of_swapReachable`), this
  lifts to `∃ k, (B^k) σ τ > 0`.  The strict `k > 0` follows
  because `σ ≠ τ` rules out the refl-case `k = 0`.

Combined with PR α-5d's non-negativity (under `c ≥ M σ σ`), this
gives the full irreducibility hypothesis required by Perron–Frobenius
(`Math.PerronFrobenius.exists_pos_eigenvec_max`).

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5, p. 41 (proof of Theorem 2.2).
- E. Seneta, *Non-negative Matrices and Markov Chains*, 3rd ed.,
  Springer 2006, §1.1.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Irreducibility of `B = c · I − M` on `H_0`.**

For a connected bipartite graph `G : SimpleGraph Λ` with positive
real symmetric coupling `J` supported on `G`-edges, and a shift
constant `c` strictly greater than every diagonal entry of `M`,
the shifted dressed Heisenberg matrix `B := c · I − M` is
**irreducible** in the Matrix-quiver sense.

Hypotheses:
* `G.Preconnected`: graph connectivity.
* `G.Adj x y → A x ≠ A y`: `G`-edges cross the bipartition.
* `J` is real (`(J x y).im = 0`), symmetric, and entrywise
  non-negative (`0 ≤ (J x y).re`).
* `J` is supported on bipartite edges
  (`A x = A y → J x y = 0`).
* `J` is strictly positive on `G`-edges
  (`G.Adj x y → 0 < (J x y).re`).
* `c` is **strictly** greater than every dressed diagonal entry
  (`∀ σ, M σ σ < c`). -/
theorem dressedHeisenbergShifted_isIrreducible
    {G : SimpleGraph Λ} (hG : G.Preconnected) (A : Λ → Bool)
    (hG_bipartite : ∀ {x y : Λ}, G.Adj x y → A x ≠ A y)
    {J : Λ → Λ → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_symm : ∀ x y, J x y = J y x)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hJ_pos_on_G : ∀ {x y : Λ}, G.Adj x y → 0 < (J x y).re)
    (c : ℝ)
    (hc : ∀ σ : H₀Index Λ, dressedHeisenbergMatrixH0 A J σ σ < c) :
    Matrix.IsIrreducible (dressedHeisenbergShifted A J c) := by
  -- Non-negativity of B (using the non-strict version of hc).
  have hc_le : ∀ σ : H₀Index Λ, dressedHeisenbergMatrixH0 A J σ σ ≤ c :=
    fun σ => le_of_lt (hc σ)
  have hB_nn : ∀ i j, 0 ≤ dressedHeisenbergShifted A J c i j :=
    dressedHeisenbergShifted_nonneg A hJ_real hJ_nn hJ_bipartite c hc_le
  -- Use isIrreducible_iff_exists_pow_pos.
  rw [Matrix.isIrreducible_iff_exists_pow_pos hB_nn]
  intro σ τ
  by_cases hστ : σ = τ
  · -- σ = τ: B σ σ > 0 (strict diagonal positivity from c > M σ σ).
    subst hστ
    refine ⟨1, Nat.one_pos, ?_⟩
    rw [pow_one, dressedHeisenbergShifted_diag]
    linarith [hc σ]
  · -- σ ≠ τ: SwapReachable chain → matrix-power positivity.
    -- Both σ.val and τ.val have magnetisation 0 (H_0 membership).
    have hmag : magnetization Λ σ.val = magnetization Λ τ.val := by
      rw [σ.property, τ.property]
    have hreach : SwapReachable G σ.val τ.val :=
      swapReachable_of_eq_magnetization hG σ.val τ.val hmag
    -- Lift via α-5m.
    obtain ⟨h_mag_τ, m, hpow⟩ := dressedHeisenbergShifted_pow_pos_of_swapReachable
      A hG_bipartite hJ_real hJ_symm hJ_nn hJ_bipartite hJ_pos_on_G c hc_le σ
      τ.val hreach
    -- The lifted ⟨τ.val, h_mag_τ⟩ should equal τ.
    have hτ_eq : (⟨τ.val, h_mag_τ⟩ : H₀Index Λ) = τ := Subtype.ext rfl
    rw [hτ_eq] at hpow
    -- m must be ≥ 1 because σ ≠ τ.
    -- If m = 0, (B^0) σ τ = (1 : Matrix _ _ ℝ) σ τ = if σ = τ then 1 else 0 = 0.
    -- This contradicts hpow > 0.
    refine ⟨m, ?_, hpow⟩
    by_contra h_zero
    push Not at h_zero
    interval_cases m
    rw [pow_zero, Matrix.one_apply_ne hστ] at hpow
    exact lt_irrefl 0 hpow

end LatticeSystem.Quantum
