import LatticeSystem.Quantum.MarshallLiebMattis.H0ShiftedSwap
import LatticeSystem.Quantum.MarshallLiebMattis.MatrixPowExtend

/-!
# Lifting `SwapReachable` to matrix-power positivity for `B = c · I − M`

This module lifts the combinatorial swap-reachability relation
(PR α-4 / α-5c) to algebraic matrix-power positivity for the
shifted dressed Heisenberg matrix `B = c · I − M`:

  For `σ : H₀Index Λ` and any `ξ : Λ → Fin 2` with
  `Relation.ReflTransGen (SwapStep G) σ.val ξ`, there exists
  `m : ℕ` such that `(B^m) σ ⟨ξ, h_mag⟩ > 0`,
  where `h_mag : magnetization Λ ξ = 0` is automatic
  (`basisSwap` preserves magnetisation, PR α-5b).

Induction on `Relation.ReflTransGen`:

* Base (refl): `ξ = σ.val`, take `m = 0` and use `(B^0) σ σ = 1 > 0`.
* Step (tail): a `SwapStep G ξ_mid ξ` extends a chain ending at
  `ξ_mid` (with IH-given `(B^m) σ ⟨ξ_mid, _⟩ > 0`) by one swap.
  - `B ⟨ξ_mid, _⟩ ⟨ξ, _⟩ > 0` by PR α-5j (single-step swap positivity).
  - `(B^(m+1)) σ ⟨ξ, _⟩ > 0` by PR α-5l (one-step matrix-power extension).

Combined with PR α-5c's `swapReachable_of_eq_magnetization`, this
gives matrix-power positivity for arbitrary `σ, τ : H₀Index Λ`,
the input shape needed for Perron–Frobenius irreducibility (α-5n+).

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5, p. 41.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- Lift `Relation.ReflTransGen (SwapStep G) σ.val ξ` to
matrix-power positivity for `B = c · I − M`.

The conclusion's `magnetization Λ ξ = 0` follows automatically from
`magnetization_basisSwap` along the chain (since `σ.val` has
magnetisation `0` by `H₀Index`-membership).

The matrix-power exponent `m` matches the chain length:
* `m = 0` if `ξ = σ.val` (refl case);
* `m = chain length ≥ 1` if `ξ ≠ σ.val` (tail case). -/
theorem dressedHeisenbergShifted_pow_pos_of_swapReachable
    {G : SimpleGraph Λ} (A : Λ → Bool)
    (hG_bipartite : ∀ {x y : Λ}, G.Adj x y → A x ≠ A y)
    {J : Λ → Λ → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_symm : ∀ x y, J x y = J y x)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hJ_pos_on_G : ∀ {x y : Λ}, G.Adj x y → 0 < (J x y).re)
    (c : ℝ)
    (hc : ∀ σ : H₀Index Λ, dressedHeisenbergMatrixH0 A J σ σ ≤ c)
    (σ : H₀Index Λ) (ξ : Λ → Fin 2)
    (hreach : Relation.ReflTransGen (SwapStep G) σ.val ξ) :
    ∃ (h_mag : magnetization Λ ξ = 0) (m : ℕ),
      0 < ((dressedHeisenbergShifted A J c) ^ m) σ ⟨ξ, h_mag⟩ := by
  -- Non-negativity of B for matrix_pow_succ_pos_of_pow_pos_step.
  have hB_nn : ∀ i j, 0 ≤ dressedHeisenbergShifted A J c i j :=
    dressedHeisenbergShifted_nonneg A hJ_real hJ_nn hJ_bipartite c hc
  induction hreach with
  | refl =>
    refine ⟨σ.property, 0, ?_⟩
    -- (B^0) σ σ = 1 > 0.
    rw [pow_zero]
    have hσ_eq : σ = ⟨σ.val, σ.property⟩ := Subtype.ext rfl
    rw [← hσ_eq, Matrix.one_apply_eq]
    exact zero_lt_one
  | tail h_init h_step ih =>
    -- Names: original ξ from earlier in chain (call it ξ_mid),
    -- and the new ξ_curr at the head of the chain.
    rename_i ξ_mid ξ_curr
    obtain ⟨h_mag_mid, m, hpow⟩ := ih
    obtain ⟨x, y, hadj, hne, hξ_curr⟩ := h_step
    -- magnetization preserved by basisSwap.
    have h_mag_curr : magnetization Λ ξ_curr = 0 := by
      rw [hξ_curr, magnetization_basisSwap]
      exact h_mag_mid
    refine ⟨h_mag_curr, m + 1, ?_⟩
    -- B ⟨ξ_mid⟩ ⟨ξ_curr⟩ > 0 by α-5j.
    have hxy : x ≠ y := G.ne_of_adj hadj
    have hAxy : A x ≠ A y := hG_bipartite hadj
    have hJxy_pos : 0 < (J x y).re := hJ_pos_on_G hadj
    have hstep_pos : 0 < dressedHeisenbergShifted A J c
        ⟨ξ_mid, h_mag_mid⟩ ⟨ξ_curr, h_mag_curr⟩ :=
      dressedHeisenbergShifted_pos_of_basisSwap A hJ_symm hxy hAxy hJxy_pos c
        hne ⟨ξ_curr, h_mag_curr⟩ hξ_curr
    -- Lift via matrix_pow_succ_pos_of_pow_pos_step.
    exact LatticeSystem.Math.matrix_pow_succ_pos_of_pow_pos_step hB_nn hpow hstep_pos

end LatticeSystem.Quantum
