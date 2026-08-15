import LatticeSystem.Quantum.MarshallLiebMattis.H0Matrix

/-!
# `basisSwap` preserves total magnetisation
(Tasaki §2.5 p. 42 ingredient)

This module proves the magnetisation-preservation property of the
bond-swap operation `basisSwap`:

  `magnetization Λ (basisSwap σ x y) = magnetization Λ σ`.

This is a key lemma for the Tasaki §2.5 p. 42 Proposition (any two
configurations with equal magnetisation are connected via a chain
of single-edge swaps), to be assembled in subsequent PRs.

The proof uses the identification `basisSwap σ x y = σ ∘ Equiv.swap x y`:
the swap is a permutation of the underlying lattice, and the
magnetisation `∑_x spinSign(σ x)` is invariant under permutation.

The module also records the affine identification of the two magnetisation
quantum numbers in use, `|σ| = |Λ| − 2 · magSumS σ`, and the resulting
equivalence of the equal-magnetisation and equal-`magSumS` hypotheses. It
is through this translation that the spin-`1/2` configuration reachability
is obtained from the spin-`S` raise/lower reachability at `N = 1`.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- `basisSwap` preserves total magnetisation:
`magnetization Λ (basisSwap σ x y) = magnetization Λ σ`. -/
theorem magnetization_basisSwap (σ : Λ → Fin 2) (x y : Λ) :
    magnetization Λ (basisSwap σ x y) = magnetization Λ σ := by
  unfold magnetization
  -- magnetization (basisSwap σ x y) = ∑_z spinSign(basisSwap σ x y z)
  -- = ∑_z spinSign(σ ((swap x y) z)) (basisSwap_eq_comp_swap)
  -- = ∑_z spinSign(σ z) (sum invariant under permutation reindexing)
  by_cases hxy : x = y
  · -- x = y: basisSwap is identity.
    subst hxy
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hzx : z = x
    · subst hzx
      unfold basisSwap; rw [Function.update_self]
    · unfold basisSwap
      rw [Function.update_of_ne hzx, Function.update_of_ne hzx]
  · -- x ≠ y: use bijection reindexing via Equiv.swap.
    rw [show (∑ z : Λ, spinSign (basisSwap σ x y z)) =
        ∑ z : Λ, spinSign (σ (Equiv.swap x y z)) from ?_]
    · -- Sum over Fintype is invariant under bijection.
      exact Equiv.sum_comp (Equiv.swap x y) (fun z => spinSign (σ z))
    · refine Finset.sum_congr rfl fun z _ => ?_
      congr 1
      -- basisSwap σ x y z = σ (Equiv.swap x y z).
      unfold basisSwap
      by_cases hzx : z = x
      · subst hzx
        rw [Function.update_of_ne hxy, Function.update_self,
            Equiv.swap_apply_left]
      · by_cases hzy : z = y
        · subst hzy
          rw [Function.update_self, Equiv.swap_apply_right]
        · rw [Function.update_of_ne hzy, Function.update_of_ne hzx,
              Equiv.swap_apply_of_ne_of_ne hzx hzy]

/-- Specialisation: `basisSwap σ x y` is in the same magnetisation
sector as `σ`. -/
theorem magnetization_basisSwap_eq_zero_iff (σ : Λ → Fin 2) (x y : Λ) :
    magnetization Λ (basisSwap σ x y) = 0 ↔ magnetization Λ σ = 0 := by
  rw [magnetization_basisSwap]

/-! ## Magnetisation versus the spin-`S` magnetisation sum at `N = 1` -/

omit [DecidableEq Λ] in
/-- The integer magnetisation in terms of the down-spin count:
`|σ| = |Λ| − 2 · Σ_x σ_x`, where `Σ_x σ_x = magSumS (N := 1) σ` is the
spin-`S` magnetisation-index sum read at `N = 1`. Each site contributes
`spinSign (σ x) = 1 − 2 · σ_x`. -/
theorem magnetization_eq_card_sub_two_mul (σ : Λ → Fin 2) :
    magnetization Λ σ = (Fintype.card Λ : ℤ) - 2 * (magSumS (N := 1) σ : ℤ) := by
  have hsign : ∀ s : Fin 2, (spinSign s : ℤ) = 1 - 2 * (s.val : ℤ) := by decide
  unfold magnetization magSumS
  simp_rw [hsign]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← Finset.mul_sum,
    Nat.cast_sum]
  simp

omit [DecidableEq Λ] in
/-- Equal magnetisation is equivalent to an equal spin-`S` magnetisation
sum at `N = 1`: the two quantum numbers differ by the affine change
`|σ| = |Λ| − 2 · magSumS σ`. This is the hypothesis translation used to
read the spin-`1/2` equal-magnetisation reachability off the spin-`S`
raise/lower reachability. -/
theorem magnetization_eq_iff_magSumS_eq (σ σ' : Λ → Fin 2) :
    magnetization Λ σ = magnetization Λ σ' ↔
      magSumS (N := 1) σ = magSumS (N := 1) σ' := by
  rw [magnetization_eq_card_sub_two_mul, magnetization_eq_card_sub_two_mul]
  omega

end LatticeSystem.Quantum
