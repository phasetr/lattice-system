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

end LatticeSystem.Quantum
