import LatticeSystem.Quantum.SpinS.ManyBodyTensorS

/-!
# Conjugating a single-site operator by a many-body tensor unitary

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

A single-site operator `onSiteS z A` is the tensor with `A` at `z` and `1` elsewhere; using
the functoriality of `manyBodyTensorS` (#3750) the gauge unitary `Θ_U = ⊗_x U` conjugates it to
`onSiteS z (U A U⁻¹)`.  This is the general single-site-unitary conjugation behind the
axis-swap gauge of Theorem 2.4.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- `onSiteS z A` is the many-body tensor with `A` at `z` and `1` elsewhere. -/
theorem onSiteS_eq_manyBodyTensorS (z : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    onSiteS z A =
      manyBodyTensorS
        (Function.update (fun _ : Λ => (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) z A) := by
  classical
  ext σ' σ
  rw [onSiteS_apply, manyBodyTensorS_apply,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ z), Function.update_self,
    Finset.prod_congr rfl (fun x hx => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hx), Matrix.one_apply]),
    Finset.prod_boole]
  by_cases hc : ∀ k, k ≠ z → σ' k = σ k
  · rw [if_pos hc, if_pos (fun x hx => hc x (Finset.ne_of_mem_erase hx)), mul_one]
  · rw [if_neg hc,
      if_neg (fun h => hc (fun k hk => h k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩))),
      mul_zero]

/-- **Conjugation of a single-site operator by the tensor unitary** `Θ_U = ⊗_x U`:
`Θ_U (onSiteS z A) Θ_{U⁻¹} = onSiteS z (U A U⁻¹)` (for `U * Uinv = 1`). -/
theorem manyBodyTensorS_conj_onSiteS {U Uinv : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hUU : U * Uinv = 1) (z : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    manyBodyTensorS (fun _ : Λ => U) * onSiteS z A * manyBodyTensorS (fun _ : Λ => Uinv) =
      onSiteS z (U * A * Uinv) := by
  rw [onSiteS_eq_manyBodyTensorS, manyBodyTensorS_mul, manyBodyTensorS_mul,
    onSiteS_eq_manyBodyTensorS]
  congr 1
  funext x
  by_cases h : x = z
  · subst h; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne h, Function.update_of_ne h, mul_one, hUU]

end LatticeSystem.Quantum
