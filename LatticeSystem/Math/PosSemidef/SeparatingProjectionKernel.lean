import LatticeSystem.Math.PosSemidef.Kernel

/-!
# Basis extraction from a kernel invariant under separating coordinate projections

Second step (PIECE 2) of Tasaki Lemma 10.10. If the kernel of a matrix `R` is invariant
under each member of a family of `0/1`-valued diagonal projections `diagonal (d x)` whose
diagonals **separate points** (`s = t` whenever `d x s = d x t` for all `x`), then the
kernel is spanned by standard basis vectors: a kernel vector `v` with `v a ≠ 0` forces
the basis vector `δ_a` into the kernel.

The proof avoids any noncommutative matrix product: it inducts over the finite set of
"coordinates" `x`, peeling one projection `diagonal (d x)` (or its complement) at a time
on the **vector** `fun s => if (∀ x ∈ T, d x s = d x a) then v s else 0`, which at `T = univ`
collapses (by separation) to `v a • δ_a`.

## Main result

* `basis_mem_ker_of_separating_projections` — `R v = 0`, `v a ≠ 0` ⟹ `R (δ_a) = 0`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4 (Lemma 10.10), pp. 363–367.
-/

namespace LatticeSystem.Math

open Matrix
open scoped BigOperators

variable {S ι : Type*} [Fintype S] [DecidableEq S] [Finite ι]

/-- **Basis extraction.** Let `R` be a matrix whose kernel is invariant under each
projection `diagonal (d x)` (for kernel vectors `w`, `R w = 0 ⟹ R (diagonal (d x) w) = 0`),
where the diagonals `d x` are `0/1`-valued and separate points. Then any kernel vector `v`
with `v a ≠ 0` forces `δ_a` into the kernel: `R (Pi.single a 1) = 0`. -/
theorem basis_mem_ker_of_separating_projections
    {R : Matrix S S ℂ} {d : ι → S → ℂ}
    (hbin : ∀ x s, d x s = 0 ∨ d x s = 1)
    (hsep : ∀ s t : S, (∀ x, d x s = d x t) → s = t)
    (hinv : ∀ x, ∀ w : S → ℂ, R.mulVec w = 0
      → R.mulVec ((Matrix.diagonal (d x)).mulVec w) = 0)
    {v : S → ℂ} (hv : R.mulVec v = 0) {a : S} (ha : v a ≠ 0) :
    R.mulVec (Pi.single a 1) = 0 := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  -- One coordinate step: keeping `{s : d x s = d x a}` preserves the kernel.
  have step : ∀ (x : ι) (w : S → ℂ), R.mulVec w = 0
      → R.mulVec (fun s => if d x s = d x a then w s else 0) = 0 := by
    intro x w hw
    rcases hbin x a with hxa | hxa
    · -- `d x a = 0`: keeping `{d x s = 0}` is the complement `w − diagonal (d x) w`.
      have hfun : (fun s => if d x s = d x a then w s else 0)
          = w - (Matrix.diagonal (d x)).mulVec w := by
        funext s
        rw [hxa, Pi.sub_apply, Matrix.mulVec_diagonal]
        rcases hbin x s with h | h <;> simp [h]
      rw [hfun, Matrix.mulVec_sub, hw, hinv x w hw, sub_zero]
    · -- `d x a = 1`: keeping `{d x s = 1}` is `diagonal (d x) w`.
      have hfun : (fun s => if d x s = d x a then w s else 0)
          = (Matrix.diagonal (d x)).mulVec w := by
        funext s
        rw [hxa, Matrix.mulVec_diagonal]
        rcases hbin x s with h | h <;> simp [h]
      rw [hfun]; exact hinv x w hw
  -- Induct over the finite coordinate set.
  have key : ∀ T : Finset ι,
      R.mulVec (fun s => if (∀ x ∈ T, d x s = d x a) then v s else 0) = 0 := by
    intro T
    induction T using Finset.induction with
    | empty => simpa using hv
    | @insert x T hx ih =>
      have hfun : (fun s => if (∀ y ∈ insert x T, d y s = d y a) then v s else 0)
          = (fun s => if d x s = d x a
              then (if (∀ y ∈ T, d y s = d y a) then v s else 0) else 0) := by
        funext s
        simp only [Finset.forall_mem_insert]
        by_cases h1 : d x s = d x a <;> by_cases h2 : ∀ y ∈ T, d y s = d y a <;>
          simp [h1, h2]
      rw [hfun]; exact step x _ ih
  -- At `T = univ`, separation collapses the projection to `v a • δ_a`.
  have huniv := key Finset.univ
  have hcollapse : (fun s => if (∀ x ∈ Finset.univ, d x s = d x a) then v s else 0)
      = v a • (Pi.single a 1 : S → ℂ) := by
    funext s
    simp only [Finset.mem_univ, forall_true_left, Pi.smul_apply, smul_eq_mul]
    by_cases hs : s = a
    · subst hs; simp [Pi.single_eq_same]
    · rw [if_neg (fun hall => hs (hsep s a hall)), Pi.single_eq_of_ne hs, mul_zero]
  rw [hcollapse, Matrix.mulVec_smul, smul_eq_zero] at huniv
  exact huniv.resolve_left ha

end LatticeSystem.Math
