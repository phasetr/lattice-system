import LatticeSystem.Quantum.SpinS.SpinSReversal
import LatticeSystem.Quantum.SpinS.TotalSpin

/-!
# Many-body spin reversal and the magnetization reflection

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

The many-body spin reversal `Θ` reverses every site's `Ŝ³` index (`σ ↦ Fin.rev ∘ σ`).  As a
permutation matrix it conjugates a single-site operator by the single-site reversal,
`Θ (onSiteS z A) Θ = onSiteS z (F A F)`, and hence reverses the total `Ŝ³_tot`:
`Θ Ŝ³_tot Θ = −Ŝ³_tot`.  This `M ↔ −M` reflection is the symmetry used in the
Mattis–Nishimori uniqueness argument (Theorem 2.4): it gives `E_M = E_{−M}` and, with the
ground state in `H_0`, the conclusion `Ŝ³_tot Φ_GS = 0`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The configuration reversal `σ ↦ Fin.rev ∘ σ`. -/
def revConfigS (σ : Λ → Fin (N + 1)) : Λ → Fin (N + 1) := fun x => Fin.rev (σ x)

omit [Fintype Λ] [DecidableEq Λ] in
theorem revConfigS_involutive (σ : Λ → Fin (N + 1)) : revConfigS (revConfigS σ) = σ := by
  funext x; simp [revConfigS, Fin.rev_rev]

/-- **Many-body spin reversal** `Θ`: the permutation matrix of `revConfigS`. -/
noncomputable def manyBodyReversalS (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ) :
    ManyBodyOpS Λ N :=
  Matrix.of fun σ' σ => if σ' = revConfigS σ then (1 : ℂ) else 0

theorem manyBodyReversalS_apply (σ' σ : Λ → Fin (N + 1)) :
    manyBodyReversalS Λ N σ' σ = if σ' = revConfigS σ then (1 : ℂ) else 0 := rfl

/-- Conjugation by `Θ` reindexes by the configuration reversal. -/
theorem manyBodyReversalS_conj_apply (M : ManyBodyOpS Λ N) (σ' σ : Λ → Fin (N + 1)) :
    (manyBodyReversalS Λ N * M * manyBodyReversalS Λ N) σ' σ =
      M (revConfigS σ') (revConfigS σ) := by
  rw [Matrix.mul_apply]
  have hΘM : ∀ τ, (manyBodyReversalS Λ N * M) σ' τ = M (revConfigS σ') τ := by
    intro τ
    rw [Matrix.mul_apply, Finset.sum_eq_single (revConfigS σ')]
    · rw [manyBodyReversalS_apply, if_pos (revConfigS_involutive σ').symm, one_mul]
    · intro ρ _ hρ
      rw [manyBodyReversalS_apply, if_neg (fun h => hρ (by rw [h, revConfigS_involutive])),
        zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_eq_single (revConfigS σ)]
  · rw [hΘM, manyBodyReversalS_apply, if_pos rfl, mul_one]
  · intro ρ _ hρ
    rw [hΘM, manyBodyReversalS_apply, if_neg hρ, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `Θ` is an involution. -/
theorem manyBodyReversalS_mul_self (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ) :
    manyBodyReversalS Λ N * manyBodyReversalS Λ N = 1 := by
  ext σ' σ
  rw [show manyBodyReversalS Λ N * manyBodyReversalS Λ N
        = manyBodyReversalS Λ N * 1 * manyBodyReversalS Λ N by rw [mul_one],
    manyBodyReversalS_conj_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h : σ' = σ
  · subst h; simp
  · have hne : ¬ (revConfigS σ' = revConfigS σ) :=
      fun hr => h (funext fun x => Fin.rev_injective (congrFun hr x))
    simp only [if_neg h, if_neg hne]

/-- **Conjugation of a single-site operator by `Θ`**:
`Θ (onSiteS z A) Θ = onSiteS z (F A F)`. -/
theorem manyBodyReversalS_conj_onSiteS (z : Λ)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    manyBodyReversalS Λ N * onSiteS z A * manyBodyReversalS Λ N =
      onSiteS z (spinReversalS N * A * spinReversalS N) := by
  ext σ' σ
  rw [manyBodyReversalS_conj_apply, onSiteS_apply, onSiteS_apply]
  have hcond : (∀ k, k ≠ z → revConfigS σ' k = revConfigS σ k) ↔
      (∀ k, k ≠ z → σ' k = σ k) := by
    constructor
    · intro h k hk; exact Fin.rev_injective (h k hk)
    · intro h k hk; rw [revConfigS, revConfigS, h k hk]
  by_cases hc : ∀ k, k ≠ z → σ' k = σ k
  · rw [if_pos (hcond.mpr hc), if_pos hc, spinReversalS_conj_apply]
    rfl
  · rw [if_neg (fun h => hc (hcond.mp h)), if_neg hc]

/-- **`Θ` reverses the total `Ŝ³_tot`**: `Θ Ŝ³_tot Θ = −Ŝ³_tot`. -/
theorem manyBodyReversalS_conj_totalSpinSOp3 (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ) :
    manyBodyReversalS Λ N * totalSpinSOp3 Λ N * manyBodyReversalS Λ N = -totalSpinSOp3 Λ N := by
  rw [totalSpinSOp3, Matrix.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [manyBodyReversalS_conj_onSiteS, spinReversalS_conj_spinSOp3, onSiteS_neg]

end LatticeSystem.Quantum
