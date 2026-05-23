import LatticeSystem.Quantum.SpinS.Theorem23Local

/-!
# Tasaki §2.5 Theorem 2.3 raised-vector site-sum expansions

This module contains the raised-direction site-sum expansion theorems, split
as a stable suffix from `Theorem23Local.lean`: the total `Ŝ^+_tot` lowered
(raised) site-sum expansion and its on-`A` / off-`A` sublattice variants. The
parent module keeps the lowered-direction ladder/site-sum machinery these are
the raising-direction companions to.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 raised-vector site-sum expansion**:
the `Ŝ^+_tot`-raised embedded sector vector is the sum of its
single-site raising contributions at each target configuration.

This is the raising-direction companion to
`totalSpinSOpMinus_mulVec_magSectorEmbedding_apply_eq_site_sum`. -/
theorem totalSpinSOpPlus_mulVec_magSectorEmbedding_apply_eq_site_sum {M : ℕ}
    (Φ : magConfigS V N (M + 1) → ℂ) (τ : V → Fin (N + 1)) :
    ((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) τ =
      ∑ x : V,
        ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ := by
  rw [totalSpinSOpPlus_def, Matrix.sum_mulVec]
  simp [Finset.sum_apply]

/-- **Tasaki §2.5 Theorem 2.3 on-`A` raised sublattice expansion**:
the `Ŝ_A^+` component of an embedded successor-sector vector is the sum
of single-site raising contributions over sites in `A`.

This is the raising-direction companion to
`sublatticeSpinSOpMinus_mulVec_magSectorEmbedding_apply_eq_onA_site_sum`
and is used after re-embedding lowered components in the cross-ladder
identity. -/
theorem sublatticeSpinSOpPlus_mulVec_magSectorEmbedding_apply_eq_onA_site_sum
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : V → Fin (N + 1)) :
    ((sublatticeSpinSOpPlus N A).mulVec (magSectorEmbedding Φ)) τ =
      ∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ := by
  classical
  rw [sublatticeSpinSOpPlus, Matrix.sum_mulVec, Finset.sum_apply]
  calc
    (∑ c : V,
      Matrix.mulVec (if A c = true then onSiteS c (spinSOpPlus N) else 0)
        (magSectorEmbedding Φ) τ) =
        ∑ c : V, if A c = true then
          Matrix.mulVec (onSiteS c (spinSOpPlus N)) (magSectorEmbedding Φ) τ
        else 0 := by
          apply Finset.sum_congr rfl
          intro x _hx
          by_cases hA : A x = true
          · simp [hA]
          · cases hx : A x <;> simp [hx] at hA ⊢
    _ = ∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ := by
          rw [Finset.sum_filter]

/-- **Tasaki §2.5 Theorem 2.3 off-`A` raised sublattice expansion**:
the `Ŝ_¬A^+` component of an embedded successor-sector vector is the sum
of single-site raising contributions over sites outside `A`.

This packages the complement sublattice with the same `A x = false`
filter used by the local coefficient comparison. -/
theorem sublatticeSpinSOpPlus_complement_mulVec_magSectorEmbedding_apply_eq_offA_site_sum
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : V → Fin (N + 1)) :
    ((sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec
        (magSectorEmbedding Φ)) τ =
      ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ := by
  classical
  rw [sublatticeSpinSOpPlus, Matrix.sum_mulVec, Finset.sum_apply]
  calc
    (∑ c : V,
      Matrix.mulVec
        (if (!A c) = true then onSiteS c (spinSOpPlus N) else 0)
        (magSectorEmbedding Φ) τ) =
        ∑ c : V, if A c = false then
          Matrix.mulVec (onSiteS c (spinSOpPlus N)) (magSectorEmbedding Φ) τ
        else 0 := by
          apply Finset.sum_congr rfl
          intro x _hx
          cases A x <;> simp
    _ = ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ := by
          rw [Finset.sum_filter]

end LatticeSystem.Quantum
