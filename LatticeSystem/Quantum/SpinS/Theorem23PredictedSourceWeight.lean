import LatticeSystem.Quantum.SpinS.Theorem23Predicted

/-!
# Tasaki §2.5 Theorem 2.3 predicted source-weight bridges

This module contains the source-weight bridge layer split from
`Theorem23Predicted.lean`. The base predicted module keeps the
predicted-Casimir, predicted-GS, and cross-ladder bridges, while this module
packages the diagonal `S^3` source-weight evaluations (single-site /
sublattice / complement / cross-sublattice). The re-embedded cross-ladder
source-weight identities at a lowering predecessor are split into
`Theorem23PredictedSourceWeightCross.lean`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.

Tracked in Issue #412 (Tasaki §2.5: Marshall-Lieb-Mattis theorem).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 single-site lowering predecessor**:
if a target configuration `τ` in sector `M + 1` has positive local
value at `x`, lowering that local value by one gives a configuration
in sector `M`.

This private copy keeps the interval-chain module from exporting the
local bookkeeping lemma while preserving the moved local module's public
API surface. -/
private theorem magSumS_single_site_lowering_predecessor {M : ℕ}
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val) :
    magSumS
        (Function.update τ.1 x
          ⟨(τ.1 x).val - 1, by omega⟩) = M := by
  classical
  have hsum_succ :
      magSumS
          (Function.update τ.1 x
            ⟨(τ.1 x).val - 1, by omega⟩) + 1 = magSumS τ.1 := by
    unfold magSumS
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ x)]
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ x)]
    simp only [Function.update_self]
    have hrest :
        (∑ y ∈ (Finset.univ : Finset V) \ {x},
            (Function.update τ.1 x
              ⟨(τ.1 x).val - 1, by omega⟩ y).val) =
          ∑ y ∈ (Finset.univ : Finset V) \ {x}, (τ.1 y).val := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyx : y ≠ x := by
        simpa using hy
      rw [Function.update_of_ne hyx]
    rw [hrest]
    have hpred_val :
        (⟨(τ.1 x).val - 1, by
          omega⟩ : Fin (N + 1)).val + 1 = (τ.1 x).val := by
      simp
      omega
    omega
  have hτ : magSumS τ.1 = M + 1 := τ.2
  omega

/-- **Tasaki §2.5 Theorem 2.3 single-site `S^3` source weight**:
the diagonal on-site `Ŝ_x^3` action multiplies an arbitrary vector by the
local source weight `N / 2 - σ x` at configuration `σ`.

This is the local diagonal-action bridge needed to evaluate the
`Ŝ_A^3 Ŝ_¬A^3` term in the re-embedded cross-ladder identity. -/
theorem onSiteS_spinSOp3_mulVec_apply
    (x : V) (N : ℕ) (Φ : (V → Fin (N + 1)) → ℂ) (σ : V → Fin (N + 1)) :
    ((onSiteS x (spinSOp3 N) : ManyBodyOpS V N).mulVec Φ) σ =
      ((N : ℂ) / 2 - ((σ x).val : ℂ)) * Φ σ := by
  classical
  change ∑ τ, (onSiteS x (spinSOp3 N) : ManyBodyOpS V N) σ τ * Φ τ =
    ((N : ℂ) / 2 - ((σ x).val : ℂ)) * Φ σ
  rw [Finset.sum_eq_single σ]
  · rw [onSiteS_apply_diag, spinSOp3_apply_diag]
  · intro τ _hτ hτσ
    rw [onSiteS_apply]
    by_cases hoff : ∀ k, k ≠ x → σ k = τ k
    · rw [if_pos hoff]
      have hx : σ x ≠ τ x := by
        intro hxeq
        apply hτσ
        funext k
        by_cases hk : k = x
        · subst k
          exact hxeq.symm
        · exact (hoff k hk).symm
      simp [spinSOp3_apply_offdiag N hx]
    · rw [if_neg hoff, zero_mul]
  · intro hσ
    simp at hσ

/-- **Tasaki §2.5 Theorem 2.3 sublattice `S^3` source weight**:
the on-`A` sublattice `Ŝ_A^3` action multiplies an arbitrary vector by the
sum of the local `S^3` weights over sites in `A`.

This is the sublattice diagonal-action bridge used to evaluate the
right-hand side of the re-embedded cross-ladder identity at source-sector
configurations. -/
theorem sublatticeSpinSOp3_mulVec_apply_eq_onA_weight
    (A : V → Bool) (N : ℕ) (Φ : (V → Fin (N + 1)) → ℂ)
    (σ : V → Fin (N + 1)) :
    ((sublatticeSpinSOp3 N A).mulVec Φ) σ =
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        ((N : ℂ) / 2 - ((σ x).val : ℂ))) * Φ σ := by
  classical
  rw [sublatticeSpinSOp3, Matrix.sum_mulVec, Finset.sum_apply]
  calc
    (∑ c : V,
      Matrix.mulVec (if A c = true then onSiteS c (spinSOp3 N) else 0) Φ σ) =
        ∑ c : V, if A c = true then
          ((N : ℂ) / 2 - ((σ c).val : ℂ)) * Φ σ
        else 0 := by
          apply Finset.sum_congr rfl
          intro x _hx
          by_cases hA : A x = true
          · simp [hA, onSiteS_spinSOp3_mulVec_apply]
          · cases hx : A x <;> simp [hx] at hA ⊢
    _ = ∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        ((N : ℂ) / 2 - ((σ x).val : ℂ)) * Φ σ := by
          rw [Finset.sum_filter]
    _ = (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        ((N : ℂ) / 2 - ((σ x).val : ℂ))) * Φ σ := by
          rw [Finset.sum_mul]

/-- **Tasaki §2.5 Theorem 2.3 complement sublattice `S^3` source weight**:
the `Ŝ_¬A^3` action multiplies an arbitrary vector by the sum of the local
`S^3` weights over sites outside `A`.

This packages the complement sublattice with the `A x = false` filter used
by the local coefficient comparison. -/
theorem sublatticeSpinSOp3_complement_mulVec_apply_eq_offA_weight
    (A : V → Bool) (N : ℕ) (Φ : (V → Fin (N + 1)) → ℂ)
    (σ : V → Fin (N + 1)) :
    ((sublatticeSpinSOp3 N (fun x => ! A x)).mulVec Φ) σ =
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        ((N : ℂ) / 2 - ((σ x).val : ℂ))) * Φ σ := by
  classical
  rw [sublatticeSpinSOp3_mulVec_apply_eq_onA_weight]
  congr 1
  apply Finset.sum_congr
  · ext x
    cases A x <;> simp
  · intro x _hx
    rfl

/-- **Tasaki §2.5 Theorem 2.3 cross-sublattice `S^3` source weight**:
the diagonal product `Ŝ_A^3 Ŝ_¬A^3` multiplies an arbitrary vector by the
product of the on-`A` and off-`A` local `S^3` weight sums.

This is the right-hand-side evaluation bridge for the re-embedded
cross-ladder source-sector identity. -/
theorem
    sublatticeSpinSOp3_mul_complement_mulVec_apply_eq_onA_offA_weight
    (A : V → Bool) (N : ℕ) (Φ : (V → Fin (N + 1)) → ℂ)
    (σ : V → Fin (N + 1)) :
    ((sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x)).mulVec Φ) σ =
      ((∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
          ((N : ℂ) / 2 - ((σ x).val : ℂ))) *
        (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
          ((N : ℂ) / 2 - ((σ x).val : ℂ)))) * Φ σ := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinSOp3_mulVec_apply_eq_onA_weight]
  rw [sublatticeSpinSOp3_complement_mulVec_apply_eq_offA_weight]
  ring

end LatticeSystem.Quantum
