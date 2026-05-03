import LatticeSystem.Quantum.SpinS.MagConfigExtremalCardinality
import LatticeSystem.Quantum.SpinS.AllAlignedState
import LatticeSystem.Quantum.SpinS.LadderBoundaryAnnihilation

/-!
# The two extremal magnetization subspaces are 1-dimensional

For `[Nonempty V]`, the magnetization subspace `magSubspaceS V N (m_max)`
(highest weight) and `magSubspaceS V N (-m_max)` (lowest weight) are
each spanned by a single vector — `|σ_⊤⟩` and `|σ_⊥⟩` respectively.

This is the analytic counterpart of PR #885's combinatorial fact
`magConfigS_card_zero / _last = 1`, lifted to subspaces of the
multi-site Hilbert space via `Ŝ^z_tot` diagonality in the `basisVecS`
basis.

The argument: `Ŝ^z_tot` is diagonal in the `basisVecS` basis with
eigenvalue `magEigenvalueS σ` at configuration `σ`. The eigenvalue
`m_max` is achieved only at `σ = allAlignedConfigS V N 0` (and
similarly `−m_max` at `Fin.last N`). The pointwise eigenvalue
equation forces all `v(σ)` to vanish except at the unique
extremal configuration.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Eigenvalue characterisation of the extremal configurations -/

/-- `magEigenvalueS σ = m_max` iff `σ = allAlignedConfigS V N 0`. -/
theorem magEigenvalueS_eq_mMax_iff_allAlignedConfigS_zero
    (σ : V → Fin (N + 1)) :
    magEigenvalueS σ = (Fintype.card V : ℂ) * (N : ℂ) / 2 ↔
      σ = allAlignedConfigS V N 0 := by
  constructor
  · intro h
    -- magEigenvalueS σ = (|V|·N : ℂ)/2 − magSumS σ = (|V|·N)/2 ⇒ magSumS σ = 0.
    have h1 : (magSumS σ : ℂ) = 0 := by
      unfold magEigenvalueS at h
      linear_combination -h
    have h2 : magSumS σ = 0 := by exact_mod_cast h1
    -- magSumS σ = 0 ⇒ each (σ x).val = 0 ⇒ σ x = 0 ⇒ σ = const 0.
    funext x
    have hsum_pos : ∀ y, 0 ≤ (σ y).val := fun y => Nat.zero_le _
    have hx_zero : (σ x).val = 0 := by
      unfold magSumS at h2
      have := Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset V))
        (f := fun y => (σ y).val) (fun y _ => hsum_pos y) |>.mp h2
      exact this x (Finset.mem_univ _)
    apply Fin.ext
    rw [hx_zero]; rfl
  · intro h
    rw [h, magEigenvalueS_allAlignedConfigS]
    rw [show ((0 : Fin (N + 1)).val : ℂ) = 0 from by simp]
    push_cast; ring

/-- `magEigenvalueS σ = −m_max` iff `σ = allAlignedConfigS V N (Fin.last N)`. -/
theorem magEigenvalueS_eq_neg_mMax_iff_allAlignedConfigS_last
    (σ : V → Fin (N + 1)) :
    magEigenvalueS σ = -((Fintype.card V : ℂ) * (N : ℂ) / 2) ↔
      σ = allAlignedConfigS V N (Fin.last N) := by
  constructor
  · intro h
    -- magEigenvalueS σ = (|V|·N : ℂ)/2 − magSumS σ = −(|V|·N)/2 ⇒ magSumS σ = |V|·N.
    have h1 : (magSumS σ : ℂ) = (Fintype.card V * N : ℕ) := by
      unfold magEigenvalueS at h
      push_cast
      linear_combination -h
    have h2 : magSumS σ = Fintype.card V * N := by exact_mod_cast h1
    -- magSumS σ = |V|·N maximal ⇒ each (σ x).val = N ⇒ σ x = Fin.last N.
    funext x
    have hUpper : ∀ y, (σ y).val ≤ N := fun y => Nat.lt_succ_iff.mp (σ y).isLt
    have h_eq : ∀ y, (σ y).val = N := by
      intro y
      have hsum_eq : ∑ z : V, (σ z).val = ∑ _ : V, N := by
        unfold magSumS at h2
        rw [h2, Finset.sum_const, Finset.card_univ, smul_eq_mul]
      have hle : ∀ z ∈ (Finset.univ : Finset V), (σ z).val ≤ N := fun z _ => hUpper z
      have h_pointwise := Finset.sum_eq_sum_iff_of_le hle |>.mp hsum_eq
      exact h_pointwise y (Finset.mem_univ y)
    apply Fin.ext
    rw [h_eq x]; rfl
  · intro h
    rw [h, magEigenvalueS_allAlignedConfigS]
    rw [show ((Fin.last N).val : ℂ) = (N : ℂ) from by simp [Fin.last]]
    push_cast; ring

/-! ## Magnetization subspace at the extremal eigenvalues -/

/-- `magSubspaceS V N m_max ≤ Submodule.span ℂ {|σ_⊤⟩}`. -/
theorem magSubspaceS_mMax_le_span_allAlignedStateS_zero :
    magSubspaceS V N ((Fintype.card V : ℂ) * (N : ℂ) / 2) ≤
      Submodule.span ℂ {(allAlignedStateS V N (0 : Fin (N + 1)) :
        (V → Fin (N + 1)) → ℂ)} := by
  intro v hv
  rw [mem_magSubspaceS_iff] at hv
  rw [Submodule.mem_span_singleton]
  refine ⟨v (allAlignedConfigS V N 0), ?_⟩
  -- Show v = v(σ_⊤) • basisVecS σ_⊤.
  funext τ
  -- Evaluate hv at τ to get magEigenvalueS τ · v τ = m_max · v τ.
  have hτ_lhs : (totalSpinSOp3 V N).mulVec v τ = magEigenvalueS τ * v τ := by
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single τ]
    · rw [totalSpinSOp3_apply_diag]
    · intros σ _ hστ
      rw [totalSpinSOp3_apply_off_diag (Ne.symm hστ), zero_mul]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  have hτ_rhs : (((Fintype.card V : ℂ) * (N : ℂ) / 2) • v) τ =
      (Fintype.card V : ℂ) * (N : ℂ) / 2 * v τ := by
    simp [Pi.smul_apply, smul_eq_mul]
  have hτ_eq : magEigenvalueS τ * v τ =
      ((Fintype.card V : ℂ) * (N : ℂ) / 2) * v τ := by
    rw [← hτ_lhs, hv, hτ_rhs]
  have hsub : (magEigenvalueS τ - (Fintype.card V : ℂ) * (N : ℂ) / 2) * v τ = 0 := by
    rw [sub_mul, hτ_eq, sub_self]
  by_cases hτeq : τ = allAlignedConfigS V N 0
  · -- τ = σ_⊤ : RHS is v(σ_⊤) • basisVecS σ_⊤ τ = v(σ_⊤) · 1 = v(σ_⊤).
    rw [hτeq]
    unfold allAlignedStateS
    simp [Pi.smul_apply, basisVecS_self, smul_eq_mul]
  · have hne : magEigenvalueS τ ≠ (Fintype.card V : ℂ) * (N : ℂ) / 2 := by
      intro hh
      exact hτeq ((magEigenvalueS_eq_mMax_iff_allAlignedConfigS_zero τ).mp hh)
    have hτv : v τ = 0 := by
      have hne' : magEigenvalueS τ - (Fintype.card V : ℂ) * (N : ℂ) / 2 ≠ 0 :=
        sub_ne_zero.mpr hne
      exact (mul_eq_zero.mp hsub).resolve_left hne'
    rw [hτv]
    -- RHS: v(σ_⊤) · basisVecS σ_⊤ τ = v(σ_⊤) · 0 = 0.
    unfold allAlignedStateS
    simp [Pi.smul_apply, basisVecS_of_ne hτeq, smul_eq_mul]

/-- The reverse inclusion: `Submodule.span ℂ {|σ_⊤⟩} ≤ magSubspaceS V N m_max`. -/
theorem span_allAlignedStateS_zero_le_magSubspaceS_mMax :
    Submodule.span ℂ {(allAlignedStateS V N (0 : Fin (N + 1)) :
      (V → Fin (N + 1)) → ℂ)} ≤
      magSubspaceS V N ((Fintype.card V : ℂ) * (N : ℂ) / 2) := by
  rw [Submodule.span_le]
  rintro v rfl
  rw [SetLike.mem_coe, mem_magSubspaceS_iff]
  rw [totalSpinSOp3_mulVec_allAlignedStateS, magEigenvalueS_allAlignedConfigS]
  rw [show ((0 : Fin (N + 1)).val : ℂ) = 0 from by simp]
  push_cast; ring_nf

/-- **`magSubspaceS V N m_max` is exactly the line through `|σ_⊤⟩`**. -/
theorem magSubspaceS_mMax_eq_span_allAlignedStateS_zero :
    magSubspaceS V N ((Fintype.card V : ℂ) * (N : ℂ) / 2) =
      Submodule.span ℂ {(allAlignedStateS V N (0 : Fin (N + 1)) :
        (V → Fin (N + 1)) → ℂ)} :=
  le_antisymm magSubspaceS_mMax_le_span_allAlignedStateS_zero
    span_allAlignedStateS_zero_le_magSubspaceS_mMax

/-- Symmetric: `magSubspaceS V N (-m_max) ≤ Submodule.span ℂ {|σ_⊥⟩}`. -/
theorem magSubspaceS_neg_mMax_le_span_allAlignedStateS_last :
    magSubspaceS V N (-((Fintype.card V : ℂ) * (N : ℂ) / 2)) ≤
      Submodule.span ℂ {(allAlignedStateS V N (Fin.last N) :
        (V → Fin (N + 1)) → ℂ)} := by
  intro v hv
  rw [mem_magSubspaceS_iff] at hv
  rw [Submodule.mem_span_singleton]
  refine ⟨v (allAlignedConfigS V N (Fin.last N)), ?_⟩
  funext τ
  have hτ_lhs : (totalSpinSOp3 V N).mulVec v τ = magEigenvalueS τ * v τ := by
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single τ]
    · rw [totalSpinSOp3_apply_diag]
    · intros σ _ hστ
      rw [totalSpinSOp3_apply_off_diag (Ne.symm hστ), zero_mul]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  have hτ_rhs : ((-((Fintype.card V : ℂ) * (N : ℂ) / 2)) • v) τ =
      -((Fintype.card V : ℂ) * (N : ℂ) / 2) * v τ := by
    simp [Pi.smul_apply, smul_eq_mul]
  have hτ_eq : magEigenvalueS τ * v τ =
      (-((Fintype.card V : ℂ) * (N : ℂ) / 2)) * v τ := by
    rw [← hτ_lhs, hv, hτ_rhs]
  have hsub : (magEigenvalueS τ - (-((Fintype.card V : ℂ) * (N : ℂ) / 2))) * v τ = 0 := by
    rw [sub_mul, hτ_eq, sub_self]
  by_cases hτeq : τ = allAlignedConfigS V N (Fin.last N)
  · rw [hτeq]
    unfold allAlignedStateS
    simp [Pi.smul_apply, basisVecS_self, smul_eq_mul]
  · have hne : magEigenvalueS τ ≠ -((Fintype.card V : ℂ) * (N : ℂ) / 2) := by
      intro hh
      exact hτeq
        ((magEigenvalueS_eq_neg_mMax_iff_allAlignedConfigS_last τ).mp hh)
    have hτv : v τ = 0 := by
      have hne' : magEigenvalueS τ - (-((Fintype.card V : ℂ) * (N : ℂ) / 2)) ≠ 0 :=
        sub_ne_zero.mpr hne
      exact (mul_eq_zero.mp hsub).resolve_left hne'
    rw [hτv]
    unfold allAlignedStateS
    simp [Pi.smul_apply, basisVecS_of_ne hτeq, smul_eq_mul]

/-- Symmetric reverse inclusion: `Submodule.span ℂ {|σ_⊥⟩} ≤
magSubspaceS V N (-m_max)`. -/
theorem span_allAlignedStateS_last_le_magSubspaceS_neg_mMax :
    Submodule.span ℂ {(allAlignedStateS V N (Fin.last N) :
      (V → Fin (N + 1)) → ℂ)} ≤
      magSubspaceS V N (-((Fintype.card V : ℂ) * (N : ℂ) / 2)) := by
  rw [Submodule.span_le]
  rintro v rfl
  rw [SetLike.mem_coe, mem_magSubspaceS_iff]
  rw [totalSpinSOp3_mulVec_allAlignedStateS, magEigenvalueS_allAlignedConfigS]
  rw [show ((Fin.last N).val : ℂ) = (N : ℂ) from by simp [Fin.last]]
  push_cast; ring_nf

/-- **`magSubspaceS V N (-m_max)` is exactly the line through `|σ_⊥⟩`**. -/
theorem magSubspaceS_neg_mMax_eq_span_allAlignedStateS_last :
    magSubspaceS V N (-((Fintype.card V : ℂ) * (N : ℂ) / 2)) =
      Submodule.span ℂ {(allAlignedStateS V N (Fin.last N) :
        (V → Fin (N + 1)) → ℂ)} :=
  le_antisymm magSubspaceS_neg_mMax_le_span_allAlignedStateS_last
    span_allAlignedStateS_last_le_magSubspaceS_neg_mMax

end LatticeSystem.Quantum
