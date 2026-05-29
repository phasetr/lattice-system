import LatticeSystem.Quantum.SpinS.Magnetization

/-!
# Linear independence of non-zero vectors in distinct magnetization sectors

(PR #3900, Issue #3739): non-zero vectors in pairwise distinct magnetization
sectors are linearly independent. Direct consequence of `magSubspaceS_disjoint`
(existing) and standard linear algebra.

Key technical lemma for the sector-decomposition + reflection argument toward
Tasaki §2.5 Theorem 2.4 obligation (2.a) uniqueness: three non-zero vectors in
three distinct magnetization sectors gives `finrank ≥ 3`, contradicting
obligation (1) `finrank ≤ 2`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Submodule

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Pair LI from distinct sectors**: if `Φ₁ ∈ magSubspaceS Λ N M₁` is non-zero
and `Φ₂ ∈ magSubspaceS Λ N M₂` with `M₁ ≠ M₂`, then `Φ₁` and `Φ₂` are linearly
independent (vacuously when `Φ₂ = 0` only `Φ₁` alone is LI, but the conclusion
is `LinearIndependent` of the two-element list which would fail for `Φ₂ = 0`).
Stronger form: both must be non-zero. -/
theorem linearIndependent_pair_of_magSubspaceS_distinct
    {M₁ M₂ : ℂ} (h_ne : M₁ ≠ M₂)
    {Φ₁ Φ₂ : (Λ → Fin (N + 1)) → ℂ}
    (h₁_mem : Φ₁ ∈ magSubspaceS Λ N M₁) (hΦ₁_ne : Φ₁ ≠ 0)
    (h₂_mem : Φ₂ ∈ magSubspaceS Λ N M₂) (hΦ₂_ne : Φ₂ ≠ 0) :
    LinearIndependent ℂ ![Φ₁, Φ₂] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  -- a • Φ₁ + b • Φ₂ = 0.
  -- a • Φ₁ ∈ magSubspaceS Λ N M₁, b • Φ₂ ∈ magSubspaceS Λ N M₂.
  -- a • Φ₁ = -b • Φ₂. By disjoint, both sides are 0.
  have h_aΦ₁ : a • Φ₁ ∈ magSubspaceS Λ N M₁ := (magSubspaceS Λ N M₁).smul_mem a h₁_mem
  have h_bΦ₂ : b • Φ₂ ∈ magSubspaceS Λ N M₂ := (magSubspaceS Λ N M₂).smul_mem b h₂_mem
  have h_neg : a • Φ₁ = -(b • Φ₂) := eq_neg_of_add_eq_zero_left hab
  have h_neg_mem : a • Φ₁ ∈ magSubspaceS Λ N M₂ := by
    rw [h_neg]
    exact (magSubspaceS Λ N M₂).neg_mem h_bΦ₂
  -- By disjoint, a • Φ₁ ∈ M₁ ∩ M₂ ⊆ ⊥.
  have h_inter : a • Φ₁ ∈ magSubspaceS Λ N M₁ ⊓ magSubspaceS Λ N M₂ :=
    ⟨h_aΦ₁, h_neg_mem⟩
  have h_disj := magSubspaceS_disjoint (Λ := Λ) (N := N) h_ne
  rw [Submodule.disjoint_def] at h_disj
  have h_aΦ₁_zero : a • Φ₁ = 0 := h_disj _ h_aΦ₁ h_neg_mem
  have ha : a = 0 := (smul_eq_zero.mp h_aΦ₁_zero).resolve_right hΦ₁_ne
  have h_bΦ₂_zero : b • Φ₂ = 0 := by
    have h := hab
    rw [ha, zero_smul, zero_add] at h
    exact h
  have hb : b = 0 := (smul_eq_zero.mp h_bΦ₂_zero).resolve_right hΦ₂_ne
  exact ⟨ha, hb⟩

end LatticeSystem.Quantum
