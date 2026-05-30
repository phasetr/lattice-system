import LatticeSystem.Quantum.SpinS.MagParityEigenspaceDecomp

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Eigenspace finrank decomposition under a commuting involution: equality version

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(h.2): strengthens `eigenspace_finrank_le_of_commuting_involution` (#3776) from `≤` to `=`.
The `≤` is tight because the two intersected `±1` eigenspaces of the involution `P` are
disjoint (a single eigenvector cannot have two distinct `P`-eigenvalues), so
`Submodule.finrank_sup_add_finrank_inf_eq` collapses to a sum (the inf contributes 0).

This is one of two ingredients for the unconditional ground-state degeneracy ≤ 2 (the other
being the per-parity-block submatrix finrank equality from (h.1) #3840 ⟶ for the full
block-diagonal Hamiltonian, `finrank ℂ (eig M μ) = ∑_p finrank ℂ (eig M.submatrix_p μ)`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Module Matrix

/-- **The ±1 eigenspaces of an involution are disjoint.** -/
private theorem eigenspace_one_inf_neg_one_eq_bot
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (P : V →ₗ[ℂ] V) :
    End.eigenspace P 1 ⊓ End.eigenspace P (-1) = ⊥ := by
  refine le_bot_iff.mp ?_
  intro v hv
  simp only [Submodule.mem_inf, End.mem_eigenspace_iff, one_smul, neg_smul] at hv
  obtain ⟨h1, hm1⟩ := hv
  -- P v = v AND P v = -v ⟹ v = -v ⟹ 2 v = 0 ⟹ v = 0.
  have hvv : v = -v := h1.symm.trans hm1
  have h2v : (2 : ℂ) • v = 0 := by
    rw [two_smul]
    nth_rw 1 [hvv]
    exact neg_add_cancel v
  have hv0 : v = 0 := by
    have h_two_ne : (2 : ℂ) ≠ 0 := by norm_num
    exact (smul_eq_zero.mp h2v).resolve_left h_two_ne
  rw [hv0]
  exact Submodule.zero_mem _

/-- **Eigenspace finrank EQUALITY under a commuting involution** (strengthens #3776 from `≤` to `=`):
for finite-dimensional `T, P` with `T ∘ P = P ∘ T` and `P ∘ P = id`, every `T`-eigenspace
**splits as a direct sum** across the two `P`-eigenspaces `±1`, giving
`finrank (eigenspace T μ) = finrank (eigenspace T μ ⊓ eigenspace P 1) + finrank (eigenspace T μ ⊓ eigenspace P (−1))`. -/
theorem eigenspace_finrank_eq_of_commuting_involution
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T P : V →ₗ[ℂ] V) (hcomm : T ∘ₗ P = P ∘ₗ T) (hP : P ∘ₗ P = LinearMap.id) (μ : ℂ) :
    finrank ℂ (End.eigenspace T μ) =
      finrank ℂ ↥(End.eigenspace T μ ⊓ End.eigenspace P 1) +
        finrank ℂ ↥(End.eigenspace T μ ⊓ End.eigenspace P (-1)) := by
  set W := End.eigenspace T μ
  -- Proof same as the ≤ version: W = (W ⊓ E₁) ⊔ (W ⊓ E_-1) and the inf is bot.
  have hPP : ∀ w : V, P (P w) = w := fun w => by
    have := congrArg (fun f => f w) hP; simpa using this
  have hsplit : ∀ w ∈ W, w ∈ (W ⊓ End.eigenspace P 1) ⊔ (W ⊓ End.eigenspace P (-1)) := by
    intro w hw
    have hWinv : P w ∈ W := by
      rw [End.mem_eigenspace_iff] at hw ⊢
      have hTP : T (P w) = P (T w) := by
        rw [← LinearMap.comp_apply, hcomm, LinearMap.comp_apply]
      rw [hTP, hw, map_smul]
    have hdecomp : w = ((2 : ℂ)⁻¹ • (w + P w)) + ((2 : ℂ)⁻¹ • (w - P w)) := by
      rw [smul_add, smul_sub]; module
    rw [hdecomp]
    apply Submodule.add_mem_sup
    · refine Submodule.mem_inf.mpr ⟨W.smul_mem _ (W.add_mem hw hWinv), ?_⟩
      rw [End.mem_eigenspace_iff, map_smul, map_add, hPP, one_smul]; module
    · refine Submodule.mem_inf.mpr ⟨W.smul_mem _ (W.sub_mem hw hWinv), ?_⟩
      rw [End.mem_eigenspace_iff, map_smul, map_sub, hPP]; module
  have hle : W ≤ (W ⊓ End.eigenspace P 1) ⊔ (W ⊓ End.eigenspace P (-1)) := hsplit
  have hge : (W ⊓ End.eigenspace P 1) ⊔ (W ⊓ End.eigenspace P (-1)) ≤ W := by
    exact sup_le inf_le_left inf_le_left
  have heq : W = (W ⊓ End.eigenspace P 1) ⊔ (W ⊓ End.eigenspace P (-1)) := le_antisymm hle hge
  conv_lhs => rw [heq]
  -- Now apply Submodule.finrank_sup_add_finrank_inf_eq, with the inner inf = 0.
  have hinf_bot : (W ⊓ End.eigenspace P 1) ⊓ (W ⊓ End.eigenspace P (-1)) = ⊥ :=
    le_antisymm
      (fun v hv => by
        simp only [Submodule.mem_inf] at hv
        have : v ∈ End.eigenspace P 1 ⊓ End.eigenspace P (-1) :=
          Submodule.mem_inf.mpr ⟨hv.1.2, hv.2.2⟩
        rw [eigenspace_one_inf_neg_one_eq_bot P] at this
        exact this)
      bot_le
  have hsum_eq := Submodule.finrank_sup_add_finrank_inf_eq
    (W ⊓ End.eigenspace P 1) (W ⊓ End.eigenspace P (-1))
  rw [hinf_bot, finrank_bot] at hsum_eq
  omega

end LatticeSystem.Quantum
