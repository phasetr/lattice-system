import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergPerMStrictGapBelowFirstCrossing
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergParametricMinEigenvalueTotal

/-!
# Argmin extraction: `∃ M_chosen` minimising per-`M` first crossings

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) first-crossing argument.

Discharges the "argmin property" axiom of capstone v4 (PR #4004) via Finset
iteration: from the violation hypothesis at any sector `M_orig`, extract an
argmin `M_chosen` minimising `sInf (perMCrossingSet ∩ Icc 0 1)` over all
valid `M` (non-empty, `≠ M_balanced`, with non-empty crossing set).

Uses `Finset.exists_min_image` on the (classically decidable) filter Finset
over `Finset.range (|Λ|·N + 1)`, evaluated on the **total** version of the
parametric min eigenvalue (PR #4006) to avoid instance-dependent gates.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Total perMCrossingSet**: set of `t` where `E_M ≤ E_balanced` (using total
def, so no `[Nonempty]` required). On non-empty `M` and `M_balanced`, agrees
with `perMCrossingSet`. -/
noncomputable def perMCrossingSet_total
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced M : ℕ) (lam' D' : ℝ) : Set ℝ :=
  { t : ℝ |
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath_total
      (Λ := Λ) hJ N M lam' D' t ≤
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath_total
      (Λ := Λ) hJ N M_balanced lam' D' t }

/-- Agreement of `perMCrossingSet_total` with `perMCrossingSet` on non-empty sectors. -/
theorem perMCrossingSet_total_eq_perMCrossingSet
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced M : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (magConfigS Λ N M)]
    (lam' D' : ℝ) :
    perMCrossingSet_total (Λ := Λ) hJ N M_balanced M lam' D' =
    perMCrossingSet (Λ := Λ) hJ N M_balanced M lam' D' := by
  unfold perMCrossingSet_total perMCrossingSet
  congr 1
  funext t
  rw [anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath_total_eq,
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath_total_eq]

/-- **Argmin extraction**: given any violation `M_orig`, there is `M_chosen`
with the argmin property over the **total** crossing set (and which is itself
non-empty + `≠ M_balanced` + has non-empty crossing set in `Icc 0 1`). -/
theorem exists_M_chosen_argmin_per_M_first_crossing
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced M_orig : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (magConfigS Λ N M_orig)]
    (hM_orig_ne : M_orig ≠ M_balanced)
    (lam' D' : ℝ)
    (hne_orig :
      (perMCrossingSet (Λ := Λ) hJ N M_balanced M_orig lam' D' ∩ Icc (0 : ℝ) 1).Nonempty) :
    ∃ M_chosen : ℕ,
      M_chosen ∈ Finset.range (Fintype.card Λ * N + 1) ∧
      M_chosen ≠ M_balanced ∧
      Nonempty (magConfigS Λ N M_chosen) ∧
      (perMCrossingSet_total (Λ := Λ) hJ N M_balanced M_chosen lam' D' ∩
        Icc (0 : ℝ) 1).Nonempty ∧
      ∀ M' ∈ Finset.range (Fintype.card Λ * N + 1), M' ≠ M_balanced →
        Nonempty (magConfigS Λ N M') →
        (perMCrossingSet_total (Λ := Λ) hJ N M_balanced M' lam' D' ∩
          Icc (0 : ℝ) 1).Nonempty →
        sInf (perMCrossingSet_total (Λ := Λ) hJ N M_balanced M_chosen lam' D' ∩
          Icc (0 : ℝ) 1) ≤
        sInf (perMCrossingSet_total (Λ := Λ) hJ N M_balanced M' lam' D' ∩
          Icc (0 : ℝ) 1) := by
  classical
  -- Build the Finset.
  set S : Finset ℕ := (Finset.range (Fintype.card Λ * N + 1)).filter
    (fun M => M ≠ M_balanced ∧ Nonempty (magConfigS Λ N M) ∧
      (perMCrossingSet_total (Λ := Λ) hJ N M_balanced M lam' D' ∩ Icc (0 : ℝ) 1).Nonempty)
    with hS_def
  -- M_orig ∈ S.
  have hM_orig_in : M_orig ∈ S := by
    rw [hS_def]
    refine Finset.mem_filter.mpr ⟨?_, hM_orig_ne, inferInstance, ?_⟩
    · rw [Finset.mem_range]
      have h_NE : Nonempty (magConfigS Λ N M_orig) := inferInstance
      obtain ⟨σ⟩ := h_NE
      have hbound := magSumS_le σ.val
      rw [σ.property] at hbound
      exact Nat.lt_succ_of_le hbound
    · rw [perMCrossingSet_total_eq_perMCrossingSet]; exact hne_orig
  -- S is non-empty.
  have hS_ne : S.Nonempty := ⟨M_orig, hM_orig_in⟩
  -- Apply Finset.exists_min_image.
  obtain ⟨M_chosen, hM_chosen_in, h_argmin⟩ :=
    Finset.exists_min_image S
      (fun M => sInf (perMCrossingSet_total (Λ := Λ) hJ N M_balanced M lam' D' ∩
        Icc (0 : ℝ) 1))
      hS_ne
  rw [hS_def] at hM_chosen_in
  rw [Finset.mem_filter] at hM_chosen_in
  obtain ⟨hM_chosen_range, h_ne_bal, h_NE_chosen, h_cross_chosen⟩ := hM_chosen_in
  refine ⟨M_chosen, hM_chosen_range, h_ne_bal, h_NE_chosen, h_cross_chosen, ?_⟩
  intro M' hM'_range h_ne_bal_M' h_NE_M' h_cross_M'
  have hM'_in : M' ∈ S := by
    rw [hS_def]
    exact Finset.mem_filter.mpr ⟨hM'_range, h_ne_bal_M', h_NE_M', h_cross_M'⟩
  exact h_argmin M' hM'_in

end LatticeSystem.Quantum
