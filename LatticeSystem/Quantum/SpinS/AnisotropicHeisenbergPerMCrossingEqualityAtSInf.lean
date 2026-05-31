import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergPerMStrictGapBelowFirstCrossing

/-!
# Per-`M` crossing equality holds at `sInf`

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) first-crossing argument.

For the per-`M` crossing set `perMCrossingSet M`, the `sInf` (intersected with
`Icc 0 1`) satisfies the **crossing equality** `E_M(γ(sInf)) = E_balanced(γ(sInf))`.

The crossing membership `E_M ≤ E_balanced` is from PR #3994 (sInf ∈ set).
The reverse `E_M ≥ E_balanced` comes from the strict-gap-below-sInf (PR #3995):
take a sequence `t_n ↑ sInf` (strict gap holds for each), pass to limit via
continuity (PR #3957), get `E_M(γ(sInf)) ≥ E_balanced(γ(sInf))`. Combined with
PR #3994's `≤` gives equality.

This is the "first crossing is a crossing equality" lemma.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Set Filter Topology

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Per-`M` crossing equality at `sInf`**: `E_M(γ(sInf)) = E_balanced(γ(sInf))`
where `sInf := sInf (perMCrossingSet M ∩ Icc 0 1)`. -/
theorem anisotropicHeisenbergS_per_M_crossing_equality_at_sInf
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced M : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (magConfigS Λ N M)]
    (lam' D' : ℝ)
    (hne : (perMCrossingSet (Λ := Λ) hJ N M_balanced M lam' D' ∩ Icc (0 : ℝ) 1).Nonempty)
    -- Strict gap at (1, 0) ⟹ t_first > 0 (rules out the degenerate t_first = 0 case).
    (h_strict_gap_SU2 :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ N M_balanced lam' D' 0 <
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ N M lam' D' 0) :
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ N M lam' D'
        (sInf (perMCrossingSet (Λ := Λ) hJ N M_balanced M lam' D' ∩ Icc (0 : ℝ) 1)) =
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ N M_balanced lam' D'
        (sInf (perMCrossingSet (Λ := Λ) hJ N M_balanced M lam' D' ∩ Icc (0 : ℝ) 1)) := by
  set t_first := sInf (perMCrossingSet (Λ := Λ) hJ N M_balanced M lam' D' ∩ Icc (0 : ℝ) 1)
    with ht_first_def
  -- ≤: from sInf ∈ set (PR #3994).
  have h_le : anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ N M lam' D' t_first ≤
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ N M_balanced lam' D' t_first := by
    have hmem := sInf_perMCrossingSet_inter_Icc_mem hJ N M_balanced M lam' D' hne
    exact hmem.1
  -- ≥: from continuity + strict gap below.
  -- For t_n ↑ t_first, strict gap: E_balanced(γ(t_n)) < E_M(γ(t_n)).
  -- By continuity (PR #3957), passing to limit: E_balanced(γ(t_first)) ≤ E_M(γ(t_first)).
  have h_ge : anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ N M_balanced lam' D' t_first ≤
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ N M lam' D' t_first := by
    -- Continuous functions.
    have hf_cont := continuous_anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ N M_balanced lam' D'
    have hg_cont := continuous_anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ N M lam' D'
    -- The set { t | f(t) ≤ g(t) } is closed. t_first is a limit of points in the strict open set
    -- { t | f(t) < g(t) }. By continuity, f(t_first) ≤ g(t_first).
    -- More directly: use `le_of_tendsto'` or the closure argument.
    -- We use: for each ε > 0, ∃ t' < t_first with t' ∈ Icc 0 1 and strict gap at t'.
    -- Actually, simpler: { t | f(t) ≤ g(t) } is closed (isClosed_le). For t_first to be in it,
    -- show t_first ∈ closure { t | strict gap at t }.
    -- Even simpler: use that the strict-gap-below holds on [0, t_first), and take limit.
    -- Use IsClosed.mem_of_tendsto or the direct: filter argument with sub-sequence.
    -- Cleanest: { t | f(t) ≤ g(t) } is closed; show t_first is a limit point of this set
    -- from below.
    -- From PR #3995, [0, t_first) ⊆ { t | f(t) < g(t) } ⊆ { t | f(t) ≤ g(t) }.
    -- Hence closure ([0, t_first)) ⊆ closure { f ≤ g } = { f ≤ g }.
    -- t_first ∈ closure ([0, t_first)) IF t_first > 0; else t_first = 0 and we handle directly.
    have h_t_first_nn : (0 : ℝ) ≤ t_first := by
      apply le_csInf hne
      intro x hx; exact hx.2.1
    rcases eq_or_lt_of_le h_t_first_nn with h_eq | h_pos
    · -- t_first = 0: contradicts strict gap at (1, 0).
      -- h_le says E_M(γ(0)) ≤ E_balanced(γ(0)), but strict gap says E_balanced(γ(0)) < E_M(γ(0)).
      exfalso
      rw [← h_eq] at h_le
      linarith
    · -- 0 < t_first. Use closure of { f ≤ g } and [0, t_first) ⊆ { f ≤ g } (≤ via strict <).
      have h_closed_le : IsClosed { t : ℝ |
          anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
            (Λ := Λ) hJ N M_balanced lam' D' t ≤
          anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
            (Λ := Λ) hJ N M lam' D' t } := isClosed_le hf_cont hg_cont
      have h_t_first_le_1 : t_first ≤ 1 := by
        obtain ⟨x, hx⟩ := hne
        exact le_trans (csInf_le
          (bddBelow_perMCrossingSet_inter_Icc hJ N M_balanced M lam' D') hx) hx.2.2
      have h_subset : Ico (0 : ℝ) t_first ⊆ { t : ℝ |
          anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
            (Λ := Λ) hJ N M_balanced lam' D' t ≤
          anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
            (Λ := Λ) hJ N M lam' D' t } := by
        intro t' ht'_mem
        have ht'_mem_Icc : t' ∈ Icc (0 : ℝ) 1 :=
          ⟨ht'_mem.1, le_trans (le_of_lt ht'_mem.2) h_t_first_le_1⟩
        have h_strict := strict_per_M_gap_of_lt_sInf_perMCrossingSet
          hJ N M_balanced M lam' D' hne ht'_mem_Icc ht'_mem.2
        exact le_of_lt h_strict
      have h_t_first_mem_closure :
          t_first ∈ closure (Ico (0 : ℝ) t_first) := by
        rw [closure_Ico (ne_of_lt h_pos)]
        exact right_mem_Icc.mpr h_t_first_nn
      have h_closure_sub : closure (Ico (0 : ℝ) t_first) ⊆
          { t : ℝ |
            anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
              (Λ := Λ) hJ N M_balanced lam' D' t ≤
            anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
              (Λ := Λ) hJ N M lam' D' t } := by
        rw [show { t : ℝ | _ ≤ _ } = closure { t : ℝ | _ ≤ _ } from h_closed_le.closure_eq.symm]
        exact closure_mono h_subset
      exact h_closure_sub h_t_first_mem_closure
  exact le_antisymm h_le h_ge

end LatticeSystem.Quantum
