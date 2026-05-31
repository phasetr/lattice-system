import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergPerMStrictGapBelowFirstCrossing
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergBalancedIsGSAtSU2
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergBalancedGSSetClosed
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergBalancedGSSetZeroMem

/-!
# Balanced IS GS at `γ(t_first_M_chosen)` via closure argument

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) first-crossing argument.

Conditional brick: given an `M_chosen ≠ M_balanced` (non-empty) that is the
argmin of per-`M` first crossings (i.e., for all other `M' ≠ M_balanced`,
`t_first_M' ≥ t_first_M_chosen`), and additionally the strict-GS axiom at
`(1, 0)` (= `0 ∈ balancedGSSet`), the balanced sector IS the GS at
`γ(t_first_M_chosen)`.

Proof: `[0, t_first_M_chosen) ⊆ balancedGSSet` (using strict gap below first
crossing + PR #3990 + the path-stays-in-region). At `t = 0`, balanced IS GS
by hypothesis. The closure `[0, t_first_M_chosen] = closure (Ico ...) ⊆
closure balancedGSSet = balancedGSSet` (since balancedGSSet closed,
PR #3983).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Balanced IS GS at `γ(t_first_M_chosen)` from closure argument**: under
the strict-GS axiom at `(1, 0)` + the path-wide strict gap below the per-`M`
first crossing (supplied as a hypothesis), the balanced sector IS the GS at
the first-crossing point. -/
theorem balanced_GS_at_first_crossing_of_argmin
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced M_chosen : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (magConfigS Λ N M_chosen)]
    [Nonempty (Λ → Fin (N + 1))]
    (lam' D' : ℝ)
    (hne_chosen :
      (perMCrossingSet (Λ := Λ) hJ N M_balanced M_chosen lam' D' ∩ Icc (0 : ℝ) 1).Nonempty)
    -- Strict-GS axiom at (1, 0).
    (h_GS_at_SU2 :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ N M_balanced lam' D' 0 =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N
          (anisotropicHeisenbergParametricPath lam' D' 0).1
          (anisotropicHeisenbergParametricPath lam' D' 0).2))
    -- Path-wide "below first crossing" strict gap (supplied; eventually from per-M sup analysis).
    (h_balanced_GS_below : ∀ t' : ℝ, t' ∈ Ico (0 : ℝ)
        (sInf (perMCrossingSet (Λ := Λ) hJ N M_balanced M_chosen lam' D' ∩ Icc (0 : ℝ) 1)) →
      t' ∈ balancedGSSet (Λ := Λ) hJ N M_balanced lam' D') :
    sInf (perMCrossingSet (Λ := Λ) hJ N M_balanced M_chosen lam' D' ∩ Icc (0 : ℝ) 1) ∈
      balancedGSSet (Λ := Λ) hJ N M_balanced lam' D' := by
  set t_first := sInf (perMCrossingSet (Λ := Λ) hJ N M_balanced M_chosen lam' D' ∩ Icc (0 : ℝ) 1)
    with ht_first_def
  -- 0 ≤ t_first.
  have h_t_first_nn : (0 : ℝ) ≤ t_first := by
    apply le_csInf hne_chosen
    intro x hx
    exact hx.2.1
  -- balancedGSSet is closed (PR #3983).
  have h_closed := isClosed_balancedGSSet (Λ := Λ) hJ N M_balanced lam' D'
  -- Ico 0 t_first ⊆ balancedGSSet by hypothesis.
  -- closure (Ico 0 t_first) ⊆ closure balancedGSSet = balancedGSSet.
  -- t_first ∈ Icc 0 t_first = closure (Ico 0 t_first) (when 0 ≤ t_first).
  rcases eq_or_lt_of_le h_t_first_nn with h_zero | h_pos
  · -- t_first = 0: directly from h_GS_at_SU2.
    rw [← h_zero]
    exact zero_mem_balancedGSSet_of_strict_GS_at_SU2 hJ N M_balanced lam' D' h_GS_at_SU2
  · -- 0 < t_first. Use closure of Ico.
    have h_subset : Ico (0 : ℝ) t_first ⊆ balancedGSSet (Λ := Λ) hJ N M_balanced lam' D' :=
      h_balanced_GS_below
    have h_closure_Ico : closure (Ico (0 : ℝ) t_first) = Icc (0 : ℝ) t_first := by
      exact closure_Ico (ne_of_lt h_pos)
    have h_t_first_in_closure : t_first ∈ closure (Ico (0 : ℝ) t_first) := by
      rw [h_closure_Ico]
      exact right_mem_Icc.mpr h_t_first_nn
    have h_closure_subset : closure (Ico (0 : ℝ) t_first) ⊆
        balancedGSSet (Λ := Λ) hJ N M_balanced lam' D' := by
      rw [show balancedGSSet (Λ := Λ) hJ N M_balanced lam' D' =
            closure (balancedGSSet (Λ := Λ) hJ N M_balanced lam' D') from h_closed.closure_eq.symm]
      exact closure_mono h_subset
    exact h_closure_subset h_t_first_in_closure

end LatticeSystem.Quantum
