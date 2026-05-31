import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergPerMCrossingSInfMem

/-!
# Strict per-`M` gap holds below the first crossing

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) first-crossing argument.

For per-`M` crossing set, `t < sInf (perMCrossingSet M ∩ Icc 0 1)` (within `Icc 0 1`)
implies the strict gap `E_M(γ(t)) > E_balanced(γ(t))` holds at `t`. Direct from
the inf-of-a-closed-set characterisation: `t < sInf S → t ∉ S` (since otherwise
`sInf S ≤ t`).

Used by the first-crossing argument's strict-gap-implies-balanced-GS step
(PR #3990 applied for `t < t_first_M`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Strict per-`M` gap holds below first crossing**: for `t ∈ Icc 0 1` with
`t < sInf (perMCrossingSet M ∩ Icc 0 1)`, the strict gap
`E_balanced(γ(t)) < E_M(γ(t))` holds. -/
theorem strict_per_M_gap_of_lt_sInf_perMCrossingSet
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced M : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (magConfigS Λ N M)]
    (lam' D' : ℝ)
    (hne : (perMCrossingSet (Λ := Λ) hJ N M_balanced M lam' D' ∩ Icc (0 : ℝ) 1).Nonempty)
    {t : ℝ} (ht_mem : t ∈ Icc (0 : ℝ) 1)
    (ht_lt : t < sInf (perMCrossingSet (Λ := Λ) hJ N M_balanced M lam' D' ∩ Icc (0 : ℝ) 1)) :
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ N M_balanced lam' D' t <
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ N M lam' D' t := by
  -- Suppose by contradiction the gap fails: E_M(γ(t)) ≤ E_balanced(γ(t)).
  -- Then t ∈ perMCrossingSet, contradicting t < sInf.
  by_contra h_neg
  push_neg at h_neg
  -- h_neg : E_M(γ(t)) ≤ E_balanced(γ(t))? Wait, the negation of `<` is `≥`.
  -- Strict gap goal: E_balanced < E_M. Negation: E_M ≤ E_balanced.
  have h_in_perM : t ∈ perMCrossingSet (Λ := Λ) hJ N M_balanced M lam' D' :=
    h_neg
  have h_in_inter :
      t ∈ perMCrossingSet (Λ := Λ) hJ N M_balanced M lam' D' ∩ Icc (0 : ℝ) 1 :=
    ⟨h_in_perM, ht_mem⟩
  have h_sInf_le := csInf_le
    (bddBelow_perMCrossingSet_inter_Icc hJ N M_balanced M lam' D') h_in_inter
  linarith

end LatticeSystem.Quantum
