import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergPerMCrossingSet

/-!
# `sInf (perMCrossingSet ∩ Icc 0 1) ∈ set` — first per-`M` crossing achieved

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) first-crossing argument.

For per-`M` closed crossing set (PR #3993), the intersection with `Icc 0 1` is
closed, bounded below, and (given non-emptiness) achieves its infimum.

Building block for the per-`M` first crossing extraction: given the violation
hypothesis `E_M(γ(1)) ≤ E_balanced(γ(1))`, `1 ∈ perMCrossingSet M`, so the
set is non-empty, and `sInf ≤ 1` is the per-`M` first crossing.

Composes:
- PR #3993 `isClosed_perMCrossingSet`.
- `isClosed_Icc`, `IsClosed.csInf_mem` (mathlib).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Per-`M` crossing set intersected with `Icc 0 1` is closed**. -/
theorem isClosed_perMCrossingSet_inter_Icc
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced M : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (magConfigS Λ N M)]
    (lam' D' : ℝ) :
    IsClosed (perMCrossingSet (Λ := Λ) hJ N M_balanced M lam' D' ∩ Icc (0 : ℝ) 1) :=
  (isClosed_perMCrossingSet hJ N M_balanced M lam' D').inter isClosed_Icc

/-- **Per-`M` crossing set ∩ `Icc 0 1` is bounded below by `0`**. -/
theorem bddBelow_perMCrossingSet_inter_Icc
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced M : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (magConfigS Λ N M)]
    (lam' D' : ℝ) :
    BddBelow (perMCrossingSet (Λ := Λ) hJ N M_balanced M lam' D' ∩ Icc (0 : ℝ) 1) :=
  ⟨0, fun _t ht => ht.2.1⟩

/-- **`sInf` of the per-`M` crossing set ∩ `Icc 0 1` lies in the set**: given
non-emptiness, the closed + bounded-below set achieves its infimum. -/
theorem sInf_perMCrossingSet_inter_Icc_mem
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced M : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (magConfigS Λ N M)]
    (lam' D' : ℝ)
    (hne : (perMCrossingSet (Λ := Λ) hJ N M_balanced M lam' D' ∩ Icc (0 : ℝ) 1).Nonempty) :
    sInf (perMCrossingSet (Λ := Λ) hJ N M_balanced M lam' D' ∩ Icc (0 : ℝ) 1) ∈
      perMCrossingSet (Λ := Λ) hJ N M_balanced M lam' D' ∩ Icc (0 : ℝ) 1 :=
  IsClosed.csInf_mem (isClosed_perMCrossingSet_inter_Icc hJ N M_balanced M lam' D')
    hne (bddBelow_perMCrossingSet_inter_Icc hJ N M_balanced M lam' D')

end LatticeSystem.Quantum
