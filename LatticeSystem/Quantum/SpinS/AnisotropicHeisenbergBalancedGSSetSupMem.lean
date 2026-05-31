import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergBalancedGSSetClosed

/-!
# `sSup (balancedGSSet ∩ Icc 0 1)` lies in the set (sup achieved)

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) first-crossing argument.

For the closed `balancedGSSet` (PR #3983) intersected with `Icc 0 1`, the
supremum is achieved (lies in the set). This requires non-emptiness, supplied
by `0 ∈ balancedGSSet` (a separate brick under the strict gap axiom).

Composes:
- PR #3983 `isClosed_balancedGSSet`.
- `isClosed_Icc` (mathlib).
- `IsClosed.csSup_mem` (mathlib).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **The balanced-GS set intersected with `Icc 0 1` is closed**. -/
theorem isClosed_balancedGSSet_inter_Icc
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced : ℕ) [Nonempty (magConfigS Λ N M_balanced)]
    [Nonempty (Λ → Fin (N + 1))] (lam' D' : ℝ) :
    IsClosed (balancedGSSet (Λ := Λ) hJ N M_balanced lam' D' ∩ Icc (0 : ℝ) 1) :=
  (isClosed_balancedGSSet hJ N M_balanced lam' D').inter isClosed_Icc

/-- **The balanced-GS set is bounded above by 1 after intersection with `Icc 0 1`**. -/
theorem bddAbove_balancedGSSet_inter_Icc
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced : ℕ) [Nonempty (magConfigS Λ N M_balanced)]
    [Nonempty (Λ → Fin (N + 1))] (lam' D' : ℝ) :
    BddAbove (balancedGSSet (Λ := Λ) hJ N M_balanced lam' D' ∩ Icc (0 : ℝ) 1) :=
  ⟨1, fun t ht => ht.2.2⟩

/-- **`sSup` of the balanced-GS set ∩ `Icc 0 1` lies in the set**: given
non-emptiness (e.g., `0 ∈ balancedGSSet`), the closed + bounded-above set
achieves its supremum. -/
theorem sSup_balancedGSSet_inter_Icc_mem
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced : ℕ) [Nonempty (magConfigS Λ N M_balanced)]
    [Nonempty (Λ → Fin (N + 1))] (lam' D' : ℝ)
    (hne : (balancedGSSet (Λ := Λ) hJ N M_balanced lam' D' ∩ Icc (0 : ℝ) 1).Nonempty) :
    sSup (balancedGSSet (Λ := Λ) hJ N M_balanced lam' D' ∩ Icc (0 : ℝ) 1) ∈
      balancedGSSet (Λ := Λ) hJ N M_balanced lam' D' ∩ Icc (0 : ℝ) 1 :=
  IsClosed.csSup_mem (isClosed_balancedGSSet_inter_Icc hJ N M_balanced lam' D')
    hne (bddAbove_balancedGSSet_inter_Icc hJ N M_balanced lam' D')

end LatticeSystem.Quantum
