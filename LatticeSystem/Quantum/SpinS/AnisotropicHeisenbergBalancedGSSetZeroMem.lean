import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergBalancedGSSetClosed

/-!
# `0 ∈ balancedGSSet` from the strict-GS axiom at `(1, 0)`

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) first-crossing argument.

The non-emptiness witness for `balancedGSSet`: under the strict-GS axiom at
`(1, 0)` (i.e., `E_M_balanced(1, 0) = hermitianMinEigenvalue Ĥ(1, 0)`,
the balanced sector IS the GS), `0 ∈ balancedGSSet`.

This is a direct consequence — `0 ∈ balancedGSSet` IS the strict-GS axiom at
`(1, 0)`, since `γ(0) = (1, 0)`. The brick wraps this equivalence cleanly
for downstream use by the first-crossing argument's `sSup ∈ set`
non-emptiness hypothesis (PR #3985).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **`0 ∈ balancedGSSet`** from the strict-GS axiom at `(1, 0)`. -/
theorem zero_mem_balancedGSSet_of_strict_GS_at_SU2
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced : ℕ) [Nonempty (magConfigS Λ N M_balanced)]
    [Nonempty (Λ → Fin (N + 1))] (lam' D' : ℝ)
    (h_GS_at_SU2 :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ N M_balanced lam' D' 0 =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N
          (anisotropicHeisenbergParametricPath lam' D' 0).1
          (anisotropicHeisenbergParametricPath lam' D' 0).2)) :
    (0 : ℝ) ∈ balancedGSSet (Λ := Λ) hJ N M_balanced lam' D' := h_GS_at_SU2

/-- **`(0 : ℝ) ∈ balancedGSSet ∩ Icc 0 1`** under the strict-GS axiom: combines
`zero_mem_balancedGSSet_of_strict_GS_at_SU2` with the trivial
`0 ∈ Icc 0 1`. -/
theorem zero_mem_balancedGSSet_inter_Icc_of_strict_GS_at_SU2
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced : ℕ) [Nonempty (magConfigS Λ N M_balanced)]
    [Nonempty (Λ → Fin (N + 1))] (lam' D' : ℝ)
    (h_GS_at_SU2 :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ N M_balanced lam' D' 0 =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N
          (anisotropicHeisenbergParametricPath lam' D' 0).1
          (anisotropicHeisenbergParametricPath lam' D' 0).2)) :
    (0 : ℝ) ∈ balancedGSSet (Λ := Λ) hJ N M_balanced lam' D' ∩ Icc (0 : ℝ) 1 :=
  ⟨zero_mem_balancedGSSet_of_strict_GS_at_SU2 hJ N M_balanced lam' D' h_GS_at_SU2,
   ⟨le_refl _, by norm_num⟩⟩

end LatticeSystem.Quantum
