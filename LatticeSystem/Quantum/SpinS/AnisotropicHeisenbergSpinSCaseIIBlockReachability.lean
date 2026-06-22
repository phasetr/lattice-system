import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIBlockReachabilityCore
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIBlockPFMin

/-!
# Case (ii): block-level reachability totality

Issue #412 (Tasaki §2.5 Theorem 2.4, Mattis--Nishimori).

This file lifts the existing full-configuration reachability totality
theorems to the fixed parity-block relations used by the case-(ii) shifted
block irreducibility and PF/min layers.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Case-(ii) wrappers with total block reachability -/

/-- Even and odd PF/min callbacks from bipartite complete graph reachability
totality and the explicit case-(ii) corner callbacks. -/
theorem caseII_axisSwapped_parityBlockPFMinPath_of_total_reachability
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    {lam D : ℝ}
    (hlam_case_ii : 1 ≤ lam) (hD_case_ii : D ≤ 0)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    (h_even_corner :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        (anisotropicHeisenbergParametricPath lam D t).1 = 1 →
        (anisotropicHeisenbergParametricPath lam D t).2 = 0 →
          axisSwappedParityBlockPFMinAt (Λ := Λ) (N := N) J hJim
            (anisotropicHeisenbergParametricPath lam D t).1
            (anisotropicHeisenbergParametricPath lam D t).2 0)
    (h_odd_corner :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        (anisotropicHeisenbergParametricPath lam D t).1 = 1 →
        (anisotropicHeisenbergParametricPath lam D t).2 = 0 →
          axisSwappedParityBlockPFMinAt (Λ := Λ) (N := N) J hJim
            (anisotropicHeisenbergParametricPath lam D t).1
            (anisotropicHeisenbergParametricPath lam D t).2 1) :
    axisSwappedParityBlockPFMinPath (Λ := Λ) (N := N) J hJim lam D 0 ∧
      axisSwappedParityBlockPFMinPath (Λ := Λ) (N := N) J hJim lam D 1 := by
  have hN_one : 1 ≤ N := by omega
  exact caseII_axisSwapped_parityBlockPFMinPath_of_reachability
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp
    hlam_case_ii hD_case_ii
    (fun σ' σ _hne =>
      parityReachableSOnBlock_total_bipartiteCompleteGraph A hA_ne hB_ne hN_one σ' σ)
    (fun σ' σ _hne =>
      ionParityReachableSOnBlock_total_bipartiteCompleteGraph A hA_ne hB_ne hN σ' σ)
    (fun σ' σ _hne =>
      bondParityReachableSOnBlock_total_bipartiteCompleteGraph A hA_ne hB_ne hN_one σ' σ)
    h_even_corner
    (fun σ' σ _hne =>
      parityReachableSOnBlock_total_bipartiteCompleteGraph A hA_ne hB_ne hN_one σ' σ)
    (fun σ' σ _hne =>
      ionParityReachableSOnBlock_total_bipartiteCompleteGraph A hA_ne hB_ne hN σ' σ)
    (fun σ' σ _hne =>
      bondParityReachableSOnBlock_total_bipartiteCompleteGraph A hA_ne hB_ne hN_one σ' σ)
    h_odd_corner

/-- Pathwise parity-block full-min bounds from bipartite complete graph
reachability totality and the explicit case-(ii) corner callbacks. -/
theorem caseII_axisSwapped_submatrix_blocks_path_of_total_reachability_pf_min
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    [Nonempty (Λ → Fin (N + 1))]
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    {lam D : ℝ}
    (hlam_case_ii : 1 ≤ lam) (hD_case_ii : D ≤ 0)
    (h_even_corner :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        (anisotropicHeisenbergParametricPath lam D t).1 = 1 →
        (anisotropicHeisenbergParametricPath lam D t).2 = 0 →
          axisSwappedParityBlockPFMinAt (Λ := Λ) (N := N) J hJim
            (anisotropicHeisenbergParametricPath lam D t).1
            (anisotropicHeisenbergParametricPath lam D t).2 0)
    (h_odd_corner :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        (anisotropicHeisenbergParametricPath lam D t).1 = 1 →
        (anisotropicHeisenbergParametricPath lam D t).2 = 0 →
          axisSwappedParityBlockPFMinAt (Λ := Λ) (N := N) J hJim
            (anisotropicHeisenbergParametricPath lam D t).1
            (anisotropicHeisenbergParametricPath lam D t).2 1) :
    (∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J
            ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
            ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N).submatrix
            (fun σ : parityConfigS Λ N 0 => σ.1)
            (fun σ : parityConfigS Λ N 0 => σ.1)))
          ((hermitianMinEigenvalue
            (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
              (anisotropicHeisenbergParametricPath lam D t).1
              (anisotropicHeisenbergParametricPath lam D t).2) : ℝ) : ℂ)) ≤ 1) ∧
      (∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J
            ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
            ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N).submatrix
            (fun σ : parityConfigS Λ N 1 => σ.1)
            (fun σ : parityConfigS Λ N 1 => σ.1)))
          ((hermitianMinEigenvalue
            (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
              (anisotropicHeisenbergParametricPath lam D t).1
              (anisotropicHeisenbergParametricPath lam D t).2) : ℝ) : ℂ)) ≤ 1) := by
  rcases caseII_axisSwapped_parityBlockPFMinPath_of_total_reachability
      (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp hA_ne hB_ne hN
      hlam_case_ii hD_case_ii h_even_corner h_odd_corner with
    ⟨h_even_pf, h_odd_pf⟩
  exact caseII_axisSwapped_submatrix_blocks_path_of_pf_min
    (Λ := Λ) (N := N) (J := J) hJim hJself hJ_star h_even_pf h_odd_pf

end LatticeSystem.Quantum
