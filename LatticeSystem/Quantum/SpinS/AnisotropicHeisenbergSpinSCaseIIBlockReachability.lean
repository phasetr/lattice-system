import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIBoundaryMoveSets
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIBlockPFMin
import LatticeSystem.Quantum.SpinS.BipartiteCompleteGraphStructural
import LatticeSystem.Quantum.SpinS.ParityReachableNoParityBondTotal
import LatticeSystem.Quantum.SpinS.ParityReachableNoSingleIonTotal

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

/-! ## Lifts from full configurations to parity blocks -/

omit [DecidableEq Λ] in
/-- Lift full parity reachability between two representatives of the same
fixed parity block to block-level reachability. -/
theorem parityReachableSOnBlock_of_parityReachableS
    {G : SimpleGraph Λ} {p : ℕ} {σ τ : parityConfigS Λ N p}
    (hreach : ParityReachableS G σ.1 τ.1) :
    parityReachableSOnBlock G σ τ := by
  classical
  rcases τ with ⟨τ, hτ⟩
  change ParityReachableS G σ.1 τ at hreach
  induction hreach with
  | refl =>
      exact parityReachableSOnBlock_refl G σ
  | tail hpre hstep ih =>
      let hρ : magSumS _ % 2 = p := by
        have hp := parityReachableS_magSumS_parity_eq hpre
        rw [hp, σ.2]
      let ρ : parityConfigS Λ N p := ⟨_, hρ⟩
      exact parityReachableSOnBlock_trans (ih hρ)
        (parityReachableSOnBlock_single (σ := ρ) (τ := ⟨_, hτ⟩) hstep)

omit [DecidableEq Λ] in
/-- Lift full ion-only parity reachability between two representatives of the
same fixed parity block to block-level ion-only reachability. -/
theorem ionParityReachableSOnBlock_of_ionParityReachableS
    {G : SimpleGraph Λ} {p : ℕ} {σ τ : parityConfigS Λ N p}
    (hreach : IonParityReachableS G σ.1 τ.1) :
    ionParityReachableSOnBlock G σ τ := by
  classical
  rcases τ with ⟨τ, hτ⟩
  change IonParityReachableS G σ.1 τ at hreach
  induction hreach with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hpre hstep ih =>
      let hρ : magSumS _ % 2 = p := by
        have hp := parityReachableS_magSumS_parity_eq
          (IonParityReachableS.to_parityReachableS hpre)
        rw [hp, σ.2]
      let ρ : parityConfigS Λ N p := ⟨_, hρ⟩
      exact Relation.ReflTransGen.trans (ih hρ)
        (Relation.ReflTransGen.single (show ionParityStepSOnBlock G ρ ⟨_, hτ⟩ from hstep))

omit [DecidableEq Λ] in
/-- Lift full bond-only parity reachability between two representatives of the
same fixed parity block to block-level bond-only reachability. -/
theorem bondParityReachableSOnBlock_of_bondParityReachableS
    {G : SimpleGraph Λ} {p : ℕ} {σ τ : parityConfigS Λ N p}
    (hreach : BondParityReachableS G σ.1 τ.1) :
    bondParityReachableSOnBlock G σ τ := by
  classical
  rcases τ with ⟨τ, hτ⟩
  change BondParityReachableS G σ.1 τ at hreach
  induction hreach with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hpre hstep ih =>
      let hρ : magSumS _ % 2 = p := by
        have hp := parityReachableS_magSumS_parity_eq
          (BondParityReachableS.to_parityReachableS hpre)
        rw [hp, σ.2]
      let ρ : parityConfigS Λ N p := ⟨_, hρ⟩
      exact Relation.ReflTransGen.trans (ih hρ)
        (Relation.ReflTransGen.single (show bondParityStepSOnBlock G ρ ⟨_, hτ⟩ from hstep))

/-! ## Totality on bipartite complete graphs -/

omit [DecidableEq Λ] in
/-- Block-level strict case-(ii) parity reachability totality on the bipartite
complete graph. -/
theorem parityReachableSOnBlock_total_bipartiteCompleteGraph
    (A : Λ → Bool)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    {p : ℕ} (σ' σ : parityConfigS Λ N p) :
    parityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ' := by
  classical
  exact parityReachableSOnBlock_of_parityReachableS
    (parityReachableS_total A hA_ne hB_ne hN (σ.2.trans σ'.2.symm))

omit [DecidableEq Λ] in
/-- Block-level ion-only parity reachability totality on the bipartite complete
graph. -/
theorem ionParityReachableSOnBlock_total_bipartiteCompleteGraph
    (A : Λ → Bool)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    {p : ℕ} (σ' σ : parityConfigS Λ N p) :
    ionParityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ' := by
  classical
  exact ionParityReachableSOnBlock_of_ionParityReachableS
    (ionParityReachableS_total A hA_ne hB_ne hN (σ.2.trans σ'.2.symm))

omit [DecidableEq Λ] in
/-- Block-level bond-only parity reachability totality on the bipartite complete
graph. -/
theorem bondParityReachableSOnBlock_total_bipartiteCompleteGraph
    (A : Λ → Bool)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    {p : ℕ} (σ' σ : parityConfigS Λ N p) :
    bondParityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ' := by
  classical
  exact bondParityReachableSOnBlock_of_bondParityReachableS
    (bondParityReachableS_total A hA_ne hB_ne hN (σ.2.trans σ'.2.symm))

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
