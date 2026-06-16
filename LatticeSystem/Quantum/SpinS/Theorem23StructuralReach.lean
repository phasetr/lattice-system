import LatticeSystem.Quantum.SpinS.MagConfig
import LatticeSystem.Quantum.SpinS.BipartiteCompleteGraphStructural
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSector

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Structural `MagSector` reachability for the Theorem 2.3 chain (no `h_intermediate`)

Extension of #3887 fix to the Tasaki §2.5 Theorem 2.3 dressed-Heisenberg chain.

Provides `raiseLowerReachableSMagSector_bipartiteCompleteGraph`
using `raiseLowerReachableS_bipartiteCompleteGraph_of_eq_magSumS`
(#3887.3) — drops `h_intermediate`, requires only `hA_ne + hB_ne + 1 ≤ N`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

omit [DecidableEq V] in
/-- **Structural MagSector reachability (no `h_intermediate`)**. -/
theorem raiseLowerReachableSMagSector_bipartiteCompleteGraph
    (A : V → Bool) {M : ℕ}
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    (σ σ' : magConfigS V N M) :
    RaiseLowerReachableSMagSector (bipartiteCompleteGraphOf A) σ σ' := by
  classical
  have hreach : RaiseLowerReachableS (bipartiteCompleteGraphOf A) σ.1 σ'.1 :=
    raiseLowerReachableS_bipartiteCompleteGraph_of_eq_magSumS A
      hA_ne hB_ne hN (σ.2.trans σ'.2.symm)
  exact raiseLowerReachableSMagSector_of_raiseLowerReachableS σ.2 σ'.2 hreach

/-- **Structural matrix-power positivity (no `h_intermediate`)**. -/
theorem exists_matrixPow_pos_of_magConfigS_bipartite
    (A : V → Bool)
    {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ ≤ c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N)
    (σ σ' : magConfigS V N M) :
    ∃ k : ℕ, 0 < (shiftedDressedSReMatrixOnMagSector A J N c M ^ k) σ' σ := by
  apply exists_matrixPow_apply_pos_of_raiseLowerReachableSMagSector
  · intro σ τ
    exact shiftedDressedSReMatrixOnMagSector_nonneg A N c M hJ_real hJ_nn
      hJ_sym hJ_bipartite hc σ τ
  · intro σ τ hstep
    exact shiftedDressedSReMatrixOnMagSector_apply_pos_of_raiseLowerStepSMagSector
      A N c M hJ_real hJ_pos hJ_sym hstep
  · exact raiseLowerReachableSMagSector_bipartiteCompleteGraph A
      hA_ne hB_ne hN σ σ'

/-- **Structural strict-positive-length matrix-power positivity**. -/
theorem exists_matrixPow_pos_length_of_magConfigS_bipartite
    (A : V → Bool)
    {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ ≤ c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N)
    {σ σ' : magConfigS V N M} (hne : σ ≠ σ') :
    ∃ k : ℕ, 1 ≤ k ∧
      0 < (shiftedDressedSReMatrixOnMagSector A J N c M ^ k) σ' σ := by
  obtain ⟨k, hpos⟩ := exists_matrixPow_pos_of_magConfigS_bipartite A c
    hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc hA_ne hB_ne hN σ σ'
  refine ⟨k, ?_, hpos⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    rw [pow_zero, Matrix.one_apply, if_neg (Ne.symm hne)] at hpos
    exact (lt_irrefl _ hpos).elim
  · exact hkpos

/-- **Structural sector-irreducibility (no `h_intermediate`)**. -/
theorem isIrreducible_shiftedDressedSReMatrixOnMagSector
    (A : V → Bool)
    {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N) :
    (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible := by
  rw [Matrix.isIrreducible_iff_exists_pow_pos
    (shiftedDressedSReMatrixOnMagSector_nonneg A N c M hJ_real hJ_nn hJ_sym
      hJ_bipartite (fun σ => le_of_lt (hc_strict σ)))]
  intro σ τ
  by_cases hne : σ = τ
  · subst hne
    refine ⟨1, Nat.one_pos, ?_⟩
    rw [pow_one, shiftedDressedSReMatrixOnMagSector_apply,
      shiftedDressedSReMatrix_apply_diag]
    linarith [hc_strict σ.1]
  · obtain ⟨k, hk_pos, hpos⟩ :=
      exists_matrixPow_pos_length_of_magConfigS_bipartite A c hJ_real hJ_pos
        hJ_nn hJ_sym hJ_bipartite (fun σ => le_of_lt (hc_strict σ))
        hA_ne hB_ne hN (Ne.symm hne)
    exact ⟨k, hk_pos, hpos⟩

end LatticeSystem.Quantum
