import LatticeSystem.Quantum.SpinS.Theorem23StructuralToySectorGroundState
import LatticeSystem.Quantum.SpinS.Theorem23GlobalMinimality

/-!
# Tasaki §2.5 Theorem 2.3 for the standard bipartite coupling — structural
(no `h_intermediate`)

(Thm23-#3887.21): structural variant of `tasaki_2_5_theorem_2_3_bipartiteToy`
closing the truly-unconditional `tasaki_2_5_theorem_2_3` statement
for the canonical toy coupling `J = bipartiteCoupling A` with `(hA_ne, hB_ne, hN)`
instead of the vacuous-at-N=1 `h_intermediate`.

This is the **capstone** of the #3887-extension structural-fix chain:
the spin-1/2 (N=1) instance is no longer vacuous — `tasaki_2_5_theorem_2_3`
genuinely produces a Marshall-positive ground state and its uniqueness across all admissible
sectors, plus global minimality, for the bipartite antiferromagnetic Heisenberg
Hamiltonian.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.3, p. 42; E. Lieb, D. Mattis,
J. Math. Phys. 3 (1962) 749.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- A non-empty domain underlies any non-zero real sector vector. -/
private theorem nonempty_magConfigS_of_fn_ne_zero_structural {N M : ℕ}
    {φ : magConfigS V N M → ℝ} (hne : φ ≠ 0) : Nonempty (magConfigS V N M) := by
  by_contra h
  rw [not_nonempty_iff] at h
  exact hne (funext (fun τ => (h.false τ).elim))

/-- **Structural Tasaki §2.5 Theorem 2.3 (Marshall–Lieb–Mattis general spin-S)** as a
`Prop`. Differs from `tasaki_2_5_theorem_2_3` in dropping `h_intermediate` and adding
`1 ≤ N`. The `|A| ≥ 1` / `|¬A| ≥ 1` cardinality hypotheses already imply
`(∃ a, A a = true)` / `(∃ b, A b = false)`, so no extra existence hypotheses are needed. -/
def tasaki_2_5_theorem_2_3
    (A : V → Bool) (N : ℕ) (J : V → V → ℂ) (c : ℝ) : Prop :=
  (∀ x y, (J x y).im = 0) →
  (∀ x y, star (J x y) = J x y) →
  (∀ x y, J x y = J y x) →
  (∀ x y, 0 ≤ (J x y).re) →
  (∀ x y, A x = A y → J x y = 0) →
  (∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re) →
  (∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c) →
  (1 ≤ N) →
  (1 ≤ (Finset.univ.filter (fun x : V => A x = true)).card) →
  (1 ≤ (Finset.univ.filter (fun x : V => (! A x) = true)).card) →
  ∃ μ : ℝ,
    (∀ M ∈ tasaki23GroundStateSectors (V := V) A N,
      [Nonempty (magConfigS V N M)] →
      ∃ v : magConfigS V N M → ℝ,
        μ < c ∧ (∀ σ, 0 < v σ) ∧
        (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
          (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
          (∀ σ, magSumS σ ≠ M → Ψ' σ = 0) →
          (∀ τ : magConfigS V N M, 0 < (marshallSignS A τ.1).re * (Ψ' τ.1).re) →
          μ' = μ ∧ ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N M,
              (Ψ' τ.1).re = r * ((marshallSignS A τ.1).re * v τ))) ∧
    (∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
      Ψ' ≠ 0 →
      (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
      μ ≤ μ')

/-- **Structural Tasaki §2.5 Theorem 2.3 for the standard bipartite antiferromagnetic
coupling** (orientation `|¬A| ≤ |A|`, no `h_intermediate`): the full
`tasaki_2_5_theorem_2_3` statement holds for `J = bipartiteCoupling A`.

This is the **truly-unconditional** §2.5 Theorem 2.3 closure for the bipartite toy
coupling — at spin-1/2 (N=1) the original `tasaki_2_5_theorem_2_3_bipartiteToy` is
vacuous because `h_intermediate` is unsatisfiable when `τ ≡ Fin.last 1`. The structural
variant proves the same conclusion from `(hA_ne, hB_ne, hN)`, which are the genuine
physical hypotheses. -/
theorem tasaki_2_5_theorem_2_3_bipartiteToy
    (A : V → Bool) (N : ℕ) (c : ℝ)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card) :
    tasaki_2_5_theorem_2_3 A N (bipartiteCoupling A) c := by
  classical
  intro _hJ_real _hJ_real' _hJ_sym _hJ_nn _hJ_bipartite _hJ_pos hc_strict hN hcardA hcardB
  have hA_ne : ∃ a, A a = true := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hcardA
    refine ⟨a, ?_⟩
    have := (Finset.mem_filter.mp ha).2
    exact this
  have hB_ne : ∃ b, A b = false := by
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hcardB
    refine ⟨b, ?_⟩
    have hbf := (Finset.mem_filter.mp hb).2
    cases hAb : A b
    · rfl
    · rw [hAb] at hbf; cases hbf
  refine ⟨(bipartiteToyMinEnergyPredicted (Λ := V) A N).re, ?_, ?_⟩
  · intro M hM _hNe
    obtain ⟨vM, hE_lt, hvM_pos, hH_M, _hReEig, huniq⟩ :=
      toy_sector_groundState_at_predicted (N := N) A c horient hc_strict
        hA_ne hB_ne hN hM
    exact ⟨vM, hE_lt, hvM_pos, hH_M, huniq⟩
  · refine tasaki23_eigenvalue_ge_common A N c (bipartiteCoupling_im A)
      (fun x y => by
        rw [Complex.star_def, Complex.conj_eq_iff_im]; exact bipartiteCoupling_im A x y)
      (fun x y => bipartiteCoupling_nonneg A x y)
      (bipartiteCoupling_symm A)
      (fun _ _ h => bipartiteCoupling_eq_zero_of_same_sublattice A h)
      hc_strict ?_ ?_
    · intro M hM
      haveI : Nonempty (magConfigS V N M) := by
        rw [tasaki23GroundStateSectors_mem_iff] at hM
        exact magConfigS_nonempty_of_le_card_mul
          (le_trans hM.2 (Nat.mul_le_mul_right N
            (by rw [← tasaki23_card_filter_A_add_card_notA A]
                exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))))
      obtain ⟨vM, _hE_lt, hvM_pos, _hH_M, hReEig, _huniq⟩ :=
        toy_sector_groundState_at_predicted (N := N) A c horient hc_strict
          hA_ne hB_ne hN hM
      exact ⟨vM, hvM_pos, hReEig⟩
    · intro M _hM_non μM φ hφ_ne hφ
      haveI : Nonempty (magConfigS V N M) := nonempty_magConfigS_of_fn_ne_zero_structural hφ_ne
      exact tasaki23_toy_sector_energy_ge_predicted (N := N) A c horient hc_strict
        hA_ne hB_ne hN hφ_ne hφ

end LatticeSystem.Quantum
