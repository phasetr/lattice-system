import LatticeSystem.Quantum.SpinS.Theorem23StructuralMLMFull

/-!
# Signature pin: Marshall–Lieb–Mattis without the scaffolding shift binder

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.2, p. 39 (statement), pp. 39–42 (proof); general coupling (2.5.13), p. 43.

`marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full`
(`LatticeSystem/Quantum/SpinS/Theorem23StructuralMLMFull.lean`) carries no auxiliary spectral
parameter. The shift the Perron–Frobenius step needs is Tasaki's own internal `α` from the proof
of Theorem A.18 (p. 475, step (1)); it is produced inside the proof from finiteness of the
configuration type rather than assumed, and Theorem 2.2 has no counterpart for it. This module
pins that binder-free signature, so re-introducing a `(c : ℝ)` binder, a strictness hypothesis
`∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c` for it, or a `μ < c` conjunct comparing the
eigenvalue against it breaks the build.

See `marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full`'s own docstring for the
exact scope of what this declaration establishes and does not. Related results proved elsewhere:
`ringSym_ground_uniqueness` (whole-Hilbert-space uniqueness, AFM ring), and, at general balanced
complete-bipartite generality,
`exists_t23_commonE_and_heisHamS_fullEig_finrank_le_one_of_casLadder_t23_pf`
(whole-Hilbert-space uniqueness) and, conditionally on a supplied sector eigenvector,
`tasaki23_sector_lift_and_casimir_zero_of_card_eq` (`S_tot = 0`).
-/

namespace LatticeSystem.Tests.MarshallLiebMattisTheorem22

open LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Signature pin.** The binder-free signature of
`marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full`: its conclusion carries no
shift parameter, no strictness hypothesis for one, and no conjunct comparing the eigenvalue
against one. -/
example (A : V → Bool) {J : V → V → ℂ} {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      (∀ σ, 0 < v σ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μ : ℂ) •
          magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
      (∀ σ, magSumS σ ≠ M →
        magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) σ = 0) ∧
      (∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
        (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
        (∀ σ, magSumS σ ≠ M → Ψ' σ = 0) →
        (∀ τ : magConfigS V N M, 0 < (marshallSignS A τ.1).re * (Ψ' τ.1).re) →
        μ' = μ ∧ ∃ r : ℝ, 0 < r ∧
          ∀ τ : magConfigS V N M,
            (Ψ' τ.1).re = r * ((marshallSignS A τ.1).re * v τ)) :=
  marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full
    A hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hA_ne hB_ne hN

/-- **Gap control (not the discriminating fixture).** The math note's discriminating
control needs a connected-`G` Theorem 2.2 capstone (C1∧C2∧C3∧C4) that this repository does not
carry (connected-`G` layers of Theorem 2.3 do exist, e.g.
`tasaki_2_5_theorem_2_3_data_of_connected`), so it cannot be pinned by applying anything here:
the declaration above has
no `G`/support binder at all, only `hJ_pos` over *every* crossing pair of `A`. What can be pinned
instead is the combinatorial fact that makes `hJ_pos` strictly stronger than connectedness (the
math note's Prop. "strictly stronger", §Delta 3): on the path on four vertices `0,1,2,3` with
sublattices `A = {0, 2}`, `B = {1, 3}`, the pair `{0, 3}` is a crossing pair with no path edge, so
this declaration's `hJ_pos` demands positivity at a pair the path does not bond. This is the
exact obstruction that a path-supported coupling satisfies while this declaration's `hJ_pos`
hypothesis excludes it. -/
example :
    (bipartiteCompleteGraphOf (fun x : Fin 4 => decide (x = 0 ∨ x = 2))).Adj 0 3 ∧
      ¬ (SimpleGraph.pathGraph 4).Adj (0 : Fin 4) 3 := by
  refine ⟨?_, ?_⟩
  · simp
  · simp [SimpleGraph.pathGraph_adj]

end LatticeSystem.Tests.MarshallLiebMattisTheorem22
