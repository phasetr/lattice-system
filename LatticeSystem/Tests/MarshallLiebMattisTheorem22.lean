import LatticeSystem.Quantum.SpinS.Theorem23StructuralMLMFull
import LatticeSystem.Quantum.SpinS.Theorem22Connected

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

This module also pins the connected-generality capstone
`tasaki_2_5_theorem_2_2_of_connected` (Theorem 2.2, p. 39, at connectedness
instead of complete-bipartite positivity, with no sector restriction), plus
the four-vertex-path discriminating witness for that hypothesis change.
-/

namespace LatticeSystem.Tests.MarshallLiebMattisTheorem22

open LatticeSystem.Quantum
open Matrix Module

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

/-- **Discriminating witness (four-vertex path, not the four-cycle).** On
`V = Fin 4`, `A = {0, 2}`, `B = {1, 3}`, the path `pathGraph 4` (edges
`{0,1},{1,2},{2,3}`) is connected (H1, Footnote 28 p. 33), bipartite for this
`A` (H2, §2.5 p. 37) and balanced (H3, `|A| = |B| = 2`), so it satisfies every
hypothesis of the new connected capstone. Yet the crossing pair `{0,3}` is not
a path edge, so it violates the old `hJ_pos` of
`marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full`, which
demands positivity at *every* crossing pair of `bipartiteCompleteGraphOf A`.
The four-cycle `cycleGraph 4` does **not** discriminate: with this same `A` its
edge set `{0,1},{1,2},{2,3},{3,0}` is *exactly* the four crossing pairs of `A`,
so `cycleGraph 4 = bipartiteCompleteGraphOf A` as graphs and the two hypotheses
coincide on it (on 4 vertices split 2+2 there are exactly four crossing pairs,
and a bipartite graph carrying all of them is complete bipartite; the path
omits `{0,3}` and is the smallest witness that does). -/
example :
    (SimpleGraph.pathGraph 4).Connected ∧
      (∀ x y : Fin 4, (SimpleGraph.pathGraph 4).Adj x y →
        decide (x = 0 ∨ x = 2) ≠ decide (y = 0 ∨ y = 2)) ∧
      (Finset.univ.filter (fun x : Fin 4 => decide (x = 0 ∨ x = 2) = true)).card =
        (Finset.univ.filter (fun x : Fin 4 => decide (x = 0 ∨ x = 2) = false)).card ∧
      (bipartiteCompleteGraphOf (fun x : Fin 4 => decide (x = 0 ∨ x = 2))).Adj 0 3 ∧
      ¬ (SimpleGraph.pathGraph 4).Adj (0 : Fin 4) 3 := by
  refine ⟨SimpleGraph.pathGraph_connected 3, ?_, by decide, ?_, ?_⟩
  · intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [SimpleGraph.pathGraph_adj]
  · simp
  · simp [SimpleGraph.pathGraph_adj]

/-- **Cycle non-discrimination (documentation).** With the same marking the
four-cycle's edges coincide exactly with the complete bipartite graph, so it
cannot serve as the discriminating witness above: it satisfies old and new
hypotheses alike. -/
example :
    ∀ x y : Fin 4, (SimpleGraph.cycleGraph 4).Adj x y ↔
      (bipartiteCompleteGraphOf (fun x : Fin 4 => decide (x = 0 ∨ x = 2))).Adj x y := by
  decide

/-- **Signature pin.** Pins the connected-generality Theorem 2.2 capstone:
Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.2,
p. 39, eq. (2.5.4), p. 39, Hamiltonian (2.5.1), p. 37, general couplings by
Remark (2.5.13), p. 43; connectedness is Footnote 28, p. 33. The complete
bipartite graph is never a hypothesis here — it is only the bond graph of the
proof's toy Hamiltonian (2.5.10), p. 41.
Hypotheses: `G` connected (H1) and bipartite w.r.t. `A` (H2), balanced
sublattices (H3), `N ≥ 1` (H4), `J` positive exactly on the edges of `G` and
zero off them (H5/(2.5.13)). Conclusions, all four conjuncts: (C1) the full
eigenspace at `μ` has `finrank ≤ 1` and `μ` is a global lower bound on every
real eigenvalue; (C3) a Marshall-signed eigenvector on the balanced sector
`|A| * N`; (C4) its sector coefficients are all strictly positive; (C2) that
eigenvector is annihilated by `totalSpinSSquared`, i.e. `S_tot = 0`. The pin is
discharged by *applying* the capstone rather than restating it, so weakening any
of those hypotheses or conclusions breaks the build. -/
example (A : V → Bool) (G : SimpleGraph V) {J : V → V → ℂ}
    (hGconn : G.Connected)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (h_card_eq : (Finset.univ.filter (fun x : V => A x = true)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card)
    (hN : 1 ≤ N)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJ_off : ∀ x y, ¬ G.Adj x y → J x y = 0) :
    ∃ μ : ℝ,
      finrank ℂ ↥(End.eigenspace
          (Matrix.toLin' (heisenbergHamiltonianS J N)) (μ : ℂ)) ≤ 1 ∧
      (∀ {μM : ℝ} {φ : (V → Fin (N + 1)) → ℂ}, φ ≠ 0 →
        (heisenbergHamiltonianS J N).mulVec φ = (μM : ℂ) • φ → μ ≤ μM) ∧
      ∃ v : magConfigS V N
          ((Finset.univ.filter (fun x : V => A x = true)).card * N) → ℝ,
        (∀ σ, 0 < v σ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding (fun τ => ((marshallSignS A τ.1).re * v τ : ℝ))) =
          (μ : ℂ) •
            magSectorEmbedding (fun τ => ((marshallSignS A τ.1).re * v τ : ℝ)) ∧
        (totalSpinSSquared V N).mulVec
            (magSectorEmbedding (fun τ => ((marshallSignS A τ.1).re * v τ : ℝ))) = 0 :=
  tasaki_2_5_theorem_2_2_of_connected
    A G N hGconn hGbip h_card_eq hN hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite
    hJ_pos_G hJ_off

end LatticeSystem.Tests.MarshallLiebMattisTheorem22
