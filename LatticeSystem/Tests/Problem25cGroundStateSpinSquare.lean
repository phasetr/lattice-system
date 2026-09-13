import LatticeSystem.Quantum.SpinS.Theorem22Connected
import LatticeSystem.Quantum.SpinS.Problem25cAxisSwapGroundStatePhase
import LatticeSystem.Quantum.SpinS.SubmatrixMinEigenvalue

/-!
# Red fixture: Tasaki Problem 2.5.c, p. 39, eq. (2.5.6) — single-site spin square

Pins the not-yet-existing capstone
`tasaki_problem_2_5_c_singleSite_spinSquare_expectation` and its printed-model
instance `tasaki_problem_2_5_c_couplingOf_half`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.c, p. 39, eq. (2.5.6), solution p. 498.
Standing assumptions of the target's hypotheses (Theorem 2.2's own, not
stronger): bipartiteness is stated for the whole of §2.5 from p. 37;
connectedness is Footnote 28, p. 33, cited by Theorem 2.2's own footnote 32,
p. 39.  The complete bipartite graph is **never** a hypothesis of Problem
2.5.c or of Theorem 2.2: it is only the bond graph of the toy Hamiltonian at
eq. (2.5.10), p. 41, internal to the book's own proof, and must not appear as
a hypothesis here.

This fixture never applies
`marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full`
(Issue #5466's unsatisfiable-hypothesis route) or any declaration depending on
`hJ_pos` over `bipartiteCompleteGraphOf`; every application below goes through
the connected-generality capstone
`tasaki_2_5_theorem_2_2_of_connected`/`tasaki_2_5_theorem_2_2_couplingOf_half`
family, discriminated at the four-vertex-path witness below.

Existing Problem 2.5.c modules cite this problem as "p. 43"; that citation is
wrong (Problem 2.5.c and eq. (2.5.6) are p. 39, solution p. 498) and this
module does not copy it and does not correct it elsewhere, per the design's
scope ruling.
-/

namespace LatticeSystem.Tests.Problem25cGroundStateSpinSquare

open LatticeSystem.Quantum
open LatticeSystem.Lattice
open Matrix Module

/-- **Discriminating witness sublattice marker.**  `A = {0, 2}` on `Fin 4`,
restated from the anonymous witness at
`LatticeSystem/Tests/MarshallLiebMattisTheorem22.lean:90` (that witness is an
unnamed `example`, not an importable declaration, hence the restatement). -/
private def witnessMarker : Fin 4 → Bool := fun x => decide (x = 0 ∨ x = 2)

/-- **Discriminating witness graph.**  The four-vertex path (edges `{0,1}`,
`{1,2}`, `{2,3}`), *not* the four-cycle: with `witnessMarker` the four-cycle's
edge set is exactly the four crossing pairs of the marker, i.e. it coincides
with `bipartiteCompleteGraphOf witnessMarker` (see
`witness_cycle_eq_completeBipartite` below), so it cannot discriminate
Theorem 2.2's hypotheses from complete-bipartite positivity.  The path omits
the crossing pair `{0,3}` and is the smallest witness that does. -/
private def witnessGraph : SimpleGraph (Fin 4) := SimpleGraph.pathGraph 4

/-- Decidability instance for `witnessGraph`'s adjacency, needed only to form
`couplingOf witnessGraph _` in the identification control below. -/
private noncomputable instance : DecidableRel witnessGraph.Adj := Classical.decRel _

/-- **H1 (Footnote 28, p. 33).** The path witness is connected. -/
private theorem witness_connected : witnessGraph.Connected :=
  SimpleGraph.pathGraph_connected 3

/-- **H2 (§2.5, p. 37).** The path witness is bipartite w.r.t. `witnessMarker`. -/
private theorem witness_bipartite :
    ∀ x y : Fin 4, witnessGraph.Adj x y → witnessMarker x ≠ witnessMarker y := by
  intro x y hxy
  fin_cases x <;> fin_cases y <;>
    simp_all [witnessGraph, witnessMarker, SimpleGraph.pathGraph_adj]

/-- **H3 (`|A| = |B|`, p. 39).** The two sublattices are balanced, `2 = 2`. -/
private theorem witness_balanced :
    (Finset.univ.filter (fun x : Fin 4 => witnessMarker x = true)).card =
      (Finset.univ.filter (fun x : Fin 4 => (! witnessMarker x) = true)).card := by
  decide

/-- **Non-discrimination of the four-cycle (documentation).**  With the same
marker, the four-cycle's edges are exactly `bipartiteCompleteGraphOf
witnessMarker`'s edges, so it satisfies the old (stronger) hypotheses too and
cannot discriminate them from Theorem 2.2's; this is why `witnessGraph` above
is the path and not the cycle. -/
private theorem witness_cycle_eq_completeBipartite :
    ∀ x y : Fin 4, (SimpleGraph.cycleGraph 4).Adj x y ↔
      (bipartiteCompleteGraphOf witnessMarker).Adj x y := by
  decide

/-- **Value + generality + anti-vacuity + axis/site control, `N = 1` (`S = 1/2`).**
Applies the not-yet-existing printed-model capstone at the path witness (H2 vs.
`bipartiteCompleteGraphOf` positivity) and `N = 1`, consumes the existence
conjunct to obtain an actual normalised ground state (anti-vacuity: an `∃ Φ`
weakened from this, or a deleted existence conjunct, leaves nothing to feed
the universal conjunct below), and checks all three axes at every site against
the literal value `S(S+1)/3 = 1/4`.  `N = 0` is deliberately excluded (every
candidate constant collapses to `0` there and the control would not
discriminate); wrong constants such as `3/4` (`N(N+2)/4`), `1/6`
(`N(N+2)/6`), or `(N+1)²/12 = 1` are all rejected by the `norm_num` step. -/
private theorem redPin_N1_axis_value_and_generality :
    ∃ Φ : (Fin 4 → Fin 2) → ℂ, Φ ≠ 0 ∧ star Φ ⬝ᵥ Φ = 1 ∧
      ∀ x : Fin 4,
        singleSiteSpinSquareExpectationS x (spinSOp1 1) Φ = 1 / 4 ∧
        singleSiteSpinSquareExpectationS x (spinSOp2 1) Φ = 1 / 4 ∧
        singleSiteSpinSquareExpectationS x (spinSOp3 1) Φ = 1 / 4 := by
  obtain ⟨_μ, _hμ_def, _hrank, ⟨Φ, hΦne, hΦnorm, hΦeig⟩, huniv⟩ :=
    tasaki_problem_2_5_c_couplingOf_half witnessMarker witnessGraph 1
      witness_connected witness_bipartite witness_balanced (le_refl 1)
  refine ⟨Φ, hΦne, hΦnorm, fun x => ?_⟩
  obtain ⟨h1, h2, h3⟩ := huniv hΦne hΦnorm hΦeig x
  exact ⟨by rw [h1]; norm_num, by rw [h2]; norm_num, by rw [h3]; norm_num⟩

/-- **Second value point, `N = 2` (`S = 1`).**  Same witness and shape as the
`N = 1` control, checked against the literal value `S(S+1)/3 = 2/3`.  A single
value point cannot distinguish `S(S+1)/3` from every wrong formula that
happens to agree at `S = 1/2`; this second point is required (design §6
control 1). -/
private theorem redPin_N2_axis_value_and_generality :
    ∃ Φ : (Fin 4 → Fin 3) → ℂ, Φ ≠ 0 ∧ star Φ ⬝ᵥ Φ = 1 ∧
      ∀ x : Fin 4,
        singleSiteSpinSquareExpectationS x (spinSOp1 2) Φ = 2 / 3 ∧
        singleSiteSpinSquareExpectationS x (spinSOp2 2) Φ = 2 / 3 ∧
        singleSiteSpinSquareExpectationS x (spinSOp3 2) Φ = 2 / 3 := by
  obtain ⟨_μ, _hμ_def, _hrank, ⟨Φ, hΦne, hΦnorm, hΦeig⟩, huniv⟩ :=
    tasaki_problem_2_5_c_couplingOf_half witnessMarker witnessGraph 2
      witness_connected witness_bipartite witness_balanced (by norm_num)
  refine ⟨Φ, hΦne, hΦnorm, fun x => ?_⟩
  obtain ⟨h1, h2, h3⟩ := huniv hΦne hΦnorm hΦeig x
  exact ⟨by rw [h1]; norm_num, by rw [h2]; norm_num, by rw [h3]; norm_num⟩

/-- **Identification control.**  Rewrites the eigen-equation at the
existential `μ` into one at `hermitianMinEigenvalue` of the same
Hamiltonian's Hermitian proof, using only the identification conjunct
(`μ = hermitianMinEigenvalue …`); deleting that conjunct removes the term
`hμ_def` this rewrite needs. -/
private theorem redPin_N1_identification_control :
    ∃ Φ : (Fin 4 → Fin 2) → ℂ, Φ ≠ 0 ∧ star Φ ⬝ᵥ Φ = 1 ∧
      (heisenbergHamiltonianS (couplingOf witnessGraph ((1 : ℂ) / 2)) 1).mulVec Φ =
        ((hermitianMinEigenvalue
            (heisenbergHamiltonianS_isHermitian_of_real
              (couplingOf_real witnessGraph (J := (1 : ℂ) / 2) (by norm_num)) 1) :
                ℝ) : ℂ) • Φ := by
  obtain ⟨μ, hμ_def, _hrank, ⟨Φ, hΦne, hΦnorm, hΦeig⟩, _huniv⟩ :=
    tasaki_problem_2_5_c_couplingOf_half witnessMarker witnessGraph 1
      witness_connected witness_bipartite witness_balanced (le_refl 1)
  exact ⟨Φ, hΦne, hΦnorm, hμ_def ▸ hΦeig⟩

end LatticeSystem.Tests.Problem25cGroundStateSpinSquare
