import LatticeSystem.Quantum.SpinS.Theorem22Connected
import LatticeSystem.Quantum.SpinS.Problem25cTheorem22GroundState
import LatticeSystem.Quantum.SpinS.Problem25dCorrelationSignBridge
import LatticeSystem.Quantum.SpinS.Problem25dTheorem22GroundState
import LatticeSystem.Quantum.SpinS.SubmatrixMinEigenvalue

/-!
# Red fixture: Tasaki Problem 2.5.d, p. 40, eq. (2.5.7) — ground-state correlation sign

Pins the not-yet-existing capstone
`tasaki_problem_2_5_d_twoSpin_correlation_sign` (applied directly under
Theorem 2.2's own hypotheses, with an explicit coupling, in
`redPin_general_capstone_N1`) **and** its printed-model instance
`tasaki_problem_2_5_d_couplingOf_half` (in the other `redPin_*` lemmas): both
are named so the general statement cannot be left unproved by discharging
only the printed case.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.d, p. 40, eq. (2.5.7); solution p. 498, equations
(S.22)-(S.23).  The hint's operator, referring to eq. (2.5.4), is the product
over the `B` sublattice of the signed spin factor
`Û := ∏_{x∈B} (−1)^{Ŝ_x^{(3)} − S}`.

Standing assumptions of the target's hypotheses (Theorem 2.2's own, not
stronger): bipartiteness is stated for the whole of §2.5 from p. 37;
connectedness is Footnote 28, p. 33, cited by Theorem 2.2's own footnote 32,
p. 39.  The complete bipartite graph is **never** a hypothesis of Problem
2.5.d or of Theorem 2.2: it is only the bond graph of the toy Hamiltonian at
eq. (2.5.10), p. 41, internal to the book's own proof, and must not appear as
a hypothesis here.  Theorem 2.3 (p. 42) is likewise not a hypothesis.

This fixture never applies
`marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full`
(Issue #5466's unsatisfiable-hypothesis route) or any declaration depending on
`hJ_pos` over `bipartiteCompleteGraphOf`; every application below goes through
the connected-generality capstone
`tasaki_2_5_theorem_2_2_of_connected`/`tasaki_2_5_theorem_2_2_couplingOf_half`
family, discriminated at the four-vertex-path witness below.
-/

namespace LatticeSystem.Tests.Problem25dGroundStateCorrelationSign

open LatticeSystem.Quantum
open LatticeSystem.Lattice
open Matrix Module

/-- **Discriminating witness sublattice marker.**  `A = {0, 2}` on `Fin 4`,
restated (this fixture's copy is `private`, and the 2.5.c fixture's own copy
is likewise `private` and not importable). -/
private def witnessMarker : Fin 4 → Bool := fun x => decide (x = 0 ∨ x = 2)

/-- **Discriminating witness graph.**  The four-vertex path (edges `{0,1}`,
`{1,2}`, `{2,3}`), *not* the four-cycle: with `witnessMarker` the four-cycle's
edge set is exactly the four crossing pairs of the marker, i.e. it coincides
with `bipartiteCompleteGraphOf witnessMarker`, so it cannot discriminate
Theorem 2.2's hypotheses from complete-bipartite positivity.  The path omits
the crossing pair `{0,3}` and is the smallest witness that does. -/
private def witnessGraph : SimpleGraph (Fin 4) := SimpleGraph.pathGraph 4

/-- **Adjacency decidability instance.**  `couplingOf` requires deciding
adjacency of its graph argument; `witnessGraph` carries no such instance by
construction, so one is supplied here (classically, since only existence is
needed) for every use of `couplingOf witnessGraph _` below. -/
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

/-- **H4 (discriminating-hypothesis check).** `{0, 3}` is a crossing pair of
`witnessMarker` (`0 ∈ A`, `3 ∈ B`) but not an edge of the path witness, so a
route requiring `hJ_pos` over `bipartiteCompleteGraphOf witnessMarker` is
inapplicable to this witness at that pair.  Recorded to document control 5;
not consumed elsewhere. -/
private theorem witness_zero_three_crossing_not_adjacent :
    witnessMarker 0 ≠ witnessMarker 3 ∧ ¬ witnessGraph.Adj 0 3 := by
  constructor
  · decide
  · simp [witnessGraph, SimpleGraph.pathGraph_adj]

/-- **Controls 1-3, 6-7 (`N = 1`, `S = 1/2`).**  Applies the not-yet-existing
printed-model capstone at the path witness and `N = 1`, consumes the
existence conjunct to obtain an actual normalised ground state (control 6:
an `∃ Φ` weakened from this, or a deleted existence conjunct, leaves nothing
to feed the universal conjunct below), and from **one and the same** `Φ`:

* control 1 (the discriminating one): `0 < (twoSpinCorrelationS 0 2 Φ).re`,
  a same-sublattice pair in `A`.  **Unprovable if an implementer proves only
  the cross-sublattice case**, since no cross conjunct can supply this term;
* control 2: `0 < (twoSpinCorrelationS 1 3 Φ).re`, a same-sublattice pair in
  the *other* class `B` — guards a branch proved for `A`-sites only, since
  the Marshall sign is a product over `A`-marked sites and the two classes
  are not symmetric in that construction;
* control 3: `(twoSpinCorrelationS 0 1 Φ).re < 0`, a cross-sublattice pair on
  the *same* `Φ` as controls 1-2 — together they pin the sign flip, so a
  statement concluding `0 < …` (or `≠ 0`) for every pair fails here;
* control 7 (identification): the eigen-equation is stated at `μ`, and
  `hμ_def` is exposed as `_hμ_def` so a deleted identification conjunct
  leaves this binder without a term to destructure. -/
private theorem redPin_N1_sign_and_generality :
    ∃ Φ : (Fin 4 → Fin 2) → ℂ, Φ ≠ 0 ∧ star Φ ⬝ᵥ Φ = 1 ∧
      0 < (twoSpinCorrelationS 0 2 Φ).re ∧
      0 < (twoSpinCorrelationS 1 3 Φ).re ∧
      (twoSpinCorrelationS 0 1 Φ).re < 0 := by
  obtain ⟨_μ, _hμ_def, _hrank, ⟨Φ, hΦne, hΦnorm, hΦeig⟩, huniv⟩ :=
    tasaki_problem_2_5_d_couplingOf_half witnessMarker witnessGraph 1
      witness_connected witness_bipartite witness_balanced (le_refl 1)
  refine ⟨Φ, hΦne, hΦnorm, ?_, ?_, ?_⟩
  · exact (huniv hΦne hΦnorm hΦeig 0 2 (by decide)).1 (by decide)
  · exact (huniv hΦne hΦnorm hΦeig 1 3 (by decide)).1 (by decide)
  · exact (huniv hΦne hΦnorm hΦeig 0 1 (by decide)).2 (by decide)

/-- **Control 4 (generality).**  Applies the not-yet-existing
`tasaki_problem_2_5_d_twoSpin_correlation_sign` *directly*, at explicit
`J = couplingOf witnessGraph (1/2)`, discharging every coupling hypothesis by
hand exactly as `tasaki_2_5_theorem_2_2_couplingOf_half`'s own proof does.
This is the identifier the design calls the target; pinning only the
printed-model instance `tasaki_problem_2_5_d_couplingOf_half` above would let
an implementer discharge the printed case alone without ever stating the
general one, which is the failure mode this lemma forecloses. -/
private theorem redPin_general_capstone_N1 :
    ∃ Φ : (Fin 4 → Fin 2) → ℂ, Φ ≠ 0 ∧ star Φ ⬝ᵥ Φ = 1 ∧
      0 < (twoSpinCorrelationS 0 2 Φ).re ∧
      0 < (twoSpinCorrelationS 1 3 Φ).re ∧
      (twoSpinCorrelationS 0 1 Φ).re < 0 := by
  have hJ_real : ∀ x y : Fin 4, (couplingOf witnessGraph ((1 : ℂ) / 2) x y).im = 0 := by
    intro x y
    unfold couplingOf
    by_cases h : witnessGraph.Adj x y
    · rw [if_pos h]; norm_num
    · rw [if_neg h, Complex.zero_im]
  have hJ_pos_G : ∀ x y : Fin 4, witnessGraph.Adj x y →
      0 < (couplingOf witnessGraph ((1 : ℂ) / 2) x y).re := by
    intro x y h
    unfold couplingOf
    rw [if_pos h]; norm_num
  have hJ_off : ∀ x y : Fin 4, ¬ witnessGraph.Adj x y →
      couplingOf witnessGraph ((1 : ℂ) / 2) x y = 0 := by
    intro x y h
    unfold couplingOf
    exact if_neg h
  have hJ_nn : ∀ x y : Fin 4, 0 ≤ (couplingOf witnessGraph ((1 : ℂ) / 2) x y).re := by
    intro x y
    by_cases h : witnessGraph.Adj x y
    · exact (hJ_pos_G x y h).le
    · rw [hJ_off x y h, Complex.zero_re]
  have hJ_bipartite : ∀ x y : Fin 4, witnessMarker x = witnessMarker y →
      couplingOf witnessGraph ((1 : ℂ) / 2) x y = 0 := by
    intro x y hxy
    unfold couplingOf
    exact if_neg fun hadj => witness_bipartite x y hadj hxy
  obtain ⟨_μ, _hμ_def, _hrank, ⟨Φ, hΦne, hΦnorm, hΦeig⟩, huniv⟩ :=
    tasaki_problem_2_5_d_twoSpin_correlation_sign
      witnessMarker witnessGraph 1 witness_connected witness_bipartite
      witness_balanced (le_refl 1) hJ_real
      (couplingOf_real witnessGraph (J := (1 : ℂ) / 2) (by norm_num))
      (couplingOf_symm witnessGraph ((1 : ℂ) / 2)) hJ_nn hJ_bipartite hJ_pos_G hJ_off
  refine ⟨Φ, hΦne, hΦnorm, ?_, ?_, ?_⟩
  · exact (huniv hΦne hΦnorm hΦeig 0 2 (by decide)).1 (by decide)
  · exact (huniv hΦne hΦnorm hΦeig 1 3 (by decide)).1 (by decide)
  · exact (huniv hΦne hΦnorm hΦeig 0 1 (by decide)).2 (by decide)

/-- **Control 8 (second spin value, `N = 2`, `S = 1`).**  Repeats controls 1
and 3 (same-sublattice positivity and cross-sublattice negativity) on the
`N = 2` ground state.  `N = 0` is excluded: every correlation degenerates
there and no control would discriminate. -/
private theorem redPin_N2_sign_control :
    ∃ Φ : (Fin 4 → Fin 3) → ℂ, Φ ≠ 0 ∧ star Φ ⬝ᵥ Φ = 1 ∧
      0 < (twoSpinCorrelationS 0 2 Φ).re ∧
      (twoSpinCorrelationS 0 1 Φ).re < 0 := by
  obtain ⟨_μ, _hμ_def, _hrank, ⟨Φ, hΦne, hΦnorm, hΦeig⟩, huniv⟩ :=
    tasaki_problem_2_5_d_couplingOf_half witnessMarker witnessGraph 2
      witness_connected witness_bipartite witness_balanced (by norm_num)
  refine ⟨Φ, hΦne, hΦnorm, ?_, ?_⟩
  · exact (huniv hΦne hΦnorm hΦeig 0 2 (by decide)).1 (by decide)
  · exact (huniv hΦne hΦnorm hΦeig 0 1 (by decide)).2 (by decide)

/-- **Control 7, restated (identification control).**  Rewrites the
eigen-equation at the existential `μ` into one at `hermitianMinEigenvalue` of
the same Hamiltonian's Hermitian proof, using only the identification
conjunct (`μ = hermitianMinEigenvalue …`); deleting that conjunct removes the
term `hμ_def` this rewrite needs. -/
private theorem redPin_N1_identification_control :
    ∃ Φ : (Fin 4 → Fin 2) → ℂ, Φ ≠ 0 ∧ star Φ ⬝ᵥ Φ = 1 ∧
      (heisenbergHamiltonianS (couplingOf witnessGraph ((1 : ℂ) / 2)) 1).mulVec Φ =
        ((hermitianMinEigenvalue
            (heisenbergHamiltonianS_isHermitian_of_real
              (couplingOf_real witnessGraph (J := (1 : ℂ) / 2) (by norm_num)) 1) :
                ℝ) : ℂ) • Φ := by
  obtain ⟨μ, hμ_def, _hrank, ⟨Φ, hΦne, hΦnorm, hΦeig⟩, _huniv⟩ :=
    tasaki_problem_2_5_d_couplingOf_half witnessMarker witnessGraph 1
      witness_connected witness_bipartite witness_balanced (le_refl 1)
  exact ⟨Φ, hΦne, hΦnorm, hμ_def ▸ hΦeig⟩

end LatticeSystem.Tests.Problem25dGroundStateCorrelationSign
