import LatticeSystem.Quantum.SpinS.Theorem23GroundStateDegeneracy
import LatticeSystem.Quantum.SpinS.Theorem22Connected
import LatticeSystem.Quantum.SpinS.ConnectedTheorem23
import LatticeSystem.Quantum.SpinS.StrictHOutsideFerrimagnetic
import LatticeSystem.Quantum.SpinS.Theorem23Sectors
import LatticeSystem.Lattice.Graph

/-!
# Red fixture: Tasaki §2.5 Theorem 2.3, p. 42 (unbalanced degeneracy)

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.3, p. 42 (statement), pp. 42–43 (proof sketch); Remark and eq. (2.5.13), p. 43
(general exchange couplings); the toy Hamiltonian (2.5.10), p. 41, is **not** a hypothesis of
the theorem, only an internal tool of the book's own proof; the degeneracy count rests on
Theorem A.16, p. 473; bipartiteness is standing from p. 37; connectedness is Footnote 28, p. 33.

Theorem 2.3 states: for a connected bipartite coupling `(Λ, B)` with `|A| ≥ 1` and `|B| ≥ 1`,
the ground states carry total spin `S_tot = ||A| − |B||·S` and the ground eigenspace is
`2 S_tot + 1` fold degenerate. This module pins two capstones, neither of which exists on
`main` yet:

* `tasaki_2_5_theorem_2_3_of_connected` — the theorem at general exchange (eq. (2.5.13),
  p. 43), for a connected bipartite coupling;
* `tasaki_2_5_theorem_2_3_couplingOf_half` — the same theorem at the printed model
  (eq. (2.5.1), p. 37, i.e. `couplingOf G (1/2)` in the ordered-pair convention of
  `heisenbergHamiltonianS`).

Both are pinned by *application* (not merely by ascribing their type), and pinned
**independently of each other**: the first pin is discharged directly at an explicit
coupling with every coupling hypothesis of `_of_connected` proved by hand, so that
implementing only the printed-model instance cannot turn this fixture green. This closes the
escape that was live in the Problem 2.5.d fixture two rounds ago, where only the printed
instance was pinned.

The pinned conjunct list forces all **three** printed conclusions: (K1) the total-spin
value, via the universal Casimir eigen-equation at `tasaki23PredictedCasimirValue`; (K2) the
degeneracy, via the `Module.finrank` equality; and (K3) the sector expansion with
Marshall-signed positive coefficients, via an explicit per-sector existence conjunct
(`∀ M ∈ tasaki23GroundStateSectors A N, Nonempty (magConfigS V N M) → ∃ v, …`, Control 9
below). K3 uses a plain (non-instance) `Nonempty` hypothesis rather than the `[Nonempty …]`
instance bracket that `tasaki_2_5_theorem_2_3_data_of_connected` carries internally
(`ConnectedTheorem23.lean:230`): the two produce the identical core `Prop` (the bracket is
only an elaboration hint, not part of the term), so this pin does not itself require or admit
a typeclass-binder escape. A capstone that omits this conjunct, or states it for only some
admissible sector, fails Control 9 to even destructure — verified by mutation.

## The witness

`V := Fin 5`, `G := SimpleGraph.pathGraph 5` (edges `{0,1},{1,2},{2,3},{3,4}`),
`A := {0, 2, 4}` (`|A| = 3`), `B := {1, 3}` (`|B| = 2`). This witness is:
* unbalanced (`|A| ≠ |B|`), which is the entire content of Theorem 2.3 over Theorem 2.2;
* connected (`pathGraph_connected`) and bipartite for this marker;
* **not** complete bipartite with respect to `A`: of the six crossing pairs, `{0,3}` and
  `{1,4}` are *not* path edges. A route through `hJ_pos` over `bipartiteCompleteGraphOf A`
  (the toy Hamiltonian's own bond graph, (2.5.10) p. 41) is inapplicable here.

Smaller or star-shaped witnesses do **not** discriminate: on `Fin 3` with `A = {0, 2}` the
path *is* the complete bipartite graph (the only crossing pairs `{0,1},{1,2}` are exactly its
edges), and a star with a single `B`-site likewise has every crossing pair as an edge — either
would silently admit a complete-bipartite-only route. This is the same trap the four-cycle
sprang for the Theorem 2.2 fixture at `|A| = |B| = 2`; five sites split 3+2 on a path is the
smallest witness this project has found that is unbalanced, connected, bipartite and *not*
complete bipartite.

## Controls (see the individual `example`s below for citations)

1. Degeneracy `= 2` at `N = 1` (fails an `≤ 1`-shaped "at most one" statement).
2. Degeneracy `= 3` at `N = 2` (fails a constant or `N`-independent formula).
3. The Casimir value at the witness is `3/4 ≠ 0` (fails a restatement of the balanced,
   `S_tot = 0` case).
4. **Marker inversion**: exchanging `A` and `B` (same graph) gives the *same* degeneracy and
   the *same* Casimir value. This is the load-bearing control against an orientation
   hypothesis (`|B| ≤ |A|`, called `horient` throughout the existing chain) that the printed
   theorem does not state. If the new capstone silently inherits `horient`, this control's
   call site (which supplies no such hypothesis, at a marker with `|B| > |A|`) fails to
   elaborate against the extra binder.
5. The balanced four-site witness (`Fin 4`, `A = {0, 2}`) gives degeneracy `1`, agreeing with
   the merged Theorem 2.2 capstone (catches an off-by-one).
6. A record that `{0, 3}` is a crossing pair of the marker and not a path edge, so control 3's
   route cannot be complete-bipartite positivity.
7. The existence conjunct is *consumed*: a ground state `Φ` is destructured out of the
   statement and fed to the universal Casimir conjunct to derive the non-zero value.
8. The degeneracy is phrased as `Module.finrank` of the Hamiltonian's `μ`-eigenspace, **not**
   as `(tasaki23GroundStateSectors A N).card`. The two are numerically equal at every witness
   (`tasaki23GroundStateSectors_card`, already proved, unconditionally, with no Hamiltonian,
   coupling or connectivity input anywhere in its proof) but are not the same reading, and the
   book's claim is a Hilbert-space dimension count (Theorem A.16), not sector bookkeeping. A
   control exercising this distinction closes the module.
9. **K3 consumption.** At the admissible sector `M = 2` (`|B|·N ≤ 2 ≤ |A|·N`, `N = 1`), the
   per-sector conjunct is instantiated and destructured into an actual Marshall-signed
   positive-coefficient eigenvector. Fails for a capstone that omits the per-sector conjunct
   entirely, or restricts it to a strict subset of the admissible sectors — verified by
   mutation (removing the conjunct breaks the destructure itself, an arity mismatch, before
   any arithmetic is checked).

## One gap this fixture cannot close (measured, not assumed)

* **Extra typeclass binders on the declaration's own parameter list.** A hypothesis
  smuggled in as a *top-level* instance binder of `tasaki_2_5_theorem_2_3_of_connected`
  itself (e.g. `[Nonempty V]`, `[DecidableRel G.Adj]`, `[IsAlgClosed ℂ]`) passes every control
  here, because instance arguments are synthesized silently at each call site and never show
  up as an elaboration failure. This is distinct from the `Nonempty (magConfigS V N M)`
  hypothesis inside the K3 conjunct above, which this fixture does pin (as a plain, explicit
  hypothesis the caller must discharge per sector, not a top-level instance). Must be checked
  by reading the elaborated binder list of the merged declaration
  (`#check @tasaki_2_5_theorem_2_3_of_connected`) by hand once it exists.
* **Smuggled explicit hypotheses.** An added explicit hypothesis that the witness below
  happens to discharge (e.g. an `hJ_pos` over `bipartiteCompleteGraphOf`, a `c`/`c_toy`
  strictness binder, or an `horient` binder that the witness order below happens to satisfy)
  narrows the theorem while leaving every example here green, because the fixture always
  supplies *some* proof for every binder it is asked for. Must be checked by enumerating the
  elaborated explicit binders and comparing them one by one against the printed hypothesis
  list (connected, bipartite, `|A|, |B| ≥ 1`, `1 ≤ N`, plus the coupling-faithfulness binders
  eq. (2.5.13) licenses) — not by this fixture passing.
-/

namespace LatticeSystem.Tests.Theorem23UnbalancedDegeneracy

open LatticeSystem.Quantum
open LatticeSystem.Lattice
open Matrix Module

/-! ## The unbalanced witness: five sites on a path, split three and two -/

/-- The `{0, 2, 4}` / `{1, 3}` split on the five-site path: `|A| = 3`, `|B| = 2`. -/
def unbalancedMarker : Fin 5 → Bool := fun x => decide (x = 0 ∨ x = 2 ∨ x = 4)

/-- **Marker-inversion control witness.** Exchanges the two sublattices of
`unbalancedMarker`: `A = {1, 3}` (`|A| = 2`), `B = {0, 2, 4}` (`|B| = 3`). -/
def unbalancedMarkerFlip : Fin 5 → Bool := fun x => ! unbalancedMarker x

/-- The balanced `{0, 2}` / `{1, 3}` split on the four-site path, matching the witness used
for the Theorem 2.2 fixture. -/
def balancedMarker : Fin 4 → Bool := fun x => decide (x = 0 ∨ x = 2)

/-- `|A| = 3` for `unbalancedMarker`. -/
theorem unbalancedMarker_card_true :
    (Finset.univ.filter (fun x : Fin 5 => unbalancedMarker x = true)).card = 3 := by decide

/-- `|B| = 2` for `unbalancedMarker`. -/
theorem unbalancedMarker_card_false :
    (Finset.univ.filter (fun x : Fin 5 => (! unbalancedMarker x) = true)).card = 2 := by decide

/-- The five-site path is connected (Footnote 28, p. 33). -/
theorem unbalancedWitness_connected : (SimpleGraph.pathGraph 5).Connected :=
  SimpleGraph.pathGraph_connected 4

/-- `unbalancedMarker` splits the five-site path bipartitely (standing assumption, p. 37). -/
theorem unbalancedWitness_bipartite :
    ∀ x y : Fin 5, (SimpleGraph.pathGraph 5).Adj x y → unbalancedMarker x ≠ unbalancedMarker y := by
  decide

/-- `unbalancedMarkerFlip` splits the five-site path bipartitely too: flipping every value of
a bipartite marker preserves bipartiteness. -/
theorem unbalancedWitnessFlip_bipartite :
    ∀ x y : Fin 5,
      (SimpleGraph.pathGraph 5).Adj x y → unbalancedMarkerFlip x ≠ unbalancedMarkerFlip y := by
  decide

/-- The four-site path is connected (Footnote 28, p. 33), matching the Theorem 2.2 witness. -/
theorem balancedWitness_connected : (SimpleGraph.pathGraph 4).Connected :=
  SimpleGraph.pathGraph_connected 3

/-- `balancedMarker` splits the four-site path bipartitely (standing assumption, p. 37). -/
theorem balancedWitness_bipartite :
    ∀ x y : Fin 4, (SimpleGraph.pathGraph 4).Adj x y → balancedMarker x ≠ balancedMarker y := by
  decide

/-- **Control 6.** `{0, 3}` is a crossing pair of `unbalancedMarker` (one in `A`, one in `B`)
but is *not* an edge of the five-site path: the witness is not complete bipartite, so no
route through `hJ_pos` over `bipartiteCompleteGraphOf unbalancedMarker` (the toy Hamiltonian's
own bond graph, (2.5.10) p. 41) is available at this witness. -/
theorem unbalancedWitness_not_completeBipartite :
    unbalancedMarker 0 ≠ unbalancedMarker 3 ∧ ¬ (SimpleGraph.pathGraph 5).Adj (0 : Fin 5) 3 := by
  decide

/-! ## Direct pin of `tasaki_2_5_theorem_2_3_of_connected`, at an explicit coupling

Applied directly at `J := couplingOf (pathGraph 5) (1/2)`, with every coupling hypothesis of
the general-exchange capstone discharged by hand from `couplingOf`'s definition and
`unbalancedWitness_bipartite`, rather than through the printed-model closure. This pins the
general capstone independently of `tasaki_2_5_theorem_2_3_couplingOf_half`: an implementation
that proves only the printed instance leaves this pin red. -/

/-- **Control 1 + control 6 + control 7 (direct `_of_connected` pin, `N = 1`).** At the
unbalanced witness with `J := couplingOf (pathGraph 5) (1/2)` and `N = 1`: the ground
eigenspace has dimension `2` (`||A| − |B||·N + 1 = 1·1 + 1`, control 1), a ground state exists
and is fed to the universal Casimir conjunct (control 7) to exhibit the non-zero predicted
value `3/4` (control 3), which fails for a restatement of Theorem 2.2's `S_tot = 0`. The
per-sector K3 conjunct (control 9) is destructured too and is passed through unchanged, to
pin it on `_of_connected` independently of the `couplingOf_half` instance below. -/
example :
    ∃ μ : ℝ,
      Module.finrank ℂ ↥(Module.End.eigenspace
          (Matrix.toLin' (heisenbergHamiltonianS (couplingOf (SimpleGraph.pathGraph 5)
            ((1 : ℂ) / 2)) 1)) (μ : ℂ)) = 2 ∧
      (∀ M ∈ tasaki23GroundStateSectors (V := Fin 5) unbalancedMarker 1,
        Nonempty (magConfigS (Fin 5) 1 M) →
        ∃ v : magConfigS (Fin 5) 1 M → ℝ,
          (∀ σ, 0 < v σ) ∧
          (heisenbergHamiltonianS (couplingOf (SimpleGraph.pathGraph 5) ((1 : ℂ) / 2)) 1).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS unbalancedMarker τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS unbalancedMarker τ.1).re * v τ : ℝ) : ℂ))) ∧
      (∃ Φ : (Fin 5 → Fin 2) → ℂ, Φ ≠ 0 ∧
        (heisenbergHamiltonianS (couplingOf (SimpleGraph.pathGraph 5) ((1 : ℂ) / 2)) 1).mulVec Φ
          = (μ : ℂ) • Φ ∧
        (totalSpinSSquared (Fin 5) 1).mulVec Φ = (((3 : ℝ) / 4 : ℝ) : ℂ) • Φ) := by
  obtain ⟨μ, hdim, hsector, hexists, hcas, hmin⟩ :=
    tasaki_2_5_theorem_2_3_of_connected (N := 1) unbalancedMarker (SimpleGraph.pathGraph 5)
      unbalancedWitness_connected unbalancedWitness_bipartite
      (by decide) (by decide) (le_refl 1)
      (fun x y => by
        unfold couplingOf
        by_cases h : (SimpleGraph.pathGraph 5).Adj x y <;> simp [h])
      (fun x y => by
        unfold couplingOf
        by_cases h : (SimpleGraph.pathGraph 5).Adj x y <;> simp [h])
      (couplingOf_symm (SimpleGraph.pathGraph 5) ((1 : ℂ) / 2))
      (fun x y => by
        unfold couplingOf
        by_cases h : (SimpleGraph.pathGraph 5).Adj x y <;> simp [h])
      (fun x y hAeq => by
        have hnadj : ¬ (SimpleGraph.pathGraph 5).Adj x y :=
          fun hadj => (unbalancedWitness_bipartite x y hadj) hAeq
        simp [couplingOf, hnadj])
      (fun x y h => by simp [couplingOf, h])
      (fun x y h => by simp [couplingOf, h])
  refine ⟨μ, ?_, hsector, ?_⟩
  · rw [hdim]
    decide
  · obtain ⟨Φ, hΦne, hΦeig⟩ := hexists
    refine ⟨Φ, hΦne, hΦeig, ?_⟩
    have hcasΦ := hcas hΦeig
    have hval : (tasaki23PredictedCasimirValue (V := Fin 5) unbalancedMarker 1 : ℝ) = 3 / 4 := by
      unfold tasaki23PredictedCasimirValue tasaki23PredictedTotalSpin
      rw [unbalancedMarker_card_true, unbalancedMarker_card_false]
      norm_num
    rw [hval] at hcasΦ
    exact hcasΦ

/-! ## Pin of `tasaki_2_5_theorem_2_3_couplingOf_half`, at the printed model -/

/-- **Control 2 (`N = 2`).** At the printed model, `N = 2`: the ground eigenspace has
dimension `3` (`1 · 2 + 1`), separating the formula from both a constant `2` and from the
Theorem 2.1 saturated formula `|V|·N + 1 = 11`. -/
example :
    ∃ μ : ℝ,
      Module.finrank ℂ ↥(Module.End.eigenspace
          (Matrix.toLin' (heisenbergHamiltonianS
            (couplingOf (SimpleGraph.pathGraph 5) ((1 : ℂ) / 2)) 2)) (μ : ℂ)) = 3 := by
  obtain ⟨μ, hdim, -, -, -, -⟩ :=
    tasaki_2_5_theorem_2_3_couplingOf_half (N := 2) unbalancedMarker (SimpleGraph.pathGraph 5)
      unbalancedWitness_connected unbalancedWitness_bipartite
      (by decide) (by decide) (by decide)
  refine ⟨μ, ?_⟩
  rw [hdim]
  decide

/-- **Control 9 (K3 consumption, load-bearing).** At the admissible sector `M = 2`
(`min(|A|, |B|)·N = 2 ≤ M ≤ max(|A|, |B|)·N = 3`, `N = 1`), the per-sector conjunct is
instantiated and destructured into an actual positive-coefficient Marshall-signed eigenvector.
Fails to even destructure for a capstone that omits this conjunct — verified by mutation:
removing it and re-running this control raises `rcases failed: ... is not an inductive
datatype`, an arity mismatch, before any arithmetic is checked. -/
example :
    ∃ μ : ℝ, ∃ v : magConfigS (Fin 5) 1 2 → ℝ, (∀ σ, 0 < v σ) ∧
      (heisenbergHamiltonianS (couplingOf (SimpleGraph.pathGraph 5) ((1 : ℂ) / 2)) 1).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS unbalancedMarker τ.1).re * v τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS unbalancedMarker τ.1).re * v τ : ℝ) : ℂ)) := by
  obtain ⟨μ, -, hsector, -, -, -⟩ :=
    tasaki_2_5_theorem_2_3_couplingOf_half (N := 1) unbalancedMarker (SimpleGraph.pathGraph 5)
      unbalancedWitness_connected unbalancedWitness_bipartite
      (by decide) (by decide) (le_refl 1)
  have hmem : 2 ∈ tasaki23GroundStateSectors (V := Fin 5) unbalancedMarker 1 := by decide
  have hne : Nonempty (magConfigS (Fin 5) 1 2) :=
    magConfigS_nonempty_of_le_card_mul
      (tasaki23GroundStateSectors_le_card_mul unbalancedMarker 1 hmem)
  obtain ⟨v, hv, heq⟩ := hsector 2 hmem hne
  exact ⟨μ, v, hv, heq⟩

/-- **Control 4 (marker inversion, the load-bearing control).** The *same* printed-model
capstone, applied at `unbalancedMarkerFlip` (`|A| = 2`, `|B| = 3`, the opposite orientation)
on the *same* graph, gives the *same* degeneracy `2` and the *same* Casimir value `3/4`. No
`horient`-shaped hypothesis is supplied at this call site (there is none in the printed
theorem, whose `S_tot` carries an *outer* absolute value); if the capstone silently inherited
one of the fixed orientation `|B| ≤ |A|` from `tasaki23_strict_hOutside_of_connected` or
`tasaki_2_5_theorem_2_3_data_of_connected`, this call site — at the opposite orientation,
supplying no such hypothesis — would fail to elaborate against the extra binder. -/
example :
    ∃ μ : ℝ,
      Module.finrank ℂ ↥(Module.End.eigenspace
          (Matrix.toLin' (heisenbergHamiltonianS
            (couplingOf (SimpleGraph.pathGraph 5) ((1 : ℂ) / 2)) 1)) (μ : ℂ)) = 2 ∧
      (∃ Φ : (Fin 5 → Fin 2) → ℂ, Φ ≠ 0 ∧
        (heisenbergHamiltonianS (couplingOf (SimpleGraph.pathGraph 5) ((1 : ℂ) / 2)) 1).mulVec Φ
          = (μ : ℂ) • Φ ∧
        (totalSpinSSquared (Fin 5) 1).mulVec Φ = (((3 : ℝ) / 4 : ℝ) : ℂ) • Φ) := by
  obtain ⟨μ, hdim, -, hexists, hcas, -⟩ :=
    tasaki_2_5_theorem_2_3_couplingOf_half (N := 1) unbalancedMarkerFlip
      (SimpleGraph.pathGraph 5)
      unbalancedWitness_connected unbalancedWitnessFlip_bipartite
      (by decide) (by decide) (le_refl 1)
  refine ⟨μ, ?_, ?_⟩
  · rw [hdim]
    decide
  · obtain ⟨Φ, hΦne, hΦeig⟩ := hexists
    refine ⟨Φ, hΦne, hΦeig, ?_⟩
    have hcasΦ := hcas hΦeig
    have hval :
        (tasaki23PredictedCasimirValue (V := Fin 5) unbalancedMarkerFlip 1 : ℝ) = 3 / 4 := by
      unfold tasaki23PredictedCasimirValue tasaki23PredictedTotalSpin
      have hcardA : (Finset.univ.filter
          (fun x : Fin 5 => unbalancedMarkerFlip x = true)).card = 2 := by decide
      have hcardB : (Finset.univ.filter
          (fun x : Fin 5 => (! unbalancedMarkerFlip x) = true)).card = 3 := by decide
      rw [hcardA, hcardB]
      norm_num
    rw [hval] at hcasΦ
    exact hcasΦ

/-- **Control 5 (balanced cross-check).** At the balanced four-site witness the printed-model
capstone gives degeneracy `1`, agreeing with the merged Theorem 2.2 capstone
`tasaki_2_5_theorem_2_2_couplingOf_half` and catching an off-by-one in the degeneracy
formula (a formula uniformly off by one would pass controls 1–2 but fail here, since `0·N`
absorbs the error differently from `1·N` and `2·N`). -/
example :
    ∃ μ : ℝ,
      Module.finrank ℂ ↥(Module.End.eigenspace
          (Matrix.toLin' (heisenbergHamiltonianS
            (couplingOf (SimpleGraph.pathGraph 4) ((1 : ℂ) / 2)) 1)) (μ : ℂ)) = 1 := by
  obtain ⟨μ, hdim, -, -, -, -⟩ :=
    tasaki_2_5_theorem_2_3_couplingOf_half (N := 1) balancedMarker (SimpleGraph.pathGraph 4)
      balancedWitness_connected balancedWitness_bipartite
      (by decide) (by decide) (by decide)
  refine ⟨μ, ?_⟩
  rw [hdim]
  decide

/-! ## Control 8: the eigenspace reading is not the sector-count reading -/

/-- **Control 8 (documentation, does not by itself pin anything new).** The cardinality of
`tasaki23GroundStateSectors` already equals `tasaki23PredictedDegeneracy` unconditionally —
`tasaki23GroundStateSectors_card` needs no Hamiltonian, coupling or connectivity hypothesis,
only `Nat.card_Icc` arithmetic. Every `example` above is phrased on `Module.finrank` of the
Hamiltonian's `μ`-eigenspace instead, which is the reading the book's own proof sketch commits
to (Theorem A.16, "the degeneracy of the ground states in the whole Hilbert space", p. 473).
A future capstone stated only as
`(tasaki23GroundStateSectors A N).card = tasaki23PredictedDegeneracy A N` would prove this
control below (already true, right now, with no new declaration) yet leave every
eigenspace-phrased pin above red — which is exactly the discrimination this control records. -/
example :
    (tasaki23GroundStateSectors (V := Fin 5) unbalancedMarker 1).card =
      tasaki23PredictedDegeneracy (V := Fin 5) unbalancedMarker 1 :=
  tasaki23GroundStateSectors_card unbalancedMarker 1

end LatticeSystem.Tests.Theorem23UnbalancedDegeneracy
