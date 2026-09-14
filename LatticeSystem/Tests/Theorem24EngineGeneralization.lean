import LatticeSystem.Quantum.SpinS.DressedAxisSwapParityStepStrictPos
import LatticeSystem.Quantum.SpinS.DressedAxisSwapParityBondStrictPos
import LatticeSystem.Quantum.SpinS.DressedAxisSwapRaiseLowerStrictNeg
import LatticeSystem.Quantum.SpinS.DressedHeisenbergRaiseLower
import LatticeSystem.Quantum.SpinS.DressedAxisSwapIonParityLambdaOne
import LatticeSystem.Quantum.SpinS.DressedAxisSwapBondParityDNonneg
import LatticeSystem.Quantum.SpinS.DressedAxisSwapBlockPowPos
import LatticeSystem.Quantum.SpinS.DressedAxisSwapBlockIrreducible
import LatticeSystem.Quantum.SpinS.DressedAxisSwapIonParityBlockIrreducibleLambdaOne
import LatticeSystem.Quantum.SpinS.DressedAxisSwapBondParityBlockIrreducibleDNonneg

/-!
# Signature pins: connected-graph generalization of the Theorem 2.4 engine (Red fixture)

Issue #5473 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori), PR-2a of the connectivity/reachability
arc. Pins the exact **future** signatures of the eleven conditional irreducibility-engine
statements that PR-2a generalizes **in place** from `bipartiteCompleteGraphOf A` to a general
`G : SimpleGraph Λ` (plus the explicit sign-gauge hypothesis `hGbip : ∀ x y, G.Adj x y →
A x ≠ A y`, since at a general `G` bipartiteness is no longer recoverable from adjacency the way
`bipartiteCompleteGraphOf_adj_sublattice_ne` recovers it today).

Each pin below states the target (post-generalization) signature and discharges it by *calling
the current, still-specialized theorem*. This must fail today: the current theorem's hypothesis
`hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re` (and, where applicable,
its step/reachability hypothesis on `bipartiteCompleteGraphOf A`) is not defeq to the pin's
`hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re` (resp. the step/reachability relation at `G`) for
an arbitrary `G`, so elaboration reports a type mismatch citing `bipartiteCompleteGraphOf A`
against the free variable `G` — not an `unknown identifier` and not an `unknown module`. After
PR-2a generalizes the eleven statements in place, each pin becomes definitionally the identity
application and typechecks.

The three unconditional complete-bipartite engines
(`shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible`,
`..._isIrreducible_lambda_one_D_pos`, `..._isIrreducible_D_nonneg`) are deliberately **not** pinned
here: PR-2a leaves their statements exactly as they are (still at `bipartiteCompleteGraphOf A`,
via `hA_ne`/`hB_ne`) and only touches their proofs, since generalizing the eleven engines they
call changes what those proofs must supply at the call site.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, pp. 43–44.
-/

namespace LatticeSystem.Tests.Theorem24EngineGeneralization

open LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Signature pin 1/11** (`shiftedDressedAxisSwappedReMatrix_apply_pos_of_parityStepS_bipartite`,
`DressedAxisSwapParityStepStrictPos.lean`). Unified `ParityStepS` strict positivity at a general
connected-bipartite `G`. -/
example (A : Λ → Bool) (G : SimpleGraph Λ) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    (c : ℝ)
    {σ τ : Λ → Fin (N + 1)} (hstep : ParityStepS G σ τ) :
    0 < shiftedDressedAxisSwappedReMatrix A J lam D N c τ σ :=
  shiftedDressedAxisSwappedReMatrix_apply_pos_of_parityStepS_bipartite
    A hJim hJnn hJ_pos_G hJself hJbip hlam hlb hub hDim hDpos c hstep

/-- **Signature pin 2/11**
(`shiftedDressedAxisSwappedReMatrix_apply_pos_of_parityBondStepS_bipartite`,
`DressedAxisSwapParityBondStrictPos.lean`). Bond-parity strict positivity at a general
connected-bipartite `G`, `D.re ≥ 0`. -/
example (A : Λ → Bool) (G : SimpleGraph Λ) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    (c : ℝ)
    {σ τ : Λ → Fin (N + 1)} (hstep : ParityBondStepS G σ τ) :
    0 < shiftedDressedAxisSwappedReMatrix A J lam D N c τ σ :=
  shiftedDressedAxisSwappedReMatrix_apply_pos_of_parityBondStepS_bipartite
    A hJim hJnn hJ_pos_G hJself hJbip hlam hlb hub hDim hDnn c hstep

/-- **Signature pin 3/11**
(`shiftedDressedAxisSwappedReMatrix_apply_pos_of_raiseLowerStepS_bipartite`,
`DressedAxisSwapRaiseLowerStrictNeg.lean`). Transverse-step strict positivity at a general
connected-bipartite `G`. -/
example (A : Λ → Bool) (G : SimpleGraph Λ) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re ≤ 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    (c : ℝ)
    {σ τ : Λ → Fin (N + 1)} (hstep : RaiseLowerStepS G σ τ) :
    0 < shiftedDressedAxisSwappedReMatrix A J lam D N c τ σ :=
  shiftedDressedAxisSwappedReMatrix_apply_pos_of_raiseLowerStepS_bipartite
    A hJim hJnn hJ_pos_G hJself hJbip hlam hlb hub hDim hDnn c hstep

/-- **Signature pin 4/11** (`neg_dressedHeisenbergSReMatrix_apply_pos_of_raiseLowerStepS_bipartite`,
`DressedHeisenbergRaiseLower.lean`). The isotropic-dressed transverse-step positivity, at a
general connected-bipartite `G`. -/
example (A : Λ → Bool) (G : SimpleGraph Λ) {J : Λ → Λ → ℂ} (M : ℕ)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    {σ τ : Λ → Fin (M + 1)}
    (hstep : RaiseLowerStepS G σ τ) :
    0 < (-dressedHeisenbergSReMatrix A J M) τ σ :=
  neg_dressedHeisenbergSReMatrix_apply_pos_of_raiseLowerStepS_bipartite
    A M hJ_real hJ_pos_G hJ_sym hstep

/-- **Signature pin 5/11**
(`shiftedDressedAxisSwappedReMatrix_apply_pos_of_ionParityStepS_lambda_one`,
`DressedAxisSwapIonParityLambdaOne.lean`). Ion-only strict positivity at `lambda = 1`, `D > 0`, at
a general connected-bipartite `G`. -/
example (A : Λ → Bool) (G : SimpleGraph Λ) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    (c : ℝ)
    {σ τ : Λ → Fin (N + 1)}
    (hstep : IonParityStepS G σ τ) :
    0 < shiftedDressedAxisSwappedReMatrix A J 1 D N c τ σ :=
  shiftedDressedAxisSwappedReMatrix_apply_pos_of_ionParityStepS_lambda_one
    A hJim hJnn hJ_pos_G hJself hJbip hDim hDpos c hstep

/-- **Signature pin 6/11** (`shiftedDressedReMatParity_pow_apply_pos_of_ionParityReach_lam1`,
`DressedAxisSwapIonParityLambdaOne.lean`). Ion-only block matrix power positivity from ion-only
reachability at a general connected-bipartite `G`. -/
example (A : Λ → Bool) (G : SimpleGraph Λ) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J 1 D N σ σ ≤ c)
    (p : ℕ)
    {σ' σ : parityConfigS Λ N p}
    (hreach : IonParityReachableS G σ.1 σ'.1) :
    ∃ k : ℕ,
      0 < (shiftedDressedAxisSwappedReMatrixOnParityBlock A J 1 D N c p ^ k) σ' σ :=
  shiftedDressedReMatParity_pow_apply_pos_of_ionParityReach_lam1
    A hJim hJnn hJ_pos_G hJself hJbip hDim hDpos hc p hreach

/-- **Signature pin 7/11**
(`shiftedDressedAxisSwappedReMatrix_apply_pos_of_bondParityStepS_bipartite`,
`DressedAxisSwapBondParityDNonneg.lean`). Bond-only strict positivity with `D.re ≥ 0`, at a
general connected-bipartite `G`. -/
example (A : Λ → Bool) (G : SimpleGraph Λ) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    (c : ℝ)
    {σ τ : Λ → Fin (N + 1)}
    (hstep : BondParityStepS G σ τ) :
    0 < shiftedDressedAxisSwappedReMatrix A J lam D N c τ σ :=
  shiftedDressedAxisSwappedReMatrix_apply_pos_of_bondParityStepS_bipartite
    A hJim hJnn hJ_pos_G hJself hJbip hlam hlb hub hDim hDnn c hstep

/-- **Signature pin 8/11**
(`shiftedDressedAxisSwappedReMatrixOnParityBlock_pow_apply_pos_of_bondParityReachable`,
`DressedAxisSwapBondParityDNonneg.lean`). Bond-only block matrix power positivity at a general
connected-bipartite `G`, `D.re ≥ 0`. -/
example (A : Λ → Bool) (G : SimpleGraph Λ) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    {c : ℝ}
    (hc : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ ≤ c)
    (p : ℕ)
    {σ' σ : parityConfigS Λ N p}
    (hreach : BondParityReachableS G σ.1 σ'.1) :
    ∃ k : ℕ,
      0 < (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p ^ k) σ' σ :=
  shiftedDressedAxisSwappedReMatrixOnParityBlock_pow_apply_pos_of_bondParityReachable
    A hJim hJnn hJ_pos_G hJself hJbip hlam hlb hub hDim hDnn hc p hreach

/-- **Signature pin 9/11**
(`shiftedDressedAxisSwappedReMatrixOnParityBlock_pow_apply_pos_of_parityReachable`,
`DressedAxisSwapBlockPowPos.lean`). Full block matrix power positivity from parity reachability
at a general connected-bipartite `G`, case (i.2) strict. -/
example (A : Λ → Bool) (G : SimpleGraph Λ) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ ≤ c)
    (p : ℕ)
    {σ' σ : parityConfigS Λ N p}
    (hreach : ParityReachableS G σ.1 σ'.1) :
    ∃ k : ℕ,
      0 < (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p ^ k) σ' σ :=
  shiftedDressedAxisSwappedReMatrixOnParityBlock_pow_apply_pos_of_parityReachable
    A hJim hJnn hJ_pos_G hJself hJbip hlam hlb hub hDim hDpos hc p hreach

/-- **Signature pin 10/11**
(`shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_of_parityReachable_total`,
`DressedAxisSwapBlockIrreducible.lean`). The interior conditional irreducibility engine, at a
general connected-bipartite `G` and an external total-reachability hypothesis over `G`. -/
example (A : Λ → Bool) (G : SimpleGraph Λ) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (p : ℕ)
    [Nonempty (parityConfigS Λ N p)]
    (hreach_total : ∀ σ' σ : parityConfigS Λ N p, σ' ≠ σ →
      ParityReachableS G σ.1 σ'.1) :
    (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p).IsIrreducible :=
  shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_of_parityReachable_total
    A hJim hJnn hJ_pos_G hJself hJbip hlam hlb hub hDim hDpos hc_strict p hreach_total

/-- **Signature pin 11/11** (`shiftedDressedReMatParity_irred_of_ionParityReach_total_lam1`,
`DressedAxisSwapIonParityBlockIrreducibleLambdaOne.lean`). The `lambda = 1` boundary conditional
irreducibility engine, at a general connected-bipartite `G`. -/
example (A : Λ → Bool) (G : SimpleGraph Λ) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J 1 D N σ σ < c)
    (p : ℕ)
    [Nonempty (parityConfigS Λ N p)]
    (hreach_total : ∀ σ' σ : parityConfigS Λ N p, σ' ≠ σ →
      IonParityReachableS G σ.1 σ'.1) :
    (shiftedDressedAxisSwappedReMatrixOnParityBlock A J 1 D N c p).IsIrreducible :=
  shiftedDressedReMatParity_irred_of_ionParityReach_total_lam1
    A hJim hJnn hJ_pos_G hJself hJbip hDim hDpos hc_strict p hreach_total

/-- **Signature pin 12/12**
(`shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_of_bondParityReachable_total`,
`DressedAxisSwapBondParityBlockIrreducibleDNonneg.lean`). The `D.re ≥ 0` boundary conditional
irreducibility engine, at a general connected-bipartite `G`. This file pins **twelve**, not
eleven, `bipartiteCompleteGraphOf`-typed conditional-engine statements: grepping
`(bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re` across the eleven modules named in the
module doc above, and excluding the three unconditional complete-bipartite engines that PR-2a
leaves stated as-is, yields exactly this set of twelve theorem names (positive control: the same
probe finds 0 occurrences of that hypothesis shape in a module known to be already general, e.g.
`ParityReachConnectedTotal.lean`). Pinning a superset of the declared eleven is deliberately safe
per the two known under-pinning failure modes (conjunct halving, engine halving); main should
reconcile the count against the design phase's own list before Green. -/
example (A : Λ → Bool) (G : SimpleGraph Λ) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (p : ℕ)
    [Nonempty (parityConfigS Λ N p)]
    (hreach_total : ∀ σ' σ : parityConfigS Λ N p, σ' ≠ σ →
      BondParityReachableS G σ.1 σ'.1) :
    (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p).IsIrreducible :=
  shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_of_bondParityReachable_total
    A hJim hJnn hJ_pos_G hJself hJbip hlam hlb hub hDim hDnn hc_strict p hreach_total

/-- **Discriminating witness (four-vertex path, not the four-cycle)**, reused from PR-1's fixture
(`Tests/ParityReachabilityConnected.lean`). On `V = Fin 4`, `A = {0, 2}`, `pathGraph 4` is
connected and bipartite for this marking, and is genuinely a different graph from
`bipartiteCompleteGraphOf A`: it is missing the crossing edge `{0, 3}`. `cycleGraph 4` would
**not** discriminate here — with this same marking its edge set is exactly the four crossing
pairs, so it coincides with `bipartiteCompleteGraphOf A` and every pin above would already hold
for it via the unchanged theorems. -/
example :
    (SimpleGraph.pathGraph 4).Connected ∧
      (bipartiteCompleteGraphOf (fun x : Fin 4 => decide (x = 0 ∨ x = 2))).Adj 0 3 ∧
      ¬ (SimpleGraph.pathGraph 4).Adj (0 : Fin 4) 3 := by
  refine ⟨SimpleGraph.pathGraph_connected 3, ?_, ?_⟩
  · simp
  · simp [SimpleGraph.pathGraph_adj]

end LatticeSystem.Tests.Theorem24EngineGeneralization
