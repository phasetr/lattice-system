import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSTheorem24
import LatticeSystem.Quantum.SpinS.DressedAxisSwapBlockIrreducibleStructural
import LatticeSystem.Quantum.SpinS.DressedAxisSwapIonParityBlockIrreducibleLambdaOne
import LatticeSystem.Quantum.SpinS.DressedAxisSwapBondParityBlockIrreducibleDNonneg

/-!
# Signature pins: connected-graph Theorem 2.4 case (i) + SU(2) endpoints (Red fixture)

Issue #5473 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori), PR-2b of the connectivity/reachability
arc. Pins the exact signatures of:

1. the three **unconditional connected-graph irreducibility engines** that PR-2b adds (the
   connected-graph analogues of the unconditional complete-bipartite engines
   `shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible`,
   `..._isIrreducible_lambda_one_D_pos`, `..._isIrreducible_D_nonneg`). Engine 3 (the `D ≥ 0`
   boundary) additionally carries `hΛnt : Nontrivial Λ`, absent from engines 1/2: it routes
   through `bondParityReachableS_total_of_connected`
   (`LatticeSystem/Quantum/SpinS/ParityReachConnectedTotal.lean:158`), which requires
   `Nontrivial V`. Without it, `Λ = Unit`, `N = 2`, `G = ⊥`, `J = 0`, `lam = D = 0`, `c = 1`,
   `p = 0` satisfies every remaining hypothesis while the shifted matrix on the two-element
   `p = 0` parity block is the identity matrix, which is not irreducible;
2. the **two R3 (SU(2) corner) region-endpoint declarations** (target `finrank ≤ 1` and zero
   axis-3 magnetization) that PR-2b adds, replacing the scaffolding-scalar hypotheses
   `c_axis`/`hc_axis_strict`, `c_mlm`/`c_toy`/`hT23` and the complete-bipartite `hA_ne`/`hB_ne`
   bookkeeping with `hGconn`/`hGbip`/`hJ_pos_G`/`hJ_off` at a general connected graph `G`. R1
   (`-1 < λ < 1`, `D ≥ 0`) and R2 (`λ = 1`, `D > 0`) connected endpoints are **not** pinned here:
   see Part 2 below.

The eight existing case-(i)/SU(2) endpoint declarations are **not** pinned for generalization
here. Unit for that eight: general spin-`S` target endpoints binding both the *fixed-graph*
positivity `hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re` and
`hT23 : tasaki_2_5_theorem_2_3 A N J c_mlm` — namely
`anisotropicHeisenbergS_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_D_nonneg_general`
and its seven siblings across `AnisotropicHeisenbergSpinSMLMEndpoint.lean`,
`AnisotropicHeisenbergSpinSDNonnegBoundary.lean`,
`AnisotropicHeisenbergSpinSLambdaOneBoundary.lean` and
`AnisotropicHeisenbergSpinSSU2Boundary.lean`. Adding the two region-dispatch wrappers of
`AnisotropicHeisenbergSpinSTheorem24.lean` makes ten, and widening the unit past the general
spin-`S` case-(i)/SU(2) endpoints (to the spin-`1/2` specializations and the case-(ii) targets)
raises it further, so the unit has to travel with the number.

It is exactly that `hJpos` which discharges the sixth premise of `hT23`
(`LatticeSystem/Quantum/SpinS/Theorem23StructuralBipartiteToy.lean:47`), which is the very same
fixed-graph positivity. A connected-graph `hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re` does not
discharge it, so none of the eight can be re-derived at a merely connected `G` along its own route.

The obstruction is therefore one of proof route, not of truth. Substituting `hJ_pos_G` for `hJpos`
*without* a connectedness hypothesis leaves `G` unconstrained and does make the SU(2) `finrank`
statement false: `Λ = Fin 2`, `A = (· = 0)`, `N = 1`, `G = ⊥`, `J ≡ 0` satisfies every hypothesis
of that connectedness-free variant (`hGbip`, `hJ_pos_G` and `hJ_off` hold vacuously at `G = ⊥`,
and `h_card_eq` reads `1 = 1`) while `H = 0` has a 4-dimensional ground eigenspace. But
`(⊥ : SimpleGraph (Fin 2))` is *not* connected, so `hGconn` removes that witness, and under
`hGconn` both SU(2) statements do hold: the support graph of `J` contains `G`, hence is connected,
and carries the sign gauge, the edge positivity and the support condition, which is exactly the
input of the Part 2 endpoints. The eight existing declarations stay at
`bipartiteCompleteGraphOf A` (fully complete bipartite, not merely connected); the connected-graph
analogue for the SU(2) corner is the R3 pin in Part 2 above.

R4 (case (ii), `λ ≥ 1`, `D ≤ 0`) is explicitly out of scope for this PR (PR-2c); no pin for it is
placed here.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, pp. 43–44.
-/

namespace LatticeSystem.Tests.Theorem24ConnectedEndpoints

open LatticeSystem.Quantum
open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Part 1: the three unconditional connected irreducibility engines (new declarations) -/

/-- **Signature pin (engine 1/3, interior).** Connected-graph analogue of the unconditional
complete-bipartite engine `shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible`
(`DressedAxisSwapBlockIrreducibleStructural.lean`), with `hGconn : G.Connected` +
`hGbip` in place of `hA_ne`/`hB_ne`. -/
example (A : Λ → Bool) (G : SimpleGraph Λ) {J : Λ → Λ → ℂ}
    (hGconn : G.Connected) (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hN : 1 ≤ N) (p : ℕ) [Nonempty (parityConfigS Λ N p)] :
    (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p).IsIrreducible :=
  shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_of_connected
    A hGconn hGbip hJim hJnn hJ_pos_G hJself hJbip hlam hlb hub hDim hDpos hc_strict hN p

/-- **Signature pin (engine 2/3, `λ = 1` boundary).** Connected-graph analogue of
`shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_lambda_one_D_pos`
(`DressedAxisSwapIonParityBlockIrreducibleLambdaOne.lean`), `hN : 2 ≤ N` (a single-ion `±2` move
needs room `1 < N`). -/
example (A : Λ → Bool) (G : SimpleGraph Λ) {J : Λ → Λ → ℂ}
    (hGconn : G.Connected) (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J 1 D N σ σ < c)
    (hN : 2 ≤ N) (p : ℕ) [Nonempty (parityConfigS Λ N p)] :
    (shiftedDressedAxisSwappedReMatrixOnParityBlock A J 1 D N c p).IsIrreducible :=
  shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_lambda_one_D_pos_of_connected
    A hGconn hGbip hJim hJnn hJ_pos_G hJself hJbip hDim hDpos hc_strict hN p

/-- **Signature pin (engine 3/3, `D = 0` boundary).** Connected-graph analogue of
`shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_D_nonneg`
(`DressedAxisSwapBondParityBlockIrreducibleDNonneg.lean`), `hN : 1 ≤ N`, and (unlike engines 1/2)
`hΛnt : Nontrivial Λ`: the bond-only totality layer this engine routes through
(`bondParityReachableS_total_of_connected`, `ParityReachConnectedTotal.lean:158`) requires
`Nontrivial V`, and this is not vacuous bookkeeping — at `Λ = Unit`, `N = 2`, `G = ⊥`, `J = 0`,
`lam = D = 0`, `c = 1`, `p = 0` every hypothesis below other than `Nontrivial Λ` holds (`⊥` is
connected on a one-point type), yet the shifted matrix on the two-element `p = 0` parity block is
the identity matrix, which is not irreducible. -/
example (A : Λ → Bool) (G : SimpleGraph Λ) {J : Λ → Λ → ℂ}
    (hΛnt : Nontrivial Λ) (hGconn : G.Connected) (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hN : 1 ≤ N) (p : ℕ) [Nonempty (parityConfigS Λ N p)] :
    (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p).IsIrreducible :=
  shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_D_nonneg_of_connected
    A hΛnt hGconn hGbip hJim hJnn hJ_pos_G hJself hJbip hlam hlb hub hDim hDnn hc_strict hN p

/-! ## Part 2: the two R3 connected region-endpoint declarations (new declarations)

R1 (`-1 < λ < 1`, `D ≥ 0`) and R2 (`λ = 1`, `D > 0`) endpoints are **not** pinned here. What blocks
them at a merely connected `G` is the `hJpos` route obstruction described above: the case-(i)
spin-`S` routes reach `h_strict_gap` through `hT23`, whose sixth premise only the fixed-graph
positivity `hJpos` discharges. Their diagonal shift is no longer an obstruction — those routes
take no axis-swapped diagonal-shift `c` hypothesis, obtaining one point-wise from
`exists_strict_diag_bound_dressedAxisSwappedAnisotropicHeisenbergSReMatrix`. They do still bind
the MLM/toy scalars `c_mlm` / `c_toy` and their strict bounds, as in
`anisotropicHeisenbergS_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_D_nonneg_general`. -/

/-- **Signature pin (R3 finrank, SU(2) corner `(λ,D) = (1,0)`).** Connected-graph analogue of
`aHeisS_target_finrank_le_one_of_MLM_casLadder_t23_pf_lam1_D_zero_gen`
(`AnisotropicHeisenbergSpinSSU2Boundary.lean:27`), `hN : 1 ≤ N`, no balanced-sector bookkeeping
(the SU(2) endpoint needs none). -/
example (A : Λ → Bool) (G : SimpleGraph Λ) {J : Λ → Λ → ℂ}
    (hGconn : G.Connected) (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJ_off : ∀ x y, ¬ G.Adj x y → J x y = 0)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y) (hJ_sym : ∀ x y, J x y = J y x)
    (hN : 1 ≤ N) [Nonempty (Λ → Fin (N + 1))]
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J 1 0 N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
          ℝ) : ℂ)) ≤ 1 :=
  aHeisS_target_finrank_le_one_lam1_D_zero_of_connected
    A G hGconn hGbip hJim hJnn hJ_pos_G hJ_off hJbip hJ_star hJ_sym hN h_card_eq

/-- **Signature pin (R3 zero-magnetization, SU(2) corner `(λ,D) = (1,0)`).** Connected-graph
analogue of `aHeisS_target_zeroMag_of_MLM_casLadder_t23_pf_lam1_D_zero_gen`
(`AnisotropicHeisenbergSpinSSU2Boundary.lean:70`). -/
example (A : Λ → Bool) (G : SimpleGraph Λ) {J : Λ → Λ → ℂ}
    (hGconn : G.Connected) (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJ_off : ∀ x y, ¬ G.Adj x y → J x y = 0)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y) (hJ_sym : ∀ x y, J x y = J y x)
    (hN : 1 ≤ N) [Nonempty (Λ → Fin (N + 1))]
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (Φ : (Λ → Fin (N + 1)) → ℂ) (hΦ_ne : Φ ≠ 0)
    (hΦ_eig : (anisotropicHeisenbergS J 1 0 N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 :=
  aHeisS_target_zeroMag_lam1_D_zero_of_connected
    A G hGconn hGbip hJim hJnn hJ_pos_G hJ_off hJbip hJ_star hJ_sym hN h_card_eq Φ hΦ_ne hΦ_eig

end LatticeSystem.Tests.Theorem24ConnectedEndpoints
