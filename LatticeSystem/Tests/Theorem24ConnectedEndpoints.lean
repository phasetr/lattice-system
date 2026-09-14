import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSTheorem24
import LatticeSystem.Quantum.SpinS.DressedAxisSwapBlockIrreducibleStructural
import LatticeSystem.Quantum.SpinS.DressedAxisSwapIonParityBlockIrreducibleLambdaOne
import LatticeSystem.Quantum.SpinS.DressedAxisSwapBondParityBlockIrreducibleDNonneg
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Signature pins: connected-graph Theorem 2.4 case (i) + SU(2) endpoints (Red fixture)

Issue #5473 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori), PR-2b of the connectivity/reachability
arc. Pins the exact signatures of:

1. the three **unconditional connected-graph irreducibility engines** that PR-2b adds (the
   connected-graph analogues of the unconditional complete-bipartite engines
   `shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible`,
   `..._isIrreducible_lambda_one_D_pos`, `..._isIrreducible_D_nonneg`);
2. the **six R1/R2/R3 region-endpoint declarations** (three regions × two conjuncts: target
   `finrank ≤ 1` and zero axis-3 magnetization) that PR-2b adds, replacing the scaffolding-scalar
   hypotheses `c_axis`/`hc_axis_strict`, `c_mlm`/`c_toy`/`hT23` and the complete-bipartite
   `hA_ne`/`hB_ne` bookkeeping with `hGconn`/`hGbip`/`hJ_pos_G`/`hJ_off` at a general connected
   graph `G`;
3. the **type mismatch** in the six existing case-(i)/SU(2) endpoint declarations that PR-2b must
   generalize: each currently requires `hJpos` stated at the fixed graph `bipartiteCompleteGraphOf
   A`, and a hypothesis of the connected-graph shape `∀ x y, G.Adj x y → 0 < (J x y).re` does not
   unify with that fixed-graph type, so it cannot be substituted into any of the six today.

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
(`DressedAxisSwapBondParityBlockIrreducibleDNonneg.lean`), `hN : 1 ≤ N`. -/
example (A : Λ → Bool) (G : SimpleGraph Λ) {J : Λ → Λ → ℂ}
    (hGconn : G.Connected) (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
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
    A hGconn hGbip hJim hJnn hJ_pos_G hJself hJbip hlam hlb hub hDim hDnn hc_strict hN p

/-! ## Part 2: the six R1/R2/R3 connected region-endpoint declarations (new declarations) -/

/-- **Signature pin (R1 finrank, `-1 < λ < 1`, `D ≥ 0`).** Connected-graph analogue of
`anisotropicHeisenbergS_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_D_nonneg_general`
(`AnisotropicHeisenbergSpinSDNonnegBoundary.lean:257`), with the scaffolding scalars
(`c_axis`, `c_mlm`/`c_toy`/`hT23`) and `hA_ne`/`hB_ne` removed, replaced by `hGconn`, `hGbip`,
`hJ_pos_G`, `hJ_off`. -/
example (A : Λ → Bool) (G : SimpleGraph Λ) {J : Λ → Λ → ℂ}
    (hGconn : G.Connected) (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJ_off : ∀ x y, ¬ G.Adj x y → J x y = 0)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y) (hJ_sym : ∀ x y, J x y = J y x)
    (hN : 1 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ) [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero : ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * N + 1) → M' ≠ M_balanced →
      (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ} (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D') :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam' : ℂ) (D' : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam' D') :
          ℝ) : ℂ)) ≤ 1 :=
  aHeisS_target_finrank_le_one_D_nonneg_of_connected
    A G hGconn hGbip hJim hJnn hJ_pos_G hJ_off hJself hJbip hJ_star hJ_sym hN h_card_eq
    M_balanced h_balanced h_centered_nonzero hlam'_lb hlam'_ub hD'

/-- **Signature pin (R1 zero-magnetization, `-1 < λ < 1`, `D ≥ 0`).** Connected-graph analogue of
`aHeisS_target_zeroMag_of_MLM_casLadder_t23_pf_D_nonneg_gen`
(`AnisotropicHeisenbergSpinSDNonnegBoundary.lean:321`). -/
example (A : Λ → Bool) (G : SimpleGraph Λ) {J : Λ → Λ → ℂ}
    (hGconn : G.Connected) (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJ_off : ∀ x y, ¬ G.Adj x y → J x y = 0)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y) (hJ_sym : ∀ x y, J x y = J y x)
    (hN : 1 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ) [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero : ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * N + 1) → M' ≠ M_balanced →
      (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ} (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D')
    (Φ : (Λ → Fin (N + 1)) → ℂ) (hΦ_ne : Φ ≠ 0)
    (hΦ_eig : (anisotropicHeisenbergS J (lam' : ℂ) (D' : ℂ) N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam' D') :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 :=
  aHeisS_target_zeroMag_D_nonneg_of_connected
    A G hGconn hGbip hJim hJnn hJ_pos_G hJ_off hJself hJbip hJ_star hJ_sym hN h_card_eq
    M_balanced h_balanced h_centered_nonzero hlam'_lb hlam'_ub hD' Φ hΦ_ne hΦ_eig

/-- **Signature pin (R2 finrank, `λ = 1`, `D > 0`).** Connected-graph analogue of
`aHeisS_target_finrank_le_one_of_MLM_casLadder_t23_pf_lam1_D_pos_gen`
(`AnisotropicHeisenbergSpinSLambdaOneBoundary.lean:525`), `hN : 2 ≤ N`. -/
example (A : Λ → Bool) (G : SimpleGraph Λ) {J : Λ → Λ → ℂ}
    (hGconn : G.Connected) (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJ_off : ∀ x y, ¬ G.Adj x y → J x y = 0)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y) (hJ_sym : ∀ x y, J x y = J y x)
    (hN : 2 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ) [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero : ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * N + 1) → M' ≠ M_balanced →
      (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {D' : ℝ} (hD' : 0 < D') :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J 1 (D' : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 D') :
          ℝ) : ℂ)) ≤ 1 :=
  aHeisS_target_finrank_le_one_lam1_D_pos_of_connected
    A G hGconn hGbip hJim hJnn hJ_pos_G hJ_off hJself hJbip hJ_star hJ_sym hN h_card_eq
    M_balanced h_balanced h_centered_nonzero hD'

/-- **Signature pin (R2 zero-magnetization, `λ = 1`, `D > 0`).** Connected-graph analogue of
`aHeisS_target_zeroMag_of_MLM_casLadder_t23_pf_lam1_D_pos_gen`
(`AnisotropicHeisenbergSpinSLambdaOneBoundary.lean:588`). -/
example (A : Λ → Bool) (G : SimpleGraph Λ) {J : Λ → Λ → ℂ}
    (hGconn : G.Connected) (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJ_off : ∀ x y, ¬ G.Adj x y → J x y = 0)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y) (hJ_sym : ∀ x y, J x y = J y x)
    (hN : 2 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ) [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero : ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * N + 1) → M' ≠ M_balanced →
      (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {D' : ℝ} (hD' : 0 < D')
    (Φ : (Λ → Fin (N + 1)) → ℂ) (hΦ_ne : Φ ≠ 0)
    (hΦ_eig : (anisotropicHeisenbergS J 1 (D' : ℂ) N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 D') :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 :=
  aHeisS_target_zeroMag_lam1_D_pos_of_connected
    A G hGconn hGbip hJim hJnn hJ_pos_G hJ_off hJself hJbip hJ_star hJ_sym hN h_card_eq
    M_balanced h_balanced h_centered_nonzero hD' Φ hΦ_ne hΦ_eig

/-- **Signature pin (R3 finrank, SU(2) corner `(λ,D) = (1,0)`).** Connected-graph analogue of
`aHeisS_target_finrank_le_one_of_MLM_casLadder_t23_pf_lam1_D_zero_gen`
(`AnisotropicHeisenbergSpinSSU2Boundary.lean:25`), `hN : 1 ≤ N`, no balanced-sector bookkeeping
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
(`AnisotropicHeisenbergSpinSSU2Boundary.lean:68`). -/
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

/-! ## Part 3: existing case-(i)/SU(2) endpoints cannot yet accept a connected-graph hypothesis

Each of the six examples below is byte-for-byte the *current* endpoint declaration's signature
with its complete-bipartite hypothesis `hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y →
0 < (J x y).re` replaced by the general connected-graph hypothesis `hJ_pos_G : ∀ x y, G.Adj x y →
0 < (J x y).re`, and applied directly. `bipartiteCompleteGraphOf A` and the free variable `G` do
not unify, so every one of the six fails to elaborate with `type mismatch`, not `unknown
identifier`: the declarations themselves already exist, only their fixed-graph hypothesis is the
obstruction PR-2b removes. -/

/-- **Type-mismatch pin (R1 finrank).** -/
example (A : Λ → Bool) {G : SimpleGraph Λ} {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y) (hJ_sym : ∀ x y, J x y = J y x)
    {c_axis : ℝ}
    (hc_axis_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c_axis)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c_mlm)
    (hc_toy_strict : ∀ σ, dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ) [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero : ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * N + 1) → M' ≠ M_balanced →
      (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ} (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D') :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam' : ℂ) (D' : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam' D') :
          ℝ) : ℂ)) ≤ 1 :=
  anisotropicHeisenbergS_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_D_nonneg_general
    A hJim hJnn hJ_pos_G hJself hJbip hJ_star hJ_sym hc_axis_strict hA_ne hB_ne hN c_mlm c_toy hT23
    hc_heis_strict hc_toy_strict h_card_eq M_balanced h_balanced h_centered_nonzero
    hlam'_lb hlam'_ub hD'

/-- **Type-mismatch pin (R1 zero-magnetization).** -/
example (A : Λ → Bool) {G : SimpleGraph Λ} {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y) (hJ_sym : ∀ x y, J x y = J y x)
    {c_axis : ℝ}
    (hc_axis_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c_axis)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c_mlm)
    (hc_toy_strict : ∀ σ, dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ) [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero : ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * N + 1) → M' ≠ M_balanced →
      (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ} (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D')
    (Φ : (Λ → Fin (N + 1)) → ℂ) (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam' : ℂ) (D' : ℂ) N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam' D') :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 :=
  aHeisS_target_zeroMag_of_MLM_casLadder_t23_pf_D_nonneg_gen
    A hJim hJnn hJ_pos_G hJself hJbip hJ_star hJ_sym hc_axis_strict hA_ne hB_ne hN c_mlm c_toy hT23
    hc_heis_strict hc_toy_strict h_card_eq M_balanced h_balanced h_centered_nonzero
    hlam'_lb hlam'_ub hD' Φ hΦ_ne hΦ_gs

/-- **Type-mismatch pin (R2 finrank).** -/
example (A : Λ → Bool) {G : SimpleGraph Λ} {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y) (hJ_sym : ∀ x y, J x y = J y x)
    {c_axis : ℝ}
    (hc_axis_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c_axis)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c_mlm)
    (hc_toy_strict : ∀ σ, dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ) [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero : ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * N + 1) → M' ≠ M_balanced →
      (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {D' : ℝ} (hD' : 0 < D') :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J 1 (D' : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 D') :
          ℝ) : ℂ)) ≤ 1 :=
  aHeisS_target_finrank_le_one_of_MLM_casLadder_t23_pf_lam1_D_pos_gen
    A hJim hJnn hJ_pos_G hJself hJbip hJ_star hJ_sym hc_axis_strict hA_ne hB_ne hN c_mlm c_toy hT23
    hc_heis_strict hc_toy_strict h_card_eq M_balanced h_balanced h_centered_nonzero hD'

/-- **Type-mismatch pin (R2 zero-magnetization).** -/
example (A : Λ → Bool) {G : SimpleGraph Λ} {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y) (hJ_sym : ∀ x y, J x y = J y x)
    {c_axis : ℝ}
    (hc_axis_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c_axis)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c_mlm)
    (hc_toy_strict : ∀ σ, dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ) [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero : ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * N + 1) → M' ≠ M_balanced →
      (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {D' : ℝ} (hD' : 0 < D')
    (Φ : (Λ → Fin (N + 1)) → ℂ) (hΦ_ne : Φ ≠ 0)
    (hΦ_eig : (anisotropicHeisenbergS J 1 (D' : ℂ) N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 D') :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 :=
  aHeisS_target_zeroMag_of_MLM_casLadder_t23_pf_lam1_D_pos_gen
    A hJim hJnn hJ_pos_G hJself hJbip hJ_star hJ_sym hc_axis_strict hA_ne hB_ne hN c_mlm c_toy hT23
    hc_heis_strict hc_toy_strict h_card_eq M_balanced h_balanced h_centered_nonzero hD'
    Φ hΦ_ne hΦ_eig

/-- **Type-mismatch pin (R3/SU(2) finrank).** -/
example (A : Λ → Bool) {G : SimpleGraph Λ} {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y) (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N) [Nonempty (Λ → Fin (N + 1))]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c_mlm)
    (hc_toy_strict : ∀ σ, dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J 1 0 N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
          ℝ) : ℂ)) ≤ 1 :=
  aHeisS_target_finrank_le_one_of_MLM_casLadder_t23_pf_lam1_D_zero_gen
    A hJim hJnn hJ_pos_G hJbip hJ_star hJ_sym hA_ne hB_ne hN c_mlm c_toy hT23
    hc_heis_strict hc_toy_strict h_card_eq

/-- **Type-mismatch pin (R3/SU(2) zero-magnetization).** -/
example (A : Λ → Bool) {G : SimpleGraph Λ} {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y) (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N) [Nonempty (Λ → Fin (N + 1))]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c_mlm)
    (hc_toy_strict : ∀ σ, dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (Φ : (Λ → Fin (N + 1)) → ℂ) (hΦ_ne : Φ ≠ 0)
    (hΦ_eig : (anisotropicHeisenbergS J 1 0 N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 :=
  aHeisS_target_zeroMag_of_MLM_casLadder_t23_pf_lam1_D_zero_gen
    A hJim hJnn hJ_pos_G hJbip hJ_star hJ_sym hA_ne hB_ne hN c_mlm c_toy hT23
    hc_heis_strict hc_toy_strict h_card_eq Φ hΦ_ne hΦ_eig

/-! ## Part 4: discriminating witness -/

/-- **Discriminating witness (four-vertex path, not the four-cycle).** On `V = Fin 4`, `A = {0,
2}`, `pathGraph 4` is connected, every edge joins opposite sublattices under this marking, and it
is genuinely a different graph from `bipartiteCompleteGraphOf A`: it is missing the crossing edge
`{0, 3}`. `cycleGraph 4` would **not** discriminate here — with this same marking its edge set is
exactly the four crossing pairs, so it coincides with `bipartiteCompleteGraphOf A`. Reused from
PR-1's/PR-2a's fixtures (`Tests/ParityReachabilityConnected.lean`,
`Tests/Theorem24EngineGeneralization.lean`). -/
example :
    (SimpleGraph.pathGraph 4).Connected ∧
      (∀ x y : Fin 4, (SimpleGraph.pathGraph 4).Adj x y →
        decide (x = 0 ∨ x = 2) ≠ decide (y = 0 ∨ y = 2)) ∧
      (bipartiteCompleteGraphOf (fun x : Fin 4 => decide (x = 0 ∨ x = 2))).Adj 0 3 ∧
      ¬ (SimpleGraph.pathGraph 4).Adj (0 : Fin 4) 3 := by
  refine ⟨SimpleGraph.pathGraph_connected 3, by decide, ?_, ?_⟩
  · simp
  · simp [SimpleGraph.pathGraph_adj]

end LatticeSystem.Tests.Theorem24ConnectedEndpoints
