import LatticeSystem.Quantum.SpinS.NeelStateOfSTotalSpinSSquaredVsPredictedGapPosNondegenerate
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy
import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelExpectations
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormEqRe

/-!
# Néel state is NOT in the predicted GS subspace at non-degenerate

PR #2902 proved that at non-degenerate (`|A| ≥ 1`, `|¬A| ≥ 1`,
`N ≥ 1`), the Néel-state `(Ŝ_tot)²` expectation strictly exceeds
the predicted GS eigenvalue:

  `‖biw‖² + ‖biw‖ < <(Ŝ_tot)²>_Néel.re`.

If `Φ_Néel(A, N)` were in `bipartiteToyGroundStateSubspacePredicted A N`,
the (Ŝ_tot)² eigenvalue expectation would equal the predicted
eigenvalue exactly, contradicting the strict gap.

Hence at non-degenerate, **Néel state is not in the predicted GS
subspace**, complementing PR #2914 (saturated case where
Néel IS in the predicted GS).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Néel ∉ predicted GS subspace** at non-degenerate
configurations under the orientation `|¬A| ≤ |A|`. -/
theorem neelStateOfS_notMem_bipartiteToyGroundStateSubspacePredicted_of_nondegenerate
    (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N)
    (horient : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : Λ => A x = true)).card) :
    neelStateOfS A N ∉ bipartiteToyGroundStateSubspacePredicted A N := by
  intro hmem
  -- From (Ŝ_tot)² eigenspace membership: (Ŝ_tot)² · Néel = λ • Néel.
  have htot_mem := hmem.1.1
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply] at htot_mem
  -- Dot with star Néel, use neelStateOfS_inner_self = 1.
  have hexpect_eq :
      dotProduct (star (neelStateOfS A N))
          ((totalSpinSSquared Λ N).mulVec (neelStateOfS A N)) =
        ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                ((N : ℂ) / 2) -
              ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                ((N : ℂ) / 2)) + 1)) := by
    rw [htot_mem, dotProduct_smul, smul_eq_mul, neelStateOfS_inner_self,
        mul_one]
  -- Take real parts on both sides.
  have hexpect_re : (dotProduct (star (neelStateOfS A N))
        ((totalSpinSSquared Λ N).mulVec (neelStateOfS A N))).re =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                ((N : ℂ) / 2) -
              ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                ((N : ℂ) / 2)) + 1)).re := by
    rw [hexpect_eq]
  -- LHS.re from PR #2896.
  have hLHS_re :=
    neelStateOfS_totalSpinSSquared_expectation_re_via_imbalance_norm_sq
      (Λ := Λ) A N
  -- ‖biw‖ = (|A| - |¬A|) · N / 2 (orientation |¬A| ≤ |A|).
  have hbiw_re_eq :=
    bipartiteImbalanceWeight_norm_eq_re_of_cardNotA_le_cardA A N horient
  rw [bipartiteImbalanceWeight_re_eq] at hbiw_re_eq
  set a : ℝ := ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
    with ha_def
  set b : ℝ := ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)
    with hb_def
  set biw : ℝ := ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ with hbiw_def
  -- RHS .re computation.
  have hRHS_re :
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                ((N : ℂ) / 2) -
              ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                ((N : ℂ) / 2)) + 1)).re =
        ((a - b) * ((N : ℝ) / 2)) * ((a - b) * ((N : ℝ) / 2) + 1) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re,
      Complex.one_im, Complex.natCast_re, Complex.natCast_im, ha_def,
      hb_def]
    ring
  rw [hRHS_re, hLHS_re] at hexpect_re
  -- hexpect_re: biw*biw + |Λ|·N/2 = (a-b)·(N/2) · ((a-b)·(N/2)+1)
  -- hbiw_re_eq: biw = (a-b) · (N/2)
  have hsubst : biw * biw + (Fintype.card Λ : ℝ) * (N : ℝ) / 2 =
      biw * (biw + 1) := by
    rw [hbiw_re_eq] at hexpect_re ⊢
    linarith [hexpect_re]
  -- Hence biw·biw + |Λ|·N/2 = biw·(biw+1) = biw·biw + biw, so |Λ|·N/2 = biw.
  -- But hgap_pos says biw·biw + biw < LHS.re = biw·biw + |Λ|·N/2.
  -- ⇒ biw < |Λ|·N/2. Contradiction.
  have hgap_pos :=
    neelStateOfS_totalSpinSSquared_expectation_re_gt_predicted_of_nondegenerate
      A N hA hAc hN
  rw [hLHS_re] at hgap_pos
  -- hgap_pos: biw·biw + biw < biw·biw + |Λ|·N/2
  -- ⇒ biw < |Λ|·N/2
  -- hsubst gives biw·biw + |Λ|·N/2 = biw·biw + biw, so |Λ|·N/2 = biw, contradicting strict.
  linarith

end LatticeSystem.Quantum
