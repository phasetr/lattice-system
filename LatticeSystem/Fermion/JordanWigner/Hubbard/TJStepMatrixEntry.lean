import LatticeSystem.Fermion.JordanWigner.Hubbard.TJExchangeBondSum
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJStepRelation

/-!
# Tasaki 11.5: a connectivity step gives a strictly negative matrix entry (Prop 11.24 PR-C1b)

For the Perron–Frobenius irreducibility step, each `TJStep s s'` must produce a strictly positive
entry of `B = c·1 − M`, i.e. a strictly *negative* off-diagonal entry `M_{s',s} < 0` of the t-J
effective matrix.  This file proves that strict negativity for `τ, J > 0`:

* a **hop** step contributes `⟨Φ_{s'}|K|Φ_s⟩ ≥ 1` (the moved-electron term equals `1`, the rest
  are non-negative), so `M_{s',s} = −τ·(≥1) + (interaction ≤ 0) ≤ −τ < 0`;
* an **exchange** step contributes an interaction bond-sum `≥ 1`, so
  `M_{s',s} = (kinetic ≤ 0) − (J/2)·(≥1) ≤ −J/2 < 0`.

Combined (`tJEffMatrix_re_neg_of_step`), every step gives `M_{s',s}.re < 0`.  This is the per-step
positivity feeding `matrix_pow_succ_pos_of_path` in the irreducibility proof.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph
open scoped BigOperators

variable {N : ℕ}

/-- **The moved-electron kinetic summand equals `1`.**  For a cyclic hop `a → b` (adjacent, source
`a` carrying spin `σ`, empty target `b`) with `s' = tJSiteHop s a b`, the `(σ, i = b, j = a)` term
of the kinetic expansion `couplingOf b a · ⟨Φ_{s'}|ĉ†_{bσ}ĉ_{aσ}|Φ_s⟩` is exactly `1`. -/
theorem tJ_cycle_hop_kinetic_summand_eq_one (N : ℕ) (hpos : 0 < N)
    (s s' : Fin (N + 1) → Fin 3) (a b : Fin (N + 1)) (σ : Fin 2)
    (hAdj : (cycleGraph (N + 1)).Adj b a) (hsa : s a = if σ = 0 then 1 else 2) (hsb : s b = 0)
    (hs' : s' = tJSiteHop s a b)
    (Ne : ℕ) (hNe : (Finset.univ.filter (fun k => s k = 1)).card
        + (Finset.univ.filter (fun k => s k = 2)).card = Ne) (hodd : Odd Ne) :
    couplingOf (cycleGraph (N + 1)) (1 : ℂ) b a *
        (∑ w, basisVec (tJConfigOf N s') w *
          ((fermionMultiCreation (2 * N + 1) (spinfulIndex N b σ) *
              fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N a σ)).mulVec
              (basisVec (tJConfigOf N s))) w) = 1 := by
  have hcoup : couplingOf (cycleGraph (N + 1)) (1 : ℂ) b a = 1 := by
    unfold couplingOf; rw [if_pos hAdj]
  rw [hcoup, one_mul]
  rcases tJ_fin2_eq σ with rfl | rfl
  · rw [if_pos rfl] at hsa
    rcases cycleGraph_adj_val_cases N hpos b a hAdj with hd | hd | ⟨hbN, ha0⟩ | ⟨haN, hb0⟩
    · rw [tJ_uphop_backward_nn_matrixElement N s s' b a hd hsa hsb, if_pos hs']
    · rw [tJ_uphop_nn_matrixElement N s s' a b hd hsa hsb, if_pos hs']
    · rw [tJ_uphop_wrap_matrixElement N s s' a b hpos ha0 hbN hsa hsb Ne hNe hodd, if_pos hs']
    · rw [tJ_uphop_backward_wrap_matrixElement N s s' b a hpos hb0 haN hsa hsb Ne hNe hodd,
        if_pos hs']
  · simp only [if_neg (by decide : ¬ (1 : Fin 2) = 0)] at hsa
    rcases cycleGraph_adj_val_cases N hpos b a hAdj with hd | hd | ⟨hbN, ha0⟩ | ⟨haN, hb0⟩
    · rw [tJ_downhop_backward_nn_matrixElement N s s' b a hd hsa hsb, if_pos hs']
    · rw [tJ_downhop_nn_matrixElement N s s' a b hd hsa hsb, if_pos hs']
    · rw [tJ_downhop_wrap_matrixElement N s s' a b hpos ha0 hbN hsa hsb Ne hNe hodd, if_pos hs']
    · rw [tJ_downhop_backward_wrap_matrixElement N s s' b a hpos hb0 haN hsa hsb Ne hNe hodd,
        if_pos hs']

/-- **A hop contributes kinetic real part `≥ 1`.**  Since every kinetic summand is `{0,1}`-valued
and the moved-electron summand `(σ, b, a)` equals `1`, the kinetic matrix element `⟨Φ_{s'}|K|Φ_s⟩`
has real part `≥ 1`. -/
theorem tJKinetic_matrixElement_re_ge_one_of_hop (N : ℕ) (hpos : 0 < N)
    (s s' : Fin (N + 1) → Fin 3) (a b : Fin (N + 1)) (σ : Fin 2)
    (hAdj : (cycleGraph (N + 1)).Adj b a) (hsa : s a = if σ = 0 then 1 else 2) (hsb : s b = 0)
    (hs' : s' = tJSiteHop s a b)
    (Ne : ℕ) (hNe : (Finset.univ.filter (fun k => s k = 1)).card
        + (Finset.univ.filter (fun k => s k = 2)).card = Ne) (hodd : Odd Ne) :
    1 ≤ (∑ w, basisVec (tJConfigOf N s') w *
          ((hubbardKineticOnGraph N (cycleGraph (N + 1)) 1).mulVec
            (basisVec (tJConfigOf N s))) w).re := by
  rw [tJKinetic_matrixElement_expand]
  simp only [Complex.re_sum]
  have hnn : ∀ (σ' : Fin 2) (i j : Fin (N + 1)),
      0 ≤ (couplingOf (cycleGraph (N + 1)) (1 : ℂ) i j *
        (∑ w, basisVec (tJConfigOf N s') w *
          ((fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ') *
              fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ')).mulVec
              (basisVec (tJConfigOf N s))) w)).re := by
    intro σ' i j
    rcases tJ_kinetic_summand_zero_or_one N hpos s s' Ne hNe hodd σ' i j with h | h <;>
      rw [h] <;> simp
  have hone : (couplingOf (cycleGraph (N + 1)) (1 : ℂ) b a *
      (∑ w, basisVec (tJConfigOf N s') w *
        ((fermionMultiCreation (2 * N + 1) (spinfulIndex N b σ) *
            fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N a σ)).mulVec
            (basisVec (tJConfigOf N s))) w)).re = 1 := by
    rw [tJ_cycle_hop_kinetic_summand_eq_one N hpos s s' a b σ hAdj hsa hsb hs' Ne hNe hodd]
    simp
  calc (1 : ℝ) = _ := hone.symm
    _ ≤ ∑ j, (couplingOf (cycleGraph (N + 1)) (1 : ℂ) b j *
          (∑ w, basisVec (tJConfigOf N s') w *
            ((fermionMultiCreation (2 * N + 1) (spinfulIndex N b σ) *
                fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ)).mulVec
                (basisVec (tJConfigOf N s))) w)).re :=
        Finset.single_le_sum (fun j _ => hnn σ b j) (Finset.mem_univ a)
    _ ≤ ∑ i, ∑ j, (couplingOf (cycleGraph (N + 1)) (1 : ℂ) i j *
          (∑ w, basisVec (tJConfigOf N s') w *
            ((fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
                fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ)).mulVec
                (basisVec (tJConfigOf N s))) w)).re :=
        Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => hnn σ i j)
          (Finset.mem_univ b)
    _ ≤ ∑ σ', ∑ i, ∑ j, (couplingOf (cycleGraph (N + 1)) (1 : ℂ) i j *
          (∑ w, basisVec (tJConfigOf N s') w *
            ((fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ') *
                fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ')).mulVec
                (basisVec (tJConfigOf N s))) w)).re :=
        Finset.single_le_sum
          (fun σ' _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hnn σ' i j)
          (Finset.mem_univ σ)

/-- **An exchange contributes interaction bond-sum real part `≥ 1`.**  Each weighted ladder summand
is `{0,1}`-valued and the exchanged-pair summand `(i, j)` equals `1`, so the ladder bond-sum has
real part `≥ 1`. -/
theorem tJInteraction_bondSum_re_ge_one_of_exchange (N : ℕ) (s s' : Fin (N + 1) → Fin 3)
    (i j : Fin (N + 1)) (hAdj : (cycleGraph (N + 1)).Adj i j) (hi : s i = 2) (hj : s j = 1)
    (hs' : s' = tJSpinSwap s i j) :
    1 ≤ (∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
          (couplingOf (cycleGraph (N + 1)) (1 : ℂ) x y *
              tJME N s s' (fermionSiteSpinPlus N x * fermionSiteSpinMinus N y)
            + couplingOf (cycleGraph (N + 1)) (1 : ℂ) x y *
              tJME N s s' (fermionSiteSpinMinus N x * fermionSiteSpinPlus N y))).re := by
  simp only [Complex.re_sum]
  have hnn : ∀ x y : Fin (N + 1),
      0 ≤ (couplingOf (cycleGraph (N + 1)) (1 : ℂ) x y *
            tJME N s s' (fermionSiteSpinPlus N x * fermionSiteSpinMinus N y)
          + couplingOf (cycleGraph (N + 1)) (1 : ℂ) x y *
            tJME N s s' (fermionSiteSpinMinus N x * fermionSiteSpinPlus N y)).re := by
    intro x y
    rcases tJ_exchange_summand_zero_or_one N s s' x y with h1 | h1 <;>
      rcases tJ_exchange_swap_summand_zero_or_one N s s' x y with h2 | h2 <;>
      · simp only [tJME] at h1 h2 ⊢
        rw [h1, h2]; norm_num
  have hone : 1 ≤ (couplingOf (cycleGraph (N + 1)) (1 : ℂ) i j *
        tJME N s s' (fermionSiteSpinPlus N i * fermionSiteSpinMinus N j)
      + couplingOf (cycleGraph (N + 1)) (1 : ℂ) i j *
        tJME N s s' (fermionSiteSpinMinus N i * fermionSiteSpinPlus N j)).re := by
    have hc : couplingOf (cycleGraph (N + 1)) (1 : ℂ) i j = 1 := by
      unfold couplingOf; rw [if_pos hAdj]
    simp only [tJME]
    rw [hc, one_mul, one_mul, fermionSpinFlip_matrixElement N s s' i j hi hj, if_pos hs']
    rcases tJ_exchange_swap_summand_zero_or_one N s s' i j with h2 | h2 <;>
      · simp only [hc, one_mul] at h2
        rw [h2]; norm_num
  calc (1 : ℝ) ≤ _ := hone
    _ ≤ ∑ y, (couplingOf (cycleGraph (N + 1)) (1 : ℂ) i y *
          tJME N s s' (fermionSiteSpinPlus N i * fermionSiteSpinMinus N y)
        + couplingOf (cycleGraph (N + 1)) (1 : ℂ) i y *
          tJME N s s' (fermionSiteSpinMinus N i * fermionSiteSpinPlus N y)).re :=
        Finset.single_le_sum (fun y _ => hnn i y) (Finset.mem_univ j)
    _ ≤ ∑ x, ∑ y, (couplingOf (cycleGraph (N + 1)) (1 : ℂ) x y *
          tJME N s s' (fermionSiteSpinPlus N x * fermionSiteSpinMinus N y)
        + couplingOf (cycleGraph (N + 1)) (1 : ℂ) x y *
          tJME N s s' (fermionSiteSpinMinus N x * fermionSiteSpinPlus N y)).re :=
        Finset.single_le_sum (fun x _ => Finset.sum_nonneg fun y _ => hnn x y) (Finset.mem_univ i)

/-- **An exchange step gives interaction real part `≤ −J/2`.**  Since the ladder bond-sum is a
non-negative real `≥ 1`, the interaction matrix element `J·⟨Φ_{s'}|Σ(n̂n̂/4 − Ŝ·Ŝ)|Φ_s⟩` has
real part `−(J/2)·(≥1) ≤ −J/2`. -/
theorem tJInteraction_matrixElement_re_le_neg_half_of_exchange (N : ℕ)
    (s s' : Fin (N + 1) → Fin 3) (i j : Fin (N + 1)) (J : ℝ) (hJ : 0 ≤ J)
    (hAdj : (cycleGraph (N + 1)).Adj i j) (hi : s i = 2) (hj : s j = 1)
    (hs' : s' = tJSpinSwap s i j) (hne : s' ≠ s) :
    ((J : ℂ) * tJME N s s' (∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
        (if (cycleGraph (N + 1)).Adj x y then
            (1 / 4 : ℂ) • (fermionSiteNumber N x * fermionSiteNumber N y)
              - fermionSpinDot N x y
          else 0))).re ≤ -(J / 2) := by
  have hbond := tJInteraction_bondSum_re_ge_one_of_exchange N s s' i j hAdj hi hj hs'
  rw [tJInteraction_matrixElement_eq N s s' hne]
  set S : ℂ := ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
      (couplingOf (cycleGraph (N + 1)) (1 : ℂ) x y *
          tJME N s s' (fermionSiteSpinPlus N x * fermionSiteSpinMinus N y)
        + couplingOf (cycleGraph (N + 1)) (1 : ℂ) x y *
          tJME N s s' (fermionSiteSpinMinus N x * fermionSiteSpinPlus N y)) with hS
  have hSim : S.im = 0 := by
    rw [hS, Complex.im_sum]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun y _ => ?_
    rcases tJ_exchange_summand_zero_or_one N s s' x y with h1 | h1 <;>
      rcases tJ_exchange_swap_summand_zero_or_one N s s' x y with h2 | h2 <;>
      · simp only [tJME] at h1 h2 ⊢
        rw [h1, h2]; norm_num
  rw [show -(1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring,
    Complex.mul_re, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, hSim]
  nlinarith [hbond, hJ, mul_nonneg hJ (by linarith [hbond] : (0 : ℝ) ≤ S.re)]

/-- **A connectivity step gives a strictly negative effective-matrix entry.**  For `τ, J > 0`, each
`TJStep s s'` produces `M_{s',s} < 0`: a hop contributes kinetic `≥ 1` (so `≤ −τ`), and an
exchange contributes interaction `≤ −J/2`.  This is the strict positivity `B_{s',s} = −M_{s',s} > 0`
feeding
the Perron–Frobenius irreducibility. -/
theorem tJEffMatrix_re_neg_of_step (N : ℕ) (hpos : 0 < N) (s s' : Fin (N + 1) → Fin 3)
    (Ne : ℕ) (hNe : (Finset.univ.filter (fun k => s k = 1)).card
        + (Finset.univ.filter (fun k => s k = 2)).card = Ne) (hodd : Odd Ne)
    (τ J : ℝ) (hτ : 0 < τ) (hJ : 0 < J) (hstep : TJStep N s s') (hne : s' ≠ s) :
    (tJEffMatrix N (cycleGraph (N + 1)) τ J s' s).re < 0 := by
  rw [tJEffMatrix_eq_tJME]
  unfold tJHamiltonian
  rw [tJME_add, tJME_smul, tJME_smul]
  have hkin_eq : tJME N s s'
      (hubbardHardcoreProjection N * hubbardKineticOnGraph N (cycleGraph (N + 1)) 1 *
        hubbardHardcoreProjection N)
      = tJME N s s' (hubbardKineticOnGraph N (cycleGraph (N + 1)) 1) :=
    tJKinetic_matrixElement_eq N (cycleGraph (N + 1)) s s'
  obtain ⟨hKre0, hKim⟩ := tJKinetic_matrixElement_nonneg N hpos s s' Ne hNe hodd
  rw [show (∑ w, basisVec (tJConfigOf N s') w *
        ((hubbardKineticOnGraph N (cycleGraph (N + 1)) 1).mulVec (basisVec (tJConfigOf N s))) w)
      = tJME N s s' (hubbardKineticOnGraph N (cycleGraph (N + 1)) 1) from rfl] at hKre0 hKim
  rw [hkin_eq, Complex.add_re, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im, hKim]
  set zKre := (tJME N s s' (hubbardKineticOnGraph N (cycleGraph (N + 1)) 1)).re with hzKre
  set intRe := ((J : ℂ) * tJME N s s' (∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
      (if (cycleGraph (N + 1)).Adj x y then
          (1 / 4 : ℂ) • (fermionSiteNumber N x * fermionSiteNumber N y)
            - fermionSpinDot N x y
        else 0))).re with hintRe
  rcases hstep with ⟨a, b, hAdj, hsa0, hsb, hs'⟩ | ⟨i, j, hAdj, hi, hj, hs'⟩
  · -- hop step: kinetic ≥ 1, interaction ≤ 0
    have hσ : ∃ σ : Fin 2, s a = if σ = 0 then 1 else 2 := by
      rcases tJ_fin3_cases (s a) with h | h | h
      · exact absurd h hsa0
      · exact ⟨0, by simp [h]⟩
      · exact ⟨1, by simp [h]⟩
    obtain ⟨σ, hsa⟩ := hσ
    have hKge1 : 1 ≤ zKre :=
      tJKinetic_matrixElement_re_ge_one_of_hop N hpos s s' a b σ hAdj.symm hsa hsb hs' Ne hNe hodd
    have hint_le : intRe ≤ 0 := (tJInteraction_matrixElement_nonpos N s s' J (le_of_lt hJ) hne).1
    nlinarith [hKge1, hτ, hint_le]
  · -- exchange step: kinetic ≥ 0, interaction ≤ −J/2
    have hint_le : intRe ≤ -(J / 2) :=
      tJInteraction_matrixElement_re_le_neg_half_of_exchange N s s' i j J (le_of_lt hJ) hAdj hi hj
        hs' hne
    nlinarith [hKre0, hτ, hint_le, hJ, mul_nonneg (le_of_lt hτ) hKre0]

end LatticeSystem.Fermion
