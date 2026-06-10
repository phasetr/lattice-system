import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandUniqueness
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandMultiplet
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandTheorem11_11
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJGroundWeightDirectSum
import LatticeSystem.Fermion.JordanWigner.Hubbard.Charges
import LatticeSystem.Math.EigenspaceWeightFinrank
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandSwapCoeff

/-!
# Tasaki §11.3.1: discharging the Theorem 11.11 classification axiom (dimension route)

The half-filled zero-energy ground subspace of the flat-band Hubbard model equals the ferromagnetic
maximal-spin multiplet.  Following the §11.5 Theorem 11.26 dimension method (not symmetric-tensor
representation theory): the multiplet (dimension `K+2`) is contained in the ground subspace (the
existence half), and the ground subspace has dimension `≤ K+2` (amplitude invariance), so they
coincide — discharging `flatBand_zeroEnergy_halfFilled_mem_ferromagneticMultipletSpan`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1, Theorem 11.11; method as in §11.5.3, Theorem 11.26.  Tracked in Issue #4346.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum Module
open scoped BigOperators

variable {K : ℕ} {ν : ℝ}

/-- **The ferromagnetic multiplet has dimension `K+2 = 2 S_max + 1`** — its `K+2` lowered states
`(Ŝ⁻_tot)^k |Φα,all↑⟩` are linearly independent (`flatBand_ferromagnetic_multiplet`). -/
theorem flatBandFerromagneticMultipletSubmodule_finrank (K : ℕ) (ν : ℝ) :
    finrank ℂ (flatBandFerromagneticMultipletSubmodule K ν) = K + 2 := by
  rw [flatBandFerromagneticMultipletSubmodule,
    finrank_span_eq_card (flatBand_ferromagnetic_multiplet K ν).1, Fintype.card_fin]

/-- **`[Ŝ^z_tot, Ĥ_flat] = 0`.**  From `[Ŝ^±_tot, Ĥ_flat] = 0` and the `su(2)` relation
`Ŝ^+ Ŝ^- − Ŝ^- Ŝ^+ = 2 Ŝ^z`: `2 Ŝ^z` commutes with `Ĥ_flat`, hence so does `Ŝ^z`. -/
theorem fermionTotalSpinZ_commute_flatBandHamiltonian (K : ℕ) (ν t U : ℝ) :
    Commute (fermionTotalSpinZ (2 * K + 1)) (flatBandHamiltonian K ν t U) := by
  have hp := fermionTotalSpinPlus_commute_flatBandHamiltonian K ν t U
  have hm := fermionTotalSpinMinus_commute_flatBandHamiltonian K ν t U
  have h2 : Commute ((2 : ℂ) • fermionTotalSpinZ (2 * K + 1)) (flatBandHamiltonian K ν t U) := by
    rw [← fermionTotalSpinPlus_commutator_fermionTotalSpinMinus]
    exact (hp.mul_left hm).sub_left (hm.mul_left hp)
  have h2' : (2 : ℂ) • (fermionTotalSpinZ (2 * K + 1) * flatBandHamiltonian K ν t U)
      = (2 : ℂ) • (flatBandHamiltonian K ν t U * fermionTotalSpinZ (2 * K + 1)) := by
    rw [← smul_mul_assoc, ← mul_smul_comm]; exact h2.eq
  exact smul_right_injective _ (by norm_num : (2 : ℂ) ≠ 0) h2'

/-- **`Ŝ^z_tot` preserves the half-filled ground subspace** (it commutes with both `Ĥ_flat` and the
total number `N̂`). -/
theorem fermionTotalSpinZ_mulVec_mem_flatBandHalfFilledGroundSubmodule (K : ℕ) (ν t U : ℝ)
    {v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ}
    (hv : v ∈ flatBandHalfFilledGroundSubmodule K ν t U) :
    (fermionTotalSpinZ (2 * K + 1)).mulVec v ∈ flatBandHalfFilledGroundSubmodule K ν t U := by
  rw [flatBandHalfFilledGroundSubmodule, Submodule.mem_inf] at hv ⊢
  obtain ⟨hker, heig⟩ := hv
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hker
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at heig
  refine ⟨?_, ?_⟩
  · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      ← (fermionTotalSpinZ_commute_flatBandHamiltonian K ν t U).eq, ← Matrix.mulVec_mulVec, hker,
      Matrix.mulVec_zero]
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      ← (fermionTotalSpinZ_commute_fermionTotalNumber (2 * K + 1)).eq, ← Matrix.mulVec_mulVec, heig,
      Matrix.mulVec_smul]

/-- **`Ŝ^z`-weight decomposition of the half-filled ground subspace** (over all weights): the ground
subspace is the supremum of its `Ŝ^z` eigenspace intersections.  `Ŝ^z` preserves it and its
eigenspaces span the whole space. -/
theorem flatBandHalfFilledGroundSubmodule_eq_iSup_inf_eigenspace (K : ℕ) (ν t U : ℝ) :
    flatBandHalfFilledGroundSubmodule K ν t U =
      ⨆ μ : ℂ, flatBandHalfFilledGroundSubmodule K ν t U ⊓
        Module.End.eigenspace (fermionTotalSpinZ (2 * K + 1)).mulVecLin μ := by
  have hinv : ∀ x ∈ flatBandHalfFilledGroundSubmodule K ν t U,
      (fermionTotalSpinZ (2 * K + 1)).mulVecLin x ∈ flatBandHalfFilledGroundSubmodule K ν t U := by
    intro x hx
    rw [Matrix.mulVecLin_apply]
    exact fermionTotalSpinZ_mulVec_mem_flatBandHalfFilledGroundSubmodule K ν t U hx
  have htop : ⨆ μ : ℂ,
      Module.End.genEigenspace (fermionTotalSpinZ (2 * K + 1)).mulVecLin μ 1 = ⊤ := by
    simpa only [Module.End.genEigenspace_one] using
      fermionTotalSpinZ_iSup_eigenspace_eq_top (2 * K + 1)
  simpa only [Module.End.genEigenspace_one] using
    Submodule.eq_iSup_inf_genEigenspace (p := flatBandHalfFilledGroundSubmodule K ν t U)
      (f := (fermionTotalSpinZ (2 * K + 1)).mulVecLin) 1 hinv htop

/-- **Off-weight blocks vanish.**  At half filling `N̂ = K+1`, the only `Ŝ^z` weights are
`a − (K+1)/2` for `a ∈ Fin (K+2)` (the number of up-spins).  For any other `μ`, a ground vector that
is also an `Ŝ^z = μ` eigenstate must vanish on every configuration: each supported `w` has electron
number `K+1` and `Ŝ^z` count `μ = (#↑) − (K+1)/2`, forcing `μ` into the weight set. -/
theorem flatBandHalfFilledGroundSubmodule_inf_eigenspace_eq_bot (K : ℕ) (ν t U : ℝ) (μ : ℂ)
    (hμ : ∀ a : Fin (K + 2), μ ≠ (((a : ℝ) - ((K + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ)) :
    flatBandHalfFilledGroundSubmodule K ν t U ⊓
      Module.End.eigenspace (fermionTotalSpinZ (2 * K + 1)).mulVecLin μ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨hvG, hveig⟩ := hv
  rw [flatBandHalfFilledGroundSubmodule, Submodule.mem_inf, Module.End.mem_eigenspace_iff,
    Matrix.mulVecLin_apply] at hvG
  obtain ⟨_, hN⟩ := hvG
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hveig
  funext w
  rw [Pi.zero_apply]
  by_cases hNum : (∑ j : Fin (2 * (2 * K + 1) + 2), ((w j).val : ℂ)) = ((K + 1 : ℕ) : ℂ)
  · refine mulVec_apply_eq_zero_of_spinZ_ne v μ hveig w (fun hcount => ?_)
    set aup : ℕ := ∑ i : Fin (2 * K + 2), (w (spinfulIndex (2 * K + 1) i 0)).val with haup
    set adown : ℕ := ∑ i : Fin (2 * K + 2), (w (spinfulIndex (2 * K + 1) i 1)).val with hadown
    have hupC : (∑ i : Fin (2 * K + 2), ((w (spinfulIndex (2 * K + 1) i 0)).val : ℂ))
        = (aup : ℂ) := by rw [haup, Nat.cast_sum]
    have hdownC : (∑ i : Fin (2 * K + 2), ((w (spinfulIndex (2 * K + 1) i 1)).val : ℂ))
        = (adown : ℂ) := by rw [hadown, Nat.cast_sum]
    have hreindex : (∑ j : Fin (2 * (2 * K + 1) + 2), ((w j).val : ℂ))
        = (aup : ℂ) + (adown : ℂ) := by
      rw [sum_spinful_reindex (2 * K + 1) (fun k => ((w k).val : ℂ)),
        Finset.sum_congr rfl
          (fun i _ => Fin.sum_univ_two (fun r => ((w (spinfulIndex (2 * K + 1) i r)).val : ℂ))),
        Finset.sum_add_distrib, hupC, hdownC]
    have hsplitC : (aup : ℂ) + (adown : ℂ) = ((K + 1 : ℕ) : ℂ) := by rw [← hreindex]; exact hNum
    have hnat : aup + adown = K + 1 := by exact_mod_cast hsplitC
    have hadownC : (adown : ℂ) = ((K + 1 : ℕ) : ℂ) - (aup : ℂ) :=
      eq_sub_of_add_eq (by rw [add_comm]; exact hsplitC)
    refine hμ ⟨aup, by omega⟩ ?_
    rw [← hcount, hupC, hdownC, hadownC]
    push_cast
    ring
  · exact mulVec_apply_eq_zero_of_number_ne (2 * K + 1) v ((K + 1 : ℕ) : ℂ) hN w hNum

/-- **Finite `Ŝ^z` weight decomposition** of the half-filled ground subspace:
`G = ⨆ a : Fin (K+2), G ⊓ eigenspace Ŝ^z (a − (K+1)/2)`.  The all-`ℂ` supremum collapses to the
`K+2` occurring half-integer weights (off-weight blocks are `⊥`). -/
theorem flatBandHalfFilledGroundSubmodule_eq_iSup_weight (K : ℕ) (ν t U : ℝ) :
    flatBandHalfFilledGroundSubmodule K ν t U =
      ⨆ a : Fin (K + 2), flatBandHalfFilledGroundSubmodule K ν t U ⊓
        Module.End.eigenspace (fermionTotalSpinZ (2 * K + 1)).mulVecLin
          (((a : ℝ) - ((K + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) := by
  refine le_antisymm ?_ (iSup_le (fun _ => inf_le_left))
  refine (flatBandHalfFilledGroundSubmodule_eq_iSup_inf_eigenspace K ν t U).le.trans
    (iSup_le (fun μ => ?_))
  by_cases hμ : ∃ a : Fin (K + 2), μ = (((a : ℝ) - ((K + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ)
  · obtain ⟨a, rfl⟩ := hμ
    exact le_iSup_of_le a le_rfl
  · rw [flatBandHalfFilledGroundSubmodule_inf_eigenspace_eq_bot K ν t U μ (not_exists.mp hμ)]
    exact bot_le

/-- **The ferromagnetic multiplet is contained in the half-filled ground subspace** (the proven
existence side of Theorem 11.11): each lowered state `(Ŝ⁻_tot)^k |Φα,all↑⟩` is a zero-energy
`N̂ = K+1` eigenstate. -/
theorem flatBandFerromagneticMultipletSubmodule_le_groundSubmodule (K : ℕ) (ν t U : ℝ) :
    flatBandFerromagneticMultipletSubmodule K ν ≤ flatBandHalfFilledGroundSubmodule K ν t U := by
  rw [flatBandFerromagneticMultipletSubmodule, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  rw [SetLike.mem_coe, flatBandHalfFilledGroundSubmodule, Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact flatBandHamiltonian_mulVec_spinMinusPow_alphaAllUpState K ν t U k
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact fermionTotalNumber_mulVec_spinMinusPow_eigenvalue (2 * K + 1) k _
      (flatBandTotalNumber_mulVec_alphaAllUpState K ν)

/-- **Ground-subspace dimension bound from one-dimensional `Ŝ^z`-weight blocks.**  Given that each
of the `K+2` `Ŝ^z`-weight blocks of the ground subspace is at most one-dimensional, the finite
weight decomposition (`flatBandHalfFilledGroundSubmodule_eq_iSup_weight`) and the independence of
distinct eigenspaces give `finrank G ≤ K+2`.  The hypothesis is the sharp linear-algebra core of the
flat-band ferromagnetic classification: no zero-energy half-filled state beyond the maximal-spin
multiplet exists in any fixed `Ŝ^z` sector. -/
theorem flatBandHalfFilledGroundSubmodule_finrank_le_of_blocks (K : ℕ) (ν t U : ℝ)
    (hblock : ∀ a : Fin (K + 2),
      finrank ℂ ↥(flatBandHalfFilledGroundSubmodule K ν t U ⊓
        Module.End.eigenspace (fermionTotalSpinZ (2 * K + 1)).mulVecLin
          (((a : ℝ) - ((K + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ)) ≤ 1) :
    finrank ℂ ↥(flatBandHalfFilledGroundSubmodule K ν t U) ≤ K + 2 := by
  have hwt : Function.Injective
      (fun a : Fin (K + 2) => (((a : ℝ) - ((K + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ)) := by
    intro a b hab
    simp only [Complex.ofReal_inj] at hab
    exact Fin.ext (by exact_mod_cast (by linarith : (a : ℝ) = (b : ℝ)))
  exact LatticeSystem.Math.finrank_le_of_weight_blocks
    (flatBandHalfFilledGroundSubmodule K ν t U)
    (fermionTotalSpinZ (2 * K + 1)).mulVecLin _ hwt
    (flatBandHalfFilledGroundSubmodule_eq_iSup_weight K ν t U).symm hblock

/-- **Reduction of the Theorem 11.11 classification to one-dimensional weight blocks.**  Under the
weight-block bound, the ground subspace has dimension `≤ K+2 = finrank` of the multiplet; since the
multiplet is contained in the ground subspace (existence side), they coincide.  This discharges the
content of the classification axiom
`flatBand_zeroEnergy_halfFilled_mem_ferromagneticMultipletSpan` modulo the sharp
`finrank(block) ≤ 1` statement. -/
theorem flatBand_groundSubmodule_eq_multipletSpan_of_blocks (K : ℕ) (ν t U : ℝ)
    (hblock : ∀ a : Fin (K + 2),
      finrank ℂ ↥(flatBandHalfFilledGroundSubmodule K ν t U ⊓
        Module.End.eigenspace (fermionTotalSpinZ (2 * K + 1)).mulVecLin
          (((a : ℝ) - ((K + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ)) ≤ 1) :
    flatBandHalfFilledGroundSubmodule K ν t U = flatBandFerromagneticMultipletSubmodule K ν := by
  refine (Submodule.eq_of_le_of_finrank_le
    (flatBandFerromagneticMultipletSubmodule_le_groundSubmodule K ν t U) ?_).symm
  rw [flatBandFerromagneticMultipletSubmodule_finrank K ν]
  exact flatBandHalfFilledGroundSubmodule_finrank_le_of_blocks K ν t U hblock

/-- **Tasaki Theorem 11.11 (uniqueness side, axiom-free).**  The half-filled zero-energy ground
subspace equals the ferromagnetic multiplet span.  Discharges the classification: every weight block
is one-dimensional (`flatBand_block_finrank_le_one`, the swap-invariant coordinate argument), so the
ground subspace has dimension `≤ K+2 = dim` of the multiplet, and the multiplet is contained in it. -/
theorem flatBand_groundSubmodule_eq_multipletSpan (K : ℕ) (ν t U : ℝ)
    (hν : 0 < ν) (ht : 0 < t) (hU : 0 < U) :
    flatBandHalfFilledGroundSubmodule K ν t U = flatBandFerromagneticMultipletSubmodule K ν :=
  flatBand_groundSubmodule_eq_multipletSpan_of_blocks K ν t U
    (fun a => flatBand_block_finrank_le_one K ν t U hν ht hU a)

end LatticeSystem.Fermion
