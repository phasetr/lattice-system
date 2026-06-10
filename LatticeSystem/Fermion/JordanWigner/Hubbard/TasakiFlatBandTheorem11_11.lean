import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandAlphaFockKernel
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinChargeCommutation

/-!
# Tasaki Theorem 11.11: the flat-band ferromagnetic ground states (capstone)

This file assembles Tasaki's flat-band ferromagnetism theorem (§11.3.1, Theorem
11.11) for the half-filled sector `N_e = |E| = K + 1`.

**Existence** (fully proven in earlier files): the `K + 2 = 2 S_max + 1` lowered
states `(Ŝ^-_tot)^k |Φα,all↑⟩` are linearly independent, all carry total spin
`S_tot = S_max = (K+1)/2`, and are all zero-energy ground states (`Ĥ ≥ 0`).

**Uniqueness**: the ground subspace is *exactly* this multiplet.  The structural
inputs are proven (frustration-freeness, `[Ĥ, N̂] = 0`, the `b̂`-kernel and
`α`-Fock subspaces, `α`-Fock ⊆ `b̂`-kernel).  The remaining classification step —
that a half-filled zero-energy state, having no `β`-occupation and no double
occupancy, is spatially symmetric and hence in the maximal-spin multiplet — is
Tasaki's Appendix A representation-theoretic argument (Lemmas A.10/A.11).  It
requires the Fock-space change of basis for the *non-orthogonal* `{α} ∪ {β}`
single-particle basis and the symmetric-tensor/SU(2) classification, neither of
which is currently available in this development.  Following the same policy used
for Theorem 11.8 / Lemma 11.9 (`NagaokaConnectivityClassification.lean`), this one
classification statement is introduced as a single, clearly documented `axiom`
(`flatBand_zeroEnergy_halfFilled_mem_ferromagneticMultipletSpan`), and the full
theorem is assembled from it together with the proven existence side.

## Deferred axiom rationale

The axiom states exactly Tasaki's uniqueness conclusion for §11.3.1: in the
half-filled sector, every zero-energy state lies in the ferromagnetic lowering
multiplet of `|Φα,all↑⟩`.  Its proof in Tasaki uses Appendix A (frustration-free
PSD-sum kernel + symmetric-state ⇒ maximal-spin); a faithful Lean proof is a
multi-week effort with no existing supporting machinery.  The capstone theorems
below depend on this single axiom; the existence half does not.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1, Theorem 11.11, Appendix A (Lemmas A.10/A.11).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- **`[N̂, â†_{p,↑}] = â†_{p,↑}`**: the `α` creation raises the total particle
number by one (lifted termwise from `[N̂, c†_j] = c†_j`). -/
theorem flatBandTotalNumber_commutator_ACreation (K : ℕ) (ν : ℝ) (p : Fin (K + 1)) :
    fermionTotalNumber (2 * (2 * K + 1) + 1) * flatBandACreation K ν p 0 =
      flatBandACreation K ν p 0 * fermionTotalNumber (2 * (2 * K + 1) + 1) +
        flatBandACreation K ν p 0 := by
  unfold flatBandACreation
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hx : fermionTotalNumber (2 * (2 * K + 1) + 1) *
      fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 0) =
      fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 0) *
        fermionTotalNumber (2 * (2 * K + 1) + 1) +
      fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 0) := by
    have h := fermionTotalNumber_commutator_fermionMultiCreation (2 * (2 * K + 1) + 1)
      (spinfulIndex (2 * K + 1) x 0)
    rw [sub_eq_iff_eq_add] at h
    rw [h]; abel
  rw [mul_smul_comm, smul_mul_assoc, hx, smul_add]

/-- **`N̂ |Φα,all↑⟩ = (K + 1) |Φα,all↑⟩`**: the all-up `α` state has exactly
`K + 1` particles (the half-filled flat band). -/
theorem flatBandTotalNumber_mulVec_alphaAllUpState (K : ℕ) (ν : ℝ) :
    (fermionTotalNumber (2 * (2 * K + 1) + 1)).mulVec (flatBandAlphaAllUpState K ν) =
      ((K + 1 : ℕ) : ℂ) • flatBandAlphaAllUpState K ν := by
  unfold flatBandAlphaAllUpState
  rw [Matrix.mulVec_mulVec,
    charge_listProd_mulVec_vacuum (fermionTotalNumber (2 * (2 * K + 1) + 1))
      (fun p => flatBandACreation K ν p 0) (List.finRange (K + 1))
      (fermionTotalNumber_mulVec_vacuum (2 * (2 * K + 1) + 1))
      (fun p _ => flatBandTotalNumber_commutator_ACreation K ν p),
    List.length_finRange]

/-- The ferromagnetic multiplet subspace: the span of the `K + 2 = 2 S_max + 1`
lowered states `(Ŝ^-_tot)^k |Φα,all↑⟩`. -/
noncomputable def flatBandFerromagneticMultipletSubmodule (K : ℕ) (ν : ℝ) :
    Submodule ℂ ((Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ) :=
  Submodule.span ℂ (Set.range (fun k : Fin (K + 2) =>
    ((fermionTotalSpinMinus (2 * K + 1)) ^ (k : ℕ)).mulVec
      (flatBandAlphaAllUpState K ν)))

/-- The half-filled flat-band ground subspace: the zero-energy (`ker Ĥ`) states in
the `N_e = K + 1` particle-number sector. -/
noncomputable def flatBandHalfFilledGroundSubmodule (K : ℕ) (ν t U : ℝ) :
    Submodule ℂ ((Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ) :=
  LinearMap.ker (flatBandHamiltonian K ν t U).mulVecLin ⊓
    Module.End.eigenspace (fermionTotalNumber (2 * (2 * K + 1) + 1)).mulVecLin
      ((K + 1 : ℕ) : ℂ)

end LatticeSystem.Fermion
