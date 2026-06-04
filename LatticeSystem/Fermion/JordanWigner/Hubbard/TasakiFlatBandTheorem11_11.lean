import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandAlphaFockKernel

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
    flatBand_charge_listProd_mulVec_vacuum (fermionTotalNumber (2 * (2 * K + 1) + 1))
      (fun p => flatBandACreation K ν p 0) (List.finRange (K + 1))
      (fermionTotalNumber_mulVec_vacuum (2 * (2 * K + 1) + 1))
      (fun p _ => flatBandTotalNumber_commutator_ACreation K ν p),
    List.length_finRange]

/-- **`[Ŝ^-_tot, N̂] = 0`**: the total lowering operator conserves particle number
(`Ŝ^-_tot = Σ_i ĉ†_{i,↓} ĉ_{i,↑}`, each term number-conserving). -/
theorem flatBand_fermionTotalSpinMinus_commute_fermionTotalNumber (N : ℕ) :
    Commute (fermionTotalSpinMinus N) (fermionTotalNumber (2 * N + 1)) := by
  unfold fermionTotalSpinMinus
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  have hcr : fermionTotalNumber (2 * N + 1) * fermionDownCreation N i =
      fermionDownCreation N i * fermionTotalNumber (2 * N + 1) + fermionDownCreation N i := by
    unfold fermionDownCreation
    rw [sub_eq_iff_eq_add.mp
      (fermionTotalNumber_commutator_fermionMultiCreation (2 * N + 1) (spinfulIndex N i 1))]
    abel
  have han : fermionTotalNumber (2 * N + 1) * fermionUpAnnihilation N i =
      fermionUpAnnihilation N i * fermionTotalNumber (2 * N + 1) - fermionUpAnnihilation N i := by
    unfold fermionUpAnnihilation
    rw [sub_eq_iff_eq_add.mp
      (fermionTotalNumber_commutator_fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N i 0))]
    abel
  have key : Commute (fermionTotalNumber (2 * N + 1))
      (fermionDownCreation N i * fermionUpAnnihilation N i) := by
    change fermionTotalNumber (2 * N + 1) *
        (fermionDownCreation N i * fermionUpAnnihilation N i) =
      fermionDownCreation N i * fermionUpAnnihilation N i * fermionTotalNumber (2 * N + 1)
    rw [← Matrix.mul_assoc, hcr, Matrix.add_mul, Matrix.mul_assoc, han, Matrix.mul_sub,
      ← Matrix.mul_assoc]
    abel
  exact key.symm

/-- **The lowering tower preserves the total-number eigenvalue** (general
eigenvalue `lam`): since `Ŝ^-_tot` commutes with `N̂`, `(Ŝ^-_tot)^k v` keeps the
`N̂`-eigenvalue of `v`. -/
theorem fermionTotalNumber_mulVec_spinMinusPow_eigenvalue (N : ℕ) (k : ℕ) (lam : ℂ)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hv : (fermionTotalNumber (2 * N + 1)).mulVec v = lam • v) :
    (fermionTotalNumber (2 * N + 1)).mulVec (((fermionTotalSpinMinus N) ^ k).mulVec v) =
      lam • (((fermionTotalSpinMinus N) ^ k).mulVec v) := by
  have hcomm : Commute (fermionTotalNumber (2 * N + 1))
      ((fermionTotalSpinMinus N) ^ k) :=
    ((flatBand_fermionTotalSpinMinus_commute_fermionTotalNumber N).symm).pow_right k
  rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]

/-- **Deferred classification input for Tasaki Theorem 11.11** (Appendix A,
Lemmas A.10/A.11): in the half-filled flat-band sector `N_e = K + 1`, every
zero-energy state of the flat-band Hamiltonian lies in the ferromagnetic lowering
multiplet generated by `|Φα,all↑⟩`.

This is the representation-theoretic classification (no `β`-occupation + no double
occupancy ⇒ spatially symmetric ⇒ maximal-spin multiplet) that Tasaki proves via
Appendix A.  A faithful Lean proof requires the Fock-space factorisation of the
*non-orthogonal* `{α} ∪ {β}` basis and the symmetric-tensor/SU(2) classification,
neither currently available; it is deferred as a single documented axiom, matching
the policy for Theorem 11.8 / Lemma 11.9.  The *existence* half of Theorem 11.11
does not depend on this axiom. -/
axiom flatBand_zeroEnergy_halfFilled_mem_ferromagneticMultipletSpan
    (K : ℕ) (ν t U : ℝ) (hν : 0 < ν) (ht : 0 < t) (hU : 0 < U)
    {v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ}
    (hE : rayleighOnVec (flatBandHamiltonian K ν t U) v = 0)
    (hN : (fermionTotalNumber (2 * (2 * K + 1) + 1)).mulVec v =
      ((K + 1 : ℕ) : ℂ) • v) :
    v ∈ Submodule.span ℂ (Set.range (fun k : Fin (K + 2) =>
      ((fermionTotalSpinMinus (2 * K + 1)) ^ (k : ℕ)).mulVec
        (flatBandAlphaAllUpState K ν)))

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

/-- **Tasaki Theorem 11.11 (flat-band ferromagnetism, half-filled ground space).**
The zero-energy `N_e = K + 1` ground subspace of the flat-band Hubbard model is
*exactly* the ferromagnetic lowering multiplet of `|Φα,all↑⟩` (the maximal-spin
`(2 S_max + 1)`-dimensional multiplet).  `≥` is the proven existence side; `≤` is
the deferred classification axiom. -/
theorem flatBand_theorem_11_11_groundSubmodule_eq_multipletSpan (K : ℕ) (ν t U : ℝ)
    (hν : 0 < ν) (ht : 0 < t) (hU : 0 < U) :
    flatBandHalfFilledGroundSubmodule K ν t U = flatBandFerromagneticMultipletSubmodule K ν := by
  apply le_antisymm
  · intro v hv
    rw [flatBandHalfFilledGroundSubmodule, Submodule.mem_inf] at hv
    obtain ⟨hker, heig⟩ := hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hker
    rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at heig
    have hE : rayleighOnVec (flatBandHamiltonian K ν t U) v = 0 := by
      unfold rayleighOnVec
      rw [hker, dotProduct_zero, Complex.zero_re]
    exact flatBand_zeroEnergy_halfFilled_mem_ferromagneticMultipletSpan K ν t U hν ht hU hE heig
  · rw [flatBandFerromagneticMultipletSubmodule, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, flatBandHalfFilledGroundSubmodule, Submodule.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      exact flatBandHamiltonian_mulVec_spinMinusPow_alphaAllUpState K ν t U k
    · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
      exact fermionTotalNumber_mulVec_spinMinusPow_eigenvalue (2 * K + 1) k _
        (flatBandTotalNumber_mulVec_alphaAllUpState K ν)

/-- **Tasaki Theorem 11.11 (maximal-spin corollary).**  Every half-filled
zero-energy ground state carries total spin `S_tot = S_max = (K+1)/2`: it is a
`(Ŝ_tot)²` eigenvector with eigenvalue `S_max(S_max + 1)`.  (Combines the ground
subspace classification with the common total spin of the multiplet.) -/
theorem flatBand_theorem_11_11_groundState_maximalSpin (K : ℕ) (ν t U : ℝ)
    (hν : 0 < ν) (ht : 0 < t) (hU : 0 < U)
    {v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ}
    (hv : v ∈ flatBandHalfFilledGroundSubmodule K ν t U) :
    (fermionTotalSpinSquared (2 * K + 1)).mulVec v =
      (((K + 1 : ℕ) : ℂ) / 2 * (((K + 1 : ℕ) : ℂ) / 2 + 1)) • v := by
  rw [flatBand_theorem_11_11_groundSubmodule_eq_multipletSpan K ν t U hν ht hU,
    flatBandFerromagneticMultipletSubmodule] at hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨k, rfl⟩ := hw
    exact (flatBand_ferromagnetic_multiplet K ν).2 k
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy, smul_add]
  | smul a x _ hx => rw [Matrix.mulVec_smul, hx, smul_comm]

end LatticeSystem.Fermion
