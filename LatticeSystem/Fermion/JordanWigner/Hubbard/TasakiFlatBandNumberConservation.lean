import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandFrustrationFree

/-!
# Tasaki §11.3.1: particle-number conservation and hard-core membership of ground states

Structural facts toward the uniqueness half of Theorem 11.11.

The flat-band Hamiltonian conserves the total particle number,
`[Ĥ, N̂] = 0` (`flatBandHamiltonian_commute_fermionTotalNumber`): the kinetic
term `b̂†_{u,σ} b̂_{u,σ}` is a mode number (raising then lowering), and the
interaction is the standard Hubbard one.  Hence ground states may be analysed
sector by sector (Tasaki works in the `N_e = |E| = K+1` sector).

Moreover, the no-double-occupancy condition (11.3.12) places any ground state in
the Hubbard hard-core subspace (`flatBand_groundState_mem_hardcoreSubspace`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- **`b̂_{u,σ} N̂ − N̂ b̂_{u,σ} = b̂_{u,σ}`**: the `b̂` operator lowers the total
number by one (lifted termwise from `c_j N̂ − N̂ c_j = c_j`). -/
theorem flatBandBAnnihilation_commutator_fermionTotalNumber (K : ℕ) (ν : ℝ)
    (u : Fin (K + 1)) (σ : Fin 2) :
    flatBandBAnnihilation K ν u σ * fermionTotalNumber (2 * (2 * K + 1) + 1) -
        fermionTotalNumber (2 * (2 * K + 1) + 1) * flatBandBAnnihilation K ν u σ =
      flatBandBAnnihilation K ν u σ := by
  unfold flatBandBAnnihilation
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
  congr 1
  rw [← neg_sub, fermionTotalNumber_commutator_fermionMultiAnnihilation]; abel

/-- **`N̂ b̂†_{u,σ} − b̂†_{u,σ} N̂ = b̂†_{u,σ}`**: the `b̂†` operator raises the total
number by one (lifted termwise from `N̂ c†_j − c†_j N̂ = c†_j`). -/
theorem flatBandBCreation_commutator_fermionTotalNumber (K : ℕ) (ν : ℝ)
    (u : Fin (K + 1)) (σ : Fin 2) :
    fermionTotalNumber (2 * (2 * K + 1) + 1) * flatBandBCreation K ν u σ -
        flatBandBCreation K ν u σ * fermionTotalNumber (2 * (2 * K + 1) + 1) =
      flatBandBCreation K ν u σ := by
  unfold flatBandBCreation
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]
  congr 1
  exact fermionTotalNumber_commutator_fermionMultiCreation (2 * (2 * K + 1) + 1)
    (spinfulIndex (2 * K + 1) x σ)

/-- **`[N̂, b̂†_{u,σ} b̂_{u,σ}] = 0`**: each flat-band mode number commutes with the
total number (`b̂†` raises and `b̂` lowers by one, cancelling). -/
theorem fermionTotalNumber_commute_flatBandBMode (K : ℕ) (ν : ℝ) (u : Fin (K + 1))
    (σ : Fin 2) :
    Commute (fermionTotalNumber (2 * (2 * K + 1) + 1))
      (flatBandBCreation K ν u σ * flatBandBAnnihilation K ν u σ) := by
  have hcr : fermionTotalNumber (2 * (2 * K + 1) + 1) * flatBandBCreation K ν u σ =
      flatBandBCreation K ν u σ * fermionTotalNumber (2 * (2 * K + 1) + 1) +
        flatBandBCreation K ν u σ := by
    rw [sub_eq_iff_eq_add.mp (flatBandBCreation_commutator_fermionTotalNumber K ν u σ)]
    abel
  have han : fermionTotalNumber (2 * (2 * K + 1) + 1) * flatBandBAnnihilation K ν u σ =
      flatBandBAnnihilation K ν u σ * fermionTotalNumber (2 * (2 * K + 1) + 1) -
        flatBandBAnnihilation K ν u σ := by
    rw [sub_eq_iff_eq_add.mp (flatBandBAnnihilation_commutator_fermionTotalNumber K ν u σ)]
    abel
  change fermionTotalNumber (2 * (2 * K + 1) + 1) *
      (flatBandBCreation K ν u σ * flatBandBAnnihilation K ν u σ) =
    flatBandBCreation K ν u σ * flatBandBAnnihilation K ν u σ *
      fermionTotalNumber (2 * (2 * K + 1) + 1)
  rw [← Matrix.mul_assoc, hcr, Matrix.add_mul, Matrix.mul_assoc, han, Matrix.mul_sub,
    ← Matrix.mul_assoc]
  abel

/-- **`[Ĥ, N̂] = 0`**: the flat-band Hamiltonian conserves the total particle
number.  The kinetic term is a sum of mode numbers (each number-conserving) and
the interaction is the standard Hubbard `n̂↑n̂↓`. -/
theorem flatBandHamiltonian_commute_fermionTotalNumber (K : ℕ) (ν t U : ℝ) :
    Commute (flatBandHamiltonian K ν t U) (fermionTotalNumber (2 * (2 * K + 1) + 1)) := by
  unfold flatBandHamiltonian
  refine Commute.add_left (Commute.smul_left ?_ _) (Commute.smul_left ?_ _)
  · exact Commute.sum_left _ _ _ (fun u _ =>
      Commute.sum_left _ _ _ (fun σ _ =>
        (fermionTotalNumber_commute_flatBandBMode K ν u σ).symm))
  · refine Commute.sum_left _ _ _ (fun x _ => ?_)
    unfold hubbardDoubleOccupancy fermionUpNumber fermionDownNumber
    exact (fermionMultiNumber_commute_fermionTotalNumber (2 * (2 * K + 1) + 1)
        (spinfulIndex (2 * K + 1) x 0)).mul_left
      (fermionMultiNumber_commute_fermionTotalNumber (2 * (2 * K + 1) + 1)
        (spinfulIndex (2 * K + 1) x 1))

/-- **Any ground state lies in the Hubbard hard-core subspace** (no double
occupancy, eq. (11.3.12)): every same-site double-occupancy operator annihilates
it. -/
theorem flatBand_groundState_mem_hardcoreSubspace (K : ℕ) (ν t U : ℝ) (ht : 0 ≤ t)
    (hU : 0 < U) {v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ}
    (hv : rayleighOnVec (flatBandHamiltonian K ν t U) v = 0) :
    v ∈ hubbardHardcoreSubspace (2 * K + 1) :=
  (mem_hubbardHardcoreSubspace_iff (2 * K + 1)).mpr
    (fun x => flatBand_groundState_doubleOccupancy_mulVec_eq_zero K ν t U ht hU hv x)

end LatticeSystem.Fermion
