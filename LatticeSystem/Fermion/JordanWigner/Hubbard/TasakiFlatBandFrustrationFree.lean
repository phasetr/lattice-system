import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandPosSemidef
import LatticeSystem.Math.RayleighPosSemidefKernel

/-!
# Tasaki §11.3.1: frustration-free conditions on the flat-band ground states

Toward the *uniqueness* half of Theorem 11.11.  The flat-band Hamiltonian is a
nonnegative combination of positive-semidefinite terms, `Ĥ = t Σ b̂† b̂ + U Σ n̂↑n̂↓`
with `t, U > 0`, and its ground energy is `0`.  Hence any ground state `v`
(energy quadratic form `rayleighOnVec Ĥ v = 0`) is annihilated by **every** term
separately (frustration-freeness, Tasaki App. A Lemmas A.10/A.11):

* `flatBand_groundState_BAnnihilation_mulVec_eq_zero`: `b̂_{u,σ} v = 0` for all
  `u, σ` (eq. (11.3.11));
* `flatBand_groundState_doubleOccupancy_mulVec_eq_zero`: `n̂_{x↑} n̂_{x↓} v = 0`
  (the no-double-occupancy form of eq. (11.3.12)).

These are the structural constraints from which Tasaki deduces that a ground state
lives in the `α`-band with no double occupancy, hence is spatially symmetric and
carries maximal spin (the remaining steps).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1, eqs. (11.3.11)/(11.3.12), App. A Lemmas A.10/A.11.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- **Energy decomposition.**  The flat-band energy quadratic form splits into the
nonnegative per-term contributions. -/
theorem flatBandHamiltonian_rayleighOnVec_decompose (K : ℕ) (ν t U : ℝ)
    (v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ) :
    rayleighOnVec (flatBandHamiltonian K ν t U) v =
      t * ∑ u : Fin (K + 1), ∑ σ : Fin 2,
          rayleighOnVec (flatBandBCreation K ν u σ * flatBandBAnnihilation K ν u σ) v
        + U * ∑ x : Fin (2 * K + 2),
          rayleighOnVec (hubbardDoubleOccupancy (2 * K + 1) x) v := by
  unfold flatBandHamiltonian
  rw [rayleighOnVec_add_matrix, rayleighOnVec_real_smul, rayleighOnVec_real_smul]
  simp only [rayleighOnVec_sum]

/-- **Eq. (11.3.11): `b̂_{u,σ} v = 0`** for any ground state `v`.  The kinetic
term `b̂†_{u,σ} b̂_{u,σ}` of the (frustration-free) ground state vanishes, hence so
does `b̂_{u,σ} v`. -/
theorem flatBand_groundState_BAnnihilation_mulVec_eq_zero (K : ℕ) (ν t U : ℝ)
    (ht : 0 < t) (hU : 0 ≤ U) {v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ}
    (hv : rayleighOnVec (flatBandHamiltonian K ν t U) v = 0) (u : Fin (K + 1)) (σ : Fin 2) :
    (flatBandBAnnihilation K ν u σ).mulVec v = 0 := by
  have hkin_nonneg : ∀ u' σ', 0 ≤ rayleighOnVec
      (flatBandBCreation K ν u' σ' * flatBandBAnnihilation K ν u' σ') v := fun u' σ' =>
    (flatBandKineticTerm_posSemidef K ν u' σ').re_dotProduct_nonneg v
  have hint_nonneg : ∀ x, 0 ≤ rayleighOnVec (hubbardDoubleOccupancy (2 * K + 1) x) v :=
    fun x => (hubbardDoubleOccupancy_posSemidef (2 * K + 1) x).re_dotProduct_nonneg v
  have hdec := flatBandHamiltonian_rayleighOnVec_decompose K ν t U v
  rw [hv] at hdec
  -- 0 = t * (kinetic sum) + U * (interaction sum), both nonnegative
  have hKin : (0 : ℝ) ≤ ∑ u' : Fin (K + 1), ∑ σ' : Fin 2,
      rayleighOnVec (flatBandBCreation K ν u' σ' * flatBandBAnnihilation K ν u' σ') v :=
    Finset.sum_nonneg (fun u' _ => Finset.sum_nonneg (fun σ' _ => hkin_nonneg u' σ'))
  have hInt : (0 : ℝ) ≤ ∑ x : Fin (2 * K + 2),
      rayleighOnVec (hubbardDoubleOccupancy (2 * K + 1) x) v :=
    Finset.sum_nonneg (fun x _ => hint_nonneg x)
  have hKinZero : (∑ u' : Fin (K + 1), ∑ σ' : Fin 2,
      rayleighOnVec (flatBandBCreation K ν u' σ' * flatBandBAnnihilation K ν u' σ') v) = 0 := by
    nlinarith [mul_nonneg ht.le hKin, mul_nonneg hU hInt, hdec]
  have hterm : rayleighOnVec
      (flatBandBCreation K ν u σ * flatBandBAnnihilation K ν u σ) v = 0 := by
    have h1 : (∑ σ' : Fin 2,
        rayleighOnVec (flatBandBCreation K ν u σ' * flatBandBAnnihilation K ν u σ') v) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun u' _ =>
        Finset.sum_nonneg (fun σ' _ => hkin_nonneg u' σ'))).mp hKinZero u (Finset.mem_univ u)
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun σ' _ => hkin_nonneg u σ')).mp h1 σ
      (Finset.mem_univ σ)
  have hKv : (flatBandBCreation K ν u σ * flatBandBAnnihilation K ν u σ).mulVec v = 0 :=
    posSemidef_mulVec_eq_zero_of_rayleighOnVec_zero (flatBandKineticTerm_posSemidef K ν u σ) hterm
  rw [← flatBandBCreation_eq_conjTranspose] at hKv
  exact conjTranspose_mul_self_mulVec_eq_zero hKv

/-- **No double occupancy: `n̂_{x↑} n̂_{x↓} v = 0`** for any ground state `v`
(the form of eq. (11.3.12)). -/
theorem flatBand_groundState_doubleOccupancy_mulVec_eq_zero (K : ℕ) (ν t U : ℝ)
    (ht : 0 ≤ t) (hU : 0 < U) {v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ}
    (hv : rayleighOnVec (flatBandHamiltonian K ν t U) v = 0) (x : Fin (2 * K + 2)) :
    (hubbardDoubleOccupancy (2 * K + 1) x).mulVec v = 0 := by
  have hkin_nonneg : ∀ u' σ', 0 ≤ rayleighOnVec
      (flatBandBCreation K ν u' σ' * flatBandBAnnihilation K ν u' σ') v := fun u' σ' =>
    (flatBandKineticTerm_posSemidef K ν u' σ').re_dotProduct_nonneg v
  have hint_nonneg : ∀ x', 0 ≤ rayleighOnVec (hubbardDoubleOccupancy (2 * K + 1) x') v :=
    fun x' => (hubbardDoubleOccupancy_posSemidef (2 * K + 1) x').re_dotProduct_nonneg v
  have hdec := flatBandHamiltonian_rayleighOnVec_decompose K ν t U v
  rw [hv] at hdec
  have hKin : (0 : ℝ) ≤ ∑ u' : Fin (K + 1), ∑ σ' : Fin 2,
      rayleighOnVec (flatBandBCreation K ν u' σ' * flatBandBAnnihilation K ν u' σ') v :=
    Finset.sum_nonneg (fun u' _ => Finset.sum_nonneg (fun σ' _ => hkin_nonneg u' σ'))
  have hInt : (0 : ℝ) ≤ ∑ x' : Fin (2 * K + 2),
      rayleighOnVec (hubbardDoubleOccupancy (2 * K + 1) x') v :=
    Finset.sum_nonneg (fun x' _ => hint_nonneg x')
  have hIntZero : (∑ x' : Fin (2 * K + 2),
      rayleighOnVec (hubbardDoubleOccupancy (2 * K + 1) x') v) = 0 := by
    nlinarith [mul_nonneg ht hKin, mul_nonneg hU.le hInt, hdec]
  have hterm : rayleighOnVec (hubbardDoubleOccupancy (2 * K + 1) x) v = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun x' _ => hint_nonneg x')).mp hIntZero x
      (Finset.mem_univ x)
  exact posSemidef_mulVec_eq_zero_of_rayleighOnVec_zero
    (hubbardDoubleOccupancy_posSemidef (2 * K + 1) x) hterm

end LatticeSystem.Fermion
