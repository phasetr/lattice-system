import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandZeroEnergy
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandMultiplet
import LatticeSystem.Fermion.JordanWigner.Hubbard.EffectiveHamiltonianSpinSymmetry
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinTotHermitian

/-!
# Tasaki §11.3.1: flat-band SU(2) lowering symmetry and the energy tower

The flat-band Hamiltonian `Ĥ = t Σ_{u,σ} b̂†_{u,σ} b̂_{u,σ} + U Σ_x n̂_{x↑} n̂_{x↓}`
is SU(2) symmetric: it commutes with `Ŝ^±_tot`.  The kinetic term is spin
symmetric (the `b̂` operators are a spin doublet, built from the *same* spatial
`β_u`), and the on-site interaction is the standard Hubbard one.

* `fermionTotalSpinPlus_commute_flatBandHamiltonian` / `…Minus…`:
  `[Ŝ^±_tot, Ĥ] = 0`.
* `flatBandHamiltonian_mulVec_spinMinusPow_alphaAllUpState`: hence the **energy
  tower** `Ĥ (Ŝ^-_tot)^k |Φα,all↑⟩ = 0` — every member of the ferromagnetic
  multiplet is a zero-energy state.

Together with `flatBand_ferromagnetic_multiplet`, the `K + 2` lowered states are
linearly independent, share total spin `S_max = (K+1)/2`, and are all zero-energy:
the maximal-spin degenerate multiplet of the existence half of Theorem 11.11.
(That `0` is the *ground* energy needs `Ĥ ≥ 0`, the remaining step.)

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1, Theorem 11.11 (existence half) and §9.3.3 (SU(2) symmetry).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- **`[Ŝ^+_tot, b̂†_{u,↑}] = 0`.**  `b̂†_{u,↑}` is a combination of up creations,
each of which commutes with `Ŝ^+_tot`. -/
theorem flatBandBCreation_up_commute_fermionTotalSpinPlus (K : ℕ) (ν : ℝ) (u : Fin (K + 1)) :
    Commute (fermionTotalSpinPlus (2 * K + 1)) (flatBandBCreation K ν u 0) := by
  unfold flatBandBCreation
  exact Commute.sum_right _ _ _ (fun x _ =>
    ((fermionUpCreation_commute_fermionTotalSpinPlus (2 * K + 1) x).symm).smul_right _)

/-- **`[Ŝ^+_tot, b̂_{u,↓}] = 0`.**  `b̂_{u,↓}` is a combination of down
annihilations, each of which commutes with `Ŝ^+_tot`. -/
theorem flatBandBAnnihilation_down_commute_fermionTotalSpinPlus (K : ℕ) (ν : ℝ)
    (u : Fin (K + 1)) :
    Commute (fermionTotalSpinPlus (2 * K + 1)) (flatBandBAnnihilation K ν u 1) := by
  unfold flatBandBAnnihilation
  exact Commute.sum_right _ _ _ (fun x _ =>
    ((fermionDownAnnihilation_commute_fermionTotalSpinPlus (2 * K + 1) x).symm).smul_right _)

/-- **`b̂_{u,↑} Ŝ^+_tot − Ŝ^+_tot b̂_{u,↑} = b̂_{u,↓}`.**  The spin-raising operator
turns the up `b̂` into the down `b̂` (lifted termwise from `[c_{x,↑}, Ŝ^+] =
c_{x,↓}`). -/
theorem flatBandBAnnihilation_up_commutator_fermionTotalSpinPlus (K : ℕ) (ν : ℝ)
    (u : Fin (K + 1)) :
    flatBandBAnnihilation K ν u 0 * fermionTotalSpinPlus (2 * K + 1) -
        fermionTotalSpinPlus (2 * K + 1) * flatBandBAnnihilation K ν u 0 =
      flatBandBAnnihilation K ν u 1 := by
  unfold flatBandBAnnihilation
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
  congr 1
  exact fermionUpAnnihilation_commutator_fermionTotalSpinPlus (2 * K + 1) x

/-- **`Ŝ^+_tot b̂†_{u,↓} − b̂†_{u,↓} Ŝ^+_tot = b̂†_{u,↑}`** (lifted termwise from
`[c^†_{x,↓}, Ŝ^+] = −c^†_{x,↑}`, i.e. `Ŝ^+ c^†_{x,↓} − c^†_{x,↓} Ŝ^+ = c^†_{x,↑}`). -/
theorem flatBandBCreation_down_commutator_fermionTotalSpinPlus (K : ℕ) (ν : ℝ)
    (u : Fin (K + 1)) :
    fermionTotalSpinPlus (2 * K + 1) * flatBandBCreation K ν u 1 -
        flatBandBCreation K ν u 1 * fermionTotalSpinPlus (2 * K + 1) =
      flatBandBCreation K ν u 0 := by
  unfold flatBandBCreation
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]
  congr 1
  have h : fermionTotalSpinPlus (2 * K + 1) * fermionDownCreation (2 * K + 1) x -
      fermionDownCreation (2 * K + 1) x * fermionTotalSpinPlus (2 * K + 1) =
      fermionUpCreation (2 * K + 1) x := by
    rw [← neg_sub, fermionDownCreation_commutator_fermionTotalSpinPlus]; abel
  exact h

/-- **Two-component kinetic term commutes with `S`.**  If the pair
`(bd0, b0), (bd1, b1)` transforms as an SU(2) doublet under `S`
(`S bd0 = bd0 S`, `S b0 = b0 S − b1`, `S bd1 = bd1 S + bd0`, `S b1 = b1 S`), then
the spin-summed number operator `bd0 b0 + bd1 b1` commutes with `S` (the
off-diagonal terms cancel). -/
private theorem commute_two_component_kinetic_of_spinPlus_relations
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (S bd0 b0 bd1 b1 : ManyBodyOp Λ)
    (hbd0 : S * bd0 = bd0 * S)
    (hb0 : S * b0 = b0 * S - b1)
    (hbd1 : S * bd1 = bd1 * S + bd0)
    (hb1 : S * b1 = b1 * S) :
    Commute S (bd0 * b0 + bd1 * b1) := by
  change S * (bd0 * b0 + bd1 * b1) = (bd0 * b0 + bd1 * b1) * S
  rw [Matrix.mul_add, Matrix.add_mul,
    ← Matrix.mul_assoc S bd0, hbd0, Matrix.mul_assoc, hb0, Matrix.mul_sub,
    ← Matrix.mul_assoc S bd1, hbd1, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hb1]
  rw [show bd1 * (b1 * S) + bd0 * b1 = bd1 * b1 * S + bd0 * b1 from by rw [Matrix.mul_assoc]]
  abel

/-- **`[Ŝ^+_tot, Σ_σ b̂†_{u,σ} b̂_{u,σ}] = 0`** for each mode `u`: the spin-summed
mode number operator is SU(2) invariant. -/
theorem fermionTotalSpinPlus_commute_flatBandBMode (K : ℕ) (ν : ℝ) (u : Fin (K + 1)) :
    Commute (fermionTotalSpinPlus (2 * K + 1))
      (∑ σ : Fin 2, flatBandBCreation K ν u σ * flatBandBAnnihilation K ν u σ) := by
  rw [Fin.sum_univ_two]
  refine commute_two_component_kinetic_of_spinPlus_relations _ _ _ _ _
    (flatBandBCreation_up_commute_fermionTotalSpinPlus K ν u).eq ?_ ?_
    (flatBandBAnnihilation_down_commute_fermionTotalSpinPlus K ν u).eq
  · have h := flatBandBAnnihilation_up_commutator_fermionTotalSpinPlus K ν u
    rw [← h]; abel
  · have h := flatBandBCreation_down_commutator_fermionTotalSpinPlus K ν u
    rw [← h]; abel

/-- **`[Ŝ^+_tot, Ĥ_hop] = 0`**: the flat-band kinetic term is SU(2) invariant
(sum over modes of the spin-summed mode number, scaled by `t`). -/
theorem fermionTotalSpinPlus_commute_flatBandHopping (K : ℕ) (ν t : ℝ) :
    Commute (fermionTotalSpinPlus (2 * K + 1))
      ((t : ℂ) • ∑ u : Fin (K + 1), ∑ σ : Fin 2,
        flatBandBCreation K ν u σ * flatBandBAnnihilation K ν u σ) :=
  (Commute.sum_right _ _ _ (fun u _ =>
    fermionTotalSpinPlus_commute_flatBandBMode K ν u)).smul_right _

/-- **`[Ŝ^+_tot, Ĥ_int] = 0`**: the on-site Hubbard interaction is SU(2)
invariant. -/
theorem fermionTotalSpinPlus_commute_flatBandInteraction (K : ℕ) (U : ℝ) :
    Commute (fermionTotalSpinPlus (2 * K + 1))
      ((U : ℂ) • ∑ x : Fin (2 * K + 2), hubbardDoubleOccupancy (2 * K + 1) x) :=
  (Commute.sum_right _ _ _ (fun x _ =>
    fermionTotalSpinPlus_commute_hubbardDoubleOccupancy (2 * K + 1) x)).smul_right _

/-- **`[Ŝ^+_tot, Ĥ] = 0`**: the flat-band Hamiltonian is SU(2) symmetric. -/
theorem fermionTotalSpinPlus_commute_flatBandHamiltonian (K : ℕ) (ν t U : ℝ) :
    Commute (fermionTotalSpinPlus (2 * K + 1)) (flatBandHamiltonian K ν t U) := by
  unfold flatBandHamiltonian
  exact (fermionTotalSpinPlus_commute_flatBandHopping K ν t).add_right
    (fermionTotalSpinPlus_commute_flatBandInteraction K U)

/-- **`[Ŝ^-_tot, Ĥ] = 0`**: derived from `[Ŝ^+_tot, Ĥ] = 0` by taking adjoints
(`Ĥ` Hermitian, `(Ŝ^+_tot)ᴴ = Ŝ^-_tot`). -/
theorem fermionTotalSpinMinus_commute_flatBandHamiltonian (K : ℕ) (ν t U : ℝ) :
    Commute (fermionTotalSpinMinus (2 * K + 1)) (flatBandHamiltonian K ν t U) := by
  have h_plus := (fermionTotalSpinPlus_commute_flatBandHamiltonian K ν t U).eq
  have h_H := flatBandHamiltonian_isHermitian K ν t U
  have h_adj := congrArg Matrix.conjTranspose h_plus
  simp only [Matrix.conjTranspose_mul, fermionTotalSpinPlus_conjTranspose (2 * K + 1),
    h_H.eq] at h_adj
  exact h_adj.symm

/-- **Energy tower: `Ĥ (Ŝ^-_tot)^k |Φα,all↑⟩ = 0`.**  Since `Ĥ` commutes with
`Ŝ^-_tot` and annihilates `|Φα,all↑⟩`, it annihilates every lowered descendant —
each member of the ferromagnetic multiplet is a zero-energy state. -/
theorem flatBandHamiltonian_mulVec_spinMinusPow_alphaAllUpState (K : ℕ) (ν t U : ℝ) (k : ℕ) :
    (flatBandHamiltonian K ν t U).mulVec
      (((fermionTotalSpinMinus (2 * K + 1)) ^ k).mulVec (flatBandAlphaAllUpState K ν)) = 0 := by
  have hcomm : Commute (flatBandHamiltonian K ν t U)
      ((fermionTotalSpinMinus (2 * K + 1)) ^ k) :=
    ((fermionTotalSpinMinus_commute_flatBandHamiltonian K ν t U).symm).pow_right k
  rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec,
    flatBandHamiltonian_mulVec_alphaAllUpState, Matrix.mulVec_zero]

end LatticeSystem.Fermion
