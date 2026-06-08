import LatticeSystem.Fermion.JordanWigner.Hubbard.NonsingularLocalHamiltonian
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandBasis

/-!
# Tasaki §11.4.3: the frustration-free decomposition (eq. (11.4.46)) — towards Lemma 11.21

The non-singular Hubbard Hamiltonian is a frustration-free sum of the local Hamiltonians `ĥ_p`
(`nonsingularLocalHamiltonian`) plus a constant and a manifestly positive remainder:

`tasakiNonsingularHamiltonian = (Σ_i ĥ_p i) − (K+1)(1+2ν²)s·1 + lam·(Σ_u N̂^β_u + Σ_x n̂↑n̂↓_x)`

(holds for all `lam, κ`; the `κ`-dependence inside `Σ_i ĥ_p i` cancels by incidence multiplicity).
This file proves the per-site multiplicity lemmas and assembles the decomposition.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.4.3, eq. (11.4.46) (pp. 429–435).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {K : ℕ} {ν : ℝ}

/-- **Cyclic reindexing**: summing `f (p - 1)` over `p ∈ Fin (K+1)` equals summing `f p`. -/
theorem sum_shift_sub_one {M : Type*} [AddCommMonoid M] (f : Fin (K + 1) → M) :
    ∑ p, f (p - 1) = ∑ p, f p :=
  Equiv.sum_comp (Equiv.subRight 1) f

/-- **Cyclic reindexing**: summing `f (p + 1)` over `p ∈ Fin (K+1)` equals summing `f p`. -/
theorem sum_shift_add_one {M : Type*} [AddCommMonoid M] (f : Fin (K + 1) → M) :
    ∑ p, f (p + 1) = ∑ p, f p :=
  Equiv.sum_comp (Equiv.addRight 1) f

/-- The sum of the local Hamiltonians collapses to the canonical single-species sums. -/
theorem sum_nonsingularLocalHamiltonian (K : ℕ) (ν s t U lam κ : ℝ) :
    (∑ i, nonsingularLocalHamiltonian K ν s t U lam κ i)
      = ((K + 1 : ℂ) * ((1 + 2 * ν ^ 2) * s)) • (1 : ManyBodyOp (Fin (2 * (2 * K + 1) + 2)))
        - (s : ℂ) • (∑ i, flatBandANumber K ν i)
        + ((t - lam : ℝ) : ℂ) • (∑ u, flatBandBNumber K ν u)
        + ((U - lam : ℝ) : ℂ) • (∑ x, hubbardDoubleOccupancy (2 * K + 1) x) := by
  simp only [nonsingularLocalHamiltonian, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.smul_sum, sum_shift_sub_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [sum_shift_sub_one (fun u => hubbardDoubleOccupancy (2 * K + 1) (deltaInternalSite K u)),
    sum_shift_sub_one (fun u => hubbardDoubleOccupancy (2 * K + 1) (deltaExternalSite K u)),
    sum_shift_add_one (fun u => hubbardDoubleOccupancy (2 * K + 1) (deltaExternalSite K u)),
    sum_deltaSite_split K (fun x => hubbardDoubleOccupancy (2 * K + 1) x)]
  push_cast
  module

/-- **The frustration-free decomposition (Tasaki eq. (11.4.46), `d = 1`).**  The non-singular Hubbard
Hamiltonian is the sum of the local Hamiltonians `ĥ_p` minus a constant plus a manifestly positive
remainder (`lam`-multiplied), for every choice of `lam, κ` (the `κ`-dependence cancels):
`tasakiNonsingularHamiltonian = (Σ_i ĥ_p i) − (K+1)(1+2ν²)s·1 + lam·(Σ_u N̂^β_u + Σ_x n̂↑n̂↓_x)`. -/
theorem tasakiNonsingular_eq_sum_localHamiltonian (K : ℕ) (ν s t U lam κ : ℝ) :
    tasakiNonsingularHamiltonian K ν t s U
      = (∑ i, nonsingularLocalHamiltonian K ν s t U lam κ i)
        - ((K + 1 : ℂ) * ((1 + 2 * ν ^ 2) * s)) • (1 : ManyBodyOp (Fin (2 * (2 * K + 1) + 2)))
        + (lam : ℂ) • ((∑ u, flatBandBNumber K ν u) +
            ∑ x, hubbardDoubleOccupancy (2 * K + 1) x) := by
  rw [sum_nonsingularLocalHamiltonian, tasakiNonsingularHamiltonian, flatBandHamiltonian]
  simp only [flatBandANumber, flatBandBNumber]
  push_cast
  module

/-- **`|Φα,all↑⟩` is an eigenvector of `Ĥ` with eigenvalue `−(K+1)(1+2ν²)s`.**  Using the
decomposition (11.4.46) at `lam = κ = 0`, `Ĥ = (Σ_i ĥ_p) − (K+1)(1+2ν²)s·1`, and every `ĥ_p`
annihilates the all-up state (`nonsingularLocalHamiltonian_mulVec_alphaAllUpState`).  Requires a
genuine chain (`1 ≤ K`).  This pins `sectorMinEnergy` at the maximal-spin sector to `−(K+1)(1+2ν²)s`
(the ground energy), the first half of the ferromagnetism assembly (Lemma 11.21). -/
theorem tasakiNonsingularHamiltonian_mulVec_alphaAllUpState (K : ℕ) (ν t s U : ℝ) (hK : 1 ≤ K) :
    (tasakiNonsingularHamiltonian K ν t s U).mulVec (flatBandAlphaAllUpState K ν)
      = (-((K + 1 : ℂ) * ((1 + 2 * ν ^ 2) * s))) • flatBandAlphaAllUpState K ν := by
  have hone : (1 : Fin (K + 1)) ≠ 0 := by
    intro h
    rw [Fin.ext_iff, Fin.val_zero, Fin.val_one' (K + 1),
      Nat.mod_eq_of_lt (by omega : 1 < K + 1)] at h
    exact one_ne_zero h
  have hi : ∀ i : Fin (K + 1), i - 1 ≠ i := fun i h => hone (sub_eq_self.mp h)
  rw [tasakiNonsingular_eq_sum_localHamiltonian K ν s t U 0 0, Matrix.add_mulVec,
    Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.sum_mulVec,
    Finset.sum_eq_zero (fun i _ =>
      nonsingularLocalHamiltonian_mulVec_alphaAllUpState K ν s t U 0 0 i (hi i)),
    Complex.ofReal_zero, zero_smul, add_zero, zero_sub, neg_smul]

end LatticeSystem.Fermion
