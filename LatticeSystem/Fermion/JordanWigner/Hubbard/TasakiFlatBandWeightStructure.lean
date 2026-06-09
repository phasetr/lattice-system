import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandOccBasis
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandNumberConservation

/-!
# Tasaki §11.3.1: number weight of the rotated occupation monomials (toward weight-block ≤ 1)

Toward the symmetric/maximal-spin classification (the residual `finrank(Ŝ^z-weight block) ≤ 1` of
Theorem 11.11), we record the diagonal `N̂`-action on the rotated occupation basis: an occupation
monomial `occMonomial f` is a total-number eigenvector with eigenvalue the number of occupied modes
`card (occFinset f)`.  Each mode creation `Ĉ†_σ(w)` raises `N̂` by one (`[N̂, Ĉ†_σ(w)] = Ĉ†_σ(w)`,
lifted termwise from the site creations), so an ordered product of `card (occFinset f)` creations on
the vacuum (annihilated by `N̂`) scales by that count.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1.  Tracked in Issue #4346.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {K : ℕ} {ν : ℝ}

/-- **`N̂ Ĉ†_σ(w) − Ĉ†_σ(w) N̂ = Ĉ†_σ(w)`**: a mode creation raises the total particle number
by one, lifted termwise from the site-creation relation `N̂ ĉ†_j − ĉ†_j N̂ = ĉ†_j`. -/
theorem flatBandModeCreation_commutator_fermionTotalNumber (K : ℕ) (σ : Fin 2)
    (w : Fin (2 * K + 2) → ℂ) :
    fermionTotalNumber (2 * (2 * K + 1) + 1) * flatBandModeCreation K σ w -
        flatBandModeCreation K σ w * fermionTotalNumber (2 * (2 * K + 1) + 1) =
      flatBandModeCreation K σ w := by
  simp only [flatBandModeCreation, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]
  congr 1
  exact fermionTotalNumber_commutator_fermionMultiCreation (2 * (2 * K + 1) + 1)
    (spinfulIndex (2 * K + 1) x σ)

/-- **The number weight of a rotated list-monomial.**  `N̂ (∏ Ĉ†) |vac⟩ = (length) • (∏ Ĉ†) |vac⟩`:
the vacuum is annihilated by `N̂` and each of the `length` creations raises `N̂` by one. -/
theorem fermionTotalNumber_mulVec_flatBandModeMonomial (K : ℕ) (ν : ℝ)
    (l : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2)) :
    (fermionTotalNumber (2 * (2 * K + 1) + 1)).mulVec (flatBandModeMonomial K ν l)
      = (l.length : ℂ) • flatBandModeMonomial K ν l := by
  induction l with
  | nil =>
    simp only [flatBandModeMonomial, List.map_nil, List.prod_nil, List.length_nil,
      Nat.cast_zero, zero_smul]
    rw [Matrix.one_mulVec, fermionTotalNumber_mulVec_vacuum]
  | cons q l' ih =>
    have hcons : flatBandModeMonomial K ν (q :: l')
        = (flatBandModeCreation K q.2 (flatBandBasis K ν q.1)).mulVec
            (flatBandModeMonomial K ν l') := by
      simp only [flatBandModeMonomial, List.map_cons, List.prod_cons]
      rw [← Matrix.mulVec_mulVec]
    have hcomm : fermionTotalNumber (2 * (2 * K + 1) + 1) *
          flatBandModeCreation K q.2 (flatBandBasis K ν q.1)
        = flatBandModeCreation K q.2 (flatBandBasis K ν q.1) *
            fermionTotalNumber (2 * (2 * K + 1) + 1)
          + flatBandModeCreation K q.2 (flatBandBasis K ν q.1) := by
      rw [eq_add_of_sub_eq
        (flatBandModeCreation_commutator_fermionTotalNumber K q.2 (flatBandBasis K ν q.1))]
      abel
    rw [hcons, Matrix.mulVec_mulVec, hcomm, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ih,
      Matrix.mulVec_smul, List.length_cons, Nat.cast_succ, add_smul, one_smul]

/-- **The number weight of an occupation monomial.**  `occMonomial f` is a total-number eigenvector
with eigenvalue `card (occFinset f)`, the number of occupied rotated modes. -/
theorem fermionTotalNumber_mulVec_occMonomial (K : ℕ) (ν : ℝ)
    (f : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2) :
    (fermionTotalNumber (2 * (2 * K + 1) + 1)).mulVec (occMonomial K ν f)
      = ((occFinset f).card : ℂ) • occMonomial K ν f := by
  rw [occMonomial, fermionTotalNumber_mulVec_flatBandModeMonomial, Finset.length_toList]

end LatticeSystem.Fermion
