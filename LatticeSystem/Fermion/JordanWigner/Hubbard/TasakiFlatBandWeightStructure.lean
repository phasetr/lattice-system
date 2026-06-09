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

/-! ## `Ŝ^z`-weight of the occupation monomials -/

/-- **The spin charge of a mode** `(1/2 if up, −1/2 if down)`. -/
noncomputable def flatBandSpinCharge (σ : Fin 2) : ℂ := (1 / 2 : ℂ) - (σ.val : ℂ)

@[simp] theorem flatBandSpinCharge_zero : flatBandSpinCharge 0 = (1 / 2 : ℂ) := by
  simp [flatBandSpinCharge]

@[simp] theorem flatBandSpinCharge_one : flatBandSpinCharge 1 = -(1 / 2 : ℂ) := by
  simp only [flatBandSpinCharge, Fin.val_one, Nat.cast_one]; norm_num

/-- **`[Ŝ^z, ĉ†_{x,σ}] = (1/2 − σ) ĉ†_{x,σ}`** (per spinful site): the up creation raises `Ŝ^z` by
`1/2`, the down creation lowers it by `1/2`.  From `Ŝ^z = ½(N̂_↑ − N̂_↓)` and the up/down number
commutators (the same-spin number raises by one, the opposite-spin number commutes). -/
theorem fermionTotalSpinZ_commutator_spinfulCreation (K : ℕ) (x : Fin (2 * K + 2)) (σ : Fin 2) :
    fermionTotalSpinZ (2 * K + 1) *
        fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ)
      = fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ) *
          fermionTotalSpinZ (2 * K + 1)
        + flatBandSpinCharge σ •
          fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ) := by
  have hup0 : fermionTotalUpNumber (2 * K + 1) *
        fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 0)
      = fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 0) *
          fermionTotalUpNumber (2 * K + 1)
        + fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 0) := by
    have h := fermionTotalUpNumber_commutator_fermionUpCreation (2 * K + 1) x
    unfold fermionUpCreation at h; rw [sub_eq_iff_eq_add] at h; rw [h]; abel
  have hdown0 : fermionTotalDownNumber (2 * K + 1) *
        fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 0)
      = fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 0) *
          fermionTotalDownNumber (2 * K + 1) := by
    have h := (fermionTotalDownNumber_commute_fermionUpCreation (2 * K + 1) x).eq
    unfold fermionUpCreation at h; rw [h]
  have hup1 : fermionTotalUpNumber (2 * K + 1) *
        fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 1)
      = fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 1) *
          fermionTotalUpNumber (2 * K + 1) := by
    have h := (fermionTotalUpNumber_commute_fermionDownCreation (2 * K + 1) x).eq
    unfold fermionDownCreation at h; rw [h]
  have hdown1 : fermionTotalDownNumber (2 * K + 1) *
        fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 1)
      = fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 1) *
          fermionTotalDownNumber (2 * K + 1)
        + fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 1) := by
    have h := fermionTotalDownNumber_commutator_fermionDownCreation (2 * K + 1) x
    unfold fermionDownCreation at h; rw [sub_eq_iff_eq_add] at h; rw [h]; abel
  unfold fermionTotalSpinZ
  rw [smul_mul_assoc, Matrix.sub_mul]
  fin_cases σ
  · simp only [Fin.isValue, Fin.mk_zero, flatBandSpinCharge_zero]
    rw [hup0, hdown0, mul_smul_comm, Matrix.mul_sub, ← smul_add]
    congr 1
    abel
  · simp only [Fin.isValue, Fin.mk_one, flatBandSpinCharge_one]
    rw [hup1, hdown1, mul_smul_comm, Matrix.mul_sub, neg_smul, ← sub_eq_add_neg, ← smul_sub]
    congr 1
    abel

/-- **`[Ŝ^z, Ĉ†_σ(w)] = (1/2 − σ) Ĉ†_σ(w)`**: a mode creation of spin `σ` is an `Ŝ^z`-weight
operator, lifted termwise from the per-site commutator. -/
theorem flatBandModeCreation_commutator_fermionTotalSpinZ (K : ℕ) (σ : Fin 2)
    (w : Fin (2 * K + 2) → ℂ) :
    fermionTotalSpinZ (2 * K + 1) * flatBandModeCreation K σ w -
        flatBandModeCreation K σ w * fermionTotalSpinZ (2 * K + 1) =
      flatBandSpinCharge σ • flatBandModeCreation K σ w := by
  simp only [flatBandModeCreation, LinearMap.coe_mk, AddHom.coe_mk, Finset.smul_sum]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [mul_smul_comm, smul_mul_assoc, fermionTotalSpinZ_commutator_spinfulCreation, smul_add,
    add_sub_cancel_left, smul_comm]

/-- **The `Ŝ^z` weight of a rotated list-monomial.**  `Ŝ^z (∏ Ĉ†_{σ_q}) |vac⟩ =
(Σ_q (1/2 − σ_q)) • (∏ Ĉ†) |vac⟩`: the vacuum has weight `0` and each creation shifts `Ŝ^z` by its
spin charge. -/
theorem fermionTotalSpinZ_mulVec_flatBandModeMonomial (K : ℕ) (ν : ℝ)
    (l : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2)) :
    (fermionTotalSpinZ (2 * K + 1)).mulVec (flatBandModeMonomial K ν l)
      = ((l.map (fun q => flatBandSpinCharge q.2)).sum) • flatBandModeMonomial K ν l := by
  induction l with
  | nil =>
    simp only [flatBandModeMonomial, List.map_nil, List.prod_nil, List.sum_nil, zero_smul]
    rw [Matrix.one_mulVec, fermionTotalSpinZ_mulVec_vacuum]
  | cons q l' ih =>
    have hcons : flatBandModeMonomial K ν (q :: l')
        = (flatBandModeCreation K q.2 (flatBandBasis K ν q.1)).mulVec
            (flatBandModeMonomial K ν l') := by
      simp only [flatBandModeMonomial, List.map_cons, List.prod_cons]
      rw [← Matrix.mulVec_mulVec]
    have hcomm : fermionTotalSpinZ (2 * K + 1) *
          flatBandModeCreation K q.2 (flatBandBasis K ν q.1)
        = flatBandModeCreation K q.2 (flatBandBasis K ν q.1) *
            fermionTotalSpinZ (2 * K + 1)
          + flatBandSpinCharge q.2 • flatBandModeCreation K q.2 (flatBandBasis K ν q.1) := by
      rw [eq_add_of_sub_eq
        (flatBandModeCreation_commutator_fermionTotalSpinZ K q.2 (flatBandBasis K ν q.1))]
      abel
    rw [hcons, Matrix.mulVec_mulVec, hcomm, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ih,
      Matrix.mulVec_smul, Matrix.smul_mulVec, List.map_cons, List.sum_cons, add_smul]
    abel

/-- **The `Ŝ^z` weight of an occupation monomial.**  `occMonomial f` is an `Ŝ^z` eigenvector with
eigenvalue `(#up-modes − #down-modes)/2 = Σ_{q ∈ occFinset f} (1/2 − σ_q)`. -/
theorem fermionTotalSpinZ_mulVec_occMonomial (K : ℕ) (ν : ℝ)
    (f : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2) :
    (fermionTotalSpinZ (2 * K + 1)).mulVec (occMonomial K ν f)
      = (∑ q ∈ occFinset f, flatBandSpinCharge q.2) • occMonomial K ν f := by
  rw [occMonomial, fermionTotalSpinZ_mulVec_flatBandModeMonomial]
  congr 1
  rw [← List.sum_toFinset (fun q => flatBandSpinCharge q.2) (occFinset f).nodup_toList,
    Finset.toList_toFinset]

end LatticeSystem.Fermion
