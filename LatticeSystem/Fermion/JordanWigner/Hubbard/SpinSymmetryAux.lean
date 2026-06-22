import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinSymmetryAuxCore

/-!
# Hubbard spin symmetry: U(1)×U(1) invariance (Tasaki §9.3.3)

This file proves that the Hubbard Hamiltonian commutes with the
following spin operators (Tasaki §9.3.3, pp. 332–336):

| Operator | Lean name | Interpretation |
|---|---|---|
| `N_↑` | `fermionTotalUpNumber` | total spin-up count |
| `N_↓` | `fermionTotalDownNumber` | total spin-down count |
| `S^z_tot` | `fermionTotalSpinZ` | z-component of total spin |

The key building blocks are:
- `fermionTotalUpNumber_commutator_fermionUpCreation`:
  $[N_\uparrow, c^\dagger_{i,\uparrow}] = c^\dagger_{i,\uparrow}$
- `fermionTotalUpNumber_commute_upHopping`:
  $[N_\uparrow, c^\dagger_{i,\uparrow} c_{j,\uparrow}] = 0$
and their down-spin counterparts.  Cross-spin commutativity
was already proved in `Charges.lean`.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph

/-! ## Down-spin commutators and same-species hopping commutativity -/

/-- $[N_\downarrow, c^\dagger_{i,\downarrow}] = c^\dagger_{i,\downarrow}$. -/
theorem fermionTotalDownNumber_commutator_fermionDownCreation
    (N : ℕ) (i : Fin (N + 1)) :
    fermionTotalDownNumber N * fermionDownCreation N i -
        fermionDownCreation N i * fermionTotalDownNumber N =
      fermionDownCreation N i := by
  unfold fermionTotalDownNumber fermionDownCreation fermionDownNumber
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [show (∑ k : Fin (N + 1),
      (fermionMultiNumber (2 * N + 1) (spinfulIndex N k 1) *
          fermionMultiCreation (2 * N + 1) (spinfulIndex N i 1) -
        fermionMultiCreation (2 * N + 1) (spinfulIndex N i 1) *
          fermionMultiNumber (2 * N + 1) (spinfulIndex N k 1))) =
    (fermionMultiNumber (2 * N + 1) (spinfulIndex N i 1) *
        fermionMultiCreation (2 * N + 1) (spinfulIndex N i 1) -
      fermionMultiCreation (2 * N + 1) (spinfulIndex N i 1) *
        fermionMultiNumber (2 * N + 1) (spinfulIndex N i 1)) from by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      rw [show (∑ k ∈ (Finset.univ : Finset (Fin (N + 1))).erase i,
            (fermionMultiNumber (2 * N + 1) (spinfulIndex N k 1) *
                fermionMultiCreation (2 * N + 1) (spinfulIndex N i 1) -
              fermionMultiCreation (2 * N + 1) (spinfulIndex N i 1) *
                fermionMultiNumber (2 * N + 1) (spinfulIndex N k 1))) = 0 from by
          apply Finset.sum_eq_zero
          intro k hk
          rw [Finset.mem_erase] at hk
          have hne : spinfulIndex N k 1 ≠ spinfulIndex N i 1 :=
            fun h => hk.1 (spinfulIndex_down_injective N h)
          exact sub_eq_zero.mpr
            (fermionMultiNumber_commute_fermionMultiCreation_of_ne hne).eq]
      rw [zero_add]]
  exact fermionMultiNumber_commutator_fermionMultiCreation_self
    (2 * N + 1) (spinfulIndex N i 1)

/-- $[N_\downarrow, c_{i,\downarrow}] = -c_{i,\downarrow}$. -/
theorem fermionTotalDownNumber_commutator_fermionDownAnnihilation
    (N : ℕ) (i : Fin (N + 1)) :
    fermionTotalDownNumber N * fermionDownAnnihilation N i -
        fermionDownAnnihilation N i * fermionTotalDownNumber N =
      -fermionDownAnnihilation N i := by
  have h := fermionTotalDownNumber_commutator_fermionDownCreation N i
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    fermionDownCreation_conjTranspose,
    (fermionTotalDownNumber_isHermitian N).eq] at h2
  rw [show fermionTotalDownNumber N * fermionDownAnnihilation N i -
        fermionDownAnnihilation N i * fermionTotalDownNumber N =
      -(fermionDownAnnihilation N i * fermionTotalDownNumber N -
          fermionTotalDownNumber N * fermionDownAnnihilation N i) from by abel]
  rw [h2]

/-- Auxiliary: `N_↓ · c†_{i,↓} = c†_{i,↓} · N_↓ + c†_{i,↓}`. -/
private theorem fermionTotalDownNumber_mul_fermionDownCreation
    (N : ℕ) (i : Fin (N + 1)) :
    fermionTotalDownNumber N * fermionDownCreation N i =
      fermionDownCreation N i * fermionTotalDownNumber N +
        fermionDownCreation N i := by
  have h := fermionTotalDownNumber_commutator_fermionDownCreation N i
  rw [sub_eq_iff_eq_add] at h
  rw [h]; abel

/-- Auxiliary: `N_↓ · c_{i,↓} = c_{i,↓} · N_↓ - c_{i,↓}`. -/
private theorem fermionTotalDownNumber_mul_fermionDownAnnihilation
    (N : ℕ) (i : Fin (N + 1)) :
    fermionTotalDownNumber N * fermionDownAnnihilation N i =
      fermionDownAnnihilation N i * fermionTotalDownNumber N -
        fermionDownAnnihilation N i := by
  have h := fermionTotalDownNumber_commutator_fermionDownAnnihilation N i
  rw [sub_eq_iff_eq_add] at h
  rw [h]; abel

/-- $[N_\downarrow, c^\dagger_{i,\downarrow} c_{j,\downarrow}] = 0$. -/
theorem fermionTotalDownNumber_commute_downHopping
    (N : ℕ) (i j : Fin (N + 1)) :
    Commute (fermionTotalDownNumber N)
      (fermionDownCreation N i * fermionDownAnnihilation N j) := by
  have h_cr := fermionTotalDownNumber_mul_fermionDownCreation N i
  have h_an := fermionTotalDownNumber_mul_fermionDownAnnihilation N j
  change fermionTotalDownNumber N *
      (fermionDownCreation N i * fermionDownAnnihilation N j) =
    (fermionDownCreation N i * fermionDownAnnihilation N j) *
      fermionTotalDownNumber N
  calc fermionTotalDownNumber N *
        (fermionDownCreation N i * fermionDownAnnihilation N j)
      = (fermionTotalDownNumber N * fermionDownCreation N i) *
          fermionDownAnnihilation N j := by rw [Matrix.mul_assoc]
    _ = (fermionDownCreation N i * fermionTotalDownNumber N +
          fermionDownCreation N i) * fermionDownAnnihilation N j := by rw [h_cr]
    _ = fermionDownCreation N i * fermionTotalDownNumber N *
          fermionDownAnnihilation N j +
        fermionDownCreation N i * fermionDownAnnihilation N j := by
          rw [Matrix.add_mul]
    _ = fermionDownCreation N i *
          (fermionTotalDownNumber N * fermionDownAnnihilation N j) +
        fermionDownCreation N i * fermionDownAnnihilation N j := by
          rw [Matrix.mul_assoc]
    _ = fermionDownCreation N i *
          (fermionDownAnnihilation N j * fermionTotalDownNumber N -
            fermionDownAnnihilation N j) +
        fermionDownCreation N i * fermionDownAnnihilation N j := by rw [h_an]
    _ = fermionDownCreation N i *
          (fermionDownAnnihilation N j * fermionTotalDownNumber N) -
        fermionDownCreation N i * fermionDownAnnihilation N j +
        fermionDownCreation N i * fermionDownAnnihilation N j := by
          rw [Matrix.mul_sub]
    _ = fermionDownCreation N i *
          (fermionDownAnnihilation N j * fermionTotalDownNumber N) := by abel
    _ = (fermionDownCreation N i * fermionDownAnnihilation N j) *
          fermionTotalDownNumber N := by rw [← Matrix.mul_assoc]

/-- $[N_\downarrow, \hat{H}_{\rm kin}] = 0$. -/
theorem fermionTotalDownNumber_commute_hubbardKinetic
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) :
    Commute (fermionTotalDownNumber N) (hubbardKinetic N t) := by
  unfold hubbardKinetic
  refine Commute.sum_right _ _ _ (fun σ _ => ?_)
  refine Commute.sum_right _ _ _ (fun i _ => ?_)
  refine Commute.sum_right _ _ _ (fun j _ => ?_)
  refine Commute.smul_right ?_ _
  fin_cases σ
  · exact fermionTotalDownNumber_commute_upHopping N i j
  · exact fermionTotalDownNumber_commute_downHopping N i j

/-- $[N_\downarrow, \hat{H}] = 0$.
(Tasaki §9.3.3, eq. (9.3.35), p. 333.) -/
theorem fermionTotalDownNumber_commute_hubbardHamiltonian
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    Commute (fermionTotalDownNumber N) (hubbardHamiltonian N t U) := by
  unfold hubbardHamiltonian
  exact (fermionTotalDownNumber_commute_hubbardKinetic N t).add_right
    (fermionTotalDownNumber_commute_hubbardOnSiteInteraction N U)

/-! ## U(1)×U(1) corollary: S^z_tot commutes with H -/

/-- $[S^z_{\rm tot}, \hat{H}] = 0$: free corollary from
$[N_\uparrow, H] = [N_\downarrow, H] = 0$ and $S^z = (N_\uparrow - N_\downarrow)/2$.
(Tasaki §9.3.3, p. 333.) -/
theorem fermionTotalSpinZ_commute_hubbardHamiltonian
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    Commute (fermionTotalSpinZ N) (hubbardHamiltonian N t U) := by
  unfold fermionTotalSpinZ
  exact ((fermionTotalUpNumber_commute_hubbardHamiltonian N t U).sub_left
    (fermionTotalDownNumber_commute_hubbardHamiltonian N t U)).smul_left _

end LatticeSystem.Fermion
