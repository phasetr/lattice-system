/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Fermion.JordanWigner.Hubbard.Charges

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

/-! ## Auxiliary: Hermiticity of N_↑ and N_↓ -/

/-- `N_↑ = Σ_i n_{i,↑}` is Hermitian. -/
theorem fermionTotalUpNumber_isHermitian (N : ℕ) :
    (fermionTotalUpNumber N).IsHermitian := by
  change (fermionTotalUpNumber N)ᴴ = fermionTotalUpNumber N
  unfold fermionTotalUpNumber fermionUpNumber
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (fermionMultiNumber_isHermitian (2 * N + 1) (spinfulIndex N i 0)).eq

/-- `N_↓ = Σ_i n_{i,↓}` is Hermitian. -/
theorem fermionTotalDownNumber_isHermitian (N : ℕ) :
    (fermionTotalDownNumber N).IsHermitian := by
  change (fermionTotalDownNumber N)ᴴ = fermionTotalDownNumber N
  unfold fermionTotalDownNumber fermionDownNumber
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (fermionMultiNumber_isHermitian (2 * N + 1) (spinfulIndex N i 1)).eq

/-! ## Auxiliary: adjoint relations for spinful operators -/

/-- `(c_{i,↑})ᴴ = c†_{i,↑}`. -/
theorem fermionUpAnnihilation_conjTranspose (N : ℕ) (i : Fin (N + 1)) :
    (fermionUpAnnihilation N i)ᴴ = fermionUpCreation N i :=
  fermionMultiAnnihilation_conjTranspose (2 * N + 1) (spinfulIndex N i 0)

/-- `(c_{i,↓})ᴴ = c†_{i,↓}`. -/
theorem fermionDownAnnihilation_conjTranspose (N : ℕ) (i : Fin (N + 1)) :
    (fermionDownAnnihilation N i)ᴴ = fermionDownCreation N i :=
  fermionMultiAnnihilation_conjTranspose (2 * N + 1) (spinfulIndex N i 1)

/-- `(c†_{i,↑})ᴴ = c_{i,↑}`. -/
theorem fermionUpCreation_conjTranspose (N : ℕ) (i : Fin (N + 1)) :
    (fermionUpCreation N i)ᴴ = fermionUpAnnihilation N i :=
  fermionMultiCreation_conjTranspose (2 * N + 1) (spinfulIndex N i 0)

/-- `(c†_{i,↓})ᴴ = c_{i,↓}`. -/
theorem fermionDownCreation_conjTranspose (N : ℕ) (i : Fin (N + 1)) :
    (fermionDownCreation N i)ᴴ = fermionDownAnnihilation N i :=
  fermionMultiCreation_conjTranspose (2 * N + 1) (spinfulIndex N i 1)

/-! ## Auxiliary: injectivity of up/down site maps -/

/-- `k ↦ spinfulIndex N k 0` is injective (up-spin positions `2k` are distinct). -/
theorem spinfulIndex_up_injective (N : ℕ) :
    Function.Injective (fun k : Fin (N + 1) => spinfulIndex N k 0) := by
  intro i j h
  unfold spinfulIndex at h
  ext
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) (congrArg Fin.val h)

/-- `k ↦ spinfulIndex N k 1` is injective (down-spin positions `2k+1` are distinct). -/
theorem spinfulIndex_down_injective (N : ℕ) :
    Function.Injective (fun k : Fin (N + 1) => spinfulIndex N k 1) := by
  intro i j h
  ext
  have h' : (spinfulIndex N i 1).val = (spinfulIndex N j 1).val := congrArg Fin.val h
  simp only [spinfulIndex] at h'
  omega

/-! ## Up-spin commutators and same-species hopping commutativity -/

/-- $[N_\uparrow, c^\dagger_{i,\uparrow}] = c^\dagger_{i,\uparrow}$:
analogue of `fermionTotalNumber_commutator_fermionMultiCreation`
for the up-spin sub-chain.  For $k = i$, the same-site commutator
$[n_{k,\uparrow}, c^\dagger_{i,\uparrow}] = c^\dagger_{i,\uparrow}$ applies;
for $k \neq i$ the number operator at JW position $2k \neq 2i$ commutes
with $c^\dagger_{i,\uparrow}$. -/
theorem fermionTotalUpNumber_commutator_fermionUpCreation
    (N : ℕ) (i : Fin (N + 1)) :
    fermionTotalUpNumber N * fermionUpCreation N i -
        fermionUpCreation N i * fermionTotalUpNumber N =
      fermionUpCreation N i := by
  unfold fermionTotalUpNumber fermionUpCreation fermionUpNumber
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [show (∑ k : Fin (N + 1),
      (fermionMultiNumber (2 * N + 1) (spinfulIndex N k 0) *
          fermionMultiCreation (2 * N + 1) (spinfulIndex N i 0) -
        fermionMultiCreation (2 * N + 1) (spinfulIndex N i 0) *
          fermionMultiNumber (2 * N + 1) (spinfulIndex N k 0))) =
    (fermionMultiNumber (2 * N + 1) (spinfulIndex N i 0) *
        fermionMultiCreation (2 * N + 1) (spinfulIndex N i 0) -
      fermionMultiCreation (2 * N + 1) (spinfulIndex N i 0) *
        fermionMultiNumber (2 * N + 1) (spinfulIndex N i 0)) from by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      rw [show (∑ k ∈ (Finset.univ : Finset (Fin (N + 1))).erase i,
            (fermionMultiNumber (2 * N + 1) (spinfulIndex N k 0) *
                fermionMultiCreation (2 * N + 1) (spinfulIndex N i 0) -
              fermionMultiCreation (2 * N + 1) (spinfulIndex N i 0) *
                fermionMultiNumber (2 * N + 1) (spinfulIndex N k 0))) = 0 from by
          apply Finset.sum_eq_zero
          intro k hk
          rw [Finset.mem_erase] at hk
          have hne : spinfulIndex N k 0 ≠ spinfulIndex N i 0 :=
            fun h => hk.1 (spinfulIndex_up_injective N h)
          exact sub_eq_zero.mpr
            (fermionMultiNumber_commute_fermionMultiCreation_of_ne hne).eq]
      rw [zero_add]]
  exact fermionMultiNumber_commutator_fermionMultiCreation_self
    (2 * N + 1) (spinfulIndex N i 0)

/-- $[N_\uparrow, c_{i,\uparrow}] = -c_{i,\uparrow}$:
dual via `conjTranspose`. -/
theorem fermionTotalUpNumber_commutator_fermionUpAnnihilation
    (N : ℕ) (i : Fin (N + 1)) :
    fermionTotalUpNumber N * fermionUpAnnihilation N i -
        fermionUpAnnihilation N i * fermionTotalUpNumber N =
      -fermionUpAnnihilation N i := by
  have h := fermionTotalUpNumber_commutator_fermionUpCreation N i
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    fermionUpCreation_conjTranspose,
    (fermionTotalUpNumber_isHermitian N).eq] at h2
  -- h2 : c_{i,↑} * N_↑ - N_↑ * c_{i,↑} = c_{i,↑}
  -- goal: N_↑ * c_{i,↑} - c_{i,↑} * N_↑ = -c_{i,↑}
  rw [show fermionTotalUpNumber N * fermionUpAnnihilation N i -
        fermionUpAnnihilation N i * fermionTotalUpNumber N =
      -(fermionUpAnnihilation N i * fermionTotalUpNumber N -
          fermionTotalUpNumber N * fermionUpAnnihilation N i) from by abel]
  rw [h2]

/-- Auxiliary: `N_↑ · c†_{i,↑} = c†_{i,↑} · N_↑ + c†_{i,↑}`. -/
private theorem fermionTotalUpNumber_mul_fermionUpCreation
    (N : ℕ) (i : Fin (N + 1)) :
    fermionTotalUpNumber N * fermionUpCreation N i =
      fermionUpCreation N i * fermionTotalUpNumber N +
        fermionUpCreation N i := by
  have h := fermionTotalUpNumber_commutator_fermionUpCreation N i
  rw [sub_eq_iff_eq_add] at h
  rw [h]; abel

/-- Auxiliary: `N_↑ · c_{i,↑} = c_{i,↑} · N_↑ - c_{i,↑}`. -/
private theorem fermionTotalUpNumber_mul_fermionUpAnnihilation
    (N : ℕ) (i : Fin (N + 1)) :
    fermionTotalUpNumber N * fermionUpAnnihilation N i =
      fermionUpAnnihilation N i * fermionTotalUpNumber N -
        fermionUpAnnihilation N i := by
  have h := fermionTotalUpNumber_commutator_fermionUpAnnihilation N i
  rw [sub_eq_iff_eq_add] at h
  rw [h]; abel

/-- $[N_\uparrow, c^\dagger_{i,\uparrow} c_{j,\uparrow}] = 0$:
the up-spin particle count commutes with any same-species hopping term.
The cancellation arises because $N_\uparrow$ acquires $+c^\dagger_{i,\uparrow}$
when sliding past the creation operator and $-c_{j,\uparrow}$ when sliding
past the annihilation operator.
(Tasaki §9.3.3, p. 333.) -/
theorem fermionTotalUpNumber_commute_upHopping
    (N : ℕ) (i j : Fin (N + 1)) :
    Commute (fermionTotalUpNumber N)
      (fermionUpCreation N i * fermionUpAnnihilation N j) := by
  have h_cr := fermionTotalUpNumber_mul_fermionUpCreation N i
  have h_an := fermionTotalUpNumber_mul_fermionUpAnnihilation N j
  change fermionTotalUpNumber N *
      (fermionUpCreation N i * fermionUpAnnihilation N j) =
    (fermionUpCreation N i * fermionUpAnnihilation N j) *
      fermionTotalUpNumber N
  calc fermionTotalUpNumber N *
        (fermionUpCreation N i * fermionUpAnnihilation N j)
      = (fermionTotalUpNumber N * fermionUpCreation N i) *
          fermionUpAnnihilation N j := by rw [Matrix.mul_assoc]
    _ = (fermionUpCreation N i * fermionTotalUpNumber N +
          fermionUpCreation N i) * fermionUpAnnihilation N j := by rw [h_cr]
    _ = fermionUpCreation N i * fermionTotalUpNumber N *
          fermionUpAnnihilation N j +
        fermionUpCreation N i * fermionUpAnnihilation N j := by
          rw [Matrix.add_mul]
    _ = fermionUpCreation N i *
          (fermionTotalUpNumber N * fermionUpAnnihilation N j) +
        fermionUpCreation N i * fermionUpAnnihilation N j := by
          rw [Matrix.mul_assoc]
    _ = fermionUpCreation N i *
          (fermionUpAnnihilation N j * fermionTotalUpNumber N -
            fermionUpAnnihilation N j) +
        fermionUpCreation N i * fermionUpAnnihilation N j := by rw [h_an]
    _ = fermionUpCreation N i *
          (fermionUpAnnihilation N j * fermionTotalUpNumber N) -
        fermionUpCreation N i * fermionUpAnnihilation N j +
        fermionUpCreation N i * fermionUpAnnihilation N j := by
          rw [Matrix.mul_sub]
    _ = fermionUpCreation N i *
          (fermionUpAnnihilation N j * fermionTotalUpNumber N) := by abel
    _ = (fermionUpCreation N i * fermionUpAnnihilation N j) *
          fermionTotalUpNumber N := by rw [← Matrix.mul_assoc]

/-- $[N_\uparrow, \hat{H}_{\rm kin}] = 0$.
For $\sigma = \uparrow$: `fermionTotalUpNumber_commute_upHopping`.
For $\sigma = \downarrow$: `fermionTotalUpNumber_commute_downHopping` (from `Charges.lean`).
(Tasaki §9.3.3, p. 333.) -/
theorem fermionTotalUpNumber_commute_hubbardKinetic
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) :
    Commute (fermionTotalUpNumber N) (hubbardKinetic N t) := by
  unfold hubbardKinetic
  refine Commute.sum_right _ _ _ (fun σ _ => ?_)
  refine Commute.sum_right _ _ _ (fun i _ => ?_)
  refine Commute.sum_right _ _ _ (fun j _ => ?_)
  refine Commute.smul_right ?_ _
  fin_cases σ
  · exact fermionTotalUpNumber_commute_upHopping N i j
  · exact fermionTotalUpNumber_commute_downHopping N i j

/-- $[N_\uparrow, \hat{H}] = 0$.
(Tasaki §9.3.3, eq. (9.3.35), p. 333.) -/
theorem fermionTotalUpNumber_commute_hubbardHamiltonian
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    Commute (fermionTotalUpNumber N) (hubbardHamiltonian N t U) := by
  unfold hubbardHamiltonian
  exact (fermionTotalUpNumber_commute_hubbardKinetic N t).add_right
    (fermionTotalUpNumber_commute_hubbardOnSiteInteraction N U)

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
