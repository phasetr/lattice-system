import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinSymmetryAux

/-!
# Hubbard spin symmetry: SU(2) invariance (Tasaki §9.3.3)

This file proves the SU(2) part of the Hubbard spin symmetry: the raising and
lowering operators `Ŝ^±_tot` and their commutation with the Hubbard Hamiltonian
(`[Ŝ^±_tot, H] = 0`, Tasaki §9.3.3, eq. (9.3.36)).  The U(1)×U(1) auxiliary
machinery (Hermiticity/adjoints of the number operators, injectivity of the
spin-site maps, the per-spin number commutators and `S^z_tot` invariance) lives
in `SpinSymmetryAux.lean`, which this file imports; downstream modules importing
`SpinSymmetry` therefore see the full §9.3.3 API unchanged.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph

/-! ## SU(2) raising/lowering operators: definitions and adjoint -/

/-- The SU(2) raising operator
$\hat{S}^+_{\rm tot} = \sum_i c^\dagger_{i,\uparrow}c_{i,\downarrow}$.
(Tasaki §9.3.3, p. 332.) -/
noncomputable def fermionTotalSpinPlus (N : ℕ) : ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ i : Fin (N + 1), fermionUpCreation N i * fermionDownAnnihilation N i

/-- The SU(2) lowering operator
$\hat{S}^-_{\rm tot} = \sum_i c^\dagger_{i,\downarrow}c_{i,\uparrow}$.
(Tasaki §9.3.3, p. 332.) -/
noncomputable def fermionTotalSpinMinus (N : ℕ) : ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ i : Fin (N + 1), fermionDownCreation N i * fermionUpAnnihilation N i

/-- $(\hat{S}^+_{\rm tot})^\dagger = \hat{S}^-_{\rm tot}$. -/
theorem fermionTotalSpinPlus_conjTranspose (N : ℕ) :
    (fermionTotalSpinPlus N)ᴴ = fermionTotalSpinMinus N := by
  unfold fermionTotalSpinPlus fermionTotalSpinMinus
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.conjTranspose_mul, fermionUpCreation_conjTranspose,
    fermionDownAnnihilation_conjTranspose]

/-! ## Anticommutator wrappers -/

/-- $\{c_{j,\uparrow}, c^\dagger_{k,\uparrow}\} = 0$ for $j \neq k$. -/
theorem fermionUpAnnihilation_upCreation_anticomm_ne
    (N : ℕ) {j k : Fin (N + 1)} (hne : j ≠ k) :
    fermionUpAnnihilation N j * fermionUpCreation N k +
    fermionUpCreation N k * fermionUpAnnihilation N j = 0 := by
  unfold fermionUpAnnihilation fermionUpCreation
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hjk | hjk
  · exact fermionMultiAnnihilation_creation_anticomm_lt (2 * N + 1) _ _
      (by simp only [spinfulIndex, Fin.val_zero]; omega)
  · exact (add_comm _ _).trans
      (fermionMultiCreation_annihilation_anticomm_lt (2 * N + 1) _ _
        (by simp only [spinfulIndex, Fin.val_zero]; omega))

/-- $\{c_{j,\uparrow}, c_{k,\downarrow}\} = 0$ for all $j, k$. -/
theorem fermionUpAnnihilation_downAnnihilation_anticomm
    (N : ℕ) (j k : Fin (N + 1)) :
    fermionUpAnnihilation N j * fermionDownAnnihilation N k +
    fermionDownAnnihilation N k * fermionUpAnnihilation N j = 0 := by
  unfold fermionUpAnnihilation fermionDownAnnihilation
  by_cases hjk : j.val ≤ k.val
  · exact fermionMultiAnnihilation_anticomm_lt (2 * N + 1) _ _
      (by simp only [spinfulIndex, Fin.val_zero, Fin.val_one]; omega)
  · simp only [not_le] at hjk
    exact (add_comm _ _).trans
      (fermionMultiAnnihilation_anticomm_lt (2 * N + 1) _ _
        (by simp only [spinfulIndex, Fin.val_zero, Fin.val_one]; omega))

/-- $\{c^\dagger_{i,\uparrow}, c^\dagger_{k,\uparrow}\} = 0$ for all $i, k$. -/
theorem fermionUpCreation_upCreation_anticomm
    (N : ℕ) (i k : Fin (N + 1)) :
    fermionUpCreation N i * fermionUpCreation N k +
    fermionUpCreation N k * fermionUpCreation N i = 0 := by
  unfold fermionUpCreation
  rcases lt_trichotomy i.val k.val with hlt | heq | hgt
  · exact fermionMultiCreation_anticomm_lt (2 * N + 1) _ _
      (by simp only [spinfulIndex, Fin.val_zero]; omega)
  · have : i = k := Fin.ext heq
    subst this; rw [← two_mul]; simp [fermionMultiCreation_sq]
  · exact (add_comm _ _).trans
      (fermionMultiCreation_anticomm_lt (2 * N + 1) _ _
        (by simp only [spinfulIndex, Fin.val_zero]; omega))

/-- $\{c^\dagger_{i,\uparrow}, c_{k,\downarrow}\} = 0$ for all $i, k$. -/
theorem fermionUpCreation_downAnnihilation_anticomm
    (N : ℕ) (i k : Fin (N + 1)) :
    fermionUpCreation N i * fermionDownAnnihilation N k +
    fermionDownAnnihilation N k * fermionUpCreation N i = 0 := by
  unfold fermionUpCreation fermionDownAnnihilation
  by_cases hik : i.val ≤ k.val
  · exact fermionMultiCreation_annihilation_anticomm_lt (2 * N + 1) _ _
      (by simp only [spinfulIndex, Fin.val_zero, Fin.val_one]; omega)
  · simp only [not_le] at hik
    exact (add_comm _ _).trans
      (fermionMultiAnnihilation_creation_anticomm_lt (2 * N + 1) _ _
        (by simp only [spinfulIndex, Fin.val_zero, Fin.val_one]; omega))

/-- $\{c^\dagger_{j,\downarrow}, c^\dagger_{k,\uparrow}\} = 0$ for all $j, k$. -/
theorem fermionDownCreation_upCreation_anticomm
    (N : ℕ) (j k : Fin (N + 1)) :
    fermionDownCreation N j * fermionUpCreation N k +
    fermionUpCreation N k * fermionDownCreation N j = 0 := by
  unfold fermionDownCreation fermionUpCreation
  rcases lt_trichotomy j.val k.val with hlt | heq | hgt
  · exact fermionMultiCreation_anticomm_lt (2 * N + 1) _ _
      (by simp only [spinfulIndex, Fin.val_zero, Fin.val_one]; omega)
  · have : j = k := Fin.ext heq
    subst this
    exact (add_comm _ _).trans
      (fermionMultiCreation_anticomm_lt (2 * N + 1) _ _
        (by simp only [spinfulIndex, Fin.val_zero, Fin.val_one]; omega))
  · exact (add_comm _ _).trans
      (fermionMultiCreation_anticomm_lt (2 * N + 1) _ _
        (by simp only [spinfulIndex, Fin.val_zero, Fin.val_one]; omega))

/-- $\{c^\dagger_{j,\downarrow}, c_{k,\downarrow}\} = 0$ for $j \neq k$. -/
theorem fermionDownCreation_downAnnihilation_anticomm_ne
    (N : ℕ) {j k : Fin (N + 1)} (hne : j ≠ k) :
    fermionDownCreation N j * fermionDownAnnihilation N k +
    fermionDownAnnihilation N k * fermionDownCreation N j = 0 := by
  unfold fermionDownCreation fermionDownAnnihilation
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hjk | hjk
  · exact fermionMultiCreation_annihilation_anticomm_lt (2 * N + 1) _ _
      (by simp only [spinfulIndex, Fin.val_one]; omega)
  · exact (add_comm _ _).trans
      (fermionMultiAnnihilation_creation_anticomm_lt (2 * N + 1) _ _
        (by simp only [spinfulIndex, Fin.val_one]; omega))

/-! ## Fermionic Leibniz rule -/

/-- In any ring, $[A, BC] = \{A, B\}C - B\{A, C\}$. -/
private theorem fermionic_leibniz {α : Type*} [Ring α] (A B C : α) :
    A * (B * C) - B * C * A = (A * B + B * A) * C - B * (A * C + C * A) := by
  noncomm_ring

/-! ## Key commutators: Tasaki §9.3.3, eq. (9.3.36) -/

/-- Per-$k$ commutator $[c_{j,↑}, c^\dagger_{k,↑} c_{k,↓}]$. -/
private theorem fermionUpAnn_commutator_spinPlusTerm
    (N : ℕ) (j k : Fin (N + 1)) :
    fermionUpAnnihilation N j *
        (fermionUpCreation N k * fermionDownAnnihilation N k) -
      fermionUpCreation N k * fermionDownAnnihilation N k *
        fermionUpAnnihilation N j =
      if j = k then fermionDownAnnihilation N j else 0 := by
  rw [fermionic_leibniz]
  by_cases hjk : j = k
  · subst hjk; simp only [ite_true]
    have h_same := fermionMultiAnticomm_self (2 * N + 1) (spinfulIndex N j 0)
    have h_cross := fermionUpAnnihilation_downAnnihilation_anticomm N j j
    unfold fermionUpAnnihilation fermionUpCreation fermionDownAnnihilation at *
    rw [h_same, Matrix.one_mul, h_cross, Matrix.mul_zero, sub_zero]
  · simp only [ite_false, hjk]
    have h1 := fermionUpAnnihilation_upCreation_anticomm_ne N hjk
    have h2 := fermionUpAnnihilation_downAnnihilation_anticomm N j k
    unfold fermionUpAnnihilation fermionUpCreation fermionDownAnnihilation at *
    rw [h1, Matrix.zero_mul, h2, Matrix.mul_zero, sub_zero]

/-- $[c_{j,\uparrow}, \hat{S}^+_{\rm tot}] = c_{j,\downarrow}$
(Tasaki §9.3.3, eq. (9.3.36)). -/
theorem fermionUpAnnihilation_commutator_fermionTotalSpinPlus
    (N : ℕ) (j : Fin (N + 1)) :
    fermionUpAnnihilation N j * fermionTotalSpinPlus N -
        fermionTotalSpinPlus N * fermionUpAnnihilation N j =
      fermionDownAnnihilation N j := by
  unfold fermionTotalSpinPlus
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp_rw [fermionUpAnn_commutator_spinPlusTerm N j]
  rw [Finset.sum_ite_eq Finset.univ j (fun _ => fermionDownAnnihilation N j)]
  simp

/-- Per-$k$ commutator $[c^\dagger_{j,↓}, c^\dagger_{k,↑} c_{k,↓}]$. -/
private theorem fermionDownCr_commutator_spinPlusTerm
    (N : ℕ) (j k : Fin (N + 1)) :
    fermionDownCreation N j *
        (fermionUpCreation N k * fermionDownAnnihilation N k) -
      fermionUpCreation N k * fermionDownAnnihilation N k *
        fermionDownCreation N j =
      if j = k then -fermionUpCreation N j else 0 := by
  rw [fermionic_leibniz]
  by_cases hjk : j = k
  · subst hjk; simp only [ite_true]
    have h_cr_cross := fermionDownCreation_upCreation_anticomm N j j
    have h_same_down_raw := fermionMultiAnticomm_self (2 * N + 1) (spinfulIndex N j 1)
    unfold fermionDownCreation fermionUpCreation fermionDownAnnihilation at *
    have h_same_down : fermionMultiCreation (2 * N + 1) (spinfulIndex N j 1) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j 1) +
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j 1) *
        fermionMultiCreation (2 * N + 1) (spinfulIndex N j 1) = 1 :=
      (add_comm _ _).trans h_same_down_raw
    rw [h_cr_cross, Matrix.zero_mul, h_same_down, Matrix.mul_one, zero_sub]
  · simp only [ite_false, hjk]
    have h1 := fermionDownCreation_upCreation_anticomm N j k
    have h2 := fermionDownCreation_downAnnihilation_anticomm_ne N hjk
    unfold fermionDownCreation fermionUpCreation fermionDownAnnihilation at *
    rw [h1, Matrix.zero_mul, h2, Matrix.mul_zero, sub_zero]

/-- $[c^\dagger_{j,\downarrow}, \hat{S}^+_{\rm tot}] = -c^\dagger_{j,\uparrow}$
(Tasaki §9.3.3, eq. (9.3.36)). -/
theorem fermionDownCreation_commutator_fermionTotalSpinPlus
    (N : ℕ) (j : Fin (N + 1)) :
    fermionDownCreation N j * fermionTotalSpinPlus N -
        fermionTotalSpinPlus N * fermionDownCreation N j =
      -fermionUpCreation N j := by
  unfold fermionTotalSpinPlus
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp_rw [fermionDownCr_commutator_spinPlusTerm N j]
  rw [Finset.sum_ite_eq Finset.univ j (fun _ => -fermionUpCreation N j)]
  simp

/-- $[c^\dagger_{i,\uparrow}, \hat{S}^+_{\rm tot}] = 0$: Commute. -/
theorem fermionUpCreation_commute_fermionTotalSpinPlus
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionUpCreation N i) (fermionTotalSpinPlus N) := by
  change fermionUpCreation N i * fermionTotalSpinPlus N =
    fermionTotalSpinPlus N * fermionUpCreation N i
  unfold fermionTotalSpinPlus
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← sub_eq_zero, fermionic_leibniz,
    fermionUpCreation_upCreation_anticomm N i k,
    fermionUpCreation_downAnnihilation_anticomm N i k]
  simp

/-- $[c_{j,\downarrow}, \hat{S}^+_{\rm tot}] = 0$: Commute. -/
theorem fermionDownAnnihilation_commute_fermionTotalSpinPlus
    (N : ℕ) (j : Fin (N + 1)) :
    Commute (fermionDownAnnihilation N j) (fermionTotalSpinPlus N) := by
  change fermionDownAnnihilation N j * fermionTotalSpinPlus N =
    fermionTotalSpinPlus N * fermionDownAnnihilation N j
  unfold fermionTotalSpinPlus
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← sub_eq_zero, fermionic_leibniz]
  have h1 : fermionDownAnnihilation N j * fermionUpCreation N k +
      fermionUpCreation N k * fermionDownAnnihilation N j = 0 :=
    (add_comm _ _).trans (fermionUpCreation_downAnnihilation_anticomm N k j)
  have h2 : fermionDownAnnihilation N j * fermionDownAnnihilation N k +
      fermionDownAnnihilation N k * fermionDownAnnihilation N j = 0 := by
    unfold fermionDownAnnihilation
    rcases lt_trichotomy j.val k.val with hlt | heq | hgt
    · exact fermionMultiAnnihilation_anticomm_lt (2 * N + 1) _ _
        (by simp only [spinfulIndex, Fin.val_one]; omega)
    · have : j = k := Fin.ext heq
      subst this; rw [← two_mul]; simp [fermionMultiAnnihilation_sq]
    · exact (add_comm _ _).trans
        (fermionMultiAnnihilation_anticomm_lt (2 * N + 1) _ _
          (by simp only [spinfulIndex, Fin.val_one]; omega))
  unfold fermionUpCreation fermionDownAnnihilation at *
  rw [h1, Matrix.zero_mul, h2, Matrix.mul_zero, sub_zero]

/-! ## Full SU(2) commutation -/

/-- For each bond $(i,j)$, $[\hat{S}^+, c^\dagger_{i,\uparrow} c_{j,\uparrow} +
c^\dagger_{i,\downarrow} c_{j,\downarrow}] = 0$.
The contributions $\mp c^\dagger_{i,\uparrow} c_{j,\downarrow}$ cancel. -/
private theorem fermionTotalSpinPlus_commute_kinetic_bond
    (N : ℕ) (i j : Fin (N + 1)) :
    Commute (fermionTotalSpinPlus N)
      (fermionUpCreation N i * fermionUpAnnihilation N j +
       fermionDownCreation N i * fermionDownAnnihilation N j) := by
  have h1 : fermionTotalSpinPlus N * fermionUpCreation N i =
      fermionUpCreation N i * fermionTotalSpinPlus N :=
    (fermionUpCreation_commute_fermionTotalSpinPlus N i).symm.eq
  have h2 : fermionTotalSpinPlus N * fermionUpAnnihilation N j =
      fermionUpAnnihilation N j * fermionTotalSpinPlus N -
      fermionDownAnnihilation N j := by
    have h := fermionUpAnnihilation_commutator_fermionTotalSpinPlus N j
    have h' := sub_eq_iff_eq_add.mp h; rw [h']; abel
  have h3 : fermionTotalSpinPlus N * fermionDownCreation N i =
      fermionDownCreation N i * fermionTotalSpinPlus N +
      fermionUpCreation N i := by
    have h := fermionDownCreation_commutator_fermionTotalSpinPlus N i
    have h' := sub_eq_iff_eq_add.mp h; rw [h']; abel
  have h4 : fermionTotalSpinPlus N * fermionDownAnnihilation N j =
      fermionDownAnnihilation N j * fermionTotalSpinPlus N :=
    (fermionDownAnnihilation_commute_fermionTotalSpinPlus N j).symm.eq
  change fermionTotalSpinPlus N *
      (fermionUpCreation N i * fermionUpAnnihilation N j +
       fermionDownCreation N i * fermionDownAnnihilation N j) =
    (fermionUpCreation N i * fermionUpAnnihilation N j +
     fermionDownCreation N i * fermionDownAnnihilation N j) *
    fermionTotalSpinPlus N
  rw [Matrix.mul_add, Matrix.add_mul,
    ← Matrix.mul_assoc (fermionTotalSpinPlus N) (fermionUpCreation N i),
    h1, Matrix.mul_assoc, h2, Matrix.mul_sub,
    ← Matrix.mul_assoc (fermionTotalSpinPlus N) (fermionDownCreation N i),
    h3, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, h4]
  rw [show fermionDownCreation N i * (fermionDownAnnihilation N j * fermionTotalSpinPlus N) +
        fermionUpCreation N i * fermionDownAnnihilation N j =
      fermionDownCreation N i * fermionDownAnnihilation N j * fermionTotalSpinPlus N +
        fermionUpCreation N i * fermionDownAnnihilation N j from by
      rw [Matrix.mul_assoc]]
  abel

/-- $[\hat{S}^+_{\rm tot}, \hat{H}_{\rm kin}] = 0$.
(Tasaki §9.3.3, p. 333.) -/
theorem fermionTotalSpinPlus_commute_hubbardKinetic
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) :
    Commute (fermionTotalSpinPlus N) (hubbardKinetic N t) := by
  have h_rearrange : hubbardKinetic N t =
      ∑ i : Fin (N + 1), ∑ j : Fin (N + 1), t i j •
        (fermionUpCreation N i * fermionUpAnnihilation N j +
         fermionDownCreation N i * fermionDownAnnihilation N j) := by
    unfold hubbardKinetic fermionUpCreation fermionUpAnnihilation
      fermionDownCreation fermionDownAnnihilation
    rw [Fin.sum_univ_two]
    simp only [smul_add, ← Finset.sum_add_distrib]
  rw [h_rearrange]
  exact Commute.sum_right _ _ _ (fun i _ =>
    Commute.sum_right _ _ _ (fun j _ =>
      Commute.smul_right (fermionTotalSpinPlus_commute_kinetic_bond N i j) _))

/-- $c^\dagger_{x,\uparrow} \cdot n_{x,\uparrow} = 0$ (Pauli exclusion). -/
private theorem fermionUpCreation_mul_fermionUpNumber_same (N : ℕ) (x : Fin (N + 1)) :
    fermionUpCreation N x * fermionUpNumber N x = 0 := by
  unfold fermionUpCreation fermionUpNumber
  rw [show fermionMultiNumber (2 * N + 1) (spinfulIndex N x 0) =
      fermionMultiCreation (2 * N + 1) (spinfulIndex N x 0) *
      fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N x 0) from rfl,
    ← Matrix.mul_assoc, fermionMultiCreation_sq, Matrix.zero_mul]

/-- $n_{x,\downarrow} \cdot c_{x,\downarrow} = 0$ (Pauli exclusion). -/
private theorem fermionDownNumber_mul_fermionDownAnnihilation_same (N : ℕ) (x : Fin (N + 1)) :
    fermionDownNumber N x * fermionDownAnnihilation N x = 0 := by
  unfold fermionDownNumber fermionDownAnnihilation
  rw [show fermionMultiNumber (2 * N + 1) (spinfulIndex N x 1) =
      fermionMultiCreation (2 * N + 1) (spinfulIndex N x 1) *
      fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N x 1) from rfl,
    Matrix.mul_assoc, fermionMultiAnnihilation_sq, Matrix.mul_zero]

/-- Per-pair: $c^\dagger_{k,\uparrow} c_{k,\downarrow}$ commutes with
$n_{x,\uparrow} n_{x,\downarrow}$.  Same-site ($k = x$): both products vanish by Pauli
exclusion.  Different sites ($k \neq x$): all four constituent operators commute pairwise. -/
theorem fermionSpinPlusTerm_commute_interactionTerm
    (N : ℕ) (k x : Fin (N + 1)) :
    Commute (fermionUpCreation N k * fermionDownAnnihilation N k)
            (fermionUpNumber N x * fermionDownNumber N x) := by
  by_cases hkx : k = x
  · -- k = x: both products vanish by Pauli exclusion.
    rw [hkx]
    have h1 := fermionUpCreation_mul_fermionUpNumber_same N x
    have h2 := fermionDownNumber_mul_fermionDownAnnihilation_same N x
    have h_an_nu : Commute (fermionDownAnnihilation N x) (fermionUpNumber N x) := by
      unfold fermionDownAnnihilation fermionUpNumber
      exact (fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne
        (spinfulIndex_up_ne_down N x x)).symm
    have h_cr_nd : Commute (fermionUpCreation N x) (fermionDownNumber N x) := by
      unfold fermionUpCreation fermionDownNumber
      exact (fermionMultiNumber_commute_fermionMultiCreation_of_ne
        (spinfulIndex_up_ne_down N x x).symm).symm
    change (fermionUpCreation N x * fermionDownAnnihilation N x) *
        (fermionUpNumber N x * fermionDownNumber N x) =
      (fermionUpNumber N x * fermionDownNumber N x) *
        (fermionUpCreation N x * fermionDownAnnihilation N x)
    have lhs_zero : (fermionUpCreation N x * fermionDownAnnihilation N x) *
        (fermionUpNumber N x * fermionDownNumber N x) = 0 :=
      calc (fermionUpCreation N x * fermionDownAnnihilation N x) *
              (fermionUpNumber N x * fermionDownNumber N x)
          = fermionUpCreation N x *
              (fermionDownAnnihilation N x * fermionUpNumber N x) *
              fermionDownNumber N x := by
                rw [Matrix.mul_assoc, ← Matrix.mul_assoc (fermionDownAnnihilation N x),
                    ← Matrix.mul_assoc (fermionUpCreation N x)]
        _ = fermionUpCreation N x *
              (fermionUpNumber N x * fermionDownAnnihilation N x) *
              fermionDownNumber N x := by rw [h_an_nu.eq]
        _ = (fermionUpCreation N x * fermionUpNumber N x) *
              (fermionDownAnnihilation N x * fermionDownNumber N x) := by
                rw [← Matrix.mul_assoc (fermionUpCreation N x), Matrix.mul_assoc]
        _ = 0 := by rw [h1, Matrix.zero_mul]
    have rhs_zero : (fermionUpNumber N x * fermionDownNumber N x) *
        (fermionUpCreation N x * fermionDownAnnihilation N x) = 0 :=
      calc (fermionUpNumber N x * fermionDownNumber N x) *
              (fermionUpCreation N x * fermionDownAnnihilation N x)
          = fermionUpNumber N x *
              (fermionDownNumber N x * fermionUpCreation N x) *
              fermionDownAnnihilation N x := by
                rw [Matrix.mul_assoc, ← Matrix.mul_assoc (fermionDownNumber N x),
                    ← Matrix.mul_assoc (fermionUpNumber N x)]
        _ = fermionUpNumber N x *
              (fermionUpCreation N x * fermionDownNumber N x) *
              fermionDownAnnihilation N x := by rw [h_cr_nd.eq]
        _ = (fermionUpNumber N x * fermionUpCreation N x) *
              (fermionDownNumber N x * fermionDownAnnihilation N x) := by
                rw [← Matrix.mul_assoc (fermionUpNumber N x), Matrix.mul_assoc]
        _ = 0 := by rw [h2, Matrix.mul_zero]
    rw [lhs_zero, rhs_zero]
  · -- c†_{k,↑} commutes with n_{x,↑}: same spin, different site (k ≠ x)
    have h_cr_nu : Commute (fermionUpCreation N k) (fermionUpNumber N x) := by
      unfold fermionUpCreation fermionUpNumber
      exact (fermionMultiNumber_commute_fermionMultiCreation_of_ne
        (fun g => hkx (spinfulIndex_up_injective N g.symm))).symm
    -- c†_{k,↑} commutes with n_{x,↓}: always different JW positions (odd vs even)
    have h_cr_nd : Commute (fermionUpCreation N k) (fermionDownNumber N x) := by
      unfold fermionUpCreation fermionDownNumber
      exact (fermionMultiNumber_commute_fermionMultiCreation_of_ne
        (spinfulIndex_up_ne_down N k x).symm).symm
    -- c_{k,↓} commutes with n_{x,↑}: always different JW positions (even vs odd)
    have h_an_nu : Commute (fermionDownAnnihilation N k) (fermionUpNumber N x) := by
      unfold fermionDownAnnihilation fermionUpNumber
      exact (fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne
        (spinfulIndex_up_ne_down N x k)).symm
    -- c_{k,↓} commutes with n_{x,↓}: same spin, different site (k ≠ x)
    have h_an_nd : Commute (fermionDownAnnihilation N k) (fermionDownNumber N x) := by
      unfold fermionDownAnnihilation fermionDownNumber
      exact (fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne
        (fun g => hkx (spinfulIndex_down_injective N g.symm))).symm
    exact (h_cr_nu.mul_right h_cr_nd).mul_left (h_an_nu.mul_right h_an_nd)

/-- $[\hat{S}^+_{\rm tot}, \hat{H}_{\rm int}] = 0$.
(Tasaki §9.3.3, p. 333.) -/
theorem fermionTotalSpinPlus_commute_hubbardOnSiteInteraction
    (N : ℕ) (U : ℂ) :
    Commute (fermionTotalSpinPlus N) (hubbardOnSiteInteraction N U) := by
  unfold hubbardOnSiteInteraction fermionTotalSpinPlus
  apply Commute.sum_right
  intro x _
  apply Commute.smul_right _ U
  exact (Commute.sum_right _ _ _ (fun k _ =>
    (fermionSpinPlusTerm_commute_interactionTerm N k x).symm)).symm

/-- $[\hat{S}^+_{\rm tot}, \hat{H}] = 0$ (Tasaki §9.3.3, eq. (9.3.35)). -/
theorem fermionTotalSpinPlus_commute_hubbardHamiltonian
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    Commute (fermionTotalSpinPlus N) (hubbardHamiltonian N t U) := by
  unfold hubbardHamiltonian
  exact (fermionTotalSpinPlus_commute_hubbardKinetic N t).add_right
    (fermionTotalSpinPlus_commute_hubbardOnSiteInteraction N U)

/-- $[\hat{S}^-_{\rm tot}, \hat{H}] = 0$: derived from $[\hat{S}^+_{\rm tot}, \hat{H}] = 0$ by
adjoints (Tasaki §9.3.3, eq. (9.3.35)). -/
theorem fermionTotalSpinMinus_commute_hubbardHamiltonian
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    {hJ : ∀ i j, star (t i j) = t j i} {hU : star U = U} :
    Commute (fermionTotalSpinMinus N) (hubbardHamiltonian N t U) := by
  have h_plus := (fermionTotalSpinPlus_commute_hubbardHamiltonian N t U).eq
  have h_H := hubbardHamiltonian_isHermitian N hJ hU
  have h_adj := congrArg Matrix.conjTranspose h_plus
  simp only [Matrix.conjTranspose_mul, fermionTotalSpinPlus_conjTranspose N,
    h_H.eq] at h_adj
  exact h_adj.symm

end LatticeSystem.Fermion
