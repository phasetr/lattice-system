import LatticeSystem.Fermion.JordanWigner.CAR
import LatticeSystem.Quantum.GibbsState
import Mathlib.Tactic.NoncommRing

/-!
# Number-operator algebra + Hubbard-skeleton + fermion vacuum

Builds on the JW + CAR machinery:
- Number / annihilation-creation commutators,
- Hubbard-skeleton Gibbs state (single-species placeholder),
- Fermion vacuum state and its eigenstate properties.

(Refactor Phase 2 PR 13 — fourth step of the JordanWigner 5-file
split, plan v4 §3.1.)
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-! ## Number / annihilation-creation commutators -/

/-- Standard fermion algebra: `[n_i, c_i] = -c_i`. -/
theorem fermionMultiNumber_commutator_fermionMultiAnnihilation_self
    (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiNumber N i * fermionMultiAnnihilation N i -
        fermionMultiAnnihilation N i * fermionMultiNumber N i =
      -fermionMultiAnnihilation N i := by
  rw [fermionMultiNumber_eq_onSite]
  unfold fermionMultiAnnihilation
  -- n_i · c_i = onSite i (σ^- σ^+) · jwString N i · onSite i σ^+
  --         = jwString N i · onSite i (σ^- σ^+ · σ^+) = 0  (σ^+ σ^+ = 0)
  have hcomm_jw_minusPlus : Commute (jwString N i)
      (onSite i (spinHalfOpMinus * spinHalfOpPlus)) :=
    jwString_commute_onSite N i (spinHalfOpMinus * spinHalfOpPlus)
  have hncv : onSite i (spinHalfOpMinus * spinHalfOpPlus) *
      (jwString N i * onSite i spinHalfOpPlus) = 0 := by
    rw [← Matrix.mul_assoc, ← hcomm_jw_minusPlus.eq, Matrix.mul_assoc,
      onSite_mul_onSite_same]
    rw [show spinHalfOpMinus * spinHalfOpPlus * spinHalfOpPlus = 0 from by
      rw [Matrix.mul_assoc, spinHalfOpPlus_mul_self, Matrix.mul_zero]]
    rw [show onSite i (0 : Matrix (Fin 2) (Fin 2) ℂ) =
        (0 : ManyBodyOp (Fin (N + 1))) from by ext σ' σ; simp [onSite_apply]]
    rw [Matrix.mul_zero]
  -- c_i · n_i = jwString N i · onSite i (σ^+ · σ^- σ^+) = jwString N i · onSite i σ^+ = c_i.
  have hcvn : (jwString N i * onSite i spinHalfOpPlus) *
      onSite i (spinHalfOpMinus * spinHalfOpPlus) =
      jwString N i * onSite i spinHalfOpPlus := by
    rw [Matrix.mul_assoc, onSite_mul_onSite_same]
    rw [show spinHalfOpPlus * (spinHalfOpMinus * spinHalfOpPlus) = spinHalfOpPlus from
      by rw [← Matrix.mul_assoc, spinHalfOpPlus_mul_spinHalfOpMinus_mul_spinHalfOpPlus]]
  rw [hncv, hcvn, zero_sub]

/-- Dual: `[n_i, c_i†] = c_i†`. Direct consequence of
`fermionMultiNumber_commutator_fermionMultiAnnihilation_self` by
taking `conjTranspose`. -/
theorem fermionMultiNumber_commutator_fermionMultiCreation_self
    (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiNumber N i * fermionMultiCreation N i -
        fermionMultiCreation N i * fermionMultiNumber N i =
      fermionMultiCreation N i := by
  have h := fermionMultiNumber_commutator_fermionMultiAnnihilation_self N i
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_neg,
    fermionMultiAnnihilation_conjTranspose,
    (fermionMultiNumber_isHermitian N i).eq] at h2
  -- h2 : c_i† · n_i - n_i · c_i† = -c_i†
  -- Rewrite goal as negation of h2.
  rw [show fermionMultiNumber N i * fermionMultiCreation N i -
        fermionMultiCreation N i * fermionMultiNumber N i =
      -(fermionMultiCreation N i * fermionMultiNumber N i -
          fermionMultiNumber N i * fermionMultiCreation N i) from by abel]
  rw [h2]
  exact neg_neg _

/-- For `i ≠ j`, `n_i` commutes with `c_j` as operators. The `σ^z_i`
factor inside `jwString N j` commutes with `n_i` (since `[n, σ^z] = 0`
as matrices); disjoint-site factors commute trivially. -/
theorem fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne
    {N : ℕ} {i j : Fin (N + 1)} (hij : i ≠ j) :
    Commute (fermionMultiNumber N i) (fermionMultiAnnihilation N j) := by
  rw [fermionMultiNumber_eq_onSite]
  unfold fermionMultiAnnihilation
  have hcomm_onSite_i_j : Commute (onSite i (spinHalfOpMinus * spinHalfOpPlus))
      (onSite j spinHalfOpPlus) := by
    change onSite i (spinHalfOpMinus * spinHalfOpPlus) * onSite j spinHalfOpPlus =
      onSite j spinHalfOpPlus * onSite i (spinHalfOpMinus * spinHalfOpPlus)
    exact onSite_mul_onSite_of_ne hij (spinHalfOpMinus * spinHalfOpPlus)
      spinHalfOpPlus
  have hcomm_onSite_i_jwString :
      Commute (onSite i (spinHalfOpMinus * spinHalfOpPlus)) (jwString N j) := by
    unfold jwString
    apply Finset.noncommProd_commute
    intro k _
    by_cases hki : k = i
    · subst hki
      change onSite k (spinHalfOpMinus * spinHalfOpPlus) * onSite k pauliZ =
        onSite k pauliZ * onSite k (spinHalfOpMinus * spinHalfOpPlus)
      rw [onSite_mul_onSite_same, onSite_mul_onSite_same,
        spinHalfOpMinus_mul_spinHalfOpPlus_commute_pauliZ.eq]
    · exact onSite_mul_onSite_of_ne (Ne.symm hki)
        (spinHalfOpMinus * spinHalfOpPlus) pauliZ
  exact hcomm_onSite_i_jwString.mul_right hcomm_onSite_i_j

/-- `[N̂, c_j] = -c_j`: the total particle-number operator shifts
annihilation operators down by one. Sum of the diagonal contribution
`[n_j, c_j] = -c_j` with the vanishing off-diagonal terms `[n_i, c_j] = 0`
for `i ≠ j`. -/
theorem fermionTotalNumber_commutator_fermionMultiAnnihilation
    (N : ℕ) (j : Fin (N + 1)) :
    fermionTotalNumber N * fermionMultiAnnihilation N j -
        fermionMultiAnnihilation N j * fermionTotalNumber N =
      -fermionMultiAnnihilation N j := by
  unfold fermionTotalNumber
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [show (∑ i : Fin (N + 1),
        (fermionMultiNumber N i * fermionMultiAnnihilation N j -
          fermionMultiAnnihilation N j * fermionMultiNumber N i)) =
      (fermionMultiNumber N j * fermionMultiAnnihilation N j -
          fermionMultiAnnihilation N j * fermionMultiNumber N j) from by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    rw [show (∑ i ∈ (Finset.univ : Finset (Fin (N + 1))).erase j,
          (fermionMultiNumber N i * fermionMultiAnnihilation N j -
            fermionMultiAnnihilation N j * fermionMultiNumber N i)) = 0 from by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_erase] at hi
      have h : fermionMultiNumber N i * fermionMultiAnnihilation N j =
          fermionMultiAnnihilation N j * fermionMultiNumber N i :=
        (fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne hi.1)
      rw [h, sub_self]]
    rw [zero_add]]
  exact fermionMultiNumber_commutator_fermionMultiAnnihilation_self N j

/-- Dual: `Commute (n_i) (c_j†)` for `i ≠ j`. Direct consequence of
`fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne` by taking
matrix `conjTranspose`. -/
theorem fermionMultiNumber_commute_fermionMultiCreation_of_ne
    {N : ℕ} {i j : Fin (N + 1)} (hij : i ≠ j) :
    Commute (fermionMultiNumber N i) (fermionMultiCreation N j) := by
  have h := fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne hij
  -- Commute A B means A * B = B * A
  -- Take conjTranspose: B† * A† = A† * B†, i.e. Commute A† B†.
  have h_eq : fermionMultiNumber N i * fermionMultiAnnihilation N j =
      fermionMultiAnnihilation N j * fermionMultiNumber N i := h
  have h2 := congrArg Matrix.conjTranspose h_eq
  simp only [Matrix.conjTranspose_mul, fermionMultiAnnihilation_conjTranspose,
    (fermionMultiNumber_isHermitian N i).eq] at h2
  -- h2 : c_j† * n_i = n_i * c_j†, i.e. Commute (fermionMultiCreation N j) (fermionMultiNumber N i).
  -- Flip for target form.
  exact h2.symm

/-- `[N̂, c_j†] = c_j†`: dual of PR #130 via adjoint. -/
theorem fermionTotalNumber_commutator_fermionMultiCreation
    (N : ℕ) (j : Fin (N + 1)) :
    fermionTotalNumber N * fermionMultiCreation N j -
        fermionMultiCreation N j * fermionTotalNumber N =
      fermionMultiCreation N j := by
  have h := fermionTotalNumber_commutator_fermionMultiAnnihilation N j
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_neg,
    fermionMultiAnnihilation_conjTranspose,
    (fermionTotalNumber_isHermitian N).eq] at h2
  -- h2 : c_j† · N̂ - N̂ · c_j† = -c_j†
  rw [show fermionTotalNumber N * fermionMultiCreation N j -
        fermionMultiCreation N j * fermionTotalNumber N =
      -(fermionMultiCreation N j * fermionTotalNumber N -
          fermionTotalNumber N * fermionMultiCreation N j) from by abel]
  rw [h2]
  exact neg_neg _

/-- The hopping operator `c_i† · c_j` commutes with the total
particle-number operator `N̂`. Follows from `[N̂, c_i†] = c_i†`
and `[N̂, c_j] = -c_j`: the shifts cancel. -/
theorem fermionTotalNumber_commute_hopping (N : ℕ) (i j : Fin (N + 1)) :
    Commute (fermionTotalNumber N)
      (fermionMultiCreation N i * fermionMultiAnnihilation N j) := by
  -- From [N̂, c_i†] = c_i†: N̂ · c_i† = c_i† · N̂ + c_i†.
  have h_cr : fermionTotalNumber N * fermionMultiCreation N i =
      fermionMultiCreation N i * fermionTotalNumber N +
        fermionMultiCreation N i := by
    have h := fermionTotalNumber_commutator_fermionMultiCreation N i
    rw [sub_eq_iff_eq_add] at h
    rw [h]; abel
  -- From [N̂, c_j] = -c_j: N̂ · c_j = c_j · N̂ - c_j.
  have h_an : fermionTotalNumber N * fermionMultiAnnihilation N j =
      fermionMultiAnnihilation N j * fermionTotalNumber N -
        fermionMultiAnnihilation N j := by
    have h := fermionTotalNumber_commutator_fermionMultiAnnihilation N j
    rw [sub_eq_iff_eq_add] at h
    rw [h]; abel
  -- Combine: N̂ · c_i† · c_j = c_i† · N̂ · c_j + c_i† · c_j
  --                        = c_i† · (c_j · N̂ - c_j) + c_i† · c_j
  --                        = c_i† · c_j · N̂ - c_i† · c_j + c_i† · c_j
  --                        = c_i† · c_j · N̂.
  change fermionTotalNumber N *
      (fermionMultiCreation N i * fermionMultiAnnihilation N j) =
    (fermionMultiCreation N i * fermionMultiAnnihilation N j) *
      fermionTotalNumber N
  calc fermionTotalNumber N *
        (fermionMultiCreation N i * fermionMultiAnnihilation N j)
      = (fermionTotalNumber N * fermionMultiCreation N i) *
          fermionMultiAnnihilation N j := by rw [Matrix.mul_assoc]
    _ = (fermionMultiCreation N i * fermionTotalNumber N +
          fermionMultiCreation N i) * fermionMultiAnnihilation N j := by rw [h_cr]
    _ = fermionMultiCreation N i * fermionTotalNumber N *
          fermionMultiAnnihilation N j +
        fermionMultiCreation N i * fermionMultiAnnihilation N j := by
          rw [Matrix.add_mul]
    _ = fermionMultiCreation N i *
          (fermionTotalNumber N * fermionMultiAnnihilation N j) +
        fermionMultiCreation N i * fermionMultiAnnihilation N j := by
          rw [Matrix.mul_assoc]
    _ = fermionMultiCreation N i *
          (fermionMultiAnnihilation N j * fermionTotalNumber N -
            fermionMultiAnnihilation N j) +
        fermionMultiCreation N i * fermionMultiAnnihilation N j := by
          rw [h_an]
    _ = fermionMultiCreation N i *
          (fermionMultiAnnihilation N j * fermionTotalNumber N) -
        fermionMultiCreation N i * fermionMultiAnnihilation N j +
        fermionMultiCreation N i * fermionMultiAnnihilation N j := by
          rw [Matrix.mul_sub]
    _ = fermionMultiCreation N i *
          (fermionMultiAnnihilation N j * fermionTotalNumber N) := by abel
    _ = (fermionMultiCreation N i * fermionMultiAnnihilation N j) *
          fermionTotalNumber N := by rw [← Matrix.mul_assoc]

/-- The site-occupation number `n_i` commutes with the total
particle-number operator `N̂ = Σ_j n_j`: since `n_i` commutes with each
`n_j` (`fermionMultiNumber_commute`), it commutes with their sum. -/
theorem fermionMultiNumber_commute_fermionTotalNumber (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionMultiNumber N i) (fermionTotalNumber N) := by
  unfold fermionTotalNumber
  exact Commute.sum_right _ _ _ (fun j _ => fermionMultiNumber_commute N i j)

/-- The density-density operator `n_i · n_j` commutes with the total
particle-number operator `N̂ = Σ_k n_k`. Since both `n_i` and `n_j`
individually commute with `N̂`
(`fermionMultiNumber_commute_fermionTotalNumber`), so does their
product. This is the foundational identity that makes any
density–density interaction (e.g. the Hubbard `U Σ_i n_{i,↑} n_{i,↓}`,
once two species are introduced) particle-number conserving. -/
theorem fermionDensityDensity_commute_fermionTotalNumber
    (N : ℕ) (i j : Fin (N + 1)) :
    Commute (fermionMultiNumber N i * fermionMultiNumber N j)
      (fermionTotalNumber N) :=
  (fermionMultiNumber_commute_fermionTotalNumber N i).mul_left
    (fermionMultiNumber_commute_fermionTotalNumber N j)

/-- The general single-particle hopping operator on `Fin (N + 1)`
modes with arbitrary complex coefficients
`t : Fin (N+1) → Fin (N+1) → ℂ`:
`H_hop = Σ_{i,j} t_{i,j} · c_i† c_j`. This is the kinetic part of
any tight-binding or Hubbard-style Hamiltonian. -/
noncomputable def fermionHopping (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℂ) : ManyBodyOp (Fin (N + 1)) :=
  ∑ i, ∑ j, t i j •
    (fermionMultiCreation N i * fermionMultiAnnihilation N j)

/-- The general hopping operator commutes with the total particle-
number operator `N̂`: every term `c_i† c_j` commutes with `N̂`
(`fermionTotalNumber_commute_hopping`), the scalar action `t_{ij} •`
preserves the commute, and finite sums of pairwise commuting
operators commute with `N̂`. This is charge conservation for the
kinetic Hamiltonian. -/
theorem fermionHopping_commute_fermionTotalNumber
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) :
    Commute (fermionHopping N t) (fermionTotalNumber N) := by
  unfold fermionHopping
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  refine Commute.sum_left _ _ _ (fun j _ => ?_)
  exact ((fermionTotalNumber_commute_hopping N i j).symm).smul_left (t i j)

/-- The general density-density interaction on `Fin (N + 1)` modes
with arbitrary complex coefficients `V : Fin (N+1) → Fin (N+1) → ℂ`:
`V_int = Σ_{i,j} V_{i,j} · n_i n_j`. Captures any density–density
potential (extended Hubbard, long-range Coulomb on a chain, etc.). -/
noncomputable def fermionDensityInteraction (N : ℕ)
    (V : Fin (N + 1) → Fin (N + 1) → ℂ) : ManyBodyOp (Fin (N + 1)) :=
  ∑ i, ∑ j, V i j •
    (fermionMultiNumber N i * fermionMultiNumber N j)

/-- The general density-density interaction commutes with the total
particle-number operator `N̂`: every term `n_i n_j` commutes with `N̂`
(`fermionDensityDensity_commute_fermionTotalNumber`), the scalar
action `V_{ij} •` preserves the commute, and finite sums commute.
Together with `fermionHopping_commute_fermionTotalNumber` this gives
charge conservation for any Hubbard-type Hamiltonian
`H = H_hop + V_int`. -/
theorem fermionDensityInteraction_commute_fermionTotalNumber
    (N : ℕ) (V : Fin (N + 1) → Fin (N + 1) → ℂ) :
    Commute (fermionDensityInteraction N V) (fermionTotalNumber N) := by
  unfold fermionDensityInteraction
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  refine Commute.sum_left _ _ _ (fun j _ => ?_)
  exact (fermionDensityDensity_commute_fermionTotalNumber N i j).smul_left
    (V i j)

/-- The canonical charge-conserving fermion Hamiltonian on
`Fin (N + 1)` modes, the sum of a single-particle hopping term and a
density–density interaction:
`H = H_hop + V_int = Σ_{i,j} t_{i,j} c_i† c_j + Σ_{i,j} V_{i,j} n_i n_j`.
Captures the algebraic skeleton of single-species Hubbard / extended
Hubbard models on a chain. -/
noncomputable def fermionGenericHamiltonian (N : ℕ)
    (t V : Fin (N + 1) → Fin (N + 1) → ℂ) : ManyBodyOp (Fin (N + 1)) :=
  fermionHopping N t + fermionDensityInteraction N V

/-- The canonical Hamiltonian `H = H_hop + V_int` commutes with the
total particle-number operator `N̂`. Both summands separately commute
with `N̂` (`fermionHopping_commute_fermionTotalNumber` and
`fermionDensityInteraction_commute_fermionTotalNumber`), so by
`Commute.add_left` so does their sum. This is the unified statement
of charge conservation for any Hubbard-type Hamiltonian. -/
theorem fermionGenericHamiltonian_commute_fermionTotalNumber
    (N : ℕ) (t V : Fin (N + 1) → Fin (N + 1) → ℂ) :
    Commute (fermionGenericHamiltonian N t V) (fermionTotalNumber N) := by
  unfold fermionGenericHamiltonian
  exact (fermionHopping_commute_fermionTotalNumber N t).add_left
    (fermionDensityInteraction_commute_fermionTotalNumber N V)

/-- The product `n_i * n_j` is Hermitian: each `n_i` is Hermitian
(`fermionMultiNumber_isHermitian`) and `n_i, n_j` commute pairwise
(`fermionMultiNumber_commute`), so the product of two commuting
Hermitian operators is Hermitian. -/
theorem fermionMultiNumber_mul_isHermitian (N : ℕ) (i j : Fin (N + 1)) :
    (fermionMultiNumber N i * fermionMultiNumber N j).IsHermitian :=
  Matrix.IsHermitian.mul_of_commute (fermionMultiNumber_isHermitian N i)
    (fermionMultiNumber_isHermitian N j) (fermionMultiNumber_commute N i j)

/-- The density-density interaction
`V_int = Σ_{i,j} V_{i,j} n_i n_j` is Hermitian whenever every
coupling entry is real (`star V_{i,j} = V_{i,j}`). Each `n_i n_j` is
Hermitian (commuting Hermitian factors), and `(V_{i,j} • n_i n_j)†
= star V_{i,j} • n_i n_j = V_{i,j} • n_i n_j` under the realness
hypothesis; the sum of Hermitians is Hermitian. -/
theorem fermionDensityInteraction_isHermitian
    (N : ℕ) {V : Fin (N + 1) → Fin (N + 1) → ℂ}
    (hV : ∀ i j, star (V i j) = V i j) :
    (fermionDensityInteraction N V).IsHermitian := by
  unfold fermionDensityInteraction Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  congr 1; funext i
  rw [Matrix.conjTranspose_sum]
  congr 1; funext j
  rw [Matrix.conjTranspose_smul, (fermionMultiNumber_mul_isHermitian N i j).eq,
    hV]

/-- Auxiliary: the conjugate transpose of a single hopping term
`c_i† * c_j` equals `c_j† * c_i`. -/
theorem fermionHoppingTerm_conjTranspose (N : ℕ) (i j : Fin (N + 1)) :
    (fermionMultiCreation N i * fermionMultiAnnihilation N j)ᴴ =
      fermionMultiCreation N j * fermionMultiAnnihilation N i := by
  rw [Matrix.conjTranspose_mul, fermionMultiAnnihilation_conjTranspose,
    fermionMultiCreation_conjTranspose]

/-- The single-particle hopping operator
`H_hop = Σ_{i,j} t_{i,j} c_i† c_j` is Hermitian when the coupling
matrix `t` is Hermitian, i.e. `star (t i j) = t j i` for all
`i, j`. The conjugate transpose flips creation/annihilation and
reverses the index order; an `i ↔ j` reindexing brings the sum back
to its original form under the Hermiticity hypothesis. -/
theorem fermionHopping_isHermitian
    (N : ℕ) {t : Fin (N + 1) → Fin (N + 1) → ℂ}
    (ht : ∀ i j, star (t i j) = t j i) :
    (fermionHopping N t).IsHermitian := by
  change (fermionHopping N t)ᴴ = fermionHopping N t
  unfold fermionHopping
  calc (∑ i, ∑ j, t i j •
          (fermionMultiCreation N i * fermionMultiAnnihilation N j))ᴴ
      = ∑ i, (∑ j, t i j •
            (fermionMultiCreation N i * fermionMultiAnnihilation N j))ᴴ := by
        rw [Matrix.conjTranspose_sum]
    _ = ∑ i, ∑ j, (t i j •
            (fermionMultiCreation N i * fermionMultiAnnihilation N j))ᴴ := by
        congr 1; funext i
        rw [Matrix.conjTranspose_sum]
    _ = ∑ i, ∑ j, t j i •
            (fermionMultiCreation N j * fermionMultiAnnihilation N i) := by
        congr 1; funext i; congr 1; funext j
        rw [Matrix.conjTranspose_smul, fermionHoppingTerm_conjTranspose, ht]
    _ = ∑ j, ∑ i, t j i •
            (fermionMultiCreation N j * fermionMultiAnnihilation N i) :=
        Finset.sum_comm
    _ = ∑ i, ∑ j, t i j •
            (fermionMultiCreation N i * fermionMultiAnnihilation N j) := rfl

/-- The canonical fermion Hamiltonian `H = H_hop + V_int` is
Hermitian whenever the hopping matrix `t` is Hermitian
(`star (t i j) = t j i`) and the density-density coupling `V` is
entry-wise real (`star (V i j) = V i j`). Direct sum of
`fermionHopping_isHermitian` and `fermionDensityInteraction_isHermitian`
via `Matrix.IsHermitian.add`. -/
theorem fermionGenericHamiltonian_isHermitian
    (N : ℕ) {t V : Fin (N + 1) → Fin (N + 1) → ℂ}
    (ht : ∀ i j, star (t i j) = t j i)
    (hV : ∀ i j, star (V i j) = V i j) :
    (fermionGenericHamiltonian N t V).IsHermitian := by
  unfold fermionGenericHamiltonian
  exact (fermionHopping_isHermitian N ht).add
    (fermionDensityInteraction_isHermitian N hV)

/-! ## Hubbard-skeleton Gibbs state

Combining the canonical fermion Hamiltonian with the generic
`gibbsState` framework gives the Gibbs state of the Hubbard
skeleton. -/

/-- The Gibbs state of the canonical Hubbard-skeleton Hamiltonian
`H = H_hop + V_int`. -/
noncomputable def fermionGenericGibbsState
    (N : ℕ) (β : ℝ) (t V : Fin (N + 1) → Fin (N + 1) → ℂ) :
    ManyBodyOp (Fin (N + 1)) :=
  LatticeSystem.Quantum.gibbsState β (fermionGenericHamiltonian N t V)

/-- The Hubbard-skeleton Gibbs state is Hermitian when `t` is
Hermitian and `V` is entry-wise real. -/
theorem fermionGenericGibbsState_isHermitian
    (N : ℕ) (β : ℝ) {t V : Fin (N + 1) → Fin (N + 1) → ℂ}
    (ht : ∀ i j, star (t i j) = t j i)
    (hV : ∀ i j, star (V i j) = V i j) :
    (fermionGenericGibbsState N β t V).IsHermitian :=
  LatticeSystem.Quantum.gibbsState_isHermitian
    (fermionGenericHamiltonian_isHermitian N ht hV) β

/-- The Hubbard-skeleton Gibbs state commutes with its
Hamiltonian (instance of the generic
`gibbsState_commute_hamiltonian`). -/
theorem fermionGenericGibbsState_commute_hamiltonian
    (N : ℕ) (β : ℝ) (t V : Fin (N + 1) → Fin (N + 1) → ℂ) :
    Commute (fermionGenericGibbsState N β t V)
      (fermionGenericHamiltonian N t V) :=
  LatticeSystem.Quantum.gibbsState_commute_hamiltonian β _

/-! ## Fermion vacuum state

The Jordan–Wigner vacuum is the all-up many-body basis vector
`|↑↑…↑⟩`, since `c_i = jwString N i · σ^+_i` and
`σ^+ |↑⟩ = 0` site-locally. -/

/-- The fermion vacuum state on `Fin (N + 1)` JW modes: the
many-body computational-basis vector `|↑↑…↑⟩`. -/
noncomputable def fermionMultiVacuum (N : ℕ) : (Fin (N + 1) → Fin 2) → ℂ :=
  LatticeSystem.Quantum.basisVec (fun _ : Fin (N + 1) => (0 : Fin 2))

/-- The vacuum is annihilated by every fermion annihilation
operator: `c_i · |vac⟩ = 0` for every site `i`. Proof:
`c_i = jwString N i · σ^+_i`; the inner factor `σ^+_i` acts on
`|↑↑…↑⟩` by sending its site-`i` entry through `σ^+`, but
`σ^+ k 0 = 0` for both `k = 0, 1` since `σ^+ = !![0,1;0,0]`,
so the result vanishes; the outer `jwString` factor then maps
zero to zero. -/
theorem fermionMultiAnnihilation_mulVec_vacuum
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionMultiAnnihilation N i).mulVec (fermionMultiVacuum N) = 0 := by
  unfold fermionMultiAnnihilation fermionMultiVacuum
  rw [← Matrix.mulVec_mulVec]
  have hinner : (LatticeSystem.Quantum.onSite i spinHalfOpPlus).mulVec
      (LatticeSystem.Quantum.basisVec
        (fun _ : Fin (N + 1) => (0 : Fin 2))) = 0 := by
    rw [LatticeSystem.Quantum.onSite_mulVec_basisVec]
    funext τ
    apply Finset.sum_eq_zero
    intro k _
    change spinHalfOpPlus k 0 *
      LatticeSystem.Quantum.basisVec
        (Function.update (fun _ => (0 : Fin 2)) i k) τ = 0
    fin_cases k <;> simp [spinHalfOpPlus]
  rw [hinner, Matrix.mulVec_zero]

/-- Each site-occupation number annihilates the vacuum:
`n_i · |vac⟩ = c_i† (c_i |vac⟩) = c_i† 0 = 0`. -/
theorem fermionMultiNumber_mulVec_vacuum (N : ℕ) (i : Fin (N + 1)) :
    (fermionMultiNumber N i).mulVec (fermionMultiVacuum N) = 0 := by
  unfold fermionMultiNumber
  rw [← Matrix.mulVec_mulVec, fermionMultiAnnihilation_mulVec_vacuum,
    Matrix.mulVec_zero]

/-- The vacuum is an `N̂`-eigenstate with eigenvalue 0:
`N̂ · |vac⟩ = (Σ_j n_j) · |vac⟩ = Σ_j (n_j · |vac⟩) = 0`. -/
theorem fermionTotalNumber_mulVec_vacuum (N : ℕ) :
    (fermionTotalNumber N).mulVec (fermionMultiVacuum N) = 0 := by
  unfold fermionTotalNumber
  rw [Matrix.sum_mulVec]
  exact Finset.sum_eq_zero (fun i _ => fermionMultiNumber_mulVec_vacuum N i)

/-- The hopping operator annihilates the vacuum:
`H_hop · |vac⟩ = Σ t_{ij} c_i† (c_j |vac⟩) = 0`. -/
theorem fermionHopping_mulVec_vacuum
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) :
    (fermionHopping N t).mulVec (fermionMultiVacuum N) = 0 := by
  unfold fermionHopping
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    fermionMultiAnnihilation_mulVec_vacuum, Matrix.mulVec_zero, smul_zero]

/-- The density-density interaction annihilates the vacuum:
`V_int · |vac⟩ = Σ V_{ij} n_i (n_j |vac⟩) = 0`. -/
theorem fermionDensityInteraction_mulVec_vacuum
    (N : ℕ) (V : Fin (N + 1) → Fin (N + 1) → ℂ) :
    (fermionDensityInteraction N V).mulVec (fermionMultiVacuum N) = 0 := by
  unfold fermionDensityInteraction
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    fermionMultiNumber_mulVec_vacuum, Matrix.mulVec_zero, smul_zero]

/-- The full Hubbard-skeleton Hamiltonian annihilates the vacuum:
`H · |vac⟩ = (H_hop + V_int) · |vac⟩ = 0 + 0 = 0`. -/
theorem fermionGenericHamiltonian_mulVec_vacuum
    (N : ℕ) (t V : Fin (N + 1) → Fin (N + 1) → ℂ) :
    (fermionGenericHamiltonian N t V).mulVec (fermionMultiVacuum N) = 0 := by
  unfold fermionGenericHamiltonian
  rw [Matrix.add_mulVec, fermionHopping_mulVec_vacuum,
    fermionDensityInteraction_mulVec_vacuum, add_zero]

/-- The single-particle state `c_i† |vac⟩` is an `N̂`-eigenstate
with eigenvalue 1. Uses `[N̂, c_i†] = c_i†` (so
`N̂ c_i† = c_i† N̂ + c_i†`) and `N̂ |vac⟩ = 0`. -/
theorem fermionTotalNumber_mulVec_singleParticle
    (N : ℕ) (i : Fin (N + 1)) :
    (fermionTotalNumber N).mulVec
        ((fermionMultiCreation N i).mulVec (fermionMultiVacuum N)) =
      (fermionMultiCreation N i).mulVec (fermionMultiVacuum N) := by
  rw [Matrix.mulVec_mulVec]
  have h_comm : fermionTotalNumber N * fermionMultiCreation N i =
      fermionMultiCreation N i * fermionTotalNumber N +
        fermionMultiCreation N i :=
    (eq_add_of_sub_eq
      (fermionTotalNumber_commutator_fermionMultiCreation N i)).trans
      (add_comm _ _)
  rw [h_comm, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    fermionTotalNumber_mulVec_vacuum, Matrix.mulVec_zero, zero_add]

/-- **Charge-eigenstate helper.** If `X` carries U(1) charge `α`
(`[N̂, X] = α • X`) and `v` is `N̂`-annihilated, then `X v` is an
`N̂`-eigenstate with eigenvalue `α`. Generalises
`fermionTotalNumber_mulVec_singleParticle` (α = 1, X = c_i†) and
`fermionTotalNumber_mulVec_twoParticle` (α = 2, X = c_i† c_j†). -/
theorem fermionTotalNumber_mulVec_eigenstate_of_commute
    {N : ℕ} {X : ManyBodyOp (Fin (N + 1))} {α : ℂ}
    (hX : fermionTotalNumber N * X - X * fermionTotalNumber N = α • X)
    {v : (Fin (N + 1) → Fin 2) → ℂ}
    (hv : (fermionTotalNumber N).mulVec v = 0) :
    (fermionTotalNumber N).mulVec (X.mulVec v) = α • X.mulVec v := by
  rw [Matrix.mulVec_mulVec]
  have h_comm : fermionTotalNumber N * X = X * fermionTotalNumber N + α • X :=
    (eq_add_of_sub_eq hX).trans (add_comm _ _)
  rw [h_comm, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_zero, zero_add, Matrix.smul_mulVec]


end LatticeSystem.Fermion
