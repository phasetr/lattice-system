/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.ManyBody
import LatticeSystem.Quantum.Pauli
import LatticeSystem.Quantum.SpinHalfBasis
import LatticeSystem.Quantum.GibbsState
import LatticeSystem.Fermion.Mode
import LatticeSystem.Fermion.JordanWigner.String
import LatticeSystem.Fermion.JordanWigner.Operators
import LatticeSystem.Fermion.JordanWigner.CAR
import LatticeSystem.Lattice.Graph

/-!
# Multi-mode fermion via Jordan–Wigner mapping

This module lifts the single-mode CAR algebra (see
`LatticeSystem/Fermion/Mode.lean`) to a multi-mode fermion system on
the linearly-ordered lattice `Λ = Fin (N + 1)` via the Jordan–Wigner
mapping.

## Conventions

The Hilbert space is the spin-1/2 many-body space
`ManyBodyOp (Fin (N + 1)) = Matrix (Fin (N + 1) → Fin 2) (...) ℂ`,
with the convention from `Fermion/Mode.lean`:
`|0⟩` (vacuum) on each site corresponds to spin-up,
`|1⟩` (occupied) to spin-down.

## Definitions

The Jordan–Wigner string at site `i` is

```
jwString N i = ∏_{j : Fin (N+1), j.val < i.val} σ^z_j
```

and the multi-mode fermion operators are

```
c_i  = jwString N i · σ^+_i
c_i† = jwString N i · σ^-_i
```

The string makes the otherwise-bosonic spin raising / lowering
operators anticommute across distinct sites, giving the correct
fermion statistics.

## Results

* `jwString_zero` — `jwString N 0 = 1` (empty product at the leftmost
  site).
* `fermionMultiAnnihilation_zero`, `fermionMultiCreation_zero` —
  `c_0 = σ^+_0`, `c_0† = σ^-_0` (no JW string at the leftmost site).
* `jwString_commute_onSite` — `[jwString N i, onSite i A] = 0` for
  any `A`.
* `fermionMultiAnnihilation_sq` — `c_i² = 0` (Pauli exclusion).
* `fermionMultiCreation_sq` — `(c_i†)² = 0`.

The cross-site anticommutation relations
`{c_i, c_j†} = δ_ij` and `{c_i, c_j} = 0` for `i ≠ j` are deferred
to follow-up PRs (they require sign-cancellation tracking through
the JW string acting on intermediate sites).
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

/-! ## Spinful (two-species) fermion operator wrappers

To realise true Hubbard / spinful fermion models we re-index a
single-species chain of length `2 * (N + 1)` as a chain of
`N + 1` spinful sites, with each site carrying a spin label
`σ : Fin 2`. The bijection `(i, σ) ↦ 2 * i + σ` puts the two
species at site `i` in the consecutive JW positions
`2 i` (spin up) and `2 i + 1` (spin down).

All algebraic facts about the two-species operators (CARs,
charge conservation, Hermiticity) follow for free from the
single-species results applied to the underlying chain. -/

/-- The spinful site index: `(i, σ) ↦ 2 * i + σ`. -/
def spinfulIndex (N : ℕ) (i : Fin (N + 1)) (σ : Fin 2) :
    Fin (2 * N + 2) :=
  ⟨2 * i.val + σ.val, by
    have hi : i.val < N + 1 := i.isLt
    have hσ : σ.val < 2 := σ.isLt
    omega⟩

/-- Spin-up annihilation operator at spinful site `i`:
the JW annihilation at the underlying single-species position
`2 * i`. -/
noncomputable def fermionUpAnnihilation (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N i 0)

/-- Spin-down annihilation operator at spinful site `i`:
the JW annihilation at the underlying single-species position
`2 * i + 1`. -/
noncomputable def fermionDownAnnihilation (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N i 1)

/-- Spin-up creation operator at spinful site `i`. -/
noncomputable def fermionUpCreation (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  fermionMultiCreation (2 * N + 1) (spinfulIndex N i 0)

/-- Spin-down creation operator at spinful site `i`. -/
noncomputable def fermionDownCreation (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  fermionMultiCreation (2 * N + 1) (spinfulIndex N i 1)

/-- Spin-up site occupation number at spinful site `i`:
`n_{i,↑} = c_{i,↑}† · c_{i,↑}`. -/
noncomputable def fermionUpNumber (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  fermionMultiNumber (2 * N + 1) (spinfulIndex N i 0)

/-- Spin-down site occupation number at spinful site `i`:
`n_{i,↓} = c_{i,↓}† · c_{i,↓}`. -/
noncomputable def fermionDownNumber (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  fermionMultiNumber (2 * N + 1) (spinfulIndex N i 1)

/-- The on-site Hubbard interaction
`H_int = U Σ_i n_{i,↑} · n_{i,↓}` on the spinful chain. -/
noncomputable def hubbardOnSiteInteraction (N : ℕ) (U : ℂ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ i : Fin (N + 1), U • (fermionUpNumber N i * fermionDownNumber N i)

/-- The Hubbard on-site interaction commutes with the total
particle-number operator `N̂` on the underlying chain (charge
conservation). -/
theorem hubbardOnSiteInteraction_commute_fermionTotalNumber
    (N : ℕ) (U : ℂ) :
    Commute (hubbardOnSiteInteraction N U) (fermionTotalNumber (2 * N + 1)) := by
  unfold hubbardOnSiteInteraction
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  exact (fermionDensityDensity_commute_fermionTotalNumber (2 * N + 1)
    (spinfulIndex N i 0) (spinfulIndex N i 1)).smul_left U

/-- The Hubbard on-site interaction is Hermitian when the coupling
`U` is real (`star U = U`). Each summand `n_{i,↑} · n_{i,↓}` is
Hermitian (commuting Hermitian factors), and the scalar `U`
preserves Hermiticity under the realness assumption. -/
theorem hubbardOnSiteInteraction_isHermitian
    (N : ℕ) {U : ℂ} (hU : star U = U) :
    (hubbardOnSiteInteraction N U).IsHermitian := by
  change (hubbardOnSiteInteraction N U)ᴴ = hubbardOnSiteInteraction N U
  unfold hubbardOnSiteInteraction
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.conjTranspose_smul]
  unfold fermionUpNumber fermionDownNumber
  rw [(fermionMultiNumber_mul_isHermitian (2 * N + 1)
    (spinfulIndex N i 0) (spinfulIndex N i 1)).eq, hU]

/-- The spin-symmetric tight-binding kinetic operator on the spinful
chain: `T = Σ_{σ} Σ_{i,j} t_{i,j} c_{i,σ}† c_{j,σ}`. Each spin
sector hops independently with the same coupling matrix `t`. -/
noncomputable def hubbardKinetic (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℂ) : ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ σ : Fin 2, ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
    t i j • (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
      fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ))

/-- The spinful kinetic operator commutes with the total particle
number `N̂` on the underlying chain. Each summand
`t_{ij} • c_{iσ}† c_{jσ}` commutes with `N̂` via
`fermionTotalNumber_commute_hopping`, and finite sums preserve
this. -/
theorem hubbardKinetic_commute_fermionTotalNumber
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) :
    Commute (hubbardKinetic N t) (fermionTotalNumber (2 * N + 1)) := by
  unfold hubbardKinetic
  refine Commute.sum_left _ _ _ (fun σ _ => ?_)
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  refine Commute.sum_left _ _ _ (fun j _ => ?_)
  exact ((fermionTotalNumber_commute_hopping (2 * N + 1)
    (spinfulIndex N i σ) (spinfulIndex N j σ)).symm).smul_left (t i j)

/-- The spinful kinetic operator is Hermitian when the hopping
matrix `t` is Hermitian (`star (t i j) = t j i`). For each fixed
spin `σ`, the inner double sum is the single-species
`fermionHopping (2N+1) t̃` for the lifted coupling
`t̃ (spinfulIndex N i σ) (spinfulIndex N j σ) = t i j`; we prove
Hermiticity term-by-term using the conjTranspose flip and a
`Finset.sum_comm` index swap. -/
theorem hubbardKinetic_isHermitian
    (N : ℕ) {t : Fin (N + 1) → Fin (N + 1) → ℂ}
    (ht : ∀ i j, star (t i j) = t j i) :
    (hubbardKinetic N t).IsHermitian := by
  change (hubbardKinetic N t)ᴴ = hubbardKinetic N t
  unfold hubbardKinetic
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  calc (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), t i j •
          (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
            fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ)))ᴴ
      = ∑ i, (∑ j, t i j •
            (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
              fermionMultiAnnihilation (2 * N + 1)
                (spinfulIndex N j σ)))ᴴ := by
        rw [Matrix.conjTranspose_sum]
    _ = ∑ i, ∑ j, (t i j •
            (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
              fermionMultiAnnihilation (2 * N + 1)
                (spinfulIndex N j σ)))ᴴ := by
        congr 1; funext i
        rw [Matrix.conjTranspose_sum]
    _ = ∑ i, ∑ j, t j i •
            (fermionMultiCreation (2 * N + 1) (spinfulIndex N j σ) *
              fermionMultiAnnihilation (2 * N + 1)
                (spinfulIndex N i σ)) := by
        congr 1; funext i; congr 1; funext j
        rw [Matrix.conjTranspose_smul,
          fermionHoppingTerm_conjTranspose, ht]
    _ = ∑ j, ∑ i, t j i •
            (fermionMultiCreation (2 * N + 1) (spinfulIndex N j σ) *
              fermionMultiAnnihilation (2 * N + 1)
                (spinfulIndex N i σ)) :=
        Finset.sum_comm
    _ = ∑ i, ∑ j, t i j •
            (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
              fermionMultiAnnihilation (2 * N + 1)
                (spinfulIndex N j σ)) := rfl

/-- The canonical (single-band) Hubbard Hamiltonian:
`H = Σ_{σ} Σ_{i,j} t_{i,j} c_{iσ}† c_{jσ} + U Σ_i n_{i↑} n_{i↓}`. -/
noncomputable def hubbardHamiltonian (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  hubbardKinetic N t + hubbardOnSiteInteraction N U

/-- The Hubbard Hamiltonian commutes with the total particle
number `N̂`: charge conservation. Direct from
`hubbardKinetic_commute_fermionTotalNumber` and
`hubbardOnSiteInteraction_commute_fermionTotalNumber` via
`Commute.add_left`. -/
theorem hubbardHamiltonian_commute_fermionTotalNumber
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    Commute (hubbardHamiltonian N t U) (fermionTotalNumber (2 * N + 1)) := by
  unfold hubbardHamiltonian
  exact (hubbardKinetic_commute_fermionTotalNumber N t).add_left
    (hubbardOnSiteInteraction_commute_fermionTotalNumber N U)

/-- The Hubbard Hamiltonian is Hermitian when the hopping matrix
`t` is Hermitian and the on-site coupling `U` is real. -/
theorem hubbardHamiltonian_isHermitian
    (N : ℕ) {t : Fin (N + 1) → Fin (N + 1) → ℂ} {U : ℂ}
    (ht : ∀ i j, star (t i j) = t j i) (hU : star U = U) :
    (hubbardHamiltonian N t U).IsHermitian := by
  unfold hubbardHamiltonian
  exact (hubbardKinetic_isHermitian N ht).add
    (hubbardOnSiteInteraction_isHermitian N hU)

/-- The Gibbs state of the canonical Hubbard Hamiltonian. -/
noncomputable def hubbardGibbsState
    (N : ℕ) (β : ℝ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  LatticeSystem.Quantum.gibbsState β (hubbardHamiltonian N t U)

/-- The Hubbard Gibbs state is Hermitian when `t` is Hermitian and
`U` is real. -/
theorem hubbardGibbsState_isHermitian
    (N : ℕ) (β : ℝ) {t : Fin (N + 1) → Fin (N + 1) → ℂ} {U : ℂ}
    (ht : ∀ i j, star (t i j) = t j i) (hU : star U = U) :
    (hubbardGibbsState N β t U).IsHermitian :=
  LatticeSystem.Quantum.gibbsState_isHermitian
    (hubbardHamiltonian_isHermitian N ht hU) β

/-- The Hubbard Gibbs state commutes with the Hubbard Hamiltonian
(generic instance of `gibbsState_commute_hamiltonian`). -/
theorem hubbardGibbsState_commute_hamiltonian
    (N : ℕ) (β : ℝ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    Commute (hubbardGibbsState N β t U) (hubbardHamiltonian N t U) :=
  LatticeSystem.Quantum.gibbsState_commute_hamiltonian β _

/-! ## Spinful conserved charges N_↑, N_↓, and S^z_tot

The spinful Hilbert space carries two natural U(1) charges
(particle numbers per spin) and one diagonal SU(2) charge
(z-component of total spin). They all commute pairwise (and with
the total particle number `N̂`); commute with the full Hubbard
Hamiltonian is deferred to a later PR. -/

/-- Total spin-up particle number `N_↑ = Σ_i n_{i,↑}`. -/
noncomputable def fermionTotalUpNumber (N : ℕ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ i : Fin (N + 1), fermionUpNumber N i

/-- Total spin-down particle number `N_↓ = Σ_i n_{i,↓}`. -/
noncomputable def fermionTotalDownNumber (N : ℕ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ i : Fin (N + 1), fermionDownNumber N i

/-- Total z-component of spin `S^z_tot = (1/2)(N_↑ − N_↓)`. -/
noncomputable def fermionTotalSpinZ (N : ℕ) : ManyBodyOp (Fin (2 * N + 2)) :=
  (1 / 2 : ℂ) • (fermionTotalUpNumber N - fermionTotalDownNumber N)

/-- `N_↑` and `N_↓` commute (sums of pairwise commuting number
operators). -/
theorem fermionTotalUpNumber_commute_fermionTotalDownNumber (N : ℕ) :
    Commute (fermionTotalUpNumber N) (fermionTotalDownNumber N) := by
  unfold fermionTotalUpNumber fermionTotalDownNumber
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  refine Commute.sum_right _ _ _ (fun j _ => ?_)
  exact fermionMultiNumber_commute (2 * N + 1)
    (spinfulIndex N i 0) (spinfulIndex N j 1)

/-- `N_↑` commutes with the total particle number `N̂` on the
underlying chain. -/
theorem fermionTotalUpNumber_commute_fermionTotalNumber (N : ℕ) :
    Commute (fermionTotalUpNumber N) (fermionTotalNumber (2 * N + 1)) := by
  unfold fermionTotalUpNumber
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  exact fermionMultiNumber_commute_fermionTotalNumber (2 * N + 1)
    (spinfulIndex N i 0)

/-- `N_↓` commutes with the total particle number `N̂` on the
underlying chain. -/
theorem fermionTotalDownNumber_commute_fermionTotalNumber (N : ℕ) :
    Commute (fermionTotalDownNumber N) (fermionTotalNumber (2 * N + 1)) := by
  unfold fermionTotalDownNumber
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  exact fermionMultiNumber_commute_fermionTotalNumber (2 * N + 1)
    (spinfulIndex N i 1)

/-- The total z-spin `S^z_tot` commutes with the total particle
number `N̂`: free corollary of the up/down individual commutes. -/
theorem fermionTotalSpinZ_commute_fermionTotalNumber (N : ℕ) :
    Commute (fermionTotalSpinZ N) (fermionTotalNumber (2 * N + 1)) := by
  unfold fermionTotalSpinZ
  refine Commute.smul_left ?_ _
  exact (fermionTotalUpNumber_commute_fermionTotalNumber N).sub_left
    (fermionTotalDownNumber_commute_fermionTotalNumber N)

/-- `N_↑` commutes with the Hubbard on-site interaction
`U Σ_i n_{i↑} n_{i↓}`. All summands are products of pairwise
commuting number operators. -/
theorem fermionTotalUpNumber_commute_hubbardOnSiteInteraction
    (N : ℕ) (U : ℂ) :
    Commute (fermionTotalUpNumber N) (hubbardOnSiteInteraction N U) := by
  unfold fermionTotalUpNumber hubbardOnSiteInteraction
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  refine Commute.sum_right _ _ _ (fun i _ => ?_)
  refine Commute.smul_right ?_ U
  unfold fermionUpNumber fermionDownNumber
  refine Commute.mul_right ?_ ?_
  · exact fermionMultiNumber_commute (2 * N + 1)
      (spinfulIndex N k 0) (spinfulIndex N i 0)
  · exact fermionMultiNumber_commute (2 * N + 1)
      (spinfulIndex N k 0) (spinfulIndex N i 1)

/-- `N_↓` commutes with the Hubbard on-site interaction. -/
theorem fermionTotalDownNumber_commute_hubbardOnSiteInteraction
    (N : ℕ) (U : ℂ) :
    Commute (fermionTotalDownNumber N) (hubbardOnSiteInteraction N U) := by
  unfold fermionTotalDownNumber hubbardOnSiteInteraction
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  refine Commute.sum_right _ _ _ (fun i _ => ?_)
  refine Commute.smul_right ?_ U
  unfold fermionUpNumber fermionDownNumber
  refine Commute.mul_right ?_ ?_
  · exact fermionMultiNumber_commute (2 * N + 1)
      (spinfulIndex N k 1) (spinfulIndex N i 0)
  · exact fermionMultiNumber_commute (2 * N + 1)
      (spinfulIndex N k 1) (spinfulIndex N i 1)

/-- `S^z_tot` commutes with the Hubbard on-site interaction. Free
corollary. -/
theorem fermionTotalSpinZ_commute_hubbardOnSiteInteraction
    (N : ℕ) (U : ℂ) :
    Commute (fermionTotalSpinZ N) (hubbardOnSiteInteraction N U) := by
  unfold fermionTotalSpinZ
  refine Commute.smul_left ?_ _
  exact (fermionTotalUpNumber_commute_hubbardOnSiteInteraction N U).sub_left
    (fermionTotalDownNumber_commute_hubbardOnSiteInteraction N U)

/-! ## Spinful vacuum eigenstate corollaries

The JW vacuum on the underlying chain `Fin (2N+2)` is the
canonical spinful vacuum. All single-species vacuum results lift
mechanically. -/

/-- The spin-up annihilation operator at any site kills the
vacuum. -/
theorem fermionUpAnnihilation_mulVec_vacuum (N : ℕ) (i : Fin (N + 1)) :
    (fermionUpAnnihilation N i).mulVec
      (fermionMultiVacuum (2 * N + 1)) = 0 :=
  fermionMultiAnnihilation_mulVec_vacuum (2 * N + 1) (spinfulIndex N i 0)

/-- The spin-down annihilation operator at any site kills the
vacuum. -/
theorem fermionDownAnnihilation_mulVec_vacuum (N : ℕ) (i : Fin (N + 1)) :
    (fermionDownAnnihilation N i).mulVec
      (fermionMultiVacuum (2 * N + 1)) = 0 :=
  fermionMultiAnnihilation_mulVec_vacuum (2 * N + 1) (spinfulIndex N i 1)

/-- `n_{i,↑} · |vac⟩ = 0`. -/
theorem fermionUpNumber_mulVec_vacuum (N : ℕ) (i : Fin (N + 1)) :
    (fermionUpNumber N i).mulVec (fermionMultiVacuum (2 * N + 1)) = 0 :=
  fermionMultiNumber_mulVec_vacuum (2 * N + 1) (spinfulIndex N i 0)

/-- `n_{i,↓} · |vac⟩ = 0`. -/
theorem fermionDownNumber_mulVec_vacuum (N : ℕ) (i : Fin (N + 1)) :
    (fermionDownNumber N i).mulVec (fermionMultiVacuum (2 * N + 1)) = 0 :=
  fermionMultiNumber_mulVec_vacuum (2 * N + 1) (spinfulIndex N i 1)

/-- `N_↑ · |vac⟩ = 0`. -/
theorem fermionTotalUpNumber_mulVec_vacuum (N : ℕ) :
    (fermionTotalUpNumber N).mulVec (fermionMultiVacuum (2 * N + 1)) = 0 := by
  unfold fermionTotalUpNumber
  rw [Matrix.sum_mulVec]
  exact Finset.sum_eq_zero (fun i _ => fermionUpNumber_mulVec_vacuum N i)

/-- `N_↓ · |vac⟩ = 0`. -/
theorem fermionTotalDownNumber_mulVec_vacuum (N : ℕ) :
    (fermionTotalDownNumber N).mulVec (fermionMultiVacuum (2 * N + 1)) = 0 := by
  unfold fermionTotalDownNumber
  rw [Matrix.sum_mulVec]
  exact Finset.sum_eq_zero (fun i _ => fermionDownNumber_mulVec_vacuum N i)

/-- The vacuum is unpolarised: `S^z_tot · |vac⟩ = 0`. -/
theorem fermionTotalSpinZ_mulVec_vacuum (N : ℕ) :
    (fermionTotalSpinZ N).mulVec (fermionMultiVacuum (2 * N + 1)) = 0 := by
  unfold fermionTotalSpinZ
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec,
    fermionTotalUpNumber_mulVec_vacuum,
    fermionTotalDownNumber_mulVec_vacuum, sub_zero, smul_zero]

/-- The Hubbard kinetic operator annihilates the vacuum. -/
theorem hubbardKinetic_mulVec_vacuum
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) :
    (hubbardKinetic N t).mulVec (fermionMultiVacuum (2 * N + 1)) = 0 := by
  unfold hubbardKinetic
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun σ _ => ?_)
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    fermionMultiAnnihilation_mulVec_vacuum, Matrix.mulVec_zero, smul_zero]

/-- The Hubbard on-site interaction annihilates the vacuum. -/
theorem hubbardOnSiteInteraction_mulVec_vacuum (N : ℕ) (U : ℂ) :
    (hubbardOnSiteInteraction N U).mulVec
      (fermionMultiVacuum (2 * N + 1)) = 0 := by
  unfold hubbardOnSiteInteraction
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Matrix.smul_mulVec]
  unfold fermionUpNumber fermionDownNumber
  rw [← Matrix.mulVec_mulVec, fermionMultiNumber_mulVec_vacuum,
    Matrix.mulVec_zero, smul_zero]

/-- The full Hubbard Hamiltonian annihilates the vacuum. -/
theorem hubbardHamiltonian_mulVec_vacuum
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    (hubbardHamiltonian N t U).mulVec
      (fermionMultiVacuum (2 * N + 1)) = 0 := by
  unfold hubbardHamiltonian
  rw [Matrix.add_mulVec, hubbardKinetic_mulVec_vacuum,
    hubbardOnSiteInteraction_mulVec_vacuum, add_zero]

/-! ## Cross-spin commutes (different species commute) -/

/-- Even and odd JW positions are distinct: `spinfulIndex N i 0 ≠
spinfulIndex N j 1` (the up-channel position `2 i` is never the
down-channel position `2 j + 1`). -/
theorem spinfulIndex_up_ne_down (N : ℕ) (i j : Fin (N + 1)) :
    spinfulIndex N i 0 ≠ spinfulIndex N j 1 := by
  intro heq
  have h := congrArg Fin.val heq
  change False
  simp [spinfulIndex] at h
  omega

/-- `N_↓` commutes with every `c_{i,↑}†`: each summand
`n_{2k+1}` and `c_{2i}†` are at distinct JW positions. -/
theorem fermionTotalDownNumber_commute_fermionUpCreation
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionTotalDownNumber N) (fermionUpCreation N i) := by
  unfold fermionTotalDownNumber fermionUpCreation
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  exact fermionMultiNumber_commute_fermionMultiCreation_of_ne
    ((spinfulIndex_up_ne_down N i k).symm).symm.symm

/-- `N_↓` commutes with every `c_{i,↑}`. -/
theorem fermionTotalDownNumber_commute_fermionUpAnnihilation
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionTotalDownNumber N) (fermionUpAnnihilation N i) := by
  unfold fermionTotalDownNumber fermionUpAnnihilation
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  exact fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne
    ((spinfulIndex_up_ne_down N i k).symm).symm.symm

/-- `N_↓` commutes with every `n_{i,↑}` (number operators always
commute, but here we record the cross-spin special case
explicitly). -/
theorem fermionTotalDownNumber_commute_fermionUpNumber
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionTotalDownNumber N) (fermionUpNumber N i) := by
  unfold fermionTotalDownNumber fermionUpNumber
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  exact fermionMultiNumber_commute (2 * N + 1)
    (spinfulIndex N k 1) (spinfulIndex N i 0)

/-- `N_↑` commutes with every `c_{i,↓}†`. -/
theorem fermionTotalUpNumber_commute_fermionDownCreation
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionTotalUpNumber N) (fermionDownCreation N i) := by
  unfold fermionTotalUpNumber fermionDownCreation
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  exact fermionMultiNumber_commute_fermionMultiCreation_of_ne
    (spinfulIndex_up_ne_down N k i)

/-- `N_↑` commutes with every `c_{i,↓}`. -/
theorem fermionTotalUpNumber_commute_fermionDownAnnihilation
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionTotalUpNumber N) (fermionDownAnnihilation N i) := by
  unfold fermionTotalUpNumber fermionDownAnnihilation
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  exact fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne
    (spinfulIndex_up_ne_down N k i)

/-- `N_↑` commutes with every `n_{i,↓}`. -/
theorem fermionTotalUpNumber_commute_fermionDownNumber
    (N : ℕ) (i : Fin (N + 1)) :
    Commute (fermionTotalUpNumber N) (fermionDownNumber N i) := by
  unfold fermionTotalUpNumber fermionDownNumber
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  exact fermionMultiNumber_commute (2 * N + 1)
    (spinfulIndex N k 0) (spinfulIndex N i 1)

/-- `N_↓` commutes with the up-sector hopping term
`c_{i,↑}† · c_{j,↑}` (cross-spin). -/
theorem fermionTotalDownNumber_commute_upHopping
    (N : ℕ) (i j : Fin (N + 1)) :
    Commute (fermionTotalDownNumber N)
      (fermionUpCreation N i * fermionUpAnnihilation N j) :=
  (fermionTotalDownNumber_commute_fermionUpCreation N i).mul_right
    (fermionTotalDownNumber_commute_fermionUpAnnihilation N j)

/-- `N_↑` commutes with the down-sector hopping term
`c_{i,↓}† · c_{j,↓}` (cross-spin). -/
theorem fermionTotalUpNumber_commute_downHopping
    (N : ℕ) (i j : Fin (N + 1)) :
    Commute (fermionTotalUpNumber N)
      (fermionDownCreation N i * fermionDownAnnihilation N j) :=
  (fermionTotalUpNumber_commute_fermionDownCreation N i).mul_right
    (fermionTotalUpNumber_commute_fermionDownAnnihilation N j)

/-! ## Hubbard-on-graph wrappers (graph-centric Hubbard) -/

/-- Hubbard kinetic operator with hopping matrix derived from a
`SimpleGraph G` and uniform edge weight `J : ℂ`. -/
noncomputable def hubbardKineticOnGraph (N : ℕ)
    (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj] (J : ℂ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  hubbardKinetic N (LatticeSystem.Lattice.couplingOf G J)

/-- The graph-built Hubbard kinetic operator commutes with `N̂`. -/
theorem hubbardKineticOnGraph_commute_fermionTotalNumber
    (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (J : ℂ) :
    Commute (hubbardKineticOnGraph N G J)
      (fermionTotalNumber (2 * N + 1)) :=
  hubbardKinetic_commute_fermionTotalNumber N _

/-- The graph-built Hubbard kinetic operator is Hermitian when
`J` is real: the coupling `couplingOf G J` is then a Hermitian
matrix on the (symmetric, decidable) graph. -/
theorem hubbardKineticOnGraph_isHermitian
    (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    {J : ℂ} (hJ : star J = J) :
    (hubbardKineticOnGraph N G J).IsHermitian := by
  unfold hubbardKineticOnGraph
  refine hubbardKinetic_isHermitian N (fun i j => ?_)
  rw [LatticeSystem.Lattice.couplingOf_real G hJ,
    LatticeSystem.Lattice.couplingOf_symm]

/-- The full Hubbard Hamiltonian with hopping derived from a
`SimpleGraph G` plus on-site interaction `U`. -/
noncomputable def hubbardHamiltonianOnGraph (N : ℕ)
    (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj] (J U : ℂ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  hubbardKineticOnGraph N G J + hubbardOnSiteInteraction N U

/-- The graph-built Hubbard Hamiltonian commutes with `N̂`. -/
theorem hubbardHamiltonianOnGraph_commute_fermionTotalNumber
    (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (J U : ℂ) :
    Commute (hubbardHamiltonianOnGraph N G J U)
      (fermionTotalNumber (2 * N + 1)) := by
  unfold hubbardHamiltonianOnGraph
  exact (hubbardKineticOnGraph_commute_fermionTotalNumber N G J).add_left
    (hubbardOnSiteInteraction_commute_fermionTotalNumber N U)

/-- The graph-built Hubbard Hamiltonian is Hermitian when both
`J` and `U` are real. -/
theorem hubbardHamiltonianOnGraph_isHermitian
    (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    {J U : ℂ} (hJ : star J = J) (hU : star U = U) :
    (hubbardHamiltonianOnGraph N G J U).IsHermitian := by
  unfold hubbardHamiltonianOnGraph
  exact (hubbardKineticOnGraph_isHermitian N G hJ).add
    (hubbardOnSiteInteraction_isHermitian N hU)

/-! ## 1D Hubbard chain instance -/

/-- The canonical 1D nearest-neighbour Hubbard Hamiltonian on a
chain of `N + 1` spinful sites, with hopping amplitude `J : ℝ`
(ferromagnetic sign convention `−J`) and on-site Coulomb
repulsion `U : ℝ`. -/
noncomputable def hubbardChainHamiltonian (N : ℕ) (J U : ℝ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  hubbardHamiltonianOnGraph N (SimpleGraph.pathGraph (N + 1))
    (-(J : ℂ)) (U : ℂ)

/-- The 1D Hubbard chain Hamiltonian is Hermitian. -/
theorem hubbardChainHamiltonian_isHermitian (N : ℕ) (J U : ℝ) :
    (hubbardChainHamiltonian N J U).IsHermitian :=
  hubbardHamiltonianOnGraph_isHermitian N _ (by simp) (by simp)

/-- The 1D Hubbard chain Hamiltonian commutes with `N̂` (charge
conservation). -/
theorem hubbardChainHamiltonian_commute_fermionTotalNumber
    (N : ℕ) (J U : ℝ) :
    Commute (hubbardChainHamiltonian N J U)
      (fermionTotalNumber (2 * N + 1)) :=
  hubbardHamiltonianOnGraph_commute_fermionTotalNumber N _ _ _

/-- `hubbardHamiltonianOnGraph` annihilates the vacuum. Both
`hubbardKinetic` and `hubbardOnSiteInteraction` do, by PR #166. -/
theorem hubbardHamiltonianOnGraph_mulVec_vacuum
    (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (J U : ℂ) :
    (hubbardHamiltonianOnGraph N G J U).mulVec
      (fermionMultiVacuum (2 * N + 1)) = 0 := by
  unfold hubbardHamiltonianOnGraph hubbardKineticOnGraph
  rw [Matrix.add_mulVec, hubbardKinetic_mulVec_vacuum,
    hubbardOnSiteInteraction_mulVec_vacuum, add_zero]

/-- The 1D Hubbard chain Hamiltonian annihilates the vacuum. Free
corollary of `hubbardHamiltonianOnGraph_mulVec_vacuum`. -/
theorem hubbardChainHamiltonian_mulVec_vacuum
    (N : ℕ) (J U : ℝ) :
    (hubbardChainHamiltonian N J U).mulVec
      (fermionMultiVacuum (2 * N + 1)) = 0 :=
  hubbardHamiltonianOnGraph_mulVec_vacuum N _ _ _

/-- The Gibbs state of the 1D Hubbard chain Hamiltonian. -/
noncomputable def hubbardChainGibbsState (N : ℕ) (β : ℝ) (J U : ℝ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  LatticeSystem.Quantum.gibbsState β (hubbardChainHamiltonian N J U)

/-- The 1D Hubbard chain Gibbs state is Hermitian. -/
theorem hubbardChainGibbsState_isHermitian (N : ℕ) (β : ℝ) (J U : ℝ) :
    (hubbardChainGibbsState N β J U).IsHermitian :=
  LatticeSystem.Quantum.gibbsState_isHermitian
    (hubbardChainHamiltonian_isHermitian N J U) β

/-- The 1D Hubbard chain Gibbs state commutes with its
Hamiltonian. -/
theorem hubbardChainGibbsState_commute_hamiltonian
    (N : ℕ) (β : ℝ) (J U : ℝ) :
    Commute (hubbardChainGibbsState N β J U)
      (hubbardChainHamiltonian N J U) :=
  LatticeSystem.Quantum.gibbsState_commute_hamiltonian β _

/-! ## Hubbard chain Gibbs expectation companions

Generic-`gibbsExpectation*` lemmas instantiated at the 1D Hubbard
chain Hamiltonian. -/

/-- Infinite-temperature (β = 0) closed form for the Hubbard
chain expectation: `⟨A⟩_0 = (1/dim) · Tr A`. -/
theorem hubbardChainGibbsExpectation_zero (N : ℕ) (J U : ℝ)
    (A : ManyBodyOp (Fin (2 * N + 2))) :
    LatticeSystem.Quantum.gibbsExpectation 0
        (hubbardChainHamiltonian N J U) A
      = ((Fintype.card (Fin (2 * N + 2) → Fin 2) : ℂ))⁻¹ *
          A.trace :=
  LatticeSystem.Quantum.gibbsExpectation_zero
    (hubbardChainHamiltonian N J U) A

/-- For Hermitian `O`, the Hubbard-chain expectation `⟨O⟩_β` is
real. -/
theorem hubbardChainGibbsExpectation_im_of_isHermitian
    (N : ℕ) (β J U : ℝ) {O : ManyBodyOp (Fin (2 * N + 2))}
    (hO : O.IsHermitian) :
    (LatticeSystem.Quantum.gibbsExpectation β
        (hubbardChainHamiltonian N J U) O).im = 0 :=
  LatticeSystem.Quantum.gibbsExpectation_im_of_isHermitian
    (hubbardChainHamiltonian_isHermitian N J U) hO β

/-- Hubbard-chain conservation law: `⟨[H, A]⟩_β = 0`. -/
theorem hubbardChainGibbsExpectation_commutator_hamiltonian
    (N : ℕ) (β J U : ℝ) (A : ManyBodyOp (Fin (2 * N + 2))) :
    LatticeSystem.Quantum.gibbsExpectation β
        (hubbardChainHamiltonian N J U)
        (hubbardChainHamiltonian N J U * A
          - A * hubbardChainHamiltonian N J U) = 0 :=
  LatticeSystem.Quantum.gibbsExpectation_commutator_hamiltonian β
    (hubbardChainHamiltonian N J U) A

/-- Hubbard-chain energy expectation is real:
`(⟨H_chain⟩_β).im = 0`. -/
theorem hubbardChainGibbsExpectation_hamiltonian_im
    (N : ℕ) (β J U : ℝ) :
    (LatticeSystem.Quantum.gibbsExpectation β
        (hubbardChainHamiltonian N J U)
        (hubbardChainHamiltonian N J U)).im = 0 :=
  LatticeSystem.Quantum.gibbsExpectation_hamiltonian_im
    (hubbardChainHamiltonian_isHermitian N J U) β

/-- Hubbard-chain energy n-th power expectation is real:
`(⟨H_chain^n⟩_β).im = 0` for any `n : ℕ`. -/
theorem hubbardChainGibbsExpectation_hamiltonian_pow_im
    (N : ℕ) (β J U : ℝ) (n : ℕ) :
    (LatticeSystem.Quantum.gibbsExpectation β
        (hubbardChainHamiltonian N J U)
        ((hubbardChainHamiltonian N J U)^n)).im = 0 :=
  LatticeSystem.Quantum.gibbsExpectation_pow_im_of_isHermitian
    (hubbardChainHamiltonian_isHermitian N J U)
    (hubbardChainHamiltonian_isHermitian N J U) β n

/-- Hubbard-chain partition function is real. -/
theorem hubbardChain_partitionFn_im (N : ℕ) (β J U : ℝ) :
    (LatticeSystem.Quantum.partitionFn β
        (hubbardChainHamiltonian N J U)).im = 0 :=
  LatticeSystem.Quantum.partitionFn_im_of_isHermitian
    (hubbardChainHamiltonian_isHermitian N J U) β

/-- Hubbard-chain real-cast equality. -/
theorem hubbardChainGibbsExpectation_ofReal_re_eq
    (N : ℕ) (β J U : ℝ) {O : ManyBodyOp (Fin (2 * N + 2))}
    (hO : O.IsHermitian) :
    (((LatticeSystem.Quantum.gibbsExpectation β
        (hubbardChainHamiltonian N J U) O).re : ℂ))
      = LatticeSystem.Quantum.gibbsExpectation β
          (hubbardChainHamiltonian N J U) O :=
  LatticeSystem.Quantum.gibbsExpectation_ofReal_re_eq_of_isHermitian
    (hubbardChainHamiltonian_isHermitian N J U) hO β

/-- Hubbard-chain Rényi-n trace identity. -/
theorem hubbardChainGibbsState_pow_trace
    (N : ℕ) (β J U : ℝ) (n : ℕ) :
    ((hubbardChainGibbsState N β J U)^n).trace
      = LatticeSystem.Quantum.partitionFn ((n : ℝ) * β)
          (hubbardChainHamiltonian N J U)
        / (LatticeSystem.Quantum.partitionFn β
            (hubbardChainHamiltonian N J U)) ^ n :=
  LatticeSystem.Quantum.gibbsState_pow_trace β
    (hubbardChainHamiltonian N J U) n

/-- The two-particle state `c_i† c_j† |vac⟩` is an `N̂`-eigenstate
with eigenvalue 2. The Leibniz rule
`[N̂, AB] = [N̂,A]B + A[N̂,B]` together with `[N̂, c_†] = c_†`
yields `[N̂, c_i† c_j†] = 2 c_i† c_j†`; applied to the vacuum and
combined with `N̂ |vac⟩ = 0` this gives the eigenvalue 2. -/
theorem fermionTotalNumber_mulVec_twoParticle
    (N : ℕ) (i j : Fin (N + 1)) :
    (fermionTotalNumber N).mulVec
        ((fermionMultiCreation N i * fermionMultiCreation N j).mulVec
          (fermionMultiVacuum N)) =
      (2 : ℂ) •
        (fermionMultiCreation N i * fermionMultiCreation N j).mulVec
          (fermionMultiVacuum N) := by
  rw [Matrix.mulVec_mulVec]
  have h₁ : fermionTotalNumber N * fermionMultiCreation N i =
      fermionMultiCreation N i * fermionTotalNumber N +
        fermionMultiCreation N i :=
    (eq_add_of_sub_eq
      (fermionTotalNumber_commutator_fermionMultiCreation N i)).trans
      (add_comm _ _)
  have h₂ : fermionTotalNumber N * fermionMultiCreation N j =
      fermionMultiCreation N j * fermionTotalNumber N +
        fermionMultiCreation N j :=
    (eq_add_of_sub_eq
      (fermionTotalNumber_commutator_fermionMultiCreation N j)).trans
      (add_comm _ _)
  have h_comm : fermionTotalNumber N *
      (fermionMultiCreation N i * fermionMultiCreation N j) =
      (fermionMultiCreation N i * fermionMultiCreation N j) *
        fermionTotalNumber N +
      (2 : ℂ) •
        (fermionMultiCreation N i * fermionMultiCreation N j) := by
    calc fermionTotalNumber N *
          (fermionMultiCreation N i * fermionMultiCreation N j)
        = (fermionTotalNumber N * fermionMultiCreation N i) *
            fermionMultiCreation N j := by rw [← Matrix.mul_assoc]
      _ = (fermionMultiCreation N i * fermionTotalNumber N +
            fermionMultiCreation N i) * fermionMultiCreation N j := by
            rw [h₁]
      _ = fermionMultiCreation N i * fermionTotalNumber N *
            fermionMultiCreation N j +
          fermionMultiCreation N i * fermionMultiCreation N j := by
            rw [Matrix.add_mul]
      _ = fermionMultiCreation N i *
            (fermionTotalNumber N * fermionMultiCreation N j) +
          fermionMultiCreation N i * fermionMultiCreation N j := by
            rw [Matrix.mul_assoc]
      _ = fermionMultiCreation N i *
            (fermionMultiCreation N j * fermionTotalNumber N +
              fermionMultiCreation N j) +
          fermionMultiCreation N i * fermionMultiCreation N j := by
            rw [h₂]
      _ = fermionMultiCreation N i *
            (fermionMultiCreation N j * fermionTotalNumber N) +
          fermionMultiCreation N i * fermionMultiCreation N j +
          fermionMultiCreation N i * fermionMultiCreation N j := by
            rw [Matrix.mul_add]
      _ = fermionMultiCreation N i * fermionMultiCreation N j *
            fermionTotalNumber N +
          (fermionMultiCreation N i * fermionMultiCreation N j +
            fermionMultiCreation N i * fermionMultiCreation N j) := by
            rw [← Matrix.mul_assoc]; abel
      _ = fermionMultiCreation N i * fermionMultiCreation N j *
            fermionTotalNumber N +
          (2 : ℂ) •
            (fermionMultiCreation N i * fermionMultiCreation N j) := by
            rw [two_smul]
  rw [h_comm, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    fermionTotalNumber_mulVec_vacuum, Matrix.mulVec_zero, zero_add,
    Matrix.smul_mulVec]

/-! ## Hubbard Gibbs state on a graph -/

/-- Gibbs state of the graph-built Hubbard Hamiltonian. -/
noncomputable def hubbardGibbsStateOnGraph (N : ℕ) (β : ℝ)
    (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj] (J U : ℂ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  LatticeSystem.Quantum.gibbsState β (hubbardHamiltonianOnGraph N G J U)

/-- Hermiticity of the graph-built Hubbard Gibbs state. -/
theorem hubbardGibbsStateOnGraph_isHermitian
    (N : ℕ) (β : ℝ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    {J U : ℂ} (hJ : star J = J) (hU : star U = U) :
    (hubbardGibbsStateOnGraph N β G J U).IsHermitian :=
  LatticeSystem.Quantum.gibbsState_isHermitian
    (hubbardHamiltonianOnGraph_isHermitian N G hJ hU) β

/-- The graph-built Hubbard Gibbs state commutes with its Hamiltonian. -/
theorem hubbardGibbsStateOnGraph_commute_hamiltonian
    (N : ℕ) (β : ℝ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (J U : ℂ) :
    Commute (hubbardGibbsStateOnGraph N β G J U)
      (hubbardHamiltonianOnGraph N G J U) :=
  LatticeSystem.Quantum.gibbsState_commute_hamiltonian β _

/-- Bridge: `hubbardChainGibbsState` = `hubbardGibbsStateOnGraph`
on `pathGraph (N+1)` with weight `-J`. -/
theorem hubbardChainGibbsState_eq_onGraph (N : ℕ) (β : ℝ) (J U : ℝ) :
    hubbardChainGibbsState N β J U
      = hubbardGibbsStateOnGraph N β (SimpleGraph.pathGraph (N + 1))
          (-(J : ℂ)) (U : ℂ) :=
  rfl

/-! ## Periodic 1D Hubbard chain (cycleGraph instance) -/

/-- The canonical 1D periodic Hubbard ring on `N + 1` spinful sites,
defined via `hubbardHamiltonianOnGraph` with the cycle graph on
`N + 1` vertices. -/
noncomputable def hubbardCycleHamiltonian (N : ℕ) (J U : ℝ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  hubbardHamiltonianOnGraph N (SimpleGraph.cycleGraph (N + 1))
    (-(J : ℂ)) (U : ℂ)

/-- Hermiticity of the periodic Hubbard chain. -/
theorem hubbardCycleHamiltonian_isHermitian (N : ℕ) (J U : ℝ) :
    (hubbardCycleHamiltonian N J U).IsHermitian :=
  hubbardHamiltonianOnGraph_isHermitian N _ (by simp) (by simp)

/-- Charge conservation for the periodic Hubbard chain. -/
theorem hubbardCycleHamiltonian_commute_fermionTotalNumber
    (N : ℕ) (J U : ℝ) :
    Commute (hubbardCycleHamiltonian N J U)
      (fermionTotalNumber (2 * N + 1)) :=
  hubbardHamiltonianOnGraph_commute_fermionTotalNumber N _ _ _

/-- Gibbs state of the periodic Hubbard chain. -/
noncomputable def hubbardCycleGibbsState (N : ℕ) (β : ℝ) (J U : ℝ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  LatticeSystem.Quantum.gibbsState β (hubbardCycleHamiltonian N J U)

/-- Hermiticity of the periodic Hubbard Gibbs state. -/
theorem hubbardCycleGibbsState_isHermitian (N : ℕ) (β : ℝ) (J U : ℝ) :
    (hubbardCycleGibbsState N β J U).IsHermitian :=
  LatticeSystem.Quantum.gibbsState_isHermitian
    (hubbardCycleHamiltonian_isHermitian N J U) β

/-- The periodic Hubbard Gibbs state commutes with the periodic
Hubbard Hamiltonian. The dual companion of
`hubbardChainGibbsState_commute_hamiltonian` (open chain). -/
theorem hubbardCycleGibbsState_commute_hamiltonian
    (N : ℕ) (β : ℝ) (J U : ℝ) :
    Commute (hubbardCycleGibbsState N β J U)
      (hubbardCycleHamiltonian N J U) :=
  LatticeSystem.Quantum.gibbsState_commute_hamiltonian β
    (hubbardCycleHamiltonian N J U)

/-! ## Periodic Hubbard chain Gibbs expectation companions -/

/-- Infinite-temperature (β = 0) closed form for the periodic
Hubbard expectation. -/
theorem hubbardCycleGibbsExpectation_zero (N : ℕ) (J U : ℝ)
    (A : ManyBodyOp (Fin (2 * N + 2))) :
    LatticeSystem.Quantum.gibbsExpectation 0
        (hubbardCycleHamiltonian N J U) A
      = ((Fintype.card (Fin (2 * N + 2) → Fin 2) : ℂ))⁻¹ *
          A.trace :=
  LatticeSystem.Quantum.gibbsExpectation_zero
    (hubbardCycleHamiltonian N J U) A

/-- For Hermitian `O`, the periodic-Hubbard expectation `⟨O⟩_β`
is real. -/
theorem hubbardCycleGibbsExpectation_im_of_isHermitian
    (N : ℕ) (β J U : ℝ) {O : ManyBodyOp (Fin (2 * N + 2))}
    (hO : O.IsHermitian) :
    (LatticeSystem.Quantum.gibbsExpectation β
        (hubbardCycleHamiltonian N J U) O).im = 0 :=
  LatticeSystem.Quantum.gibbsExpectation_im_of_isHermitian
    (hubbardCycleHamiltonian_isHermitian N J U) hO β

/-- Periodic-Hubbard conservation law: `⟨[H, A]⟩_β = 0`. -/
theorem hubbardCycleGibbsExpectation_commutator_hamiltonian
    (N : ℕ) (β J U : ℝ) (A : ManyBodyOp (Fin (2 * N + 2))) :
    LatticeSystem.Quantum.gibbsExpectation β
        (hubbardCycleHamiltonian N J U)
        (hubbardCycleHamiltonian N J U * A
          - A * hubbardCycleHamiltonian N J U) = 0 :=
  LatticeSystem.Quantum.gibbsExpectation_commutator_hamiltonian β
    (hubbardCycleHamiltonian N J U) A

/-- Periodic-Hubbard energy expectation is real. -/
theorem hubbardCycleGibbsExpectation_hamiltonian_im
    (N : ℕ) (β J U : ℝ) :
    (LatticeSystem.Quantum.gibbsExpectation β
        (hubbardCycleHamiltonian N J U)
        (hubbardCycleHamiltonian N J U)).im = 0 :=
  LatticeSystem.Quantum.gibbsExpectation_hamiltonian_im
    (hubbardCycleHamiltonian_isHermitian N J U) β

/-- Periodic-Hubbard energy n-th power expectation is real. -/
theorem hubbardCycleGibbsExpectation_hamiltonian_pow_im
    (N : ℕ) (β J U : ℝ) (n : ℕ) :
    (LatticeSystem.Quantum.gibbsExpectation β
        (hubbardCycleHamiltonian N J U)
        ((hubbardCycleHamiltonian N J U)^n)).im = 0 :=
  LatticeSystem.Quantum.gibbsExpectation_pow_im_of_isHermitian
    (hubbardCycleHamiltonian_isHermitian N J U)
    (hubbardCycleHamiltonian_isHermitian N J U) β n

/-- Periodic-Hubbard partition function is real. -/
theorem hubbardCycle_partitionFn_im (N : ℕ) (β J U : ℝ) :
    (LatticeSystem.Quantum.partitionFn β
        (hubbardCycleHamiltonian N J U)).im = 0 :=
  LatticeSystem.Quantum.partitionFn_im_of_isHermitian
    (hubbardCycleHamiltonian_isHermitian N J U) β

/-- Periodic-Hubbard real-cast equality. -/
theorem hubbardCycleGibbsExpectation_ofReal_re_eq
    (N : ℕ) (β J U : ℝ) {O : ManyBodyOp (Fin (2 * N + 2))}
    (hO : O.IsHermitian) :
    (((LatticeSystem.Quantum.gibbsExpectation β
        (hubbardCycleHamiltonian N J U) O).re : ℂ))
      = LatticeSystem.Quantum.gibbsExpectation β
          (hubbardCycleHamiltonian N J U) O :=
  LatticeSystem.Quantum.gibbsExpectation_ofReal_re_eq_of_isHermitian
    (hubbardCycleHamiltonian_isHermitian N J U) hO β

/-- Periodic-Hubbard Rényi-n trace identity. -/
theorem hubbardCycleGibbsState_pow_trace
    (N : ℕ) (β J U : ℝ) (n : ℕ) :
    ((hubbardCycleGibbsState N β J U)^n).trace
      = LatticeSystem.Quantum.partitionFn ((n : ℝ) * β)
          (hubbardCycleHamiltonian N J U)
        / (LatticeSystem.Quantum.partitionFn β
            (hubbardCycleHamiltonian N J U)) ^ n :=
  LatticeSystem.Quantum.gibbsState_pow_trace β
    (hubbardCycleHamiltonian N J U) n

end LatticeSystem.Fermion
