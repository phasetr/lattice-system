import LatticeSystem.Fermion.JordanWigner.Hubbard.HardcoreSubspace
import LatticeSystem.Fermion.JordanWigner.Hubbard.DoubleOccupancyCommute
import LatticeSystem.Math.MatrixAnalysis.NoncommProd

/-!
# Hubbard hard-core projection

This file continues the Tasaki §11.2 Nagaoka-ferromagnetism infrastructure
started in `HardcoreSubspace.lean`. It builds the hard-core projection: the
operator product

  `P̂_hc = ∏ᵢ (1 - n_{i,↑} n_{i,↓})`

over all spinful sites `i`, where each factor `1 - n_{i,↑} n_{i,↓}` projects
out the doubly-occupied configuration at site `i`. The same-site
double-occupancy operators are pairwise commuting idempotents
(`fermionUpNumber_mul_fermionDownNumber_sq`,
`fermionUpNumber_mul_fermionDownNumber_commute`), so the factors are
pairwise commuting idempotents and the product is a well-defined projection.

The projection lands in the hard-core subspace
(`hubbardHardcoreSubspace`), fixes every hard-core vector, and is idempotent.
Each same-site double-occupancy operator annihilates the product, which is the
operator-level no-double-occupancy statement consumed by the one-hole basis
and effective Hamiltonian layers.

Tracked in Issue #4130. References: Tasaki, *Physics and Mathematics of
Quantum Many-Body Systems*, 1st edition, §11.2, pp. 381-388; this file
formalizes unnumbered no-double-occupancy infrastructure used before
Theorems 11.5 and 11.7.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-! ## The hard-core factor `1 - n_{i,↑} n_{i,↓}`

The generic `Finset.noncommProd` helpers used below
(`Matrix.noncommProd_isHermitian`, `Matrix.noncommProd_mul_self_of_idempotent`,
`Matrix.noncommProd_mulVec_eq_self`) live in `Math/MatrixAnalysis/NoncommProd.lean`. -/

/-- The single-site hard-core factor `1 - n_{i,↑} n_{i,↓}` at spinful site
`i`: the complementary projection that annihilates the doubly-occupied
configuration at site `i` and fixes every other site configuration. -/
noncomputable def hubbardHardcoreFactor (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  1 - hubbardDoubleOccupancy N i

/-- The hard-core factor is idempotent: `(1 - n_{i,↑} n_{i,↓})² =
1 - n_{i,↑} n_{i,↓}`, since the double-occupancy operator is idempotent. -/
theorem hubbardHardcoreFactor_mul_self (N : ℕ) (i : Fin (N + 1)) :
    hubbardHardcoreFactor N i * hubbardHardcoreFactor N i =
      hubbardHardcoreFactor N i := by
  have hsq : hubbardDoubleOccupancy N i * hubbardDoubleOccupancy N i =
      hubbardDoubleOccupancy N i := by
    unfold hubbardDoubleOccupancy
    exact fermionUpNumber_mul_fermionDownNumber_sq N i
  unfold hubbardHardcoreFactor
  rw [sub_mul, one_mul, mul_sub, mul_one, hsq, sub_self, sub_zero]

/-- The double-occupancy operator annihilates its own hard-core factor:
`n_{i,↑} n_{i,↓} · (1 - n_{i,↑} n_{i,↓}) = 0`. -/
theorem hubbardDoubleOccupancy_mul_hardcoreFactor (N : ℕ) (i : Fin (N + 1)) :
    hubbardDoubleOccupancy N i * hubbardHardcoreFactor N i = 0 := by
  have hsq : hubbardDoubleOccupancy N i * hubbardDoubleOccupancy N i =
      hubbardDoubleOccupancy N i := by
    unfold hubbardDoubleOccupancy
    exact fermionUpNumber_mul_fermionDownNumber_sq N i
  unfold hubbardHardcoreFactor
  rw [mul_sub, mul_one, hsq, sub_self]

/-- The same-site double-occupancy operator `n_{i,↑} n_{i,↓}` is Hermitian:
it is the product of two commuting Hermitian number operators. -/
theorem hubbardDoubleOccupancy_isHermitian (N : ℕ) (i : Fin (N + 1)) :
    (hubbardDoubleOccupancy N i).IsHermitian := by
  unfold hubbardDoubleOccupancy fermionUpNumber fermionDownNumber
  exact fermionMultiNumber_mul_isHermitian (2 * N + 1)
    (spinfulIndex N i 0) (spinfulIndex N i 1)

/-- The hard-core factor `1 - n_{i,↑} n_{i,↓}` is Hermitian. -/
theorem hubbardHardcoreFactor_isHermitian (N : ℕ) (i : Fin (N + 1)) :
    (hubbardHardcoreFactor N i).IsHermitian := by
  unfold hubbardHardcoreFactor
  exact Matrix.isHermitian_one.sub (hubbardDoubleOccupancy_isHermitian N i)

/-- Hard-core factors for distinct (or equal) sites commute, inherited from
the cross-site commutativity of the double-occupancy operators. -/
theorem hubbardHardcoreFactor_commute (N : ℕ) (i j : Fin (N + 1)) :
    Commute (hubbardHardcoreFactor N i) (hubbardHardcoreFactor N j) := by
  have h : Commute (hubbardDoubleOccupancy N i) (hubbardDoubleOccupancy N j) := by
    unfold hubbardDoubleOccupancy
    exact fermionUpNumber_mul_fermionDownNumber_commute N i j
  unfold hubbardHardcoreFactor
  exact (Commute.one_left _).sub_left
    ((Commute.one_right _).sub_right h)

/-- A hard-core vector is fixed by every hard-core factor:
`(1 - n_{i,↑} n_{i,↓}) · ψ = ψ` when `ψ ∈ hubbardHardcoreSubspace`. -/
theorem hubbardHardcoreFactor_mulVec_eq_self_of_mem
    (N : ℕ) {ψ : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hψ : ψ ∈ hubbardHardcoreSubspace N) (i : Fin (N + 1)) :
    (hubbardHardcoreFactor N i).mulVec ψ = ψ := by
  unfold hubbardHardcoreFactor
  rw [Matrix.sub_mulVec, Matrix.one_mulVec,
    hubbardDoubleOccupancy_mulVec_eq_zero_of_mem_hardcore N hψ i, sub_zero]

/-! ## The hard-core projection -/

/-- The finite-volume Hubbard hard-core projection
`P̂_hc = ∏ᵢ (1 - n_{i,↑} n_{i,↓})`, the non-commutative product of the
pairwise-commuting hard-core factors over all spinful sites. It projects onto
the no-double-occupancy (hard-core) subspace used in the infinite-`U` /
one-hole Nagaoka sector. -/
noncomputable def hubbardHardcoreProjection (N : ℕ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  (Finset.univ : Finset (Fin (N + 1))).noncommProd
    (fun i => hubbardHardcoreFactor N i)
    (fun i _ j _ _ => hubbardHardcoreFactor_commute N i j)

/-- The hard-core projection is idempotent: `P̂_hc² = P̂_hc`. -/
theorem hubbardHardcoreProjection_mul_self (N : ℕ) :
    hubbardHardcoreProjection N * hubbardHardcoreProjection N =
      hubbardHardcoreProjection N := by
  unfold hubbardHardcoreProjection
  exact Matrix.noncommProd_mul_self_of_idempotent _ _ _
    (fun i _ => hubbardHardcoreFactor_mul_self N i)

/-- The hard-core projection is Hermitian: it is a non-commutative product
of pairwise-commuting Hermitian factors. -/
theorem hubbardHardcoreProjection_isHermitian (N : ℕ) :
    (hubbardHardcoreProjection N).IsHermitian := by
  unfold hubbardHardcoreProjection
  exact Matrix.noncommProd_isHermitian _ _ _
    (fun i _ => hubbardHardcoreFactor_isHermitian N i)

/-- Each same-site double-occupancy operator annihilates the hard-core
projection: `n_{j,↑} n_{j,↓} · P̂_hc = 0`. This is the operator-level
no-double-occupancy statement: the projection extracts the hard-core
component. -/
theorem hubbardDoubleOccupancy_mul_hardcoreProjection
    (N : ℕ) (j : Fin (N + 1)) :
    hubbardDoubleOccupancy N j * hubbardHardcoreProjection N = 0 := by
  have hmem : j ∈ (Finset.univ : Finset (Fin (N + 1))) := Finset.mem_univ j
  unfold hubbardHardcoreProjection
  rw [← Finset.mul_noncommProd_erase Finset.univ hmem
        (fun i => hubbardHardcoreFactor N i)
        (fun i _ j _ _ => hubbardHardcoreFactor_commute N i j),
    ← Matrix.mul_assoc, hubbardDoubleOccupancy_mul_hardcoreFactor,
    Matrix.zero_mul]

/-- A hard-core vector is fixed by the hard-core projection:
`P̂_hc · ψ = ψ` when `ψ ∈ hubbardHardcoreSubspace`. -/
theorem hubbardHardcoreProjection_mulVec_eq_self_of_mem
    (N : ℕ) {ψ : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hψ : ψ ∈ hubbardHardcoreSubspace N) :
    (hubbardHardcoreProjection N).mulVec ψ = ψ := by
  unfold hubbardHardcoreProjection
  exact Matrix.noncommProd_mulVec_eq_self _ _ _ ψ
    (fun i _ => hubbardHardcoreFactor_mulVec_eq_self_of_mem N hψ i)

/-- The hard-core projection lands in the hard-core subspace: every
same-site double-occupancy operator annihilates `P̂_hc · ψ`. -/
theorem hubbardHardcoreProjection_mulVec_mem
    (N : ℕ) (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    (hubbardHardcoreProjection N).mulVec ψ ∈ hubbardHardcoreSubspace N := by
  rw [mem_hubbardHardcoreSubspace_iff]
  intro j
  rw [Matrix.mulVec_mulVec, hubbardDoubleOccupancy_mul_hardcoreProjection,
    Matrix.zero_mulVec]

end LatticeSystem.Fermion
