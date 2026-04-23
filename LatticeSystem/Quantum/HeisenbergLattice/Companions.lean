/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.HeisenbergLattice
import LatticeSystem.Quantum.GibbsState.Covariance

/-!
# Full Gibbs expectation companion family — 2D / 3D Heisenberg

Backfilled in Phase 3 PR P3-5 (#334) to bring the 2D / 3D
variants up to parity with the 1D open / periodic chain
companion families in `HeisenbergChain/Gibbs.lean`. Each lemma
is a 1-line application of the corresponding generic primitive
in `Quantum/GibbsState.lean` / `Quantum/GibbsState/Covariance.lean`,
demonstrating that the existing generic Gibbs companion API is
comprehensive (#241 deferred item 1; #283 P3-5).

Extracted from the parent `Quantum/HeisenbergLattice.lean` in
codex audit Item 9 (#388 follow-up): the parent stays as
content (couplings, Hermiticity, basic Gibbs state defs +
`_isHermitian` + `_commute_hamiltonian` + `_partitionFn_im` +
`_GibbsExpectation_hamiltonian_im` + `*Coupling_conj` reality
lemmas), and this sub-file holds the full 33-companion
expectation family (`_zero` / `_im_of_isHermitian` /
`_commutator_hamiltonian` / `_mul_hamiltonian_im` /
`_hamiltonian_sq_im` / `_hamiltonian_pow_im` /
`_anticommutator_im` / `_commutator_re` /
`_HamiltonianVariance_im` / `_ofReal_re_eq` / `_pow_trace`
× 3 variants).
-/

namespace LatticeSystem.Quantum

open Matrix

/-! ## 2D square-lattice Heisenberg expectation companions -/

/-- Infinite-temperature (β = 0) closed form. -/
theorem squareLatticeHeisenbergGibbsExpectation_zero (J : ℝ) (N : ℕ)
    (A : ManyBodyOp (Fin (N + 1) × Fin (N + 1))) :
    gibbsExpectation 0 (heisenbergHamiltonian (squareLatticeCoupling N J)) A
      = ((Fintype.card (Fin (N + 1) × Fin (N + 1) → Fin 2) : ℂ))⁻¹ * A.trace :=
  gibbsExpectation_zero (heisenbergHamiltonian (squareLatticeCoupling N J)) A

/-- For Hermitian `O`, `(⟨O⟩_β).im = 0`. -/
theorem squareLatticeHeisenbergGibbsExpectation_im_of_isHermitian
    (β J : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 1) × Fin (N + 1))}
    (hO : O.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (squareLatticeCoupling N J)) O).im
      = 0 :=
  gibbsExpectation_im_of_isHermitian
    (squareLatticeHeisenberg_isHermitian N J) hO β

/-- Conservation law: `⟨[H, A]⟩_β = 0`. -/
theorem squareLatticeHeisenbergGibbsExpectation_commutator_hamiltonian
    (β J : ℝ) (N : ℕ) (A : ManyBodyOp (Fin (N + 1) × Fin (N + 1))) :
    gibbsExpectation β (heisenbergHamiltonian (squareLatticeCoupling N J))
        (heisenbergHamiltonian (squareLatticeCoupling N J) * A
          - A * heisenbergHamiltonian (squareLatticeCoupling N J)) = 0 :=
  gibbsExpectation_commutator_hamiltonian β
    (heisenbergHamiltonian (squareLatticeCoupling N J)) A

/-- For Hermitian `O`, `(⟨H · O⟩_β).im = 0`. -/
theorem squareLatticeHeisenbergGibbsExpectation_mul_hamiltonian_im
    (β J : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 1) × Fin (N + 1))}
    (hO : O.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (squareLatticeCoupling N J))
        (heisenbergHamiltonian (squareLatticeCoupling N J) * O)).im = 0 :=
  gibbsExpectation_mul_hamiltonian_im
    (squareLatticeHeisenberg_isHermitian N J) hO β

/-- `(⟨H^2⟩_β).im = 0`. -/
theorem squareLatticeHeisenbergGibbsExpectation_hamiltonian_sq_im
    (β J : ℝ) (N : ℕ) :
    (gibbsExpectation β (heisenbergHamiltonian (squareLatticeCoupling N J))
        ((heisenbergHamiltonian (squareLatticeCoupling N J))^2)).im = 0 := by
  rw [pow_two]
  exact gibbsExpectation_sq_im_of_isHermitian
    (squareLatticeHeisenberg_isHermitian N J)
    (squareLatticeHeisenberg_isHermitian N J) β

/-- `(⟨H^n⟩_β).im = 0` for any `n : ℕ`. -/
theorem squareLatticeHeisenbergGibbsExpectation_hamiltonian_pow_im
    (β J : ℝ) (N : ℕ) (n : ℕ) :
    (gibbsExpectation β (heisenbergHamiltonian (squareLatticeCoupling N J))
        ((heisenbergHamiltonian (squareLatticeCoupling N J))^n)).im = 0 :=
  gibbsExpectation_pow_im_of_isHermitian
    (squareLatticeHeisenberg_isHermitian N J)
    (squareLatticeHeisenberg_isHermitian N J) β n

/-- For Hermitian `A, B`, `(⟨A · B + B · A⟩_β).im = 0`. -/
theorem squareLatticeHeisenbergGibbsExpectation_anticommutator_im
    (β J : ℝ) (N : ℕ) {A B : ManyBodyOp (Fin (N + 1) × Fin (N + 1))}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (squareLatticeCoupling N J))
        (A * B + B * A)).im = 0 :=
  gibbsExpectation_anticommutator_im
    (squareLatticeHeisenberg_isHermitian N J) hA hB β

/-- For Hermitian `A, B`, `(⟨A · B − B · A⟩_β).re = 0`. -/
theorem squareLatticeHeisenbergGibbsExpectation_commutator_re
    (β J : ℝ) (N : ℕ) {A B : ManyBodyOp (Fin (N + 1) × Fin (N + 1))}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (squareLatticeCoupling N J))
        (A * B - B * A)).re = 0 :=
  gibbsExpectation_commutator_re
    (squareLatticeHeisenberg_isHermitian N J) hA hB β

/-- Energy variance is real: `(Var_β(H)).im = 0`. -/
theorem squareLatticeHeisenbergGibbsHamiltonianVariance_im
    (β J : ℝ) (N : ℕ) :
    (gibbsVariance β (heisenbergHamiltonian (squareLatticeCoupling N J))
        (heisenbergHamiltonian (squareLatticeCoupling N J))).im = 0 :=
  gibbsVariance_im_of_isHermitian
    (squareLatticeHeisenberg_isHermitian N J)
    (squareLatticeHeisenberg_isHermitian N J) β

/-- For Hermitian `O`, `((⟨O⟩_β).re : ℂ) = ⟨O⟩_β`. -/
theorem squareLatticeHeisenbergGibbsExpectation_ofReal_re_eq
    (β J : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 1) × Fin (N + 1))}
    (hO : O.IsHermitian) :
    (((gibbsExpectation β (heisenbergHamiltonian (squareLatticeCoupling N J)) O).re
        : ℂ))
      = gibbsExpectation β (heisenbergHamiltonian (squareLatticeCoupling N J)) O :=
  gibbsExpectation_ofReal_re_eq_of_isHermitian
    (squareLatticeHeisenberg_isHermitian N J) hO β

/-- Rényi-n trace identity: `Tr(ρ_β^n) = Z(n β) / Z(β)^n`. -/
theorem squareLatticeHeisenbergGibbsState_pow_trace
    (β J : ℝ) (N : ℕ) (n : ℕ) :
    ((squareLatticeHeisenbergGibbsState β J N)^n).trace
      = partitionFn ((n : ℝ) * β)
          (heisenbergHamiltonian (squareLatticeCoupling N J))
        / (partitionFn β
            (heisenbergHamiltonian (squareLatticeCoupling N J))) ^ n :=
  gibbsState_pow_trace β
    (heisenbergHamiltonian (squareLatticeCoupling N J)) n

/-! ## 2D square-torus Heisenberg expectation companions -/

/-- Infinite-temperature (β = 0) closed form. -/
theorem squareTorusHeisenbergGibbsExpectation_zero (J : ℝ) (N : ℕ)
    (A : ManyBodyOp (Fin (N + 2) × Fin (N + 2))) :
    gibbsExpectation 0 (heisenbergHamiltonian (squareTorusCoupling N J)) A
      = ((Fintype.card (Fin (N + 2) × Fin (N + 2) → Fin 2) : ℂ))⁻¹ * A.trace :=
  gibbsExpectation_zero (heisenbergHamiltonian (squareTorusCoupling N J)) A

/-- For Hermitian `O`, `(⟨O⟩_β).im = 0`. -/
theorem squareTorusHeisenbergGibbsExpectation_im_of_isHermitian
    (β J : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 2) × Fin (N + 2))}
    (hO : O.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (squareTorusCoupling N J)) O).im
      = 0 :=
  gibbsExpectation_im_of_isHermitian
    (squareTorusHeisenberg_isHermitian N J) hO β

/-- Conservation law: `⟨[H, A]⟩_β = 0`. -/
theorem squareTorusHeisenbergGibbsExpectation_commutator_hamiltonian
    (β J : ℝ) (N : ℕ) (A : ManyBodyOp (Fin (N + 2) × Fin (N + 2))) :
    gibbsExpectation β (heisenbergHamiltonian (squareTorusCoupling N J))
        (heisenbergHamiltonian (squareTorusCoupling N J) * A
          - A * heisenbergHamiltonian (squareTorusCoupling N J)) = 0 :=
  gibbsExpectation_commutator_hamiltonian β
    (heisenbergHamiltonian (squareTorusCoupling N J)) A

/-- For Hermitian `O`, `(⟨H · O⟩_β).im = 0`. -/
theorem squareTorusHeisenbergGibbsExpectation_mul_hamiltonian_im
    (β J : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 2) × Fin (N + 2))}
    (hO : O.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (squareTorusCoupling N J))
        (heisenbergHamiltonian (squareTorusCoupling N J) * O)).im = 0 :=
  gibbsExpectation_mul_hamiltonian_im
    (squareTorusHeisenberg_isHermitian N J) hO β

/-- `(⟨H^2⟩_β).im = 0`. -/
theorem squareTorusHeisenbergGibbsExpectation_hamiltonian_sq_im
    (β J : ℝ) (N : ℕ) :
    (gibbsExpectation β (heisenbergHamiltonian (squareTorusCoupling N J))
        ((heisenbergHamiltonian (squareTorusCoupling N J))^2)).im = 0 := by
  rw [pow_two]
  exact gibbsExpectation_sq_im_of_isHermitian
    (squareTorusHeisenberg_isHermitian N J)
    (squareTorusHeisenberg_isHermitian N J) β

/-- `(⟨H^n⟩_β).im = 0` for any `n : ℕ`. -/
theorem squareTorusHeisenbergGibbsExpectation_hamiltonian_pow_im
    (β J : ℝ) (N : ℕ) (n : ℕ) :
    (gibbsExpectation β (heisenbergHamiltonian (squareTorusCoupling N J))
        ((heisenbergHamiltonian (squareTorusCoupling N J))^n)).im = 0 :=
  gibbsExpectation_pow_im_of_isHermitian
    (squareTorusHeisenberg_isHermitian N J)
    (squareTorusHeisenberg_isHermitian N J) β n

/-- For Hermitian `A, B`, `(⟨A · B + B · A⟩_β).im = 0`. -/
theorem squareTorusHeisenbergGibbsExpectation_anticommutator_im
    (β J : ℝ) (N : ℕ) {A B : ManyBodyOp (Fin (N + 2) × Fin (N + 2))}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (squareTorusCoupling N J))
        (A * B + B * A)).im = 0 :=
  gibbsExpectation_anticommutator_im
    (squareTorusHeisenberg_isHermitian N J) hA hB β

/-- For Hermitian `A, B`, `(⟨A · B − B · A⟩_β).re = 0`. -/
theorem squareTorusHeisenbergGibbsExpectation_commutator_re
    (β J : ℝ) (N : ℕ) {A B : ManyBodyOp (Fin (N + 2) × Fin (N + 2))}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (squareTorusCoupling N J))
        (A * B - B * A)).re = 0 :=
  gibbsExpectation_commutator_re
    (squareTorusHeisenberg_isHermitian N J) hA hB β

/-- Energy variance is real. -/
theorem squareTorusHeisenbergGibbsHamiltonianVariance_im
    (β J : ℝ) (N : ℕ) :
    (gibbsVariance β (heisenbergHamiltonian (squareTorusCoupling N J))
        (heisenbergHamiltonian (squareTorusCoupling N J))).im = 0 :=
  gibbsVariance_im_of_isHermitian
    (squareTorusHeisenberg_isHermitian N J)
    (squareTorusHeisenberg_isHermitian N J) β

/-- For Hermitian `O`, `((⟨O⟩_β).re : ℂ) = ⟨O⟩_β`. -/
theorem squareTorusHeisenbergGibbsExpectation_ofReal_re_eq
    (β J : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 2) × Fin (N + 2))}
    (hO : O.IsHermitian) :
    (((gibbsExpectation β (heisenbergHamiltonian (squareTorusCoupling N J)) O).re
        : ℂ))
      = gibbsExpectation β (heisenbergHamiltonian (squareTorusCoupling N J)) O :=
  gibbsExpectation_ofReal_re_eq_of_isHermitian
    (squareTorusHeisenberg_isHermitian N J) hO β

/-- Rényi-n trace identity. -/
theorem squareTorusHeisenbergGibbsState_pow_trace
    (β J : ℝ) (N : ℕ) (n : ℕ) :
    ((squareTorusHeisenbergGibbsState β J N)^n).trace
      = partitionFn ((n : ℝ) * β)
          (heisenbergHamiltonian (squareTorusCoupling N J))
        / (partitionFn β
            (heisenbergHamiltonian (squareTorusCoupling N J))) ^ n :=
  gibbsState_pow_trace β
    (heisenbergHamiltonian (squareTorusCoupling N J)) n

/-! ## 3D cubic-lattice Heisenberg expectation companions -/

/-- Infinite-temperature (β = 0) closed form. -/
theorem cubicLatticeHeisenbergGibbsExpectation_zero (J : ℝ) (N : ℕ)
    (A : ManyBodyOp ((Fin (N + 1) × Fin (N + 1)) × Fin (N + 1))) :
    gibbsExpectation 0 (heisenbergHamiltonian (cubicLatticeCoupling N J)) A
      = ((Fintype.card
            ((Fin (N + 1) × Fin (N + 1)) × Fin (N + 1) → Fin 2) : ℂ))⁻¹
          * A.trace :=
  gibbsExpectation_zero (heisenbergHamiltonian (cubicLatticeCoupling N J)) A

/-- For Hermitian `O`, `(⟨O⟩_β).im = 0`. -/
theorem cubicLatticeHeisenbergGibbsExpectation_im_of_isHermitian
    (β J : ℝ) (N : ℕ)
    {O : ManyBodyOp ((Fin (N + 1) × Fin (N + 1)) × Fin (N + 1))}
    (hO : O.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (cubicLatticeCoupling N J)) O).im
      = 0 :=
  gibbsExpectation_im_of_isHermitian
    (cubicLatticeHeisenberg_isHermitian N J) hO β

/-- Conservation law: `⟨[H, A]⟩_β = 0`. -/
theorem cubicLatticeHeisenbergGibbsExpectation_commutator_hamiltonian
    (β J : ℝ) (N : ℕ)
    (A : ManyBodyOp ((Fin (N + 1) × Fin (N + 1)) × Fin (N + 1))) :
    gibbsExpectation β (heisenbergHamiltonian (cubicLatticeCoupling N J))
        (heisenbergHamiltonian (cubicLatticeCoupling N J) * A
          - A * heisenbergHamiltonian (cubicLatticeCoupling N J)) = 0 :=
  gibbsExpectation_commutator_hamiltonian β
    (heisenbergHamiltonian (cubicLatticeCoupling N J)) A

/-- For Hermitian `O`, `(⟨H · O⟩_β).im = 0`. -/
theorem cubicLatticeHeisenbergGibbsExpectation_mul_hamiltonian_im
    (β J : ℝ) (N : ℕ)
    {O : ManyBodyOp ((Fin (N + 1) × Fin (N + 1)) × Fin (N + 1))}
    (hO : O.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (cubicLatticeCoupling N J))
        (heisenbergHamiltonian (cubicLatticeCoupling N J) * O)).im = 0 :=
  gibbsExpectation_mul_hamiltonian_im
    (cubicLatticeHeisenberg_isHermitian N J) hO β

/-- `(⟨H^2⟩_β).im = 0`. -/
theorem cubicLatticeHeisenbergGibbsExpectation_hamiltonian_sq_im
    (β J : ℝ) (N : ℕ) :
    (gibbsExpectation β (heisenbergHamiltonian (cubicLatticeCoupling N J))
        ((heisenbergHamiltonian (cubicLatticeCoupling N J))^2)).im = 0 := by
  rw [pow_two]
  exact gibbsExpectation_sq_im_of_isHermitian
    (cubicLatticeHeisenberg_isHermitian N J)
    (cubicLatticeHeisenberg_isHermitian N J) β

/-- `(⟨H^n⟩_β).im = 0` for any `n : ℕ`. -/
theorem cubicLatticeHeisenbergGibbsExpectation_hamiltonian_pow_im
    (β J : ℝ) (N : ℕ) (n : ℕ) :
    (gibbsExpectation β (heisenbergHamiltonian (cubicLatticeCoupling N J))
        ((heisenbergHamiltonian (cubicLatticeCoupling N J))^n)).im = 0 :=
  gibbsExpectation_pow_im_of_isHermitian
    (cubicLatticeHeisenberg_isHermitian N J)
    (cubicLatticeHeisenberg_isHermitian N J) β n

/-- For Hermitian `A, B`, `(⟨A · B + B · A⟩_β).im = 0`. -/
theorem cubicLatticeHeisenbergGibbsExpectation_anticommutator_im
    (β J : ℝ) (N : ℕ)
    {A B : ManyBodyOp ((Fin (N + 1) × Fin (N + 1)) × Fin (N + 1))}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (cubicLatticeCoupling N J))
        (A * B + B * A)).im = 0 :=
  gibbsExpectation_anticommutator_im
    (cubicLatticeHeisenberg_isHermitian N J) hA hB β

/-- For Hermitian `A, B`, `(⟨A · B − B · A⟩_β).re = 0`. -/
theorem cubicLatticeHeisenbergGibbsExpectation_commutator_re
    (β J : ℝ) (N : ℕ)
    {A B : ManyBodyOp ((Fin (N + 1) × Fin (N + 1)) × Fin (N + 1))}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (gibbsExpectation β (heisenbergHamiltonian (cubicLatticeCoupling N J))
        (A * B - B * A)).re = 0 :=
  gibbsExpectation_commutator_re
    (cubicLatticeHeisenberg_isHermitian N J) hA hB β

/-- Energy variance is real. -/
theorem cubicLatticeHeisenbergGibbsHamiltonianVariance_im
    (β J : ℝ) (N : ℕ) :
    (gibbsVariance β (heisenbergHamiltonian (cubicLatticeCoupling N J))
        (heisenbergHamiltonian (cubicLatticeCoupling N J))).im = 0 :=
  gibbsVariance_im_of_isHermitian
    (cubicLatticeHeisenberg_isHermitian N J)
    (cubicLatticeHeisenberg_isHermitian N J) β

/-- For Hermitian `O`, `((⟨O⟩_β).re : ℂ) = ⟨O⟩_β`. -/
theorem cubicLatticeHeisenbergGibbsExpectation_ofReal_re_eq
    (β J : ℝ) (N : ℕ)
    {O : ManyBodyOp ((Fin (N + 1) × Fin (N + 1)) × Fin (N + 1))}
    (hO : O.IsHermitian) :
    (((gibbsExpectation β (heisenbergHamiltonian (cubicLatticeCoupling N J)) O).re
        : ℂ))
      = gibbsExpectation β (heisenbergHamiltonian (cubicLatticeCoupling N J)) O :=
  gibbsExpectation_ofReal_re_eq_of_isHermitian
    (cubicLatticeHeisenberg_isHermitian N J) hO β

/-- Rényi-n trace identity. -/
theorem cubicLatticeHeisenbergGibbsState_pow_trace
    (β J : ℝ) (N : ℕ) (n : ℕ) :
    ((cubicLatticeHeisenbergGibbsState β J N)^n).trace
      = partitionFn ((n : ℝ) * β)
          (heisenbergHamiltonian (cubicLatticeCoupling N J))
        / (partitionFn β
            (heisenbergHamiltonian (cubicLatticeCoupling N J))) ^ n :=
  gibbsState_pow_trace β
    (heisenbergHamiltonian (cubicLatticeCoupling N J)) n

end LatticeSystem.Quantum
