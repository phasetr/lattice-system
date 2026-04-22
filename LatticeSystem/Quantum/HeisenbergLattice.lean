/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.HeisenbergChain
import LatticeSystem.Quantum.GibbsState

/-!
# 2D / 3D Heisenberg lattice models

Extracted from `HeisenbergChain.lean` per refactor plan v4 §3.1
("HeisenbergChain から Lattice (2D / 3D) を分離"): the 2D / 3D
Heisenberg coupling functions and their Gibbs / expectation
machinery do not belong in a "chain" namespace.

This file contains:
- 2D open square-lattice coupling (`squareLatticeCoupling`),
- 2D periodic square-lattice / torus coupling
  (`squareTorusCoupling`),
- 3D open cubic-lattice coupling (`cubicLatticeCoupling`),
- Gibbs states + commute-with-H + Hermiticity for each,
- **Full Gibbs expectation companion family for each variant**
  (parity with the 1D open / periodic chain in
  `HeisenbergChain/Gibbs.lean`): `_GibbsExpectation_zero`,
  `_im_of_isHermitian`, `_commutator_hamiltonian`,
  `_mul_hamiltonian_im`, `_hamiltonian_im`, `_hamiltonian_sq_im`,
  `_hamiltonian_pow_im`, `_anticommutator_im`, `_commutator_re`,
  `_HamiltonianVariance_im`, `_partitionFn_im`,
  `_ofReal_re_eq`, `_GibbsState_pow_trace` (≥ 14 companions × 3
  variants = 42 lemmas total).

(Refactor Phase 2 PR 16 — first HeisenbergChain extraction,
plan v4 §3.1. Phase 3 PR #334 backfilled the missing 33 2D / 3D
companions to reach parity with the 1D variants.)
-/

namespace LatticeSystem.Quantum

open Matrix LatticeSystem.Lattice SimpleGraph

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## 2D square lattice as a box product of path graphs

The standard 2D square lattice on `(N + 1) × (N + 1)` sites with
open boundary conditions is the box product
`pathGraph (N + 1) □ pathGraph (N + 1)` of two path graphs.
Heisenberg Hermiticity follows for free from the graph-centric
framework. -/

/-- Open-boundary 2D square-lattice coupling on
`Fin (N+1) × Fin (N+1)`: returns `-J` on nearest-neighbour bonds of
the box product `pathGraph (N+1) □ pathGraph (N+1)`, zero
otherwise. The negative sign matches Tasaki's ferromagnetic
convention (`J > 0` is ferromagnetic). -/
noncomputable def squareLatticeCoupling (N : ℕ) (J : ℝ) :
    Fin (N + 1) × Fin (N + 1) → Fin (N + 1) × Fin (N + 1) → ℂ :=
  LatticeSystem.Lattice.couplingOf
    (SimpleGraph.pathGraph (N + 1) □ SimpleGraph.pathGraph (N + 1))
    (-(J : ℂ))

/-- The 2D square-lattice Heisenberg Hamiltonian is Hermitian. Free
corollary of `heisenbergHamiltonian_couplingOf_isHermitian`. -/
theorem squareLatticeHeisenberg_isHermitian (N : ℕ) (J : ℝ) :
    (heisenbergHamiltonian (squareLatticeCoupling N J)).IsHermitian :=
  heisenbergHamiltonian_couplingOf_isHermitian _ (by simp)

/-! ## 2D periodic square lattice (torus) as a box product of cycle graphs

The 2D discrete torus on `(N + 2) × (N + 2)` sites is the box
product `cycleGraph (N + 2) □ cycleGraph (N + 2)` of two cycle
graphs. Heisenberg Hermiticity follows for free. -/

/-- Periodic 2D square-lattice (torus) coupling on
`Fin (N + 2) × Fin (N + 2)`: returns `-J` on nearest-neighbour bonds
of the box product `cycleGraph (N+2) □ cycleGraph (N+2)`, zero
otherwise. -/
noncomputable def squareTorusCoupling (N : ℕ) (J : ℝ) :
    Fin (N + 2) × Fin (N + 2) → Fin (N + 2) × Fin (N + 2) → ℂ :=
  LatticeSystem.Lattice.couplingOf
    (SimpleGraph.cycleGraph (N + 2) □ SimpleGraph.cycleGraph (N + 2))
    (-(J : ℂ))

/-- The 2D periodic square-lattice (torus) Heisenberg Hamiltonian
is Hermitian. Free corollary of
`heisenbergHamiltonian_couplingOf_isHermitian`. -/
theorem squareTorusHeisenberg_isHermitian (N : ℕ) (J : ℝ) :
    (heisenbergHamiltonian (squareTorusCoupling N J)).IsHermitian :=
  heisenbergHamiltonian_couplingOf_isHermitian _ (by simp)

/-! ## 3D cubic lattice as a triple box product of path graphs

The standard 3D cubic lattice on `(N + 1)^3` sites with open
boundary conditions is the box product of three path graphs.
Hermiticity of the corresponding Heisenberg Hamiltonian follows
for free. -/

/-- Open-boundary 3D cubic-lattice coupling on
`(Fin (N+1) × Fin (N+1)) × Fin (N+1)`: returns `-J` on
nearest-neighbour bonds of the iterated box product, zero
otherwise. -/
noncomputable def cubicLatticeCoupling (N : ℕ) (J : ℝ) :
    (Fin (N + 1) × Fin (N + 1)) × Fin (N + 1) →
      (Fin (N + 1) × Fin (N + 1)) × Fin (N + 1) → ℂ :=
  LatticeSystem.Lattice.couplingOf
    ((SimpleGraph.pathGraph (N + 1) □ SimpleGraph.pathGraph (N + 1)) □
      SimpleGraph.pathGraph (N + 1))
    (-(J : ℂ))

/-- The 3D cubic-lattice Heisenberg Hamiltonian is Hermitian. Free
corollary of `heisenbergHamiltonian_couplingOf_isHermitian`. -/
theorem cubicLatticeHeisenberg_isHermitian (N : ℕ) (J : ℝ) :
    (heisenbergHamiltonian (cubicLatticeCoupling N J)).IsHermitian :=
  heisenbergHamiltonian_couplingOf_isHermitian _ (by simp)

/-! ## Gibbs states for the 2D / 3D Heisenberg lattices

Each higher-dimensional Heisenberg Hamiltonian inherits its Gibbs
state via the generic `gibbsState β H` constructor; Hermiticity
and commute-with-Hamiltonian follow as one-line corollaries of
`gibbsState_isHermitian` and `gibbsState_commute_hamiltonian`. -/

/-- Gibbs state of the 2D open-boundary square-lattice Heisenberg
Hamiltonian. -/
noncomputable def squareLatticeHeisenbergGibbsState (β J : ℝ) (N : ℕ) :
    ManyBodyOp (Fin (N + 1) × Fin (N + 1)) :=
  gibbsState β (heisenbergHamiltonian (squareLatticeCoupling N J))

/-- Hermiticity of the 2D open-boundary square-lattice Gibbs state. -/
theorem squareLatticeHeisenbergGibbsState_isHermitian (β J : ℝ) (N : ℕ) :
    (squareLatticeHeisenbergGibbsState β J N).IsHermitian :=
  gibbsState_isHermitian (squareLatticeHeisenberg_isHermitian N J) β

/-- The 2D open-boundary square-lattice Gibbs state commutes with
its Hamiltonian. -/
theorem squareLatticeHeisenbergGibbsState_commute_hamiltonian
    (β J : ℝ) (N : ℕ) :
    Commute (squareLatticeHeisenbergGibbsState β J N)
      (heisenbergHamiltonian (squareLatticeCoupling N J)) :=
  gibbsState_commute_hamiltonian β _

/-- Gibbs state of the 2D periodic-boundary square-lattice (torus)
Heisenberg Hamiltonian. -/
noncomputable def squareTorusHeisenbergGibbsState (β J : ℝ) (N : ℕ) :
    ManyBodyOp (Fin (N + 2) × Fin (N + 2)) :=
  gibbsState β (heisenbergHamiltonian (squareTorusCoupling N J))

/-- Hermiticity of the 2D torus Gibbs state. -/
theorem squareTorusHeisenbergGibbsState_isHermitian (β J : ℝ) (N : ℕ) :
    (squareTorusHeisenbergGibbsState β J N).IsHermitian :=
  gibbsState_isHermitian (squareTorusHeisenberg_isHermitian N J) β

/-- The 2D torus Gibbs state commutes with its Hamiltonian. -/
theorem squareTorusHeisenbergGibbsState_commute_hamiltonian
    (β J : ℝ) (N : ℕ) :
    Commute (squareTorusHeisenbergGibbsState β J N)
      (heisenbergHamiltonian (squareTorusCoupling N J)) :=
  gibbsState_commute_hamiltonian β _

/-- Gibbs state of the 3D open-boundary cubic-lattice Heisenberg
Hamiltonian. -/
noncomputable def cubicLatticeHeisenbergGibbsState (β J : ℝ) (N : ℕ) :
    ManyBodyOp ((Fin (N + 1) × Fin (N + 1)) × Fin (N + 1)) :=
  gibbsState β (heisenbergHamiltonian (cubicLatticeCoupling N J))

/-- Hermiticity of the 3D cubic-lattice Gibbs state. -/
theorem cubicLatticeHeisenbergGibbsState_isHermitian (β J : ℝ) (N : ℕ) :
    (cubicLatticeHeisenbergGibbsState β J N).IsHermitian :=
  gibbsState_isHermitian (cubicLatticeHeisenberg_isHermitian N J) β

/-- The 3D cubic-lattice Gibbs state commutes with its Hamiltonian. -/
theorem cubicLatticeHeisenbergGibbsState_commute_hamiltonian
    (β J : ℝ) (N : ℕ) :
    Commute (cubicLatticeHeisenbergGibbsState β J N)
      (heisenbergHamiltonian (cubicLatticeCoupling N J)) :=
  gibbsState_commute_hamiltonian β _

/-! ## Expectation companions for 2D / 3D Heisenberg lattices

Each higher-dimensional Heisenberg Gibbs state inherits the same
expectation-theorem family as the 1D chain via the generic
`gibbsExpectation*` lemmas. -/

/-- 2D open square-lattice Heisenberg energy expectation is real. -/
theorem squareLatticeHeisenbergGibbsExpectation_hamiltonian_im
    (β J : ℝ) (N : ℕ) :
    (gibbsExpectation β
        (heisenbergHamiltonian (squareLatticeCoupling N J))
        (heisenbergHamiltonian (squareLatticeCoupling N J))).im = 0 :=
  gibbsExpectation_hamiltonian_im
    (squareLatticeHeisenberg_isHermitian N J) β

/-- 2D open square-lattice partition function is real. -/
theorem squareLatticeHeisenberg_partitionFn_im (β J : ℝ) (N : ℕ) :
    (partitionFn β
        (heisenbergHamiltonian (squareLatticeCoupling N J))).im = 0 :=
  partitionFn_im_of_isHermitian
    (squareLatticeHeisenberg_isHermitian N J) β

/-- 2D torus Heisenberg energy expectation is real. -/
theorem squareTorusHeisenbergGibbsExpectation_hamiltonian_im
    (β J : ℝ) (N : ℕ) :
    (gibbsExpectation β
        (heisenbergHamiltonian (squareTorusCoupling N J))
        (heisenbergHamiltonian (squareTorusCoupling N J))).im = 0 :=
  gibbsExpectation_hamiltonian_im
    (squareTorusHeisenberg_isHermitian N J) β

/-- 2D torus partition function is real. -/
theorem squareTorusHeisenberg_partitionFn_im (β J : ℝ) (N : ℕ) :
    (partitionFn β
        (heisenbergHamiltonian (squareTorusCoupling N J))).im = 0 :=
  partitionFn_im_of_isHermitian
    (squareTorusHeisenberg_isHermitian N J) β

/-- 3D cubic-lattice Heisenberg energy expectation is real. -/
theorem cubicLatticeHeisenbergGibbsExpectation_hamiltonian_im
    (β J : ℝ) (N : ℕ) :
    (gibbsExpectation β
        (heisenbergHamiltonian (cubicLatticeCoupling N J))
        (heisenbergHamiltonian (cubicLatticeCoupling N J))).im = 0 :=
  gibbsExpectation_hamiltonian_im
    (cubicLatticeHeisenberg_isHermitian N J) β

/-- 3D cubic-lattice partition function is real. -/
theorem cubicLatticeHeisenberg_partitionFn_im (β J : ℝ) (N : ℕ) :
    (partitionFn β
        (heisenbergHamiltonian (cubicLatticeCoupling N J))).im = 0 :=
  partitionFn_im_of_isHermitian
    (cubicLatticeHeisenberg_isHermitian N J) β

/-! ## Full Gibbs expectation companion family — 2D / 3D Heisenberg

Backfilled in Phase 3 PR P3-5 to bring the 2D / 3D variants up to
parity with the 1D open / periodic chain companion families in
`HeisenbergChain/Gibbs.lean`. Each lemma is a 1-line application
of the corresponding generic primitive in
`Quantum/GibbsState.lean` / `Quantum/GibbsState/Covariance.lean`,
demonstrating that the existing generic Gibbs companion API is
comprehensive (#241 deferred item 1; #283 P3-5).
-/

/-! ### 2D square-lattice Heisenberg expectation companions -/

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

/-! ### 2D square-torus Heisenberg expectation companions -/

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

/-! ### 3D cubic-lattice Heisenberg expectation companions -/

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


/-- Every entry of `squareLatticeCoupling N J` is real. -/
theorem squareLatticeCoupling_conj
    (N : ℕ) (J : ℝ) (x y : Fin (N + 1) × Fin (N + 1)) :
    starRingEnd ℂ (squareLatticeCoupling N J x y)
      = squareLatticeCoupling N J x y := by
  apply LatticeSystem.Lattice.couplingOf_real
  change star (-(J : ℂ)) = -(J : ℂ)
  rw [star_neg]
  exact congrArg Neg.neg (Complex.conj_ofReal J)

/-- Every entry of `squareTorusCoupling N J` is real. -/
theorem squareTorusCoupling_conj
    (N : ℕ) (J : ℝ) (x y : Fin (N + 2) × Fin (N + 2)) :
    starRingEnd ℂ (squareTorusCoupling N J x y)
      = squareTorusCoupling N J x y := by
  apply LatticeSystem.Lattice.couplingOf_real
  change star (-(J : ℂ)) = -(J : ℂ)
  rw [star_neg]
  exact congrArg Neg.neg (Complex.conj_ofReal J)

/-- Every entry of `cubicLatticeCoupling N J` is real. -/
theorem cubicLatticeCoupling_conj
    (N : ℕ) (J : ℝ)
    (x y : (Fin (N + 1) × Fin (N + 1)) × Fin (N + 1)) :
    starRingEnd ℂ (cubicLatticeCoupling N J x y)
      = cubicLatticeCoupling N J x y := by
  apply LatticeSystem.Lattice.couplingOf_real
  change star (-(J : ℂ)) = -(J : ℂ)
  rw [star_neg]
  exact congrArg Neg.neg (Complex.conj_ofReal J)

end LatticeSystem.Quantum
