/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.ManyBody
import LatticeSystem.Quantum.Pauli
import LatticeSystem.Quantum.GibbsState
import LatticeSystem.Lattice.Graph

/-!
# One-dimensional quantum Ising chain on an open boundary

Given a coupling `J : ℝ`, external field `h : ℝ`, and a chain of `N + 1`
sites, the open-chain quantum Ising Hamiltonian is

```
H = -J Σ_{i=0..N-1} σ^z_i σ^z_{i+1} - h Σ_{i=0..N} σ^x_i.
```

Using the `N + 1` parametrization lets the coupling sum `Σ_{i : Fin N}`
automatically reduce to `0` when there is only a single site, so the
definition is uniform.

The main results of this module are:

* `quantumIsingHamiltonian_isHermitian` — self-adjointness of `H` for
  real parameters `J`, `h`.
* `quantumIsingGibbsState β J h N` and its inherited properties
  (Hermiticity, commutativity with `H`, the β = 0 closed form),
  bridging this concrete chain to the abstract Gibbs framework of
  `GibbsState.lean`. See Tasaki, *Physics and Mathematics of Quantum
  Many-Body Systems*, §3.3, p. 80.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {N : ℕ}

/-! ## Generic (graph-friendly) Ising operators

These mirror the structure of `spinHalfDot` and
`heisenbergHamiltonian`: the bond operator `spinZDot x y` and the
Hamiltonian `isingHamiltonianGeneric J h` work for any finite
vertex type `Λ` with a pairwise coupling `J : Λ → Λ → ℂ`. -/

/-- The Ising bond operator: `σ^z_x · σ^z_y` on the many-body
space. For `x = y` this collapses to `(σ^z_x)^2 = I`; in practical
use one passes a coupling `J` that vanishes on the diagonal (e.g.
`couplingOf G c`). -/
noncomputable def spinZDot {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (x y : Λ) : ManyBodyOp Λ :=
  onSite x pauliZ * onSite y pauliZ

/-- `spinZDot x y` is Hermitian: distinct sites commute, so the
product of two commuting Hermitian matrices is Hermitian; the
`x = y` case is `(σ^z)^2`, also Hermitian. -/
theorem spinZDot_isHermitian {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (x y : Λ) : (spinZDot x y).IsHermitian := by
  by_cases hxy : x = y
  · subst hxy
    have h := onSite_isHermitian x pauliZ_isHermitian
    exact Matrix.IsHermitian.mul_of_commute h h rfl
  · exact Matrix.IsHermitian.mul_of_commute
      (onSite_isHermitian x pauliZ_isHermitian)
      (onSite_isHermitian y pauliZ_isHermitian)
      (onSite_mul_onSite_of_ne hxy pauliZ pauliZ)

/-- The generic Ising Hamiltonian on any finite vertex set `Λ`
with pairwise coupling `J` and uniform transverse field `h`:
`H = Σ_{x,y} J(x,y) σ^z_x σ^z_y − h Σ_x σ^x_x`.
For graph-defined Ising one passes `J = couplingOf G (-c/2)` with
edge weight `c`; the standard chain version corresponds to the
path graph. -/
noncomputable def isingHamiltonianGeneric
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (J : Λ → Λ → ℂ) (h : ℂ) : ManyBodyOp Λ :=
  ∑ x : Λ, ∑ y : Λ, J x y • spinZDot x y - h • ∑ x : Λ, onSite x pauliX

/-- The generic Ising Hamiltonian is Hermitian for entry-wise real
`J` and real `h`. Since each `spinZDot x y` is Hermitian and number
operators commute pairwise, real `J` already suffices (no symmetry
hypothesis needed; the matrix structure absorbs it). -/
theorem isingHamiltonianGeneric_isHermitian
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {J : Λ → Λ → ℂ} (hreal : ∀ x y, star (J x y) = J x y)
    {h : ℂ} (hh : star h = h) :
    (isingHamiltonianGeneric J h).IsHermitian := by
  unfold isingHamiltonianGeneric Matrix.IsHermitian
  rw [Matrix.conjTranspose_sub]
  refine congrArg₂ _ ?_ ?_
  · rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Matrix.conjTranspose_smul, (spinZDot_isHermitian x y).eq, hreal]
  · rw [Matrix.conjTranspose_smul]
    have hsumH : (∑ x : Λ, onSite x pauliX).IsHermitian := by
      classical
      induction (Finset.univ : Finset Λ) using Finset.induction_on with
      | empty => simp [Matrix.IsHermitian]
      | @insert a t hns ih =>
        rw [Finset.sum_insert hns]
        exact Matrix.IsHermitian.add (onSite_isHermitian a pauliX_isHermitian) ih
    rw [hsumH.eq, hh]

/-! ## Graph-centric Ising wrappers -/

/-- The Ising Hamiltonian on a graph `G` with edge weight `J : ℂ`
and uniform transverse field `h : ℂ`:
`H = Σ_{x,y} (couplingOf G J)(x,y) σ^z_x σ^z_y − h Σ_x σ^x_x`.
The symmetric double sum double-counts each undirected edge — same
convention as `heisenbergHamiltonian (couplingOf G J)`. -/
noncomputable def isingHamiltonianOnGraph
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (J h : ℂ) :
    ManyBodyOp Λ :=
  isingHamiltonianGeneric (LatticeSystem.Lattice.couplingOf G J) h

/-- The graph-built Ising Hamiltonian is Hermitian when `J` and
`h` are real. -/
theorem isingHamiltonianOnGraph_isHermitian
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (G : SimpleGraph Λ) [DecidableRel G.Adj] {J h : ℂ}
    (hJ : star J = J) (hh : star h = h) :
    (isingHamiltonianOnGraph G J h).IsHermitian :=
  isingHamiltonianGeneric_isHermitian
    (LatticeSystem.Lattice.couplingOf_real G hJ) hh

/-- The Gibbs state of a graph-built Ising Hamiltonian. -/
noncomputable def isingGibbsStateOnGraph
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (β : ℝ) (J h : ℝ) :
    ManyBodyOp Λ :=
  gibbsState β (isingHamiltonianOnGraph G (J : ℂ) (h : ℂ))

/-- The graph-built Ising Gibbs state is Hermitian. -/
theorem isingGibbsStateOnGraph_isHermitian
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (β : ℝ) (J h : ℝ) :
    (isingGibbsStateOnGraph G β J h).IsHermitian :=
  gibbsState_isHermitian
    (isingHamiltonianOnGraph_isHermitian G (by simp) (by simp)) β

/-- The graph-built Ising Gibbs state commutes with its
Hamiltonian. -/
theorem isingGibbsStateOnGraph_commute_hamiltonian
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (β : ℝ) (J h : ℝ) :
    Commute (isingGibbsStateOnGraph G β J h)
      (isingHamiltonianOnGraph G (J : ℂ) (h : ℂ)) :=
  gibbsState_commute_hamiltonian β _


/-- Site-`i` `σ^z` operator on the `N + 1`-site many-body space. -/
noncomputable def spinZ (N : ℕ) (i : Fin (N + 1)) : ManyBodyOp (Fin (N + 1)) :=
  onSite i pauliZ

/-- Site-`i` `σ^x` operator on the `N + 1`-site many-body space. -/
noncomputable def spinX (N : ℕ) (i : Fin (N + 1)) : ManyBodyOp (Fin (N + 1)) :=
  onSite i pauliX

/-- Each single-site `σ^z` operator is Hermitian. -/
theorem spinZ_isHermitian (i : Fin (N + 1)) : (spinZ N i).IsHermitian :=
  onSite_isHermitian i pauliZ_isHermitian

/-- Each single-site `σ^x` operator is Hermitian. -/
theorem spinX_isHermitian (i : Fin (N + 1)) : (spinX N i).IsHermitian :=
  onSite_isHermitian i pauliX_isHermitian

/-- `i.castSucc` and `i.succ` are distinct elements of `Fin (N + 1)`. -/
theorem castSucc_ne_succ (i : Fin N) :
    (i.castSucc : Fin (N + 1)) ≠ i.succ := by
  intro heq
  have hval : (i.castSucc : Fin (N + 1)).val = (i.succ : Fin (N + 1)).val :=
    congr_arg Fin.val heq
  simp [Fin.castSucc, Fin.succ] at hval

/-- Nearest-neighbour `σ^z` operators at sites `i` and `i+1` commute. -/
theorem spinZ_mul_spinZ_succ_commute (i : Fin N) :
    spinZ N i.castSucc * spinZ N i.succ = spinZ N i.succ * spinZ N i.castSucc :=
  onSite_mul_onSite_of_ne (castSucc_ne_succ i) pauliZ pauliZ

/-- Nearest-neighbour `σ^z σ^z` is Hermitian. -/
theorem spinZ_mul_spinZ_succ_isHermitian (i : Fin N) :
    (spinZ N i.castSucc * spinZ N i.succ).IsHermitian :=
  Matrix.IsHermitian.mul_of_commute
    (spinZ_isHermitian _) (spinZ_isHermitian _) (spinZ_mul_spinZ_succ_commute i)

/-- The quantum Ising Hamiltonian on an open chain of `N + 1` sites. -/
noncomputable def quantumIsingHamiltonian (N : ℕ) (J h : ℝ) :
    ManyBodyOp (Fin (N + 1)) :=
  (-(J : ℂ)) • ∑ i : Fin N, spinZ N i.castSucc * spinZ N i.succ
    + (-(h : ℂ)) • ∑ i : Fin (N + 1), spinX N i

/-! ## Helpers for Hermiticity under sums and real scalar multiples -/

/-- Hermiticity is preserved under finite sums. -/
private lemma isHermitian_sum {ι : Type*} {n : Type*}
    (s : Finset ι) {f : ι → Matrix n n ℂ} (hf : ∀ i ∈ s, (f i).IsHermitian) :
    (∑ i ∈ s, f i).IsHermitian := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.IsHermitian]
  | @insert a t hns ih =>
    rw [Finset.sum_insert hns]
    refine Matrix.IsHermitian.add (hf a (Finset.mem_insert_self a t)) ?_
    exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Hermiticity is preserved under `Finset.univ` sums. -/
private lemma isHermitian_univ_sum {ι : Type*} [Fintype ι] {n : Type*}
    {f : ι → Matrix n n ℂ} (hf : ∀ i, (f i).IsHermitian) :
    (∑ i, f i).IsHermitian :=
  isHermitian_sum Finset.univ (fun i _ => hf i)

/-- Scaling a Hermitian matrix by a real scalar preserves Hermiticity. -/
private lemma isHermitian_smul_real {n : Type*}
    (c : ℝ) {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    ((c : ℂ) • M).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hM]
  congr 1
  simp

/-- The quantum Ising Hamiltonian is Hermitian. -/
theorem quantumIsingHamiltonian_isHermitian (N : ℕ) (J h : ℝ) :
    (quantumIsingHamiltonian N J h).IsHermitian := by
  unfold quantumIsingHamiltonian
  refine Matrix.IsHermitian.add ?_ ?_
  · have hsum : (∑ i : Fin N,
        spinZ N i.castSucc * spinZ N i.succ).IsHermitian :=
      isHermitian_univ_sum (fun i => spinZ_mul_spinZ_succ_isHermitian i)
    have := isHermitian_smul_real (-J) hsum
    simpa using this
  · have hsum : (∑ i : Fin (N + 1), spinX N i).IsHermitian :=
      isHermitian_univ_sum (fun i => spinX_isHermitian i)
    have := isHermitian_smul_real (-h) hsum
    simpa using this

/-! ## Gibbs state for the quantum Ising chain -/

/-- The Gibbs state of the open-boundary 1D quantum Ising chain on
`Fin (N + 1)` sites with real coupling `J`, transverse field `h`, and
inverse temperature `β`. -/
noncomputable def quantumIsingGibbsState (β J h : ℝ) (N : ℕ) :
    ManyBodyOp (Fin (N + 1)) :=
  gibbsState β (quantumIsingHamiltonian N J h)

/-- The Ising-chain Gibbs state is Hermitian. -/
theorem quantumIsingGibbsState_isHermitian (β J h : ℝ) (N : ℕ) :
    (quantumIsingGibbsState β J h N).IsHermitian :=
  gibbsState_isHermitian (quantumIsingHamiltonian_isHermitian N J h) β

/-- The Ising-chain Gibbs state commutes with its Hamiltonian. -/
theorem quantumIsingGibbsState_commute_hamiltonian (β J h : ℝ) (N : ℕ) :
    Commute (quantumIsingGibbsState β J h N) (quantumIsingHamiltonian N J h) :=
  gibbsState_commute_hamiltonian β (quantumIsingHamiltonian N J h)

/-- Infinite-temperature (β = 0) closed form for the Ising-chain
expectation: `⟨A⟩_0 = (1/dim) · Tr A` for any observable `A`,
independent of `J` and `h`. -/
theorem quantumIsingGibbsExpectation_zero (J h : ℝ) (N : ℕ)
    (A : ManyBodyOp (Fin (N + 1))) :
    gibbsExpectation 0 (quantumIsingHamiltonian N J h) A
      = ((Fintype.card (Fin (N + 1) → Fin 2) : ℂ))⁻¹ * A.trace :=
  gibbsExpectation_zero (quantumIsingHamiltonian N J h) A

/-- For any Hermitian observable `O`, the Ising-chain expectation
`⟨O⟩_β` is real (imaginary part vanishes). -/
theorem quantumIsingGibbsExpectation_im_of_isHermitian
    (β J h : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 1))} (hO : O.IsHermitian) :
    (gibbsExpectation β (quantumIsingHamiltonian N J h) O).im = 0 :=
  gibbsExpectation_im_of_isHermitian (quantumIsingHamiltonian_isHermitian N J h) hO β

/-- Ising-chain conservation law: `⟨[H, A]⟩_β = 0`. -/
theorem quantumIsingGibbsExpectation_commutator_hamiltonian
    (β J h : ℝ) (N : ℕ) (A : ManyBodyOp (Fin (N + 1))) :
    gibbsExpectation β (quantumIsingHamiltonian N J h)
        (quantumIsingHamiltonian N J h * A - A * quantumIsingHamiltonian N J h) = 0 :=
  gibbsExpectation_commutator_hamiltonian β (quantumIsingHamiltonian N J h) A

/-- Ising-chain energy expectation is real: `(⟨H_Ising⟩_β).im = 0`. -/
theorem quantumIsingGibbsExpectation_hamiltonian_im (β J h : ℝ) (N : ℕ) :
    (gibbsExpectation β (quantumIsingHamiltonian N J h)
        (quantumIsingHamiltonian N J h)).im = 0 :=
  gibbsExpectation_hamiltonian_im (quantumIsingHamiltonian_isHermitian N J h) β

/-- For Hermitian `O`, the Ising-chain expectation `⟨H_Ising · O⟩_β` is real. -/
theorem quantumIsingGibbsExpectation_mul_hamiltonian_im
    (β J h : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 1))} (hO : O.IsHermitian) :
    (gibbsExpectation β (quantumIsingHamiltonian N J h)
        (quantumIsingHamiltonian N J h * O)).im = 0 :=
  gibbsExpectation_mul_hamiltonian_im (quantumIsingHamiltonian_isHermitian N J h) hO β

/-- Ising-chain energy-squared expectation is real:
`(⟨H_Ising^2⟩_β).im = 0`. -/
theorem quantumIsingGibbsExpectation_hamiltonian_sq_im (β J h : ℝ) (N : ℕ) :
    (gibbsExpectation β (quantumIsingHamiltonian N J h)
        ((quantumIsingHamiltonian N J h)^2)).im = 0 := by
  rw [pow_two]
  exact gibbsExpectation_sq_im_of_isHermitian
    (quantumIsingHamiltonian_isHermitian N J h)
    (quantumIsingHamiltonian_isHermitian N J h) β

/-- Ising-chain energy n-th power expectation is real:
`(⟨H_Ising^n⟩_β).im = 0` for any `n : ℕ`. -/
theorem quantumIsingGibbsExpectation_hamiltonian_pow_im
    (β J h : ℝ) (N : ℕ) (n : ℕ) :
    (gibbsExpectation β (quantumIsingHamiltonian N J h)
        ((quantumIsingHamiltonian N J h)^n)).im = 0 :=
  gibbsExpectation_pow_im_of_isHermitian
    (quantumIsingHamiltonian_isHermitian N J h)
    (quantumIsingHamiltonian_isHermitian N J h) β n

/-- Ising-chain anticommutator expectation is real:
for Hermitian `A, B`, `(⟨A · B + B · A⟩_β).im = 0`. -/
theorem quantumIsingGibbsExpectation_anticommutator_im
    (β J h : ℝ) (N : ℕ) {A B : ManyBodyOp (Fin (N + 1))}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (gibbsExpectation β (quantumIsingHamiltonian N J h)
        (A * B + B * A)).im = 0 :=
  gibbsExpectation_anticommutator_im
    (quantumIsingHamiltonian_isHermitian N J h) hA hB β

/-- Ising-chain commutator expectation is purely imaginary:
for Hermitian `A, B`, `(⟨A · B − B · A⟩_β).re = 0`. -/
theorem quantumIsingGibbsExpectation_commutator_re
    (β J h : ℝ) (N : ℕ) {A B : ManyBodyOp (Fin (N + 1))}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (gibbsExpectation β (quantumIsingHamiltonian N J h)
        (A * B - B * A)).re = 0 :=
  gibbsExpectation_commutator_re
    (quantumIsingHamiltonian_isHermitian N J h) hA hB β

/-- Ising-chain energy expectation as a sum of bond and transverse-field
contributions:
`⟨H_Ising⟩_β = (-J) · ∑ ⟨σ^z_i σ^z_{i+1}⟩_β + (-h) · ∑ ⟨σ^x_i⟩_β`. -/
theorem quantumIsingGibbsExpectation_self_eq (β J h : ℝ) (N : ℕ) :
    gibbsExpectation β (quantumIsingHamiltonian N J h)
        (quantumIsingHamiltonian N J h) =
      (-(J : ℂ)) * (∑ i : Fin N,
          gibbsExpectation β (quantumIsingHamiltonian N J h)
            (spinZ N i.castSucc * spinZ N i.succ))
        + (-(h : ℂ)) * (∑ i : Fin (N + 1),
            gibbsExpectation β (quantumIsingHamiltonian N J h) (spinX N i)) := by
  unfold quantumIsingHamiltonian
  rw [gibbsExpectation_add, gibbsExpectation_smul, gibbsExpectation_sum,
    gibbsExpectation_smul, gibbsExpectation_sum]

/-- Ising-chain energy variance is real: `(Var_β(H_Ising)).im = 0`. -/
theorem quantumIsingGibbsHamiltonianVariance_im (β J h : ℝ) (N : ℕ) :
    (gibbsVariance β (quantumIsingHamiltonian N J h)
        (quantumIsingHamiltonian N J h)).im = 0 :=
  gibbsVariance_im_of_isHermitian
    (quantumIsingHamiltonian_isHermitian N J h)
    (quantumIsingHamiltonian_isHermitian N J h) β

/-- Ising-chain partition function is real:
`(partitionFn β H_Ising).im = 0`. -/
theorem quantumIsing_partitionFn_im (β J h : ℝ) (N : ℕ) :
    (partitionFn β (quantumIsingHamiltonian N J h)).im = 0 :=
  partitionFn_im_of_isHermitian (quantumIsingHamiltonian_isHermitian N J h) β

/-- Ising-chain expectation real-cast equality:
for Hermitian `O`, `((⟨O⟩_β).re : ℂ) = ⟨O⟩_β`. -/
theorem quantumIsingGibbsExpectation_ofReal_re_eq
    (β J h : ℝ) (N : ℕ) {O : ManyBodyOp (Fin (N + 1))} (hO : O.IsHermitian) :
    (((gibbsExpectation β (quantumIsingHamiltonian N J h) O).re : ℂ))
      = gibbsExpectation β (quantumIsingHamiltonian N J h) O :=
  gibbsExpectation_ofReal_re_eq_of_isHermitian
    (quantumIsingHamiltonian_isHermitian N J h) hO β

/-- Ising-chain Rényi-n trace identity:
`Tr(ρ_β^n) = Z(n β) / Z(β)^n`. -/
theorem quantumIsingGibbsState_pow_trace (β J h : ℝ) (N : ℕ) (n : ℕ) :
    ((quantumIsingGibbsState β J h N)^n).trace
      = partitionFn ((n : ℝ) * β) (quantumIsingHamiltonian N J h)
        / (partitionFn β (quantumIsingHamiltonian N J h)) ^ n :=
  gibbsState_pow_trace β (quantumIsingHamiltonian N J h) n

/-! ## Bridge: `quantumIsingHamiltonian` = graph-built Ising on `pathGraph`

Concrete milestone: the N=1 case is proved here. The generic N
bridge `quantumIsingHamiltonian N J h
  = isingHamiltonianGeneric (couplingOf (pathGraph (N+1)) (-J/2)) h`
is deferred to a follow-up PR; the pattern scales but the generic
proof needs an edge-enumeration sum lemma for `pathGraph` that is
currently not in mathlib. -/

/-- **Generic-N bridge**: the \(N+1\)-site open-chain quantum
Ising Hamiltonian equals the graph-built Ising Hamiltonian on
`pathGraph (N+1)` with weight `-J/2`. The factor `1/2` compensates
for the symmetric double-sum convention (each undirected edge
contributes twice in the graph-built version). The proof uses
`sum_pathGraph_adj` to decompose the adjacency double sum into the
edge-indexed single sum, then `spinZ_commute` (i.e. `onSite` at
distinct sites commutes) to identify the two orientations. -/
theorem quantumIsingHamiltonian_eq_isingHamiltonianGeneric
    (N : ℕ) (J h : ℝ) :
    quantumIsingHamiltonian N J h
      = isingHamiltonianGeneric
          (LatticeSystem.Lattice.couplingOf
            (SimpleGraph.pathGraph (N + 1)) (-(J : ℂ) / 2))
          (h : ℂ) := by
  unfold quantumIsingHamiltonian isingHamiltonianGeneric
  -- Decompose the RHS bond sum via the pathGraph adjacency helper.
  have h_bond :
      ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
          LatticeSystem.Lattice.couplingOf (SimpleGraph.pathGraph (N + 1))
            (-(J : ℂ) / 2) x y • spinZDot x y
        = (-(J : ℂ)) • ∑ i : Fin N, spinZ N i.castSucc * spinZ N i.succ := by
    -- couplingOf unfolds to an `if`
    have : ∀ x y : Fin (N + 1),
        LatticeSystem.Lattice.couplingOf (SimpleGraph.pathGraph (N + 1))
          (-(J : ℂ) / 2) x y • spinZDot x y
        = (if (SimpleGraph.pathGraph (N + 1)).Adj x y
           then (-(J : ℂ) / 2) • spinZDot x y else 0) := by
      intro x y
      unfold LatticeSystem.Lattice.couplingOf
      by_cases h : (SimpleGraph.pathGraph (N + 1)).Adj x y
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, zero_smul]
    simp_rw [this]
    rw [LatticeSystem.Lattice.sum_pathGraph_adj]
    -- Σ_i ((-J/2) • spinZDot cs s + (-J/2) • spinZDot s cs)
    -- = Σ_i ((-J/2) • spinZDot cs s + (-J/2) • spinZDot cs s)  (by symmetry)
    -- = Σ_i (-J) • spinZDot cs s
    have h_comm_i : ∀ i : Fin N,
        spinZDot (i.succ : Fin (N+1)) i.castSucc
          = spinZDot i.castSucc i.succ := by
      intro i
      unfold spinZDot
      have h_ne : (i.succ : Fin (N+1)) ≠ i.castSucc := by
        intro heq
        have := congrArg Fin.val heq
        simp [Fin.castSucc, Fin.succ] at this
      exact onSite_mul_onSite_of_ne h_ne pauliZ pauliZ
    simp_rw [h_comm_i]
    -- Goal: Σ_i ((-J/2) • spinZDot cs s + (-J/2) • spinZDot cs s)
    --     = (-J) • Σ_i (spinZ cs * spinZ s)
    have h_combine : ∀ i : Fin N,
        (-(J : ℂ) / 2) • spinZDot i.castSucc i.succ
          + (-(J : ℂ) / 2) • spinZDot i.castSucc i.succ
        = (-(J : ℂ)) • spinZDot i.castSucc i.succ := by
      intro i; rw [← add_smul]; congr 1; ring
    simp_rw [h_combine]
    rw [← Finset.smul_sum]
    rfl
  rw [h_bond]
  -- Now: (-J) • bond + (-h) • Σ spinX = (-J) • bond - h • Σ onSite pauliX
  rw [sub_eq_add_neg]
  congr 1
  change (-(h : ℂ)) • ∑ i : Fin (N + 1), spinX N i
    = -((h : ℂ) • ∑ x : Fin (N + 1), onSite x pauliX)
  simp only [spinX, neg_smul]

/-- N=1 corollary of the generic bridge (PR #185 milestone kept
for direct reference). -/
theorem quantumIsingHamiltonian_one_eq_isingHamiltonianGeneric
    (J h : ℝ) :
    quantumIsingHamiltonian 1 J h
      = isingHamiltonianGeneric
          (LatticeSystem.Lattice.couplingOf
            (SimpleGraph.pathGraph 2) (-(J : ℂ) / 2))
          (h : ℂ) :=
  quantumIsingHamiltonian_eq_isingHamiltonianGeneric 1 J h

/-- Bridge: `quantumIsingGibbsState = isingGibbsStateOnGraph` on
`pathGraph (N+1)` with edge weight `-J/2`. Direct corollary of the
chain Hamiltonian bridge. -/
theorem quantumIsingGibbsState_eq_isingGibbsStateOnGraph
    (β J h : ℝ) (N : ℕ) :
    quantumIsingGibbsState β J h N
      = isingGibbsStateOnGraph (SimpleGraph.pathGraph (N + 1)) β
          (-(J / 2)) h := by
  unfold quantumIsingGibbsState isingGibbsStateOnGraph isingHamiltonianOnGraph
  rw [quantumIsingHamiltonian_eq_isingHamiltonianGeneric]
  congr 1
  · push_cast; ring

/-! ## Periodic Ising chain (cycleGraph) -/

/-- Periodic 1D quantum Ising Hamiltonian on `N + 2` sites, via
`isingHamiltonianOnGraph` with `cycleGraph (N + 2)`. -/
noncomputable def isingCycleHamiltonian (N : ℕ) (J h : ℝ) :
    ManyBodyOp (Fin (N + 2)) :=
  isingHamiltonianOnGraph (SimpleGraph.cycleGraph (N + 2))
    (-(J : ℂ)) (h : ℂ)

/-- Hermiticity of the periodic Ising chain. -/
theorem isingCycleHamiltonian_isHermitian (N : ℕ) (J h : ℝ) :
    (isingCycleHamiltonian N J h).IsHermitian :=
  isingHamiltonianOnGraph_isHermitian _ (by simp) (by simp)

/-- Gibbs state of the periodic Ising chain. -/
noncomputable def isingCycleGibbsState (N : ℕ) (β : ℝ) (J h : ℝ) :
    ManyBodyOp (Fin (N + 2)) :=
  gibbsState β (isingCycleHamiltonian N J h)

/-- Hermiticity of the periodic Ising Gibbs state. -/
theorem isingCycleGibbsState_isHermitian (N : ℕ) (β : ℝ) (J h : ℝ) :
    (isingCycleGibbsState N β J h).IsHermitian :=
  gibbsState_isHermitian (isingCycleHamiltonian_isHermitian N J h) β

/-- The periodic Ising Gibbs state commutes with the periodic Ising
Hamiltonian. The dual companion of `quantumIsingGibbsState_commute_hamiltonian`
(open chain) and `isingGibbsStateOnGraph_commute_hamiltonian` (graph). -/
theorem isingCycleGibbsState_commute_hamiltonian
    (N : ℕ) (β : ℝ) (J h : ℝ) :
    Commute (isingCycleGibbsState N β J h) (isingCycleHamiltonian N J h) :=
  gibbsState_commute_hamiltonian β (isingCycleHamiltonian N J h)

end LatticeSystem.Quantum
