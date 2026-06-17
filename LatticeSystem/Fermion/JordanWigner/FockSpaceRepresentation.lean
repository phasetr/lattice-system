import LatticeSystem.Fermion.JWAbstract
import LatticeSystem.Fermion.JWAbstractCrossSite
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Fock space representation of tight-binding electrons (Tasaki §9.2.3)

This file sets up the second-quantized (Fock space) representation of
the Slater determinant states used throughout Part III of

  Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer (2020), §9.2.3, pp. 314–321.

We work with the concrete Jordan–Wigner representation already developed
in `LatticeSystem.Fermion.JWAbstract`, where for a finite, linearly
ordered mode-index type `Λ` the smeared creation operator

  `Ĉ†(φ) = Σ_x φ(x) ĉ†_x`               (Tasaki eq. (9.2.46))

acts on the many-body space `(Λ → Fin 2) → ℂ`. The Slater determinant
state of single-electron wave functions `φ⁽¹⁾, …, φ⁽ᴺ⁾` is

  `|Φ⟩ = Ĉ†(φ⁽¹⁾) ⋯ Ĉ†(φ⁽ᴺ⁾) |Φvac⟩`.   (Tasaki eq. (9.2.52))

## Main results

* `fermionCreationFromVector`, `slaterState` — the smeared creation
  operator and the Slater determinant state.
* `lemma_9_1_slater_inner_det` — **Tasaki Lemma 9.1** (p. 319, eq.
  (9.2.53)): the inner product of two Slater determinant states equals
  the determinant of the single-particle overlap (Gram) matrix.
* `lemma_9_1_slater_inner_perm_sum` — the explicit permutation-sum form
  of eq. (9.2.53), derived from `lemma_9_1_slater_inner_det`.
* `lemma_9_2_slater_ne_zero_iff_linearIndependent` — **Tasaki Lemma 9.2**
  (p. 320): the Slater determinant state is nonvanishing iff its
  single-electron wave functions are linearly independent.
* `lemma_9_3_slater_proportional_of_span_eq` — **Tasaki Lemma 9.3**
  (p. 320–321): two Slater determinant states built from families
  spanning the same subspace are proportional by a nonzero constant.

## Status of Lemma 9.1

Tasaki's Lemma 9.1 is the determinant overlap identity for Slater
states. In the concrete Jordan–Wigner representation it is a
finite-dimensional linear-algebra statement, and it is **proved here
sorry-free** (`lemma_9_1_slater_inner_det`). The proof moves the
creation operators from the bra to the ket as smeared annihilation
operators (the adjoint `(Ĉ†(φ))ᴴ = Ĉ(φ*)`), then anticommutes the
resulting annihilation operator through the ket's creation string via
the smeared canonical anticommutation relations, killing the vacuum at
the end. This yields exactly the row-0 cofactor (Laplace) expansion of
the Gram determinant, so the result follows by induction on the number
of electrons together with `Matrix.det_succ_row_zero`. The `n = 0`
instance is `fockInner_vacuum_self`. The downstream Lemmas 9.2 and 9.3
are proved from this identity.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators ComplexOrder

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [LinearOrder Λ]

/-- The Jordan–Wigner Fock vacuum `|Φvac⟩`: the all-empty
computational-basis configuration `(fun _ => 0)` (Tasaki §9.2.3,
p. 314). It is annihilated by every `ĉ_x`. -/
noncomputable def fermionVacuumAbstract : (Λ → Fin 2) → ℂ :=
  basisVec (fun _ : Λ => (0 : Fin 2))

/-- The smeared creation operator `Ĉ†(φ) = Σ_x φ(x) ĉ†_x`
(Tasaki eq. (9.2.46), p. 313). -/
noncomputable def fermionCreationFromVector (φ : Λ → ℂ) : ManyBodyOp Λ :=
  ∑ x : Λ, φ x • fermionCreationAbstract x

/-- The smeared annihilation operator `Ĉ(φ) = Σ_x φ(x)* ĉ_x` written
without the conjugation on the coefficients, i.e. `Σ_x φ(x) ĉ_x`; the
physical `Ĉ(φ)` is obtained by feeding the conjugated vector. We keep
the linear (un-conjugated) form here for algebraic convenience
(Tasaki eq. (9.2.46), p. 313). -/
noncomputable def fermionAnnihilationFromVector (φ : Λ → ℂ) : ManyBodyOp Λ :=
  ∑ x : Λ, φ x • fermionAnnihilationAbstract x

/-- The Fock-space inner product `⟨v, w⟩ = Σ_τ v(τ)* w(τ)` of two
many-body vectors. -/
noncomputable def fockInner (v w : (Λ → Fin 2) → ℂ) : ℂ :=
  dotProduct (star v) w

/-- The single-electron overlap `⟨φ, ψ⟩ = Σ_x φ(x)* ψ(x)`
(Tasaki eq. (9.2.53) entries). -/
noncomputable def singleParticleInner (φ ψ : Λ → ℂ) : ℂ :=
  ∑ x : Λ, star (φ x) * ψ x

/-- The Slater determinant state `|Φ⟩ = Ĉ†(φ⁽¹⁾) ⋯ Ĉ†(φ⁽ᴺ⁾) |Φvac⟩`
(Tasaki eq. (9.2.52), p. 319). The creation operators are applied in
list order via an ordered `List.prod`, since matrix multiplication is
noncommutative. -/
noncomputable def slaterState (φs : List (Λ → ℂ)) : (Λ → Fin 2) → ℂ :=
  ((φs.map fermionCreationFromVector).prod).mulVec fermionVacuumAbstract

/-- The single-particle overlap (Gram) matrix
`(G)_{j,k} = ⟨φ⁽ʲ⁾, ψ⁽ᵏ⁾⟩` of Tasaki eq. (9.2.53). -/
noncomputable def slaterGram {n : ℕ} (φ ψ : Fin n → Λ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun j k => singleParticleInner (φ j) (ψ k)

/-- The empty Slater state is the vacuum: `|Φ⟩ = |Φvac⟩` when there are
no creation operators (the `n = 0` case of eq. (9.2.52)). -/
@[simp]
theorem slaterState_nil :
    slaterState ([] : List (Λ → ℂ)) = fermionVacuumAbstract := by
  unfold slaterState
  rw [List.map_nil, List.prod_nil, Matrix.one_mulVec]

omit [LinearOrder Λ] in
/-- The Fock vacuum is normalized: `⟨Φvac, Φvac⟩ = 1`. This is the
`n = 0` instance of Lemma 9.1 (the determinant of the empty Gram matrix
is `1`), proved independently as a consistency guard for the axiom
`lemma_9_1_slater_inner_det`. -/
theorem fockInner_vacuum_self :
    fockInner (Λ := Λ) fermionVacuumAbstract fermionVacuumAbstract = 1 := by
  unfold fockInner fermionVacuumAbstract dotProduct
  have hstar : ∀ τ : Λ → Fin 2,
      star (basisVec (fun _ : Λ => (0 : Fin 2)) τ)
        = basisVec (fun _ : Λ => (0 : Fin 2)) τ := by
    intro τ
    rw [basisVec_apply]
    split <;> simp
  simp_rw [Pi.star_apply, hstar]
  rw [basisVec_inner]
  simp

/-! ### Algebraic core of Lemma 9.1

The following `private` helpers prove the smeared canonical
anticommutation relations and the vacuum-killing identity needed for the
induction proof of Lemma 9.1. They are stated for the smeared operators
`Ĉ(φ)` / `Ĉ†(ψ)` and reduce to the per-site CAR from
`LatticeSystem.Fermion.JWAbstract` /
`LatticeSystem.Fermion.JWAbstractCrossSite`. (The public companions live
in `LatticeSystem.Fermion.JordanWigner.SmearedCAR`, which imports this
file; we keep `private` copies here to avoid an import cycle.) -/

omit [LinearOrder Λ] in
/-- Expansion of the anticommutator of two coefficient-weighted operator
sums into a weighted double sum of per-pair anticommutators (algebraic
core of the smeared CAR). -/
private lemma sumSmulAnticommEqDoubleSum
    (φ ψ : Λ → ℂ) (f g : Λ → ManyBodyOp Λ) :
    (∑ x : Λ, φ x • f x) * (∑ y : Λ, ψ y • g y) +
        (∑ y : Λ, ψ y • g y) * (∑ x : Λ, φ x • f x)
      = ∑ x : Λ, ∑ y : Λ, (φ x * ψ y) • (f x * g y + g y * f x) := by
  have hST : (∑ x : Λ, φ x • f x) * (∑ y : Λ, ψ y • g y)
      = ∑ x : Λ, ∑ y : Λ, (φ x * ψ y) • (f x * g y) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hTS : (∑ y : Λ, ψ y • g y) * (∑ x : Λ, φ x • f x)
      = ∑ x : Λ, ∑ y : Λ, (φ x * ψ y) • (g y * f x) := by
    rw [Finset.sum_mul]
    rw [show (∑ y : Λ, (ψ y • g y) * ∑ x : Λ, φ x • f x)
        = ∑ y : Λ, ∑ x : Λ, (φ x * ψ y) • (g y * f x) from by
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm (ψ y) (φ x)]]
    rw [Finset.sum_comm]
  rw [hST, hTS, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_add]

/-- **Smeared mixed CAR** (Tasaki §9.2.3, p. 313): `Ĉ(φ) Ĉ†(ψ) +
Ĉ†(ψ) Ĉ(φ) = (Σ_x φ(x) ψ(x)) · 1`. `private` copy used by Lemma 9.1. -/
private theorem fermionFromVectorAnticommMixed (φ ψ : Λ → ℂ) :
    fermionAnnihilationFromVector φ * fermionCreationFromVector ψ +
        fermionCreationFromVector ψ * fermionAnnihilationFromVector φ
      = (∑ x : Λ, φ x * ψ x) • (1 : ManyBodyOp Λ) := by
  unfold fermionAnnihilationFromVector fermionCreationFromVector
  rw [sumSmulAnticommEqDoubleSum φ ψ fermionAnnihilationAbstract
    fermionCreationAbstract]
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x]
  · rw [fermionMultiAnticommAbstract_self]
  · intro y _ hyx
    rw [fermionAnnihilationAbstract_creation_anticomm_of_ne (Ne.symm hyx),
      smul_zero]
  · intro hx; exact absurd (Finset.mem_univ x) hx

/-- **Smeared annihilation vacuum-killing** (Tasaki §9.2.3, p. 314):
`Ĉ(φ) |Φvac⟩ = 0`. `private` copy used by Lemma 9.1. -/
private theorem fermionAnnihilationFromVectorMulVecVacuum (φ : Λ → ℂ) :
    (fermionAnnihilationFromVector φ).mulVec
        (fermionVacuumAbstract : (Λ → Fin 2) → ℂ) = 0 := by
  have hsite : ∀ x : Λ, (fermionAnnihilationAbstract x).mulVec
      (fermionVacuumAbstract : (Λ → Fin 2) → ℂ) = 0 := by
    intro x
    unfold fermionAnnihilationAbstract fermionVacuumAbstract
    rw [← Matrix.mulVec_mulVec, onSite_mulVec_basisVec]
    have hzero : (fun τ : Λ → Fin 2 =>
        ∑ k : Fin 2, spinHalfOpPlus k ((fun _ : Λ => (0 : Fin 2)) x) *
          basisVec (Function.update (fun _ : Λ => (0 : Fin 2)) x k) τ)
        = (0 : (Λ → Fin 2) → ℂ) := by
      funext τ
      refine Finset.sum_eq_zero fun k _ => ?_
      have : spinHalfOpPlus k (0 : Fin 2) = 0 := by
        fin_cases k <;> simp [spinHalfOpPlus]
      rw [this, zero_mul]
    rw [hzero, Matrix.mulVec_zero]
  unfold fermionAnnihilationFromVector
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Matrix.smul_mulVec, hsite x, smul_zero]

/-- The Slater state of a cons list factors as one creation operator
acting on the Slater state of the tail:
`|Φ_{a :: φs}⟩ = Ĉ†(a) |Φ_{φs}⟩`. -/
private theorem slaterState_cons (a : Λ → ℂ) (φs : List (Λ → ℂ)) :
    slaterState (a :: φs)
      = (fermionCreationFromVector a).mulVec (slaterState φs) := by
  unfold slaterState
  rw [List.map_cons, List.prod_cons, Matrix.mulVec_mulVec]

/-- `(Ĉ†(φ))ᴴ = Ĉ(φ*)`: the adjoint of the smeared creation operator is
the smeared annihilation operator of the conjugated wave function. -/
private theorem fermionCreationFromVector_conjTranspose (φ : Λ → ℂ) :
    (fermionCreationFromVector φ)ᴴ
      = fermionAnnihilationFromVector (fun x => star (φ x)) := by
  unfold fermionCreationFromVector fermionAnnihilationFromVector
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.conjTranspose_smul, fermionCreationAbstract_conjTranspose]

omit [LinearOrder Λ] in
/-- Adjoint move for the Fock inner product:
`⟨A v, w⟩ = ⟨v, Aᴴ w⟩`. -/
private theorem fockInner_mulVec_left (A : ManyBodyOp Λ)
    (v w : (Λ → Fin 2) → ℂ) :
    fockInner (A.mulVec v) w = fockInner v (Aᴴ.mulVec w) := by
  unfold fockInner
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec]

omit [LinearOrder Λ] in
/-- `fockInner` is linear in its second argument over a finite sum with
scalar weights. -/
private theorem fockInner_sum_smul_right {m : ℕ} (u : (Λ → Fin 2) → ℂ)
    (c : Fin m → ℂ) (w : Fin m → (Λ → Fin 2) → ℂ) :
    fockInner u (∑ k, c k • w k) = ∑ k, c k * fockInner u (w k) := by
  unfold fockInner
  rw [dotProduct_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dotProduct_smul, smul_eq_mul]

/-- Prepending a creation operator to the Slater state of an `ofFn`
family is the Slater state of the `Fin.cons` family:
`Ĉ†(a) |Φ_{ofFn g}⟩ = |Φ_{ofFn (Fin.cons a g)}⟩`. -/
private theorem creationFromVector_mulVec_slaterState_ofFn
    {n : ℕ} (a : Λ → ℂ) (g : Fin n → Λ → ℂ) :
    (fermionCreationFromVector a).mulVec (slaterState (List.ofFn g))
      = slaterState (List.ofFn (Fin.cons a g)) := by
  have h : List.ofFn (Fin.cons a g) = a :: List.ofFn g := by
    rw [List.ofFn_succ]
    simp
  rw [h, slaterState_cons]

omit [Fintype Λ] [DecidableEq Λ] [LinearOrder Λ] in
/-- Index bookkeeping for the Laplace recursion: prepending `ψ 0` to the
tail family `(fun i => ψ i.succ)` with index `k` removed equals the
original family `ψ` with index `k.succ` removed:
`Fin.cons (ψ 0) ((fun i => ψ i.succ) ∘ k.succAbove) = ψ ∘ k.succ.succAbove`. -/
private theorem cons_tail_succAbove_eq
    {n : ℕ} (ψ : Fin (n + 2) → Λ → ℂ) (k : Fin (n + 1)) :
    (Fin.cons (ψ 0) (fun i : Fin n => ψ (k.succAbove i).succ) :
        Fin (n + 1) → Λ → ℂ)
      = fun i : Fin (n + 1) => ψ (k.succ.succAbove i) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rw [Fin.cons_zero, Fin.succ_succAbove_zero]
  · intro j
    rw [Fin.cons_succ, Fin.succ_succAbove_succ]

/-- **Pull-through identity.** Acting on a Slater state with a smeared
annihilation operator `Ĉ(χ)` produces the row-0 cofactor (Laplace)
expansion: each electron `j` is removed from the ket (reindexed by
`j.succAbove`) with the alternating sign `(-1)^j` and the overlap scalar
`Σ_x χ(x) ψ⁽ʲ⁾(x)`. This is the operator form of one Laplace expansion
step underlying Lemma 9.1; the proof is by induction on the number of
electrons, anticommuting `Ĉ(χ)` past the leading creation operator via
the smeared mixed CAR and killing the vacuum at the end. -/
private theorem annihilationFromVector_mulVec_slaterState
    {n : ℕ} (χ : Λ → ℂ) (ψ : Fin (n + 1) → Λ → ℂ) :
    (fermionAnnihilationFromVector χ).mulVec (slaterState (List.ofFn ψ))
      = ∑ j : Fin (n + 1), ((-1 : ℂ) ^ (j : ℕ) * (∑ x : Λ, χ x * ψ j x)) •
          slaterState (List.ofFn (fun i : Fin n => ψ (j.succAbove i))) := by
  induction n with
  | zero =>
    -- only the j = 0 term; the tail family is empty and Ĉ(χ) kills the vacuum
    rw [Fin.sum_univ_one]
    have hofn : (List.ofFn ψ) = [ψ 0] := by
      rw [List.ofFn_succ]; simp
    rw [hofn]
    have hempty : (List.ofFn (fun i : Fin 0 => ψ ((0 : Fin 1).succAbove i)))
        = ([] : List (Λ → ℂ)) := by simp
    rw [hempty, slaterState_nil]
    -- |Φ_{[ψ₀]}⟩ = Ĉ†(ψ₀)|Φvac⟩; pull Ĉ(χ) through with the mixed CAR
    rw [show ([ψ 0] : List (Λ → ℂ)) = ψ 0 :: [] from rfl, slaterState_cons,
      slaterState_nil, Matrix.mulVec_mulVec]
    have hmixed := fermionFromVectorAnticommMixed χ (ψ 0)
    have hsub : fermionAnnihilationFromVector χ * fermionCreationFromVector (ψ 0)
        = (∑ x : Λ, χ x * ψ 0 x) • (1 : ManyBodyOp Λ)
          - fermionCreationFromVector (ψ 0) * fermionAnnihilationFromVector χ :=
      eq_sub_of_add_eq hmixed
    rw [hsub, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, fermionAnnihilationFromVectorMulVecVacuum,
      Matrix.mulVec_zero, sub_zero, Fin.val_zero, pow_zero, one_mul]
  | succ m ih =>
    -- head/tail split of the ket
    have hofn : (List.ofFn ψ)
        = ψ 0 :: List.ofFn (fun i : Fin (m + 1) => ψ i.succ) := List.ofFn_succ
    rw [hofn, slaterState_cons, Matrix.mulVec_mulVec]
    -- move Ĉ(χ) past the leading Ĉ†(ψ₀) with the mixed CAR
    have hmixed := fermionFromVectorAnticommMixed χ (ψ 0)
    have hsub : fermionAnnihilationFromVector χ * fermionCreationFromVector (ψ 0)
        = (∑ x : Λ, χ x * ψ 0 x) • (1 : ManyBodyOp Λ)
          - fermionCreationFromVector (ψ 0) * fermionAnnihilationFromVector χ :=
      eq_sub_of_add_eq hmixed
    rw [hsub, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    -- IH applied to the tail family `fun i => ψ i.succ`
    rw [← Matrix.mulVec_mulVec, ih (fun i : Fin (m + 1) => ψ i.succ)]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]
    -- pull the leading Ĉ†(ψ₀) into each cofactor Slater state and reindex
    rw [show (fun k : Fin (m + 1) =>
          ((-1 : ℂ) ^ (k : ℕ) * (∑ x : Λ, χ x * ψ k.succ x)) •
            (fermionCreationFromVector (ψ 0)).mulVec
              (slaterState (List.ofFn
                (fun i : Fin m => ψ (k.succAbove i).succ))))
        = fun k : Fin (m + 1) =>
            ((-1 : ℂ) ^ (k : ℕ) * (∑ x : Λ, χ x * ψ k.succ x)) •
              slaterState (List.ofFn (fun i : Fin (m + 1) =>
                ψ (k.succ.succAbove i))) from by
      funext k
      rw [creationFromVector_mulVec_slaterState_ofFn, cons_tail_succAbove_eq ψ k]]
    -- expand the target Laplace sum into its j = 0 and j = k.succ parts
    rw [Fin.sum_univ_succ (f := fun j : Fin (m + 2) =>
      ((-1 : ℂ) ^ (j : ℕ) * (∑ x : Λ, χ x * ψ j x)) •
        slaterState (List.ofFn (fun i : Fin (m + 1) => ψ (j.succAbove i))))]
    -- the j = 0 term: ψ ∘ (0).succAbove = the tail family
    have h0 : (fun i : Fin (m + 1) => ψ ((0 : Fin (m + 2)).succAbove i))
        = fun i : Fin (m + 1) => ψ i.succ := by
      funext i; rw [Fin.zero_succAbove]
    rw [Fin.val_zero, pow_zero, one_mul, h0]
    -- match termwise: leading scalar term equal, cofactor sums equal up to sign
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    refine congrArg₂ _ rfl (Finset.sum_congr rfl fun k _ => ?_)
    -- (-1)^(k.succ) = -(-1)^k gives the sign flip
    rw [Fin.val_succ, pow_succ, mul_comm ((-1 : ℂ) ^ (k : ℕ)) (-1), mul_assoc,
      neg_one_mul, neg_smul]

/-- **Tasaki Lemma 9.1** (1st ed., Springer 2020, §9.2.3, p. 319, eq.
(9.2.53)). The inner product of the two Slater determinant states
`|Φ⟩ = Ĉ†(φ⁽¹⁾) ⋯ Ĉ†(φ⁽ᴺ⁾)|Φvac⟩` and `|Ψ⟩ = Ĉ†(ψ⁽¹⁾) ⋯ Ĉ†(ψ⁽ᴺ⁾)|Φvac⟩`
equals the determinant of the single-particle overlap (Gram) matrix
`(⟨φ⁽ʲ⁾, ψ⁽ᵏ⁾⟩)_{j,k}`.

Proof by induction on the electron number `n`. The bra's leading creation
operator is moved to the ket as a smeared annihilation operator (the
adjoint `(Ĉ†(φ₀))ᴴ = Ĉ(φ₀*)`, `fockInner_mulVec_left`), then
`annihilationFromVector_mulVec_slaterState` anticommutes it through the
ket's creation string, producing the row-0 cofactor expansion. The
induction hypothesis identifies each cofactor Fock overlap with the Gram
submatrix determinant, and `Matrix.det_succ_row_zero` reassembles the
full determinant. The `n = 0` instance is `fockInner_vacuum_self`. -/
theorem lemma_9_1_slater_inner_det {n : ℕ} (φ ψ : Fin n → Λ → ℂ) :
    fockInner (slaterState (List.ofFn φ)) (slaterState (List.ofFn ψ))
      = (slaterGram φ ψ).det := by
  induction n with
  | zero =>
    have hφ : (List.ofFn φ) = ([] : List (Λ → ℂ)) := by simp
    have hψ : (List.ofFn ψ) = ([] : List (Λ → ℂ)) := by simp
    rw [hφ, hψ, slaterState_nil, fockInner_vacuum_self, Matrix.det_fin_zero]
  | succ m ih =>
    -- split off the leading creation operator of the bra
    have hofn : (List.ofFn φ)
        = φ 0 :: List.ofFn (fun i : Fin m => φ i.succ) := List.ofFn_succ
    rw [hofn, slaterState_cons, fockInner_mulVec_left,
      fermionCreationFromVector_conjTranspose,
      annihilationFromVector_mulVec_slaterState, fockInner_sum_smul_right]
    -- IH identifies each cofactor overlap with the Gram submatrix determinant
    have hsub : ∀ j : Fin (m + 1),
        fockInner (slaterState (List.ofFn (fun i : Fin m => φ i.succ)))
            (slaterState (List.ofFn (fun i : Fin m => ψ (j.succAbove i))))
          = ((slaterGram φ ψ).submatrix Fin.succ j.succAbove).det := by
      intro j
      rw [ih (fun i : Fin m => φ i.succ) (fun i : Fin m => ψ (j.succAbove i))]
      rfl
    -- reassemble the row-0 Laplace expansion of the Gram determinant
    rw [(slaterGram φ ψ).det_succ_row_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hscalar : (∑ x : Λ, star (φ 0 x) * ψ j x) = slaterGram φ ψ 0 j := by
      simp only [slaterGram, singleParticleInner]
    rw [hsub j, hscalar, mul_assoc]

/-- **Tasaki Lemma 9.1**, explicit permutation-sum form of eq. (9.2.53):

  `⟨Φ, Ψ⟩ = Σ_p (sign p) ∏_j ⟨φ⁽ʲ⁾, ψ⁽ᵖ⁽ʲ⁾⁾⟩`,

obtained from the determinant identity `lemma_9_1_slater_inner_det` by
the Leibniz expansion of the determinant. -/
theorem lemma_9_1_slater_inner_perm_sum {n : ℕ} (φ ψ : Fin n → Λ → ℂ) :
    fockInner (slaterState (List.ofFn φ)) (slaterState (List.ofFn ψ))
      = ∑ p : Equiv.Perm (Fin n),
          (Equiv.Perm.sign p : ℂ)
            * ∏ j : Fin n, singleParticleInner (φ j) (ψ (p j)) := by
  rw [lemma_9_1_slater_inner_det, ← Matrix.det_transpose, Matrix.det_apply']
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rfl

/-- The `Λ × Fin n` coefficient matrix whose `j`-th column is the
single-electron wave function `φ⁽ʲ⁾`:
`(slaterCoeffMatrix φ) x j = φ⁽ʲ⁾(x)`. -/
noncomputable def slaterCoeffMatrix {n : ℕ} (φ : Fin n → Λ → ℂ) :
    Matrix Λ (Fin n) ℂ :=
  Matrix.of (fun x j => φ j x)

omit [DecidableEq Λ] [LinearOrder Λ] in
/-- The single-particle overlap (Gram) matrix of a family with itself is
the conjugate-transpose square `Aᴴ A` of its coefficient matrix
`A = slaterCoeffMatrix φ`: `(G)_{j,k} = ⟨φ⁽ʲ⁾, φ⁽ᵏ⁾⟩ = (Aᴴ A)_{j,k}`. -/
theorem slaterGram_self_eq_conjTranspose_mul_self {n : ℕ} (φ : Fin n → Λ → ℂ) :
    slaterGram φ φ = (slaterCoeffMatrix φ)ᴴ * slaterCoeffMatrix φ := by
  ext j k
  simp only [slaterGram, singleParticleInner, Matrix.mul_apply,
    Matrix.conjTranspose_apply, slaterCoeffMatrix, Matrix.of_apply]

omit [DecidableEq Λ] [LinearOrder Λ] in
/-- The Gram determinant of a family with itself is nonzero iff the family
is linearly independent. This is the linear-algebra core behind Lemma 9.2:
`det(⟨φ⁽ʲ⁾, φ⁽ᵏ⁾⟩) ≠ 0 ↔ φ` are linearly independent, via `G = Aᴴ A`,
`ker(Aᴴ A) = ker A`, and the column-injectivity criterion. -/
theorem slaterGram_self_det_ne_zero_iff {n : ℕ} (φ : Fin n → Λ → ℂ) :
    (slaterGram φ φ).det ≠ 0 ↔ LinearIndependent ℂ φ := by
  have hcol : (slaterCoeffMatrix φ).col = φ := by
    funext j; funext x; rfl
  have hLI : LinearIndependent ℂ φ ↔
      Function.Injective (slaterCoeffMatrix φ).mulVec := by
    rw [Matrix.mulVec_injective_iff, hcol]
  have hker :
      Function.Injective ((slaterCoeffMatrix φ)ᴴ * slaterCoeffMatrix φ).mulVec ↔
        Function.Injective (slaterCoeffMatrix φ).mulVec := by
    rw [← Matrix.coe_mulVecLin, ← Matrix.coe_mulVecLin,
      ← LinearMap.ker_eq_bot, ← LinearMap.ker_eq_bot,
      Matrix.ker_mulVecLin_eq_bot_iff, Matrix.ker_mulVecLin_eq_bot_iff]
    constructor
    · intro h v hv
      exact h v ((Matrix.conjTranspose_mul_self_mulVec_eq_zero _ v).mpr hv)
    · intro h v hv
      exact h v ((Matrix.conjTranspose_mul_self_mulVec_eq_zero _ v).mp hv)
  rw [slaterGram_self_eq_conjTranspose_mul_self, ← isUnit_iff_ne_zero,
    ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit,
    hker, ← hLI]

/-- **Tasaki Lemma 9.2** (1st ed., Springer 2020, §9.2.3, p. 320). The
Slater determinant state `|Φ⟩ = Ĉ†(φ⁽¹⁾) ⋯ Ĉ†(φ⁽ᴺ⁾)|Φvac⟩` is
nonvanishing if and only if the `N` single-electron wave functions
`φ⁽¹⁾, …, φ⁽ᴺ⁾` are linearly independent.

Proof: by Lemma 9.1 (with `ψ = φ`) the squared norm `⟨Φ, Φ⟩` equals the
Gram determinant `det(⟨φ⁽ʲ⁾, φ⁽ᵏ⁾⟩)`; the Fock inner product is positive
definite, so `Φ = 0` iff `⟨Φ, Φ⟩ = 0`, and the Gram determinant vanishes
iff the family is linearly dependent. -/
theorem lemma_9_2_slater_ne_zero_iff_linearIndependent {n : ℕ}
    (φ : Fin n → Λ → ℂ) :
    slaterState (List.ofFn φ) ≠ 0 ↔ LinearIndependent ℂ φ := by
  rw [← slaterGram_self_det_ne_zero_iff, ← lemma_9_1_slater_inner_det,
    ne_eq, ne_eq, not_iff_not]
  unfold fockInner
  exact dotProduct_star_self_eq_zero.symm

/-! ## Lemma 9.3: equal span implies proportional Slater states -/

omit [LinearOrder Λ] in
/-- Conjugate symmetry (Hermitian property) of the Fock inner product:
`⟨v, w⟩ = ⟨w, v⟩*`. -/
theorem fockInner_conj_symm (v w : (Λ → Fin 2) → ℂ) :
    fockInner v w = star (fockInner w v) := by
  unfold fockInner dotProduct
  simp only [star_sum, star_mul', star_star, Pi.star_apply]
  exact Finset.sum_congr rfl (fun x _ => by ring)

omit [LinearOrder Λ] in
/-- The Fock inner product is additive (subtractive) in its second
argument. -/
theorem fockInner_sub_right (u v w : (Λ → Fin 2) → ℂ) :
    fockInner u (v - w) = fockInner u v - fockInner u w := by
  unfold fockInner; rw [dotProduct_sub]

omit [LinearOrder Λ] in
/-- The Fock inner product is homogeneous in its second argument. -/
theorem fockInner_smul_right (u v : (Λ → Fin 2) → ℂ) (s : ℂ) :
    fockInner u (s • v) = s * fockInner u v := by
  unfold fockInner; rw [dotProduct_smul]; rfl

omit [DecidableEq Λ] [LinearOrder Λ] in
/-- The single-particle overlap is linear in its second argument over a
finite linear combination: `⟨χ, Σ_k β_k φ_k⟩ = Σ_k β_k ⟨χ, φ_k⟩`. -/
theorem singleParticleInner_sum_right {n : ℕ} (χ : Λ → ℂ)
    (β : Fin n → ℂ) (φ : Fin n → Λ → ℂ) :
    singleParticleInner χ (∑ k, β k • φ k)
      = ∑ k, β k * singleParticleInner χ (φ k) := by
  unfold singleParticleInner
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun x _ => by ring

/-- The change-of-basis matrix expressing the family `ψ` in terms of the
linearly independent family `φ` (which spans the same subspace):
`ψ⁽ʲ⁾ = Σ_k (slaterChangeMatrix φ ψ … )_{j,k} φ⁽ᵏ⁾`. -/
noncomputable def slaterChangeMatrix {n : ℕ} (φ ψ : Fin n → Λ → ℂ)
    (hφ : LinearIndependent ℂ φ)
    (hspan : Submodule.span ℂ (Set.range φ) = Submodule.span ℂ (Set.range ψ)) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun j k => hφ.repr ⟨ψ j, by
    rw [hspan]; exact Submodule.subset_span (Set.mem_range_self j)⟩ k

omit [Fintype Λ] [DecidableEq Λ] [LinearOrder Λ] in
/-- The defining property of `slaterChangeMatrix`:
`ψ⁽ʲ⁾ = Σ_k β_{j,k} φ⁽ᵏ⁾`. -/
theorem slaterChangeMatrix_sum {n : ℕ} (φ ψ : Fin n → Λ → ℂ)
    (hφ : LinearIndependent ℂ φ)
    (hspan : Submodule.span ℂ (Set.range φ) = Submodule.span ℂ (Set.range ψ))
    (j : Fin n) :
    ψ j = ∑ k, slaterChangeMatrix φ ψ hφ hspan j k • φ k := by
  have hmem : ψ j ∈ Submodule.span ℂ (Set.range φ) := by
    rw [hspan]; exact Submodule.subset_span (Set.mem_range_self j)
  have h := hφ.linearCombination_repr ⟨ψ j, hmem⟩
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype] at h
  · simp only [slaterChangeMatrix]
    exact_mod_cast h.symm
  · intro i; simp

omit [DecidableEq Λ] [LinearOrder Λ] in
/-- The off-diagonal Gram matrix transforms by the change matrix:
`G(χ, ψ) = G(χ, φ) · βᵀ`. -/
theorem slaterGram_change {n : ℕ} (χ φ ψ : Fin n → Λ → ℂ)
    (hφ : LinearIndependent ℂ φ)
    (hspan : Submodule.span ℂ (Set.range φ) = Submodule.span ℂ (Set.range ψ)) :
    slaterGram χ ψ = slaterGram χ φ * (slaterChangeMatrix φ ψ hφ hspan)ᵀ := by
  ext i j
  simp only [slaterGram, Matrix.mul_apply, Matrix.transpose_apply]
  rw [slaterChangeMatrix_sum φ ψ hφ hspan j, singleParticleInner_sum_right]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The Fock overlap transforms by the change determinant:
`⟨Φ_χ, Φ_ψ⟩ = det(β) · ⟨Φ_χ, Φ_φ⟩`. Combines Lemma 9.1 with the Gram
transformation `slaterGram_change` and determinant multiplicativity. -/
theorem fockInner_slater_change {n : ℕ} (χ φ ψ : Fin n → Λ → ℂ)
    (hφ : LinearIndependent ℂ φ)
    (hspan : Submodule.span ℂ (Set.range φ) = Submodule.span ℂ (Set.range ψ)) :
    fockInner (slaterState (List.ofFn χ)) (slaterState (List.ofFn ψ))
      = (slaterChangeMatrix φ ψ hφ hspan).det
        * fockInner (slaterState (List.ofFn χ)) (slaterState (List.ofFn φ)) := by
  rw [lemma_9_1_slater_inner_det, lemma_9_1_slater_inner_det,
    slaterGram_change χ φ ψ hφ hspan, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- **Tasaki Lemma 9.3** (1st ed., Springer 2020, §9.2.3, pp. 320–321).
If two families `{φ⁽¹⁾, …, φ⁽ᴺ⁾}` and `{ψ⁽¹⁾, …, ψ⁽ᴺ⁾}` of single-electron
states span the same `N`-dimensional subspace, then their Slater
determinant states are proportional by a nonzero constant: there is
`c ≠ 0` with `|Ψ⟩ = c |Φ⟩`.

Proof: writing `ψ⁽ʲ⁾ = Σ_k β_{j,k} φ⁽ᵏ⁾` (the change matrix `β`), Lemma 9.1
gives `⟨Φ_χ, Φ_ψ⟩ = det(β) ⟨Φ_χ, Φ_φ⟩` for every `χ`. With `c = det(β)` the
vector `w = |Ψ⟩ − c|Φ⟩` is orthogonal to both `|Φ⟩` and `|Ψ⟩`, hence to
itself (`⟨w, w⟩ = 0`), so `w = 0` by positive-definiteness. Finally `c ≠ 0`
because `|Ψ⟩ ≠ 0` (Lemma 9.2 applied to the linearly independent `ψ`). -/
theorem lemma_9_3_slater_proportional_of_span_eq {n : ℕ}
    {φ ψ : Fin n → Λ → ℂ} (hφ : LinearIndependent ℂ φ)
    (hψ : LinearIndependent ℂ ψ)
    (hspan : Submodule.span ℂ (Set.range φ) = Submodule.span ℂ (Set.range ψ)) :
    ∃ c : ℂ, c ≠ 0 ∧
      slaterState (List.ofFn ψ) = c • slaterState (List.ofFn φ) := by
  set Sφ := slaterState (List.ofFn φ) with hSφ
  set Sψ := slaterState (List.ofFn ψ) with hSψ
  set c := (slaterChangeMatrix φ ψ hφ hspan).det with hc
  have key : ∀ χ : Fin n → Λ → ℂ,
      fockInner (slaterState (List.ofFn χ)) Sψ
        = c * fockInner (slaterState (List.ofFn χ)) Sφ :=
    fun χ => fockInner_slater_change χ φ ψ hφ hspan
  have hφw : fockInner Sφ (Sψ - c • Sφ) = 0 := by
    rw [fockInner_sub_right, fockInner_smul_right, key φ]; ring
  have hψw : fockInner Sψ (Sψ - c • Sφ) = 0 := by
    rw [fockInner_sub_right, fockInner_smul_right, key ψ]; ring
  have hself : fockInner (Sψ - c • Sφ) (Sψ - c • Sφ) = 0 := by
    rw [fockInner_sub_right, fockInner_smul_right,
      fockInner_conj_symm (Sψ - c • Sφ) Sψ, hψw,
      fockInner_conj_symm (Sψ - c • Sφ) Sφ, hφw]
    simp
  have hw0 : Sψ - c • Sφ = 0 :=
    dotProduct_star_self_eq_zero.mp hself
  have hprop : Sψ = c • Sφ := sub_eq_zero.mp hw0
  refine ⟨c, ?_, hprop⟩
  intro hc0
  rw [hc0, zero_smul] at hprop
  exact (lemma_9_2_slater_ne_zero_iff_linearIndependent ψ).mpr hψ hprop

end LatticeSystem.Fermion
