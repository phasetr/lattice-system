import Mathlib.Data.Finset.NoncommProd
import Mathlib.Data.Matrix.Mul
import LatticeSystem.Math.MatrixAnalysis.HermitianSum

/-!
# Non-commutative products of pairwise-commuting matrices

Generic linear-algebra facts about `Finset.noncommProd` of a family of `Matrix n n ℂ` that is
*pairwise commuting*.  These were re-proved as private (or near-duplicate public) helpers in several
fermion / Jordan–Wigner files:

* `Matrix.noncommProd_isHermitian` — a product of pairwise-commuting Hermitian matrices is
  Hermitian.  Previously copied in `Fermion/JWAbstract.lean`, `Fermion/JordanWigner/Operators.lean`,
  and `Fermion/JordanWigner/Hubbard/HardcoreProjection.lean` (the last with an explicit
  "duplicated because of an import cycle" note).
* `Matrix.noncommProd_sq_of_sq_one` — a product of pairwise-commuting involutions is an
  involution.  Previously copied in `Fermion/JWAbstract.lean` and
  `Fermion/JordanWigner/Operators.lean`.
* `Matrix.noncommProd_mul_self_of_idempotent` — a product of pairwise-commuting idempotents is
  idempotent.  Previously in `Fermion/JordanWigner/Hubbard/HardcoreProjection.lean`.
* `Matrix.noncommProd_mulVec_eq_self` — a product of matrices each fixing a vector `ψ` also fixes
  `ψ`.  Previously in `Fermion/JordanWigner/Hubbard/HardcoreProjection.lean`.

None of these depend on any fermion-specific structure, so they belong in the generic
matrix-analysis layer.  Hosting them upstream of the Jordan–Wigner files also removes the import
cycle that forced the `HardcoreProjection` duplication.
-/

namespace Matrix

variable {ι : Type*} {n : Type*} [Fintype n] [DecidableEq n]

/-- A non-commutative product of pairwise-commuting Hermitian matrices is Hermitian. -/
theorem noncommProd_isHermitian
    (s : Finset ι) (f : ι → Matrix n n ℂ)
    (hcomm : (s : Set ι).Pairwise (fun a b => Commute (f a) (f b)))
    (hHerm : ∀ a ∈ s, (f a).IsHermitian) :
    (s.noncommProd f hcomm).IsHermitian := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.noncommProd_empty]
    exact Matrix.isHermitian_one
  | @insert a t hat ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hat]
    have hcomm_t : (t : Set ι).Pairwise (fun a b => Commute (f a) (f b)) :=
      hcomm.mono fun x hx => Finset.mem_insert_of_mem hx
    have hHerm_t : ∀ b ∈ t, (f b).IsHermitian :=
      fun b hb => hHerm b (Finset.mem_insert_of_mem hb)
    refine Matrix.IsHermitian.mul_of_commute
      (hHerm a (Finset.mem_insert_self a t)) (ih hcomm_t hHerm_t) ?_
    apply Finset.noncommProd_commute
    intro b hb
    have hab : a ≠ b := fun h => hat (h ▸ hb)
    exact hcomm (Finset.mem_insert_self a t) (Finset.mem_insert_of_mem hb) hab

/-- A non-commutative product of pairwise-commuting matrices, each squaring to the identity, itself
squares to the identity. -/
theorem noncommProd_sq_of_sq_one
    (s : Finset ι) (f : ι → Matrix n n ℂ)
    (hcomm : (s : Set ι).Pairwise (fun a b => Commute (f a) (f b)))
    (hSq : ∀ a ∈ s, f a * f a = 1) :
    s.noncommProd f hcomm * s.noncommProd f hcomm = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.noncommProd_empty]; rw [Matrix.one_mul]
  | @insert a t hat ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hat]
    have hcomm_t : (t : Set ι).Pairwise (fun a b => Commute (f a) (f b)) :=
      hcomm.mono fun x hx => Finset.mem_insert_of_mem hx
    have hSq_t : ∀ b ∈ t, f b * f b = 1 :=
      fun b hb => hSq b (Finset.mem_insert_of_mem hb)
    have hcomm_a : Commute (f a) (t.noncommProd f hcomm_t) := by
      apply Finset.noncommProd_commute
      intro b hb
      have hab : a ≠ b := fun h => hat (h ▸ hb)
      exact hcomm (Finset.mem_insert_self a t) (Finset.mem_insert_of_mem hb) hab
    rw [show f a * t.noncommProd f hcomm_t * (f a * t.noncommProd f hcomm_t)
          = (f a * f a) * (t.noncommProd f hcomm_t * t.noncommProd f hcomm_t) by
        rw [Matrix.mul_assoc,
          ← Matrix.mul_assoc (t.noncommProd f hcomm_t) (f a),
          ← hcomm_a.eq, Matrix.mul_assoc, Matrix.mul_assoc]]
    rw [hSq a (Finset.mem_insert_self a t), Matrix.one_mul,
      ih hcomm_t hSq_t]

/-- A non-commutative product of pairwise-commuting idempotent matrices is itself idempotent.  This
is the projection analogue of `noncommProd_sq_of_sq_one`: instead of `f a * f a = 1` we assume
`f a * f a = f a`. -/
theorem noncommProd_mul_self_of_idempotent
    (s : Finset ι) (f : ι → Matrix n n ℂ)
    (hcomm : (s : Set ι).Pairwise (fun a b => Commute (f a) (f b)))
    (hId : ∀ a ∈ s, f a * f a = f a) :
    s.noncommProd f hcomm * s.noncommProd f hcomm = s.noncommProd f hcomm := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.noncommProd_empty]; rw [Matrix.one_mul]
  | @insert a t hat ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hat]
    have hcomm_t : (t : Set ι).Pairwise (fun a b => Commute (f a) (f b)) :=
      hcomm.mono fun x hx => Finset.mem_insert_of_mem hx
    have hId_t : ∀ b ∈ t, f b * f b = f b :=
      fun b hb => hId b (Finset.mem_insert_of_mem hb)
    have hcomm_a : Commute (f a) (t.noncommProd f hcomm_t) := by
      apply Finset.noncommProd_commute
      intro b hb
      have hab : a ≠ b := fun h => hat (h ▸ hb)
      exact hcomm (Finset.mem_insert_self a t) (Finset.mem_insert_of_mem hb) hab
    rw [show f a * t.noncommProd f hcomm_t * (f a * t.noncommProd f hcomm_t)
          = (f a * f a) * (t.noncommProd f hcomm_t * t.noncommProd f hcomm_t) by
        rw [Matrix.mul_assoc,
          ← Matrix.mul_assoc (t.noncommProd f hcomm_t) (f a),
          ← hcomm_a.eq, Matrix.mul_assoc, Matrix.mul_assoc]]
    rw [hId a (Finset.mem_insert_self a t), ih hcomm_t hId_t]

/-- A non-commutative product of matrices, each of which fixes a vector `ψ` under `mulVec`, also
fixes `ψ`. -/
theorem noncommProd_mulVec_eq_self
    (s : Finset ι) (f : ι → Matrix n n ℂ)
    (hcomm : (s : Set ι).Pairwise (fun a b => Commute (f a) (f b)))
    (ψ : n → ℂ) (hfix : ∀ a ∈ s, (f a).mulVec ψ = ψ) :
    (s.noncommProd f hcomm).mulVec ψ = ψ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.noncommProd_empty]; rw [Matrix.one_mulVec]
  | @insert a t hat ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hat]
    have hcomm_t : (t : Set ι).Pairwise (fun a b => Commute (f a) (f b)) :=
      hcomm.mono fun x hx => Finset.mem_insert_of_mem hx
    have hfix_t : ∀ b ∈ t, (f b).mulVec ψ = ψ :=
      fun b hb => hfix b (Finset.mem_insert_of_mem hb)
    rw [← Matrix.mulVec_mulVec, ih hcomm_t hfix_t,
      hfix a (Finset.mem_insert_self a t)]

end Matrix
