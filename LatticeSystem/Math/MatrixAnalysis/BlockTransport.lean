import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbation

/-!
# Coordinate-block ground-state transport

Two model-independent facts about a matrix that *leaves a coordinate block invariant*: one relating
its unique-ground-state predicate on that block to the same predicate for the block's submatrix on
the whole restricted space, and one identifying the kernel of a diagonal matrix with the coordinate
span of the indices where it vanishes.

Both facts are the generic transport layer needed whenever a Hamiltonian preserves a coordinate
subspace (e.g. one cut out by a diagonal indicator): rather than reproving ground-state uniqueness
or a kernel computation for each concrete model, a model only has to supply the block-invariance
hypothesis (`H i j = 0` whenever `P j` and `¬ P i`) or the vanishing-locus characterization of a
diagonal matrix's entries, and these two lemmas transport it. A matrix that is block-*supported*
(`H = P̂ H P̂`) is invariant in this sense via `blockSupport_apply_eq_zero`.

## Main results

* `coordinateSpan` — the subspace of `EuclideanSpace ℂ n` spanned by the standard basis vectors at
  indices satisfying a decidable predicate `P`.
* `coordinateRestrict` — the restriction of a vector of `EuclideanSpace ℂ n` to the coordinates
  satisfying `P`, landing in `EuclideanSpace ℂ {i // P i}`.
* `coordinateExtend` — the extension by zero of a vector of `EuclideanSpace ℂ {i // P i}`, the
  inverse of `coordinateRestrict` on the coordinate span.
* `mem_coordinateSpan_iff` — membership in the coordinate span is exactly vanishing of every
  coordinate outside `P`.
* `blockSupport_apply_eq_zero` — a matrix conjugated by the diagonal indicator of `P` has no
  entries outside the `P`-block, hence in particular leaves the coordinate span invariant.
* `isUniqueGroundStateOn_coordinateSpan_iff_submatrix` — for `H` leaving the coordinate block of `P`
  invariant (`H i j = 0` whenever `P j` and `¬ P i`) and a candidate `φ` in the coordinate span,
  `H`'s unique ground state on the coordinate span of `P` at `φ` is equivalent to the submatrix
  restriction of `H` to that block having the restricted candidate as its unique ground state on the
  whole restricted space.
* `matrixKernel_diagonal_eq_coordinateSpan` — the kernel of a diagonal matrix equals the coordinate
  span of the predicate characterizing its zero entries.
-/

namespace LatticeSystem.Math

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The coordinate span of a predicate.** The subspace of `EuclideanSpace ℂ n` spanned by the
standard basis vectors at indices satisfying the decidable predicate `P`; equivalently, the
subspace of vectors supported on `P`. -/
noncomputable def coordinateSpan (P : n → Prop) [DecidablePred P] :
    Submodule ℂ (EuclideanSpace ℂ n) :=
  Submodule.span ℂ (Set.range fun i : {i // P i} => EuclideanSpace.basisFun n ℂ i.val)

/-- **Coordinate restriction.** Restrict a vector of `EuclideanSpace ℂ n` to the coordinates
satisfying `P`, landing in `EuclideanSpace ℂ {i // P i}`. -/
noncomputable def coordinateRestrict (P : n → Prop) [DecidablePred P]
    (φ : EuclideanSpace ℂ n) : EuclideanSpace ℂ {i // P i} :=
  WithLp.toLp 2 (fun i : {i // P i} => (WithLp.ofLp φ) i.val)

/-- **Coordinate extension.** Extend a vector of `EuclideanSpace ℂ {i // P i}` by zero to all of
`EuclideanSpace ℂ n`; the result is supported on `P`, and extension is inverse to
`coordinateRestrict` on the coordinate span. -/
noncomputable def coordinateExtend (P : n → Prop) [DecidablePred P]
    (ψ : EuclideanSpace ℂ {i // P i}) : EuclideanSpace ℂ n :=
  WithLp.toLp 2 (fun i => if h : P i then (WithLp.ofLp ψ) ⟨i, h⟩ else 0)

section Coordinates

variable {P : n → Prop} [DecidablePred P]

omit [Fintype n] [DecidableEq n] in
/-- The coordinates of a restricted vector are the coordinates of the original vector at the
indices satisfying `P`. -/
@[simp]
theorem coordinateRestrict_apply (φ : EuclideanSpace ℂ n) (i : {i // P i}) :
    coordinateRestrict P φ i = φ i.val := rfl

omit [Fintype n] [DecidableEq n] in
/-- The coordinates of an extended vector: the given ones at indices satisfying `P`, zero
elsewhere. -/
@[simp]
theorem coordinateExtend_apply (ψ : EuclideanSpace ℂ {i // P i}) (i : n) :
    coordinateExtend P ψ i = if h : P i then ψ ⟨i, h⟩ else 0 := rfl

omit [DecidableEq n] in
/-- A finite sum over `n` whose summands vanish outside `P` collapses to a sum over the subtype
`{i // P i}`. -/
private theorem sum_eq_sum_subtype {M : Type*} [AddCommMonoid M] (f : n → M)
    (hf : ∀ i, ¬ P i → f i = 0) : ∑ i, f i = ∑ i : {i // P i}, f i.val := by
  rw [← Finset.sum_subtype (Finset.univ.filter P) (fun x => by simp) f]
  refine (Finset.sum_subset (Finset.filter_subset _ _) fun x _ hx => hf x ?_).symm
  simpa using hx

omit [DecidableEq n] in
/-- **Membership in the coordinate span is support on `P`.** A vector lies in the span of the
standard basis vectors at the indices satisfying `P` exactly when all its other coordinates
vanish. -/
theorem mem_coordinateSpan_iff (v : EuclideanSpace ℂ n) :
    v ∈ coordinateSpan P ↔ ∀ i, ¬ P i → v i = 0 := by
  classical
  constructor
  · intro hv i hi
    induction hv using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        have hik : i ≠ k.val := fun h => hi (by rw [h]; exact k.property)
        simp [EuclideanSpace.basisFun_apply, hik]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  · intro hv
    refine (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨fun k => v k.val, ?_⟩
    have hrepr : ∑ i : n, v i • EuclideanSpace.basisFun n ℂ i = v := by
      have h := (EuclideanSpace.basisFun n ℂ).sum_repr' v
      simp only [EuclideanSpace.basisFun_inner] at h
      exact h
    refine Eq.trans ?_ hrepr
    exact (sum_eq_sum_subtype (fun i => v i • EuclideanSpace.basisFun n ℂ i)
      (fun i hi => by simp [hv i hi])).symm

omit [DecidableEq n] in
/-- Extended vectors lie in the coordinate span. -/
theorem coordinateExtend_mem_coordinateSpan (ψ : EuclideanSpace ℂ {i // P i}) :
    coordinateExtend P ψ ∈ coordinateSpan P := by
  refine (mem_coordinateSpan_iff _).mpr fun i hi => ?_
  simp [hi]

omit [Fintype n] [DecidableEq n] in
/-- Restricting an extended vector recovers it. -/
@[simp]
theorem coordinateRestrict_coordinateExtend (ψ : EuclideanSpace ℂ {i // P i}) :
    coordinateRestrict P (coordinateExtend P ψ) = ψ := by
  refine PiLp.ext fun i => ?_
  simp [i.property]

omit [DecidableEq n] in
/-- Extending a restricted vector recovers it, provided the vector is supported on `P`. -/
theorem coordinateExtend_coordinateRestrict {v : EuclideanSpace ℂ n} (hv : v ∈ coordinateSpan P) :
    coordinateExtend P (coordinateRestrict P v) = v := by
  refine PiLp.ext fun i => ?_
  by_cases h : P i
  · simp [h]
  · simp [h, (mem_coordinateSpan_iff v).mp hv i h]

omit [Fintype n] [DecidableEq n] in
/-- Coordinate restriction is homogeneous. -/
theorem coordinateRestrict_smul (c : ℂ) (φ : EuclideanSpace ℂ n) :
    coordinateRestrict P (c • φ) = c • coordinateRestrict P φ := rfl

omit [Fintype n] [DecidableEq n] in
/-- Coordinate extension is homogeneous. -/
theorem coordinateExtend_smul (c : ℂ) (ψ : EuclideanSpace ℂ {i // P i}) :
    coordinateExtend P (c • ψ) = c • coordinateExtend P ψ := by
  refine PiLp.ext fun i => ?_
  by_cases h : P i <;> simp [h]

omit [DecidableEq n] in
/-- **Coordinate extension is isometric**: extending by zero does not change the Euclidean norm. -/
theorem norm_coordinateExtend (ψ : EuclideanSpace ℂ {i // P i}) :
    ‖coordinateExtend P ψ‖ = ‖ψ‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  rw [sum_eq_sum_subtype (P := P) (fun i => ‖coordinateExtend P ψ i‖ ^ 2)
    (fun i hi => by simp [hi])]
  exact Finset.sum_congr rfl fun k _ => by simp [k.property]

end Coordinates

section BlockSupport

variable {H : Matrix n n ℂ} {P : n → Prop} [DecidablePred P]

/-- **A matrix conjugated by the diagonal indicator of `P` has no entries outside the `P`-block.**
This is the standard way a model supplies the invariance hypothesis
`hInv : ∀ i j, P j → ¬ P i → H i j = 0` of
`isUniqueGroundStateOn_coordinateSpan_iff_submatrix`: block support is strictly stronger than block
invariance, so a conjugated matrix qualifies via `Or.inl`. -/
theorem blockSupport_apply_eq_zero
    (hblock : H = Matrix.diagonal (fun i => if P i then (1 : ℂ) else 0) * H
        * Matrix.diagonal (fun i => if P i then (1 : ℂ) else 0))
    {i j : n} (hij : ¬ P i ∨ ¬ P j) : H i j = 0 := by
  have h : H i j
      = (Matrix.diagonal (fun i => if P i then (1 : ℂ) else 0) * H
        * Matrix.diagonal (fun i => if P i then (1 : ℂ) else 0)) i j := by rw [← hblock]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  rcases hij with hi | hj
  · rw [if_neg hi, zero_mul, zero_mul] at h
    exact h
  · rw [if_neg hj, mul_zero] at h
    exact h

/-- **The coordinate span is invariant under a block-invariant matrix.** For a vector supported on
`P`, only the `P`-columns contribute, and those vanish on the `¬P`-rows by `hInv`. -/
private theorem toEuclideanLin_mem_coordinateSpan (hInv : ∀ i j, P j → ¬ P i → H i j = 0)
    {v : EuclideanSpace ℂ n} (hv : v ∈ coordinateSpan P) :
    Matrix.toEuclideanLin H v ∈ coordinateSpan P := by
  refine (mem_coordinateSpan_iff _).mpr fun i hi => ?_
  have hval : (Matrix.toEuclideanLin H v) i = ∑ k, H i k * v k := rfl
  rw [hval]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : P k
  · rw [hInv i k hk hi, zero_mul]
  · rw [(mem_coordinateSpan_iff v).mp hv k hk, mul_zero]

/-- **Restriction intertwines a matrix with its submatrix on span vectors.** For a vector supported
on `P`, restricting the matrix action to the `P`-coordinates is the action of the `P`-block
submatrix on the restricted vector; no hypothesis on `H` is needed, since the discarded columns are
multiplied by vanishing coordinates. -/
private theorem coordinateRestrict_toEuclideanLin {v : EuclideanSpace ℂ n}
    (hv : v ∈ coordinateSpan P) :
    coordinateRestrict P (Matrix.toEuclideanLin H v)
      = Matrix.toEuclideanLin (H.submatrix Subtype.val Subtype.val) (coordinateRestrict P v) := by
  refine PiLp.ext fun j => ?_
  have hlhs : coordinateRestrict P (Matrix.toEuclideanLin H v) j = ∑ k, H j.val k * v k := rfl
  have hrhs : Matrix.toEuclideanLin (H.submatrix Subtype.val Subtype.val)
      (coordinateRestrict P v) j = ∑ k : {i // P i}, H j.val k.val * v k.val := rfl
  rw [hlhs, hrhs]
  exact sum_eq_sum_subtype (fun k => H j.val k * v k)
    fun k hk => by simp [(mem_coordinateSpan_iff v).mp hv k hk]

end BlockSupport

/-- **Generic block-transport of the unique-ground-state predicate.** The hypothesis
`hInv : ∀ i j, P j → ¬ P i → H i j = 0` says that rows outside `P` vanish at columns inside `P`,
i.e. `H` leaves the coordinate span of `P` invariant; it is weaker than block support
`H = P̂ · H · P̂`, and in particular holds for a Hamiltonian that is merely block-*diagonal* across
`P`/`¬P`. For a candidate `φ` in the coordinate span of `P`, `H` having `φ` as its unique ground
state on the coordinate span is equivalent to the submatrix restriction of `H` to that block having
the restricted candidate `coordinateRestrict P φ` as its unique ground state on the whole restricted
space `⊤`. -/
theorem isUniqueGroundStateOn_coordinateSpan_iff_submatrix {H : Matrix n n ℂ}
    {P : n → Prop} [DecidablePred P]
    (hInv : ∀ i j, P j → ¬ P i → H i j = 0)
    {E : ℝ} {φ : EuclideanSpace ℂ n} (hφ : φ ∈ coordinateSpan P) :
    IsUniqueGroundStateOn (coordinateSpan P) H E φ ↔
      IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ {i // P i}))
        (H.submatrix Subtype.val Subtype.val) E (coordinateRestrict P φ) := by
  have hmemH : ∀ v : EuclideanSpace ℂ n, v ∈ coordinateSpan P →
      Matrix.toEuclideanLin H v ∈ coordinateSpan P :=
    fun _ hv => toEuclideanLin_mem_coordinateSpan hInv hv
  have hres : ∀ v : EuclideanSpace ℂ n, v ∈ coordinateSpan P →
      coordinateRestrict P (Matrix.toEuclideanLin H v)
        = Matrix.toEuclideanLin (H.submatrix Subtype.val Subtype.val) (coordinateRestrict P v) :=
    fun _ hv => coordinateRestrict_toEuclideanLin hv
  have hext : ∀ ψ : EuclideanSpace ℂ {i // P i}, Matrix.toEuclideanLin H (coordinateExtend P ψ)
      = coordinateExtend P
        (Matrix.toEuclideanLin (H.submatrix Subtype.val Subtype.val) ψ) := by
    intro ψ
    have hmemψ := coordinateExtend_mem_coordinateSpan (P := P) ψ
    have h := hres _ hmemψ
    rw [coordinateRestrict_coordinateExtend] at h
    rw [← h, coordinateExtend_coordinateRestrict (hmemH _ hmemψ)]
  have hzero : ∀ ψ : EuclideanSpace ℂ {i // P i}, coordinateExtend P ψ = 0 → ψ = 0 := by
    intro ψ h
    exact norm_eq_zero.mp (by rw [← norm_coordinateExtend ψ, h, norm_zero])
  have hzero' : ∀ v : EuclideanSpace ℂ n, v ∈ coordinateSpan P →
      coordinateRestrict P v = 0 → v = 0 := by
    intro v hv h
    refine norm_eq_zero.mp ?_
    rw [← coordinateExtend_coordinateRestrict hv, norm_coordinateExtend, h, norm_zero]
  constructor
  · rintro ⟨hmem, hnorm, heig, hground, huniq⟩
    have hnorm' : ‖coordinateRestrict P φ‖ = 1 := by
      rw [← norm_coordinateExtend (coordinateRestrict P φ),
        coordinateExtend_coordinateRestrict hmem]
      exact hnorm
    have heig' : Matrix.toEuclideanLin (H.submatrix Subtype.val Subtype.val)
        (coordinateRestrict P φ) = (E : ℂ) • coordinateRestrict P φ := by
      rw [← hres _ hmem, heig, coordinateRestrict_smul]
    have hne : coordinateRestrict P φ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hnorm'
      exact zero_ne_one hnorm'
    refine ⟨Submodule.mem_top, hnorm', heig',
      ⟨⟨coordinateRestrict P φ, Submodule.mem_top, hne, heig'⟩, ?_⟩, ?_⟩
    · rintro μ ⟨ψ, -, hψ0, hψeig⟩
      refine hground.2 μ ⟨coordinateExtend P ψ, coordinateExtend_mem_coordinateSpan ψ,
        fun h => hψ0 (hzero ψ h), ?_⟩
      rw [hext ψ, hψeig, coordinateExtend_smul]
    · rintro ψ - hψeig
      obtain ⟨c, hc⟩ := huniq (coordinateExtend P ψ) (coordinateExtend_mem_coordinateSpan ψ)
        (by rw [hext ψ, hψeig, coordinateExtend_smul])
      exact ⟨c, by rw [← coordinateRestrict_coordinateExtend ψ, hc, coordinateRestrict_smul]⟩
  · rintro ⟨-, hnorm, heig, hground, huniq⟩
    have hnormφ : ‖φ‖ = 1 := by
      rw [← coordinateExtend_coordinateRestrict hφ, norm_coordinateExtend]
      exact hnorm
    have heigφ : Matrix.toEuclideanLin H φ = (E : ℂ) • φ := by
      calc Matrix.toEuclideanLin H φ
          = coordinateExtend P (coordinateRestrict P (Matrix.toEuclideanLin H φ)) :=
            (coordinateExtend_coordinateRestrict (hmemH _ hφ)).symm
        _ = coordinateExtend P (coordinateRestrict P ((E : ℂ) • φ)) := by
            rw [hres _ hφ, heig, coordinateRestrict_smul]
        _ = (E : ℂ) • φ := coordinateExtend_coordinateRestrict ((coordinateSpan P).smul_mem _ hφ)
    have hne : φ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hnormφ
      exact zero_ne_one hnormφ
    refine ⟨hφ, hnormφ, heigφ, ⟨⟨φ, hφ, hne, heigφ⟩, ?_⟩, ?_⟩
    · rintro μ ⟨ψ, hψmem, hψ0, hψeig⟩
      refine hground.2 μ ⟨coordinateRestrict P ψ, Submodule.mem_top,
        fun h => hψ0 (hzero' ψ hψmem h), ?_⟩
      rw [← hres _ hψmem, hψeig, coordinateRestrict_smul]
    · intro ψ hψmem hψeig
      obtain ⟨c, hc⟩ := huniq (coordinateRestrict P ψ) Submodule.mem_top
        (by rw [← hres _ hψmem, hψeig, coordinateRestrict_smul])
      refine ⟨c, ?_⟩
      rw [← coordinateExtend_coordinateRestrict hψmem, hc, coordinateExtend_smul,
        coordinateExtend_coordinateRestrict hφ]

/-- **The kernel of a diagonal matrix is the coordinate span of its zero-entry predicate.**
If a diagonal matrix's entries vanish exactly on a decidable predicate `P`, its kernel (as a
subspace of `EuclideanSpace ℂ n`) is the coordinate span of `P`. -/
theorem matrixKernel_diagonal_eq_coordinateSpan (d : n → ℂ) (P : n → Prop) [DecidablePred P]
    (hP : ∀ i, d i = 0 ↔ P i) :
    matrixKernel (Matrix.diagonal d) = coordinateSpan P := by
  refine Submodule.ext fun v => ?_
  rw [mem_coordinateSpan_iff]
  constructor
  · intro hv i hi
    have hker : (Matrix.diagonal d).mulVec (WithLp.ofLp v) = 0 := by
      have h0 : Matrix.toEuclideanLin (Matrix.diagonal d) v = 0 := LinearMap.mem_ker.mp hv
      have hofLp : WithLp.ofLp (Matrix.toEuclideanLin (Matrix.diagonal d) v)
          = (Matrix.diagonal d).mulVec (WithLp.ofLp v) := rfl
      rw [← hofLp, h0]
      rfl
    have hi' := congrFun hker i
    rw [Matrix.mulVec_diagonal, Pi.zero_apply] at hi'
    exact (mul_eq_zero.mp hi').resolve_left fun h => hi ((hP i).mp h)
  · intro hv
    refine LinearMap.mem_ker.mpr ?_
    apply WithLp.ofLp_injective 2
    funext i
    change (Matrix.diagonal d).mulVec (WithLp.ofLp v) i = 0
    rw [Matrix.mulVec_diagonal]
    by_cases h : P i
    · rw [(hP i).mpr h, zero_mul]
    · rw [hv i h, mul_zero]

end LatticeSystem.Math
