import LatticeSystem.Math.MatrixAnalysis.BlockTransport
import LatticeSystem.Math.SubmoduleFinrankLeOne

/-!
# Ground-state transport across reindexing, constant shifts, and `finrank ≤ 1`

Generic (model-independent) ground-state infrastructure needed for the Theorem 10.4 (Lieb
repulsive Hubbard half-filling) discharge arc, PR-11a
(Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020,
§10.2.2). This complements `BlockTransport.lean`'s coordinate-block transport with three further
generic facts about `IsUniqueGroundStateOn` (`Math/MatrixAnalysis/DegeneratePerturbation.lean`):
reindexing along an `Equiv`, real constant shifts, and the promotion of an eigenspace `finrank ≤ 1`
bound plus energy minimality to a genuine unique-ground-state witness. It also carries the
eigenspace analogue of `BlockTransport.lean`'s `matrixKernel_diagonal_eq_coordinateSpan` and the
downward-restriction (`mono`) lemma for `IsUniqueGroundStateOn` along a submodule inclusion.

## Main results

* `isUniqueGroundStateOn_reindex_iff` — `IsUniqueGroundStateOn ⊤ H E φ` transports along an index
  `Equiv e : m ≃ n` to `IsUniqueGroundStateOn ⊤ (H.submatrix e e) E (φ ∘ e)` (up to the coordinate
  reindexing of the candidate vector).
* `isUniqueGroundStateOn_sub_smul_one_iff` — shifting `H` by a real constant multiple of the
  identity shifts the ground energy by the same constant and preserves the ground state and
  ground-space predicate.
* `isUniqueGroundStateOn_of_finrank_eigenspace_le_one` — from `finrank ≤ 1` of the `E`-eigenspace
  of `H` (as a `Module.End` on the ambient Pi type via `Matrix.toLin'`), a nonzero `E`-eigenvector,
  and eigenvalue-minimality among all real eigenvalues of `H`, constructs a normalized
  `IsUniqueGroundStateOn ⊤ H E` witness. Reuses `exists_smul_of_mem_of_finrank_le_one`
  (`Math/SubmoduleFinrankLeOne.lean`) rather than re-deriving scalar dependence.
* `secondOrderEffectiveHamiltonian_eq_kernelProjectionMatrix_conj` — the second-order effective
  Hamiltonian is sandwiched by the kernel projection of `H0`,
  `Ĥeff = P̂₀ · Ĥeff · P̂₀`, a consequence of idempotence of `kernelProjectionMatrix`.
* `eigenspace_diagonal_eq_coordinateSpan` — the eigenspace analogue of
  `matrixKernel_diagonal_eq_coordinateSpan` (`BlockTransport.lean`): the `L`-eigenspace of a
  diagonal matrix equals the coordinate span of the predicate characterizing entries equal to `L`.
* `coordinateSpan_inf_coordinateSpan` — an intersection of coordinate spans is the coordinate span
  of the conjunction of the two predicates.
* `IsUniqueGroundStateOn.mono` — `IsUniqueGroundStateOn` restricts downward along a submodule
  inclusion `K ≤ K'`, given the candidate lies in the smaller submodule.
-/

namespace LatticeSystem.Math

open Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- **Reindexing transport of `IsUniqueGroundStateOn`, one implication.** For an index equivalence
`e : m ≃ n`, a unique ground state of `H` on `⊤` induces one of the `e`-submatrix of `H` at the
`e`-reindexed candidate vector, with the same ground energy. -/
private theorem isUniqueGroundStateOn_submatrix_of_equiv {H : Matrix n n ℂ} (e : m ≃ n) {E : ℝ}
    {φ : EuclideanSpace ℂ n}
    (hGS : IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n)) H E φ) :
    IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ m)) (H.submatrix e e) E
      (WithLp.toLp 2 fun j => (WithLp.ofLp φ) (e j)) := by
  obtain ⟨-, hnorm, heig, hground, huniq⟩ := hGS
  set L : EuclideanSpace ℂ n ≃ₗᵢ[ℂ] EuclideanSpace ℂ m :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm
  have hLφ : L φ = (WithLp.toLp 2 fun j => (WithLp.ofLp φ) (e j)) := rfl
  have hinter : ∀ v : EuclideanSpace ℂ n,
      Matrix.toEuclideanLin (H.submatrix e e) (L v) = L (Matrix.toEuclideanLin H v) := by
    intro v
    refine PiLp.ext fun j => ?_
    have hlhs : Matrix.toEuclideanLin (H.submatrix e e) (L v) j
        = ∑ k : m, H (e j) (e k) * v (e k) := rfl
    have hrhs : L (Matrix.toEuclideanLin H v) j = ∑ i : n, H (e j) i * v i := rfl
    rw [hlhs, hrhs]
    exact Equiv.sum_comp e fun i => H (e j) i * v i
  have hback : ∀ (μ : ℝ) (ψ : EuclideanSpace ℂ m),
      Matrix.toEuclideanLin (H.submatrix e e) ψ = (μ : ℂ) • ψ →
        Matrix.toEuclideanLin H (L.symm ψ) = (μ : ℂ) • L.symm ψ := by
    intro μ ψ h
    apply L.injective
    rw [← hinter, L.apply_symm_apply, h, map_smul, L.apply_symm_apply]
  rw [← hLφ]
  have hnorm' : ‖L φ‖ = 1 := by rw [L.norm_map]; exact hnorm
  have heig' : Matrix.toEuclideanLin (H.submatrix e e) (L φ) = (E : ℂ) • L φ := by
    rw [hinter, heig, map_smul]
  have hne' : L φ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm'
    exact zero_ne_one hnorm'
  refine ⟨Submodule.mem_top, hnorm', heig', ⟨⟨L φ, Submodule.mem_top, hne', heig'⟩, ?_⟩, ?_⟩
  · rintro μ ⟨ψ, -, hψ0, hψeig⟩
    refine hground.2 μ ⟨L.symm ψ, Submodule.mem_top, ?_, hback μ ψ hψeig⟩
    intro h
    exact hψ0 (by rw [← L.apply_symm_apply ψ, h, map_zero])
  · rintro ψ - hψeig
    obtain ⟨c, hc⟩ := huniq (L.symm ψ) Submodule.mem_top (hback E ψ hψeig)
    exact ⟨c, by rw [← L.apply_symm_apply ψ, hc, map_smul]⟩

/-- **Reindexing transport of `IsUniqueGroundStateOn`.** For an index equivalence `e : m ≃ n`,
`H` has `φ` as its unique ground state on `⊤` over `n` iff the `e`-submatrix of `H` has the
`e`-reindexed candidate as its unique ground state on `⊤` over `m`. -/
theorem isUniqueGroundStateOn_reindex_iff (H : Matrix n n ℂ) (e : m ≃ n) (E : ℝ)
    (φ : EuclideanSpace ℂ n) :
    IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n)) H E φ ↔
      IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ m))
        (H.submatrix e e) E (WithLp.toLp 2 (fun j => (WithLp.ofLp φ) (e j))) := by
  refine ⟨isUniqueGroundStateOn_submatrix_of_equiv e, fun h => ?_⟩
  have h' := isUniqueGroundStateOn_submatrix_of_equiv e.symm h
  have hmat : (H.submatrix e e).submatrix e.symm e.symm = H := by
    rw [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]
  have hvec : (WithLp.toLp 2 fun i =>
        (WithLp.ofLp (WithLp.toLp 2 fun j => (WithLp.ofLp φ) (e j))) (e.symm i)) = φ := by
    refine PiLp.ext fun i => ?_
    simp
  rw [hmat, hvec] at h'
  exact h'

/-- **Real constant shift preserves unique-ground-state transport.** Shifting `H` by `(a : ℂ) • 1`
shifts the ground energy by `a` and leaves the ground submodule, candidate, and uniqueness clause
unchanged: `IsUniqueGroundStateOn K H E φ ↔ IsUniqueGroundStateOn K (H - (a : ℂ) • 1) (E - a) φ`. -/
theorem isUniqueGroundStateOn_sub_smul_one_iff (K : Submodule ℂ (EuclideanSpace ℂ n))
    (H : Matrix n n ℂ) (a : ℝ) (E : ℝ) (φ : EuclideanSpace ℂ n) :
    IsUniqueGroundStateOn K H E φ ↔
      IsUniqueGroundStateOn K (H - (a : ℂ) • (1 : Matrix n n ℂ)) (E - a) φ := by
  have hone : ∀ ψ : EuclideanSpace ℂ n, Matrix.toEuclideanLin (1 : Matrix n n ℂ) ψ = ψ := by
    intro ψ
    apply WithLp.ofLp_injective 2
    exact Matrix.one_mulVec (WithLp.ofLp ψ)
  have hsub : ∀ ψ : EuclideanSpace ℂ n,
      Matrix.toEuclideanLin (H - (a : ℂ) • (1 : Matrix n n ℂ)) ψ
        = Matrix.toEuclideanLin H ψ - (a : ℂ) • ψ := by
    intro ψ
    have hmap : Matrix.toEuclideanLin (H - (a : ℂ) • (1 : Matrix n n ℂ))
        = Matrix.toEuclideanLin H - (a : ℂ) • Matrix.toEuclideanLin (1 : Matrix n n ℂ) := by
      rw [map_sub, map_smul]
    rw [hmap, LinearMap.sub_apply, LinearMap.smul_apply, hone]
  have hkey : ∀ (μ : ℝ) (ψ : EuclideanSpace ℂ n),
      Matrix.toEuclideanLin (H - (a : ℂ) • (1 : Matrix n n ℂ)) ψ = ((μ : ℝ) : ℂ) • ψ
        ↔ Matrix.toEuclideanLin H ψ = ((μ + a : ℝ) : ℂ) • ψ := by
    intro μ ψ
    rw [hsub, sub_eq_iff_eq_add, Complex.ofReal_add, add_smul]
  have hEa : (E - a + a : ℝ) = E := by ring
  constructor
  · rintro ⟨hmem, hnorm, heig, hground, huniq⟩
    have hshift : ∀ ψ : EuclideanSpace ℂ n, Matrix.toEuclideanLin H ψ = (E : ℂ) • ψ →
        Matrix.toEuclideanLin (H - (a : ℂ) • (1 : Matrix n n ℂ)) ψ = ((E - a : ℝ) : ℂ) • ψ := by
      intro ψ h
      exact (hkey (E - a) ψ).mpr (by rw [hEa]; exact h)
    obtain ⟨ψ₀, hψ₀mem, hψ₀0, hψ₀eig⟩ := hground.1
    refine ⟨hmem, hnorm, hshift φ heig,
      ⟨⟨ψ₀, hψ₀mem, hψ₀0, hshift ψ₀ hψ₀eig⟩, ?_⟩, ?_⟩
    · rintro μ ⟨ψ, hψmem, hψ0, hψeig⟩
      have hle := hground.2 (μ + a) ⟨ψ, hψmem, hψ0, (hkey μ ψ).mp hψeig⟩
      linarith
    · intro ψ hψmem hψeig
      have h := (hkey (E - a) ψ).mp hψeig
      rw [hEa] at h
      exact huniq ψ hψmem h
  · rintro ⟨hmem, hnorm, heig, hground, huniq⟩
    have hunshift : ∀ ψ : EuclideanSpace ℂ n,
        Matrix.toEuclideanLin (H - (a : ℂ) • (1 : Matrix n n ℂ)) ψ = ((E - a : ℝ) : ℂ) • ψ →
          Matrix.toEuclideanLin H ψ = (E : ℂ) • ψ := by
      intro ψ h
      have h' := (hkey (E - a) ψ).mp h
      rwa [hEa] at h'
    obtain ⟨ψ₀, hψ₀mem, hψ₀0, hψ₀eig⟩ := hground.1
    refine ⟨hmem, hnorm, hunshift φ heig,
      ⟨⟨ψ₀, hψ₀mem, hψ₀0, hunshift ψ₀ hψ₀eig⟩, ?_⟩, ?_⟩
    · rintro μ ⟨ψ, hψmem, hψ0, hψeig⟩
      have hμa : (μ - a + a : ℝ) = μ := by ring
      have hle := hground.2 (μ - a)
        ⟨ψ, hψmem, hψ0, (hkey (μ - a) ψ).mpr (by rw [hμa]; exact hψeig)⟩
      linarith
    · intro ψ hψmem hψeig
      exact huniq ψ hψmem ((hkey (E - a) ψ).mpr (by rw [hEa]; exact hψeig))

/-- **From `finrank ≤ 1` and minimality to a unique ground state.** If the `E`-eigenspace of `H`
(as a `Module.End` on the Pi type `n → ℂ` via `Matrix.toLin'`) has `finrank ≤ 1`, `x : n → ℂ` is a
nonzero vector of that eigenspace, and `E` is `≤` every real eigenvalue of `H` (witnessed by a
nonzero `Matrix.toLin'`-eigenvector), then the `EuclideanSpace`-normalization of `x` is `H`'s
unique ground state on `⊤`. -/
theorem isUniqueGroundStateOn_of_finrank_eigenspace_le_one (H : Matrix n n ℂ) (E : ℝ)
    (x : n → ℂ)
    (hx_mem : x ∈ Module.End.eigenspace (Matrix.toLin' H) (E : ℂ))
    (hx0 : x ≠ 0)
    (hfin : Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' H) (E : ℂ)) ≤ 1)
    (hmin : ∀ μ : ℝ, (∃ y : n → ℂ, y ≠ 0 ∧ Matrix.toLin' H y = (μ : ℂ) • y) → E ≤ μ) :
    IsUniqueGroundStateOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n)) H E
      ((‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖⁻¹ : ℂ) •
        (WithLp.toLp 2 x : EuclideanSpace ℂ n)) := by
  have hbridge : ∀ (v : EuclideanSpace ℂ n) (c : ℂ),
      Matrix.toEuclideanLin H v = c • v ↔ Matrix.toLin' H (WithLp.ofLp v) = c • WithLp.ofLp v := by
    intro v c
    have h1 : WithLp.ofLp (Matrix.toEuclideanLin H v) = Matrix.toLin' H (WithLp.ofLp v) := rfl
    have h2 : WithLp.ofLp (c • v) = c • WithLp.ofLp v := rfl
    constructor
    · intro h
      rw [← h1, ← h2, h]
    · intro h
      apply WithLp.ofLp_injective 2
      rw [h1, h2, h]
  set x' : EuclideanSpace ℂ n := WithLp.toLp 2 x
  have hofLp : WithLp.ofLp x' = x := rfl
  have hx'0 : x' ≠ 0 := by
    intro h
    exact hx0 (by rw [← hofLp, h]; rfl)
  have heigx : Matrix.toEuclideanLin H x' = (E : ℂ) • x' :=
    (hbridge x' (E : ℂ)).mpr (by rw [hofLp]; exact Module.End.mem_eigenspace_iff.mp hx_mem)
  have hnorm : ‖((‖x'‖⁻¹ : ℂ) • x')‖ = 1 := norm_smul_inv_norm hx'0
  have hne : ((‖x'‖⁻¹ : ℂ) • x') ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have heig : Matrix.toEuclideanLin H ((‖x'‖⁻¹ : ℂ) • x') = (E : ℂ) • (‖x'‖⁻¹ : ℂ) • x' := by
    rw [map_smul, heigx, smul_comm]
  have hmin' : ∀ μ : ℝ, (∃ ψ : EuclideanSpace ℂ n,
      ψ ∈ (⊤ : Submodule ℂ (EuclideanSpace ℂ n)) ∧ ψ ≠ 0 ∧
        Matrix.toEuclideanLin H ψ = (μ : ℂ) • ψ) → E ≤ μ := by
    rintro μ ⟨ψ, -, hψ0, hψeig⟩
    refine hmin μ ⟨WithLp.ofLp ψ, fun h => hψ0 (WithLp.ofLp_injective 2 h),
      (hbridge ψ (μ : ℂ)).mp hψeig⟩
  refine ⟨Submodule.mem_top, hnorm, heig,
    ⟨⟨(‖x'‖⁻¹ : ℂ) • x', Submodule.mem_top, hne, heig⟩, hmin'⟩, ?_⟩
  rintro ψ - hψeig
  have hψ_mem : WithLp.ofLp ψ ∈ Module.End.eigenspace (Matrix.toLin' H) (E : ℂ) :=
    Module.End.mem_eigenspace_iff.mpr ((hbridge ψ (E : ℂ)).mp hψeig)
  obtain ⟨c, hc⟩ := exists_smul_of_mem_of_finrank_le_one hfin hx_mem hψ_mem hx0
  have hnormne : (‖x'‖ : ℂ) ≠ 0 := by
    simpa using norm_ne_zero_iff.mpr hx'0
  refine ⟨c * (‖x'‖ : ℂ), ?_⟩
  have hψx : ψ = c • x' := by
    apply WithLp.ofLp_injective 2
    exact hc.symm
  rw [hψx, smul_smul, mul_assoc, mul_inv_cancel₀ hnormne, mul_one]

/-- **The second-order effective Hamiltonian is block-diagonal on the kernel of `H0`.**
Writing `Ĥeff = secondOrderEffectiveHamiltonian H0 V H0inv` and `P̂₀ = kernelProjectionMatrix H0`,
one has `Ĥeff = P̂₀ · Ĥeff · P̂₀`; a direct consequence of idempotence of
`kernelProjectionMatrix`, supplying the `hblock` hypothesis of
`isUniqueGroundStateOn_coordinateSpan_iff_submatrix` for `Ĥeff` generically (once `P̂₀` is
identified with a coordinate-block indicator via `matrixKernel_diagonal_eq_coordinateSpan`). -/
theorem secondOrderEffectiveHamiltonian_eq_kernelProjectionMatrix_conj
    (H0 V H0inv : Matrix n n ℂ) :
    secondOrderEffectiveHamiltonian H0 V H0inv
      = kernelProjectionMatrix H0 * secondOrderEffectiveHamiltonian H0 V H0inv
        * kernelProjectionMatrix H0 := by
  have hP := kernelProjectionMatrix_isIdempotent H0
  have hconj : kernelProjectionMatrix H0
        * (kernelProjectionMatrix H0 * V * H0inv * V * kernelProjectionMatrix H0)
        * kernelProjectionMatrix H0
      = kernelProjectionMatrix H0 * V * H0inv * V * kernelProjectionMatrix H0 := by
    simp only [← Matrix.mul_assoc, hP]
    rw [Matrix.mul_assoc _ (kernelProjectionMatrix H0) (kernelProjectionMatrix H0), hP]
  rw [secondOrderEffectiveHamiltonian, Matrix.mul_neg, Matrix.neg_mul, hconj]

/-- **The eigenspace analogue of `matrixKernel_diagonal_eq_coordinateSpan`.** If a diagonal
matrix's entries equal `L` exactly on a decidable predicate `P`, its `L`-eigenspace (as a subspace
of `EuclideanSpace ℂ n`) is the coordinate span of `P`. -/
theorem eigenspace_diagonal_eq_coordinateSpan (d : n → ℂ) (L : ℂ) (P : n → Prop) [DecidablePred P]
    (hP : ∀ i, d i = L ↔ P i) :
    Module.End.eigenspace (Matrix.toEuclideanLin (Matrix.diagonal d)) L = coordinateSpan P := by
  refine Submodule.ext fun v => ?_
  rw [Module.End.mem_eigenspace_iff, mem_coordinateSpan_iff]
  have hval : ∀ i, (Matrix.toEuclideanLin (Matrix.diagonal d) v) i = d i * v i := by
    intro i
    change (Matrix.diagonal d).mulVec (WithLp.ofLp v) i = _
    rw [Matrix.mulVec_diagonal]
  have hsmul : ∀ i, (L • v) i = L * v i := fun _ => rfl
  constructor
  · intro hv i hi
    have hi' : (Matrix.toEuclideanLin (Matrix.diagonal d) v) i = (L • v) i := by rw [hv]
    rw [hval i, hsmul i] at hi'
    have hzero : (d i - L) * v i = 0 := by rw [sub_mul, hi', sub_self]
    exact (mul_eq_zero.mp hzero).resolve_left fun h => hi ((hP i).mp (sub_eq_zero.mp h))
  · intro hv
    refine PiLp.ext fun i => ?_
    rw [hval i, hsmul i]
    by_cases h : P i
    · rw [(hP i).mpr h]
    · rw [hv i h, mul_zero, mul_zero]

omit [DecidableEq n] in
/-- **An intersection of coordinate spans is a coordinate span.** If a predicate `R` is the
conjunction of `P` and `Q` pointwise, then `coordinateSpan P ⊓ coordinateSpan Q = coordinateSpan R`.
The conjunction is passed as a separate predicate `R` with a defining `Iff`, rather than as the
literal `fun i => P i ∧ Q i`, so that callers may compose the two supports into any equivalent
(and independently decidable) form. -/
theorem coordinateSpan_inf_coordinateSpan (P Q R : n → Prop) [DecidablePred P] [DecidablePred Q]
    [DecidablePred R] (hR : ∀ i, R i ↔ P i ∧ Q i) :
    coordinateSpan P ⊓ coordinateSpan Q = coordinateSpan R := by
  refine Submodule.ext fun v => ?_
  rw [Submodule.mem_inf, mem_coordinateSpan_iff, mem_coordinateSpan_iff, mem_coordinateSpan_iff]
  constructor
  · rintro ⟨hP, hQ⟩ i hi
    by_cases h : P i
    · exact hQ i fun hq => hi ((hR i).mpr ⟨h, hq⟩)
    · exact hP i h
  · intro h
    exact ⟨fun i hi => h i fun hr => hi ((hR i).mp hr).1,
      fun i hi => h i fun hr => hi ((hR i).mp hr).2⟩

/-- **`IsUniqueGroundStateOn` restricts downward along a submodule inclusion.** If `H` has a
unique ground state `φ` on a submodule `K'`, and `φ` lies in a smaller submodule `K ≤ K'`, then
`φ` is also the unique ground state of `H` on `K`. -/
theorem IsUniqueGroundStateOn.mono {K K' : Submodule ℂ (EuclideanSpace ℂ n)} (hKK' : K ≤ K')
    {H : Matrix n n ℂ} {E : ℝ} {φ : EuclideanSpace ℂ n} (hφK : φ ∈ K)
    (hGS : IsUniqueGroundStateOn K' H E φ) : IsUniqueGroundStateOn K H E φ := by
  obtain ⟨-, hnorm, heig, hground, huniq⟩ := hGS
  have hne : φ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  refine ⟨hφK, hnorm, heig, ⟨⟨φ, hφK, hne, heig⟩, ?_⟩, ?_⟩
  · rintro μ ⟨ψ, hψmem, hψ0, hψeig⟩
    exact hground.2 μ ⟨ψ, hKK' hψmem, hψ0, hψeig⟩
  · intro ψ hψmem hψeig
    exact huniq ψ (hKK' hψmem) hψeig

end LatticeSystem.Math
