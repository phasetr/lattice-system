import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBand

/-!
# Flat-band projection matrix P₀: foundations (Tasaki §11.3.4, toward Theorem 11.15)

The orthogonal projection `P₀` onto the flat band `ker T` (`generalFlatBandProjectionMatrix`) is
Hermitian and idempotent, and its entries are inner products `(P₀)_{xy} = ⟪e_x, P₀ e_y⟫`.  These are
the foundations of the bridge
`generalFlatBandProjectionIrreducible T ↔ generalFlatBandBasisConnected I μ` that (composed with the
proved Theorem 11.17) discharges Theorem 11.15.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed., Springer, 2020), §11.3.4, Theorem 11.15, pp. 408-412.  Tracked in Issue #4453.
-/

namespace LatticeSystem.Fermion

open Matrix
open scoped ComplexOrder

variable {M : ℕ} (T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ)

/-- **The projection-matrix entry as an inner product**: `(P₀)_{xy} = ⟪e_x, P₀ e_y⟫`, the
orthonormal-basis matrix element of the orthogonal projection onto `ker T`. -/
theorem generalFlatBandProjectionMatrix_apply (x y : Fin (M + 1)) :
    generalFlatBandProjectionMatrix T x y
      = inner ℂ (EuclideanSpace.basisFun (Fin (M + 1)) ℂ x)
        ((generalFlatBandKernel T).starProjection
          (EuclideanSpace.basisFun (Fin (M + 1)) ℂ y)) := by
  rw [generalFlatBandProjectionMatrix, LinearMap.toMatrixOrthonormal_apply_apply]
  rfl

/-- **`P₀` is Hermitian**: the orthogonal projection onto `ker T` is self-adjoint, so its
orthonormal-basis matrix is Hermitian.  Hence the support matrix `|(P₀)_{xy}|²` is symmetric and its
irreducibility is the strong connectivity of an *undirected* support graph. -/
theorem generalFlatBandProjectionMatrix_isHermitian :
    (generalFlatBandProjectionMatrix T).IsHermitian := by
  ext x y
  rw [Matrix.conjTranspose_apply, generalFlatBandProjectionMatrix_apply,
    generalFlatBandProjectionMatrix_apply, ← starRingEnd_apply, inner_conj_symm]
  exact (Submodule.inner_starProjection_left_eq_right (generalFlatBandKernel T) _ _)

/-- **`P₀` is idempotent**: `P₀ · P₀ = P₀` (the matrix of a projection). -/
theorem generalFlatBandProjectionMatrix_isIdempotent :
    generalFlatBandProjectionMatrix T * generalFlatBandProjectionMatrix T
      = generalFlatBandProjectionMatrix T := by
  have h := (generalFlatBandKernel T).isIdempotentElem_starProjection
  unfold generalFlatBandProjectionMatrix
  rw [← map_mul (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin (M + 1)) ℂ))]
  congr 1
  rw [← ContinuousLinearMap.coe_mul, h]

/-- **The diagonal projection density is the squared norm of the projected basis vector**:
`(P₀)_{xx} = ⟪P₀ e_x, P₀ e_x⟫`.  Self-adjointness moves one `P₀` across the inner product and
idempotence merges them, so the diagonal entry equals `‖P₀ e_x‖²`. -/
theorem generalFlatBandProjectionMatrix_diag_eq (x : Fin (M + 1)) :
    generalFlatBandProjectionMatrix T x x
      = inner ℂ
          ((generalFlatBandKernel T).starProjection
            (EuclideanSpace.basisFun (Fin (M + 1)) ℂ x))
          ((generalFlatBandKernel T).starProjection
            (EuclideanSpace.basisFun (Fin (M + 1)) ℂ x)) := by
  rw [generalFlatBandProjectionMatrix_apply]
  conv_lhs => rw [← (generalFlatBandKernel T).isIdempotentElem_starProjection.eq]
  exact (Submodule.inner_starProjection_left_eq_right (generalFlatBandKernel T) _ _).symm

/-- **Active site ⟺ the basis vector is not orthogonal to the flat band**: `(P₀)_{xx} ≠ 0` iff
`P₀ e_x ≠ 0` iff `e_x ∉ (ker T)ᗮ`.  The diagonal density `‖P₀ e_x‖²` is nonzero exactly when the
projection of `e_x` onto the flat band is nonzero. -/
theorem generalFlatBand_diag_ne_zero_iff (x : Fin (M + 1)) :
    generalFlatBandProjectionMatrix T x x ≠ 0
      ↔ EuclideanSpace.basisFun (Fin (M + 1)) ℂ x ∉ (generalFlatBandKernel T)ᗮ := by
  rw [generalFlatBandProjectionMatrix_diag_eq, ← Submodule.starProjection_apply_eq_zero_iff,
    ne_eq, not_iff_not, inner_self_eq_zero]

/-- **A special-basis vector lies in the flat band** (as a Euclidean vector): for `z ∈ I`,
`μ_z ∈ ker T`.  `T.mulVec (μ z) = 0` lifts to `toEuclideanLin T (toLp μ_z) = 0`. -/
theorem generalFlatBand_mu_mem_kernel {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {z : Fin (M + 1)} (hz : z ∈ I) :
    (WithLp.toLp 2 (μ z) : EuclideanSpace ℂ (Fin (M + 1))) ∈ generalFlatBandKernel T := by
  rw [generalFlatBandKernel, LinearMap.mem_ker]
  have hrfl : Matrix.toEuclideanLin T (WithLp.toLp 2 (μ z))
      = WithLp.toLp 2 (T.mulVec (μ z)) := rfl
  rw [hrfl, hbasis.2.1 z hz]
  rfl

/-- **Every index site is active**: `I ⊆ Λ₀`.  For `z ∈ I` the localised vector `μ_z` lies in the
flat band and has `μ_z(z) ≠ 0`, so `e_z` is not orthogonal to `ker T`, i.e. `(P₀)_{zz} ≠ 0`. -/
theorem generalFlatBand_special_index_active {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {z : Fin (M + 1)} (hz : z ∈ I) :
    generalFlatBandProjectionMatrix T z z ≠ 0 := by
  rw [generalFlatBand_diag_ne_zero_iff]
  intro hperp
  have hortho := (Submodule.mem_orthogonal _ _).mp hperp (WithLp.toLp 2 (μ z))
    (generalFlatBand_mu_mem_kernel T hbasis hz)
  rw [← inner_conj_symm, EuclideanSpace.basisFun_inner] at hortho
  exact hbasis.2.2.2.1 z hz (by simpa using hortho)

/-- **The flat band is spanned by the special basis**: `ker T = span{μ_z : z ∈ I}` (as Euclidean
vectors).  The `|I| = D₀` vectors `μ_z` are linearly independent and lie in `ker T`, whose dimension
is `D₀`, so they span it. -/
theorem generalFlatBand_kernel_eq_span {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ) :
    generalFlatBandKernel T
      = Submodule.span ℂ (Set.range (fun z : I =>
        (WithLp.toLp 2 (μ z.1) : EuclideanSpace ℂ (Fin (M + 1))))) := by
  have hli : LinearIndependent ℂ
      (fun z : I => (WithLp.toLp 2 (μ z.1) : EuclideanSpace ℂ (Fin (M + 1)))) :=
    hbasis.2.2.1.map' (WithLp.linearEquiv 2 ℂ (Fin (M + 1) → ℂ)).symm.toLinearMap
      (LinearEquiv.ker _)
  refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
  · rw [Submodule.span_le]
    rintro v ⟨z, rfl⟩
    exact generalFlatBand_mu_mem_kernel T hbasis z.2
  · rw [finrank_span_eq_card hli, Fintype.card_coe,
      show Module.finrank ℂ ↥(generalFlatBandKernel T) = generalFlatBandDim T from rfl, ← hbasis.1]

/-- **Active site ⟺ covered by a special-basis vector**: `(P₀)_{xx} ≠ 0` iff some `μ_z` (`z ∈ I`)
has `μ_z(x) ≠ 0`.  Since `ker T = span{μ_z}`, `e_x` is non-orthogonal to the flat band exactly when
some spanning vector has a nonzero `x`-coordinate. -/
theorem generalFlatBand_active_iff_exists_mu_ne {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (x : Fin (M + 1)) :
    generalFlatBandProjectionMatrix T x x ≠ 0 ↔ ∃ z ∈ I, μ z x ≠ 0 := by
  rw [generalFlatBand_diag_ne_zero_iff]
  constructor
  · intro hperp
    by_contra hall
    push Not at hall
    apply hperp
    rw [Submodule.mem_orthogonal]
    intro v hv
    rw [generalFlatBand_kernel_eq_span T hbasis] at hv
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨z, rfl⟩ := hw
      rw [← inner_conj_symm, EuclideanSpace.basisFun_inner]
      simp [hall z.1 z.2]
    | zero => simp
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]
  · rintro ⟨z, hz, hzx⟩
    intro hperp
    have hortho := (Submodule.mem_orthogonal _ _).mp hperp (WithLp.toLp 2 (μ z))
      (generalFlatBand_mu_mem_kernel T hbasis hz)
    rw [← inner_conj_symm, EuclideanSpace.basisFun_inner] at hortho
    exact hzx (by simpa using hortho)

/-- **The projection support matrix is symmetric**: `|P₀_{xy}|² = |P₀_{yx}|²`.  Since `P₀` is
Hermitian (`P₀_{yx} = conj P₀_{xy}`) and `normSq` is conjugation-invariant, the real nonnegative
support matrix on `Λ₀` is symmetric — its irreducibility is the connectivity of an *undirected*
support graph (strong connectivity = connectivity for a symmetric nonnegative matrix). -/
theorem generalFlatBandProjectionSupportMatrix_isSymm :
    (generalFlatBandProjectionSupportMatrix T).IsSymm := by
  ext x y
  simp only [Matrix.transpose_apply, generalFlatBandProjectionSupportMatrix]
  rw [← (generalFlatBandProjectionMatrix_isHermitian T).apply x.1 y.1, ← starRingEnd_apply,
    Complex.normSq_conj]

/-- **Special-basis coordinates determine flat-band vectors**: a flat-band vector vanishing at every
index site is zero.  Writing `v = Σ_z c_z μ_z` (`ker T = span{μ_z}`) and evaluating at an index `w`,
the localisation `μ_{z'}(w) = δ_{z'w}μ_w(w)` collapses the sum to `c_w μ_w(w)`; since `v_w = 0` and
`μ_w(w) ≠ 0`, every coefficient vanishes.  This is the engine of the cut/block argument: a flat-band
vector supported off a coordinate block is killed. -/
theorem generalFlatBand_kernel_coord_determined {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {v : EuclideanSpace ℂ (Fin (M + 1))} (hv : v ∈ generalFlatBandKernel T)
    (hcoord : ∀ w ∈ I, WithLp.ofLp v w = 0) : v = 0 := by
  classical
  rw [generalFlatBand_kernel_eq_span T hbasis, Submodule.mem_span_range_iff_exists_fun] at hv
  obtain ⟨c, hc⟩ := hv
  have hc0 : ∀ z : I, c z = 0 := by
    intro z
    have hz : inner ℂ (EuclideanSpace.basisFun (Fin (M + 1)) ℂ z.1) v = 0 := by
      rw [EuclideanSpace.basisFun_inner]; exact hcoord z.1 z.2
    rw [← hc, inner_sum] at hz
    simp only [inner_smul_right, EuclideanSpace.basisFun_inner] at hz
    rw [Finset.sum_eq_single z (fun z' _ hz' => by
      rw [hbasis.2.2.2.2 z'.1 z'.2 z.1 z.2 (fun h => hz' (Subtype.ext h)), mul_zero])
      (fun h => absurd (Finset.mem_univ z) h)] at hz
    exact (mul_eq_zero.mp hz).resolve_right (hbasis.2.2.2.1 z.1 z.2)
  rw [← hc]
  simp only [hc0, zero_smul, Finset.sum_const_zero]

end LatticeSystem.Fermion
