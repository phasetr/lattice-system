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

/-- **An inactive site projects to zero**: if `(P₀)_{xx} = 0` then `P₀ e_x = 0` (the basis vector
`e_x` lies entirely in `(ker T)ᗮ`).  Contrapositive of the active-site criterion. -/
theorem generalFlatBand_proj_apply_eq_zero_of_diag_zero (x : Fin (M + 1))
    (h : generalFlatBandProjectionMatrix T x x = 0) :
    (generalFlatBandKernel T).starProjection (EuclideanSpace.basisFun (Fin (M + 1)) ℂ x) = 0 := by
  rw [Submodule.starProjection_apply_eq_zero_iff]
  by_contra hmem
  exact (generalFlatBand_diag_ne_zero_iff T x).mpr hmem h

/-- **An inactive site has a zero projection row**: if `(P₀)_{xx} = 0` then `(P₀)_{xy} = 0` for
every `y`.  Self-adjointness moves `P₀` onto `e_x`, which projects to zero. -/
theorem generalFlatBand_proj_row_eq_zero_of_diag_zero (x y : Fin (M + 1))
    (h : generalFlatBandProjectionMatrix T x x = 0) :
    generalFlatBandProjectionMatrix T x y = 0 := by
  rw [generalFlatBandProjectionMatrix_apply,
    ← Submodule.inner_starProjection_left_eq_right,
    generalFlatBand_proj_apply_eq_zero_of_diag_zero T x h, inner_zero_left]

/-- **Off-diagonal projection entry as an inner product of projected basis vectors**:
`(P₀)_{xy} = ⟪P₀ e_x, P₀ e_y⟫`.  Idempotence and self-adjointness move both `P₀`'s onto the basis
vectors. -/
theorem generalFlatBand_proj_offdiag_eq (x y : Fin (M + 1)) :
    generalFlatBandProjectionMatrix T x y
      = inner ℂ
          ((generalFlatBandKernel T).starProjection
            (EuclideanSpace.basisFun (Fin (M + 1)) ℂ x))
          ((generalFlatBandKernel T).starProjection
            (EuclideanSpace.basisFun (Fin (M + 1)) ℂ y)) := by
  rw [generalFlatBandProjectionMatrix_apply]
  conv_lhs => rw [← (generalFlatBandKernel T).isIdempotentElem_starProjection.eq]
  exact (Submodule.inner_starProjection_left_eq_right (generalFlatBandKernel T) _ _).symm

/-- **Support edges connect active sites**: if `(P₀)_{xy} ≠ 0` then both `x` and `y` are active
(`(P₀)_{xx} ≠ 0` and `(P₀)_{yy} ≠ 0`).  An inactive site has a zero projection row (and, by
symmetry, column), so the support graph of `P₀` lives on `Λ₀`. -/
theorem generalFlatBand_proj_active_of_ne_zero (x y : Fin (M + 1))
    (h : generalFlatBandProjectionMatrix T x y ≠ 0) :
    generalFlatBandProjectionMatrix T x x ≠ 0 ∧ generalFlatBandProjectionMatrix T y y ≠ 0 := by
  refine ⟨fun hx => h (generalFlatBand_proj_row_eq_zero_of_diag_zero T x y hx), fun hy => h ?_⟩
  have hyx := generalFlatBand_proj_row_eq_zero_of_diag_zero T y x hy
  rw [← (generalFlatBandProjectionMatrix_isHermitian T).apply y x] at hyx
  exact (star_eq_zero.mp hyx)

/-- **Special-basis vectors with disjoint site supports are orthogonal**: if for every site `x`
either `μ_z(x) = 0` or `μ_{z'}(x) = 0`, then `⟪μ_z, μ_{z'}⟫ = 0`.  The inner product is the
site-sum `Σ_x conj(μ_z(x)) μ_{z'}(x)`, and every term vanishes.  This makes the per-side flat-band
subspaces of a basis cut orthogonal. -/
theorem generalFlatBand_mu_orthogonal_of_disjoint_support
    (μ : Fin (M + 1) → Fin (M + 1) → ℂ) (z z' : Fin (M + 1))
    (hdisj : ∀ x, μ z x = 0 ∨ μ z' x = 0) :
    inner ℂ (WithLp.toLp 2 (μ z) : EuclideanSpace ℂ (Fin (M + 1)))
        (WithLp.toLp 2 (μ z')) = 0 := by
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero (fun x _ => ?_)
  rcases hdisj x with h | h <;> simp [RCLike.inner_apply, h]

/-- **No site is shared across a basis cut**: if a set `J ⊆ I` is closed under basis-graph
adjacency (a union of connected components), then no site `x` is covered by both a `J`-index and an
`(I∖J)`-index.  A shared site would be a basis edge `z ~ z'` (`z ∈ J`, `z' ∉ J`), forcing `z' ∈ J` —
contradiction.  This makes the active-site side-assignment of a basis cut well-defined. -/
theorem generalFlatBand_no_shared_site_of_saturated {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} {J : Finset ↥I}
    (hsat : ∀ z ∈ J, ∀ z' : ↥I, (generalFlatBandBasisGraph I μ).Adj z z' → z' ∈ J)
    {x : Fin (M + 1)} {z : ↥I} (hz : z ∈ J) (hzx : μ z.1 x ≠ 0)
    {z' : ↥I} (hz' : z' ∉ J) (hz'x : μ z'.1 x ≠ 0) : False := by
  have hne : z ≠ z' := fun h => hz' (h ▸ hz)
  exact hz' (hsat z hz z' ⟨fun h => hne (Subtype.ext h), x, hzx, hz'x⟩)

/-- **A basis vector with no support from a side is orthogonal to that side's flat-band subspace**:
if every `μ_z` (`z ∈ J`) vanishes at `x`, then `e_x ⊥ span{μ_z : z ∈ J}`.  Each generator gives
`⟪μ_z, e_x⟫ = conj(μ_z(x)) = 0`, so `e_x` is orthogonal to the span.  This places `P₀ e_x` in the
complementary side, the heart of the block-diagonal decomposition. -/
theorem generalFlatBand_basisVec_mem_orthogonal_of_side {I : Finset (Fin (M + 1))}
    (μ : Fin (M + 1) → Fin (M + 1) → ℂ) (S : Set ↥I) {x : Fin (M + 1)}
    (hx : ∀ z ∈ S, μ z.1 x = 0) :
    EuclideanSpace.basisFun (Fin (M + 1)) ℂ x
      ∈ (Submodule.span ℂ ((fun z : ↥I =>
        (WithLp.toLp 2 (μ z.1) : EuclideanSpace ℂ (Fin (M + 1)))) '' S))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro v hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨z, hzS, rfl⟩ := hw
    rw [← inner_conj_symm, EuclideanSpace.basisFun_inner]
    simp [hx z hzS]
  | zero => simp
  | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
  | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]

/-- **`P₀` preserves orthogonality to a flat-band subspace**: if `V ≤ ker T` and `e_x ⊥ V`, then
`P₀ e_x ⊥ V`.  For `w ∈ V ⊆ ker T`, `P₀` fixes `w`, so by self-adjointness
`⟪w, P₀ e_x⟫ = ⟪P₀ w, e_x⟫ = ⟪w, e_x⟫ = 0`.  Combined with the side orthogonality this places
`P₀ e_x` on the same side as `x`. -/
theorem generalFlatBand_proj_mem_orthogonal {V : Submodule ℂ (EuclideanSpace ℂ (Fin (M + 1)))}
    (hV : V ≤ generalFlatBandKernel T) {x : Fin (M + 1)}
    (hx : EuclideanSpace.basisFun (Fin (M + 1)) ℂ x ∈ Vᗮ) :
    (generalFlatBandKernel T).starProjection (EuclideanSpace.basisFun (Fin (M + 1)) ℂ x) ∈ Vᗮ := by
  rw [Submodule.mem_orthogonal]
  intro w hw
  rw [← Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr (hV hw)]
  exact (Submodule.mem_orthogonal _ _).mp hx w hw

end LatticeSystem.Fermion
