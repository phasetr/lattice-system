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

/-- **The flat band splits over a cut of the index set**: for any `S ⊆ I`,
`ker T = span{μ_z : z ∈ S} ⊔ span{μ_z : z ∈ Sᶜ}`.  The full spanning set is the union of the two
sides, and `span` distributes over a union.  Together with side-orthogonality this is the orthogonal
block decomposition of `ker T`. -/
theorem generalFlatBand_kernel_eq_sup {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (S : Set ↥I) :
    generalFlatBandKernel T
      = Submodule.span ℂ ((fun z : ↥I =>
          (WithLp.toLp 2 (μ z.1) : EuclideanSpace ℂ (Fin (M + 1)))) '' S)
        ⊔ Submodule.span ℂ ((fun z : ↥I =>
          (WithLp.toLp 2 (μ z.1) : EuclideanSpace ℂ (Fin (M + 1)))) '' Sᶜ) := by
  rw [generalFlatBand_kernel_eq_span T hbasis, ← Submodule.span_union, ← Set.image_union,
    Set.union_compl_self, Set.image_univ]

/-- **The two sides of a disjoint-support cut span orthogonal subspaces**: if every `μ_z` (`z ∈ S`)
and `μ_{z'}` (`z' ∈ Sᶜ`) have disjoint site supports, then `span{μ_z : z ∈ S} ⊥ span{μ_z : z ∈ Sᶜ}`.
Each generator pair is orthogonal (`generalFlatBand_mu_orthogonal_of_disjoint_support`), and
orthogonality lifts through the span on both sides.  For a saturated basis cut the hypothesis is
supplied by `generalFlatBand_no_shared_site_of_saturated`. -/
theorem generalFlatBand_side_subspaces_orthogonal {I : Finset (Fin (M + 1))}
    (μ : Fin (M + 1) → Fin (M + 1) → ℂ) (S : Set ↥I)
    (hdisj : ∀ z ∈ S, ∀ z' ∈ Sᶜ, ∀ x, μ z.1 x = 0 ∨ μ z'.1 x = 0) :
    Submodule.span ℂ ((fun z : ↥I =>
        (WithLp.toLp 2 (μ z.1) : EuclideanSpace ℂ (Fin (M + 1)))) '' S)
      ≤ (Submodule.span ℂ ((fun z : ↥I =>
        (WithLp.toLp 2 (μ z.1) : EuclideanSpace ℂ (Fin (M + 1)))) '' Sᶜ))ᗮ := by
  rw [Submodule.span_le]
  rintro _ ⟨z, hzS, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_orthogonal]
  intro v hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨z', hz'S, rfl⟩ := hw
    exact generalFlatBand_mu_orthogonal_of_disjoint_support μ z'.1 z.1
      (fun x => (hdisj z hzS z' hz'S x).symm)
  | zero => rw [inner_zero_left]
  | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
  | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]

/-- **The projection of a side basis vector lands on that same side**: for a disjoint-support cut
`S`, if every `μ_z` (`z ∈ S`) vanishes at `y` (so `y` is on the `Sᶜ`-side), then
`P₀ e_y ∈ span{μ_z : z ∈ Sᶜ}`.  Indeed `P₀ e_y ∈ ker T = V_S ⊕ V_Sᶜ` decomposes as `a + b`
(`a ∈ V_S`, `b ∈ V_Sᶜ`); but `P₀ e_y ⊥ V_S` (from `e_y ⊥ V_S` preserved by `P₀`) and `V_S ⊥ V_Sᶜ`
force `⟪a, a⟫ = ⟪a, P₀ e_y⟫ = 0`, so `a = 0` and `P₀ e_y = b ∈ V_Sᶜ`.  This is the block-diagonal
heart: `P₀` carries each side into itself. -/
theorem generalFlatBand_proj_mem_side {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (S : Set ↥I) (hdisj : ∀ z ∈ S, ∀ z' ∈ Sᶜ, ∀ x, μ z.1 x = 0 ∨ μ z'.1 x = 0)
    {y : Fin (M + 1)} (hy : ∀ z ∈ S, μ z.1 y = 0) :
    (generalFlatBandKernel T).starProjection (EuclideanSpace.basisFun (Fin (M + 1)) ℂ y)
      ∈ Submodule.span ℂ ((fun z : ↥I =>
        (WithLp.toLp 2 (μ z.1) : EuclideanSpace ℂ (Fin (M + 1)))) '' Sᶜ) := by
  set Pe := (generalFlatBandKernel T).starProjection
    (EuclideanSpace.basisFun (Fin (M + 1)) ℂ y) with hPe
  have hVS_le : Submodule.span ℂ ((fun z : ↥I =>
      (WithLp.toLp 2 (μ z.1) : EuclideanSpace ℂ (Fin (M + 1)))) '' S)
      ≤ generalFlatBandKernel T :=
    le_sup_left.trans (generalFlatBand_kernel_eq_sup T hbasis S).ge
  have hmemK : Pe ∈ generalFlatBandKernel T := Submodule.starProjection_apply_mem _ _
  rw [generalFlatBand_kernel_eq_sup T hbasis S] at hmemK
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmemK
  have hPeS : Pe ∈ (Submodule.span ℂ ((fun z : ↥I =>
      (WithLp.toLp 2 (μ z.1) : EuclideanSpace ℂ (Fin (M + 1)))) '' S))ᗮ :=
    generalFlatBand_proj_mem_orthogonal T hVS_le
      (generalFlatBand_basisVec_mem_orthogonal_of_side μ S hy)
  have ha0 : a = 0 := by
    have h1 : inner ℂ a Pe = 0 := (Submodule.mem_orthogonal _ _).mp hPeS a ha
    have h2 : inner ℂ a b = (0 : ℂ) := by
      have hba : inner ℂ b a = (0 : ℂ) :=
        (Submodule.mem_orthogonal _ _).mp
          (generalFlatBand_side_subspaces_orthogonal μ S hdisj ha) b hb
      rw [← inner_conj_symm, hba, map_zero]
    rw [← hab, inner_add_right, h2, add_zero] at h1
    exact inner_self_eq_zero.mp h1
  rw [← hab, ha0, zero_add]
  exact hb

/-- **The projection is block-diagonal across a basis cut**: if `x` is supported only by the
`S`-side (every `μ_z`, `z ∈ Sᶜ`, vanishes at `x`) and `y` only by the `Sᶜ`-side, then
`(P₀)_{xy} = 0`.  Indeed `(P₀)_{xy} = ⟪P₀ e_x, P₀ e_y⟫` with `P₀ e_x ∈ V_S`, `P₀ e_y ∈ V_Sᶜ`
(`generalFlatBand_proj_mem_side`, the `S`-side case via `compl_compl`), and `V_S ⊥ V_Sᶜ`.  This is
the block-diagonal structure: `P₀` has no entries linking the two sides of a basis cut. -/
theorem generalFlatBand_proj_offdiag_eq_zero_across_cut {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (S : Set ↥I) (hdisj : ∀ z ∈ S, ∀ z' ∈ Sᶜ, ∀ x, μ z.1 x = 0 ∨ μ z'.1 x = 0)
    {x y : Fin (M + 1)} (hxS : ∀ z ∈ Sᶜ, μ z.1 x = 0) (hyS : ∀ z ∈ S, μ z.1 y = 0) :
    generalFlatBandProjectionMatrix T x y = 0 := by
  have hPy : (generalFlatBandKernel T).starProjection
      (EuclideanSpace.basisFun (Fin (M + 1)) ℂ y)
      ∈ Submodule.span ℂ ((fun z : ↥I =>
        (WithLp.toLp 2 (μ z.1) : EuclideanSpace ℂ (Fin (M + 1)))) '' Sᶜ) :=
    generalFlatBand_proj_mem_side T hbasis S hdisj hyS
  have hPx : (generalFlatBandKernel T).starProjection
      (EuclideanSpace.basisFun (Fin (M + 1)) ℂ x)
      ∈ Submodule.span ℂ ((fun z : ↥I =>
        (WithLp.toLp 2 (μ z.1) : EuclideanSpace ℂ (Fin (M + 1)))) '' S) := by
    have h := generalFlatBand_proj_mem_side T hbasis Sᶜ
      (fun z hz z' hz' xx => (hdisj z' (by simpa using hz') z hz xx).symm) hxS
    simpa only [compl_compl] using h
  rw [generalFlatBand_proj_offdiag_eq T x y, ← inner_conj_symm,
    (Submodule.mem_orthogonal _ _).mp
      (generalFlatBand_side_subspaces_orthogonal μ S hdisj hPx) _ hPy, map_zero]

/-- **The projection of a kernel vector expands over the basis**: for `v ∈ ker T`,
`P₀ v = Σ_x v_x (P₀ e_x)` (since `v = Σ_x v_x e_x` and `P₀` is linear). -/
theorem generalFlatBand_starProjection_expand
    {v : EuclideanSpace ℂ (Fin (M + 1))} :
    (generalFlatBandKernel T).starProjection v
      = ∑ x, v x • (generalFlatBandKernel T).starProjection
          (EuclideanSpace.basisFun (Fin (M + 1)) ℂ x) := by
  have hexpand : v = ∑ x, v x •
      (EuclideanSpace.basisFun (Fin (M + 1)) ℂ x : EuclideanSpace ℂ (Fin (M + 1))) := by
    have h := (EuclideanSpace.basisFun (Fin (M + 1)) ℂ).sum_repr v
    simp only [EuclideanSpace.basisFun_repr] at h
    exact h.symm
  conv_lhs => rw [hexpand]
  rw [map_sum]
  simp only [map_smul]

/-- **Matrix–vector form of the projection on a kernel vector**: for `v ∈ ker T`,
`v y = Σ_x v_x (P₀)_{yx}`.  Indeed `v = P₀ v` and expanding `v = Σ_x v_x e_x` through the linear
`P₀` gives `⟪e_y, v⟫ = ⟪e_y, P₀ v⟫ = Σ_x v_x ⟪e_y, P₀ e_x⟫`. -/
theorem generalFlatBand_kernel_coord_matvec
    {v : EuclideanSpace ℂ (Fin (M + 1))} (hv : v ∈ generalFlatBandKernel T) (y : Fin (M + 1)) :
    v y = ∑ x, v x * generalFlatBandProjectionMatrix T y x := by
  have hvfix : (generalFlatBandKernel T).starProjection v = v :=
    Submodule.starProjection_eq_self_iff.mpr hv
  calc v y = inner ℂ (EuclideanSpace.basisFun (Fin (M + 1)) ℂ y) v := by
        rw [EuclideanSpace.basisFun_inner]
    _ = inner ℂ (EuclideanSpace.basisFun (Fin (M + 1)) ℂ y)
          (∑ x, v x • (generalFlatBandKernel T).starProjection
            (EuclideanSpace.basisFun (Fin (M + 1)) ℂ x)) := by
        rw [← generalFlatBand_starProjection_expand, hvfix]
    _ = ∑ x, v x * generalFlatBandProjectionMatrix T y x := by
        rw [inner_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [inner_smul_right, ← generalFlatBandProjectionMatrix_apply]

/-- **Coordinate restriction of a kernel vector across a `P₀`-block cut stays in `ker T`**: if `W`
is a coordinate set with no `P₀` entries linking it to its complement (`(P₀)_{yx} = 0` for `x ∈ W`,
`y ∉ W`), then for `v ∈ ker T` the truncation `1_W · v = Σ_{x∈W} v_x e_x` is again in `ker T`.
Indeed `1_W·v = Σ_{x∈W} v_x (P₀ e_x)` (a sum of kernel elements): for `y ∈ W` the block hypothesis
(with `P₀` Hermitian) kills the `x∉W` part of `v_y = Σ_x v_x (P₀)_{yx}`, and for `y ∉ W` the
`x∈W` sum vanishes outright.  This is the linear-algebra core of "`P₀` reducible ⟹ basis cut". -/
theorem generalFlatBand_restrict_mem_kernel (W : Finset (Fin (M + 1)))
    (hcol : ∀ x ∈ W, ∀ y ∉ W, generalFlatBandProjectionMatrix T y x = 0)
    {v : EuclideanSpace ℂ (Fin (M + 1))} (hv : v ∈ generalFlatBandKernel T) :
    (∑ x ∈ W, v x • (EuclideanSpace.basisFun (Fin (M + 1)) ℂ x :
      EuclideanSpace ℂ (Fin (M + 1)))) ∈ generalFlatBandKernel T := by
  have hHerm := generalFlatBandProjectionMatrix_isHermitian T
  have key : (∑ x ∈ W, v x • (EuclideanSpace.basisFun (Fin (M + 1)) ℂ x :
        EuclideanSpace ℂ (Fin (M + 1))))
      = ∑ x ∈ W, v x • (generalFlatBandKernel T).starProjection
          (EuclideanSpace.basisFun (Fin (M + 1)) ℂ x) := by
    ext y
    have coord : ∀ w : EuclideanSpace ℂ (Fin (M + 1)),
        w y = inner ℂ (EuclideanSpace.basisFun (Fin (M + 1)) ℂ y) w :=
      fun w => by rw [EuclideanSpace.basisFun_inner]
    have hbf : ∀ a b : Fin (M + 1),
        inner ℂ (EuclideanSpace.basisFun (Fin (M + 1)) ℂ a)
          (EuclideanSpace.basisFun (Fin (M + 1)) ℂ b : EuclideanSpace ℂ (Fin (M + 1)))
          = if a = b then (1 : ℂ) else 0 :=
      fun a b => orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin (M + 1)) ℂ).orthonormal a b
    rw [coord, coord, inner_sum, inner_sum]
    -- LHS term: ⟪e_y, v x • e_x⟫ = if y = x then v x else 0
    have hL : (∑ x ∈ W, inner ℂ (EuclideanSpace.basisFun (Fin (M + 1)) ℂ y)
          (v x • (EuclideanSpace.basisFun (Fin (M + 1)) ℂ x :
            EuclideanSpace ℂ (Fin (M + 1)))))
        = ∑ x ∈ W, (if y = x then v x else 0) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [inner_smul_right, hbf y x]; split_ifs <;> simp
    -- RHS term: ⟪e_y, v x • P₀ e_x⟫ = v x * (P₀)_{yx}
    have hR : (∑ x ∈ W, inner ℂ (EuclideanSpace.basisFun (Fin (M + 1)) ℂ y)
          (v x • (generalFlatBandKernel T).starProjection
            (EuclideanSpace.basisFun (Fin (M + 1)) ℂ x)))
        = ∑ x ∈ W, v x * generalFlatBandProjectionMatrix T y x := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [inner_smul_right, ← generalFlatBandProjectionMatrix_apply]
    rw [hL, hR, Finset.sum_ite_eq W y (fun x => v x)]
    by_cases hy : y ∈ W
    · rw [if_pos hy, generalFlatBand_kernel_coord_matvec T hv y]
      symm
      refine Finset.sum_subset (Finset.subset_univ W) (fun x _ hxW => ?_)
      have hxy : generalFlatBandProjectionMatrix T x y = 0 := hcol y hy x hxW
      have hyx : generalFlatBandProjectionMatrix T y x = 0 := by
        have h := hHerm.apply y x; rw [hxy] at h; simpa using h.symm
      rw [hyx, mul_zero]
    · rw [if_neg hy]
      refine (Finset.sum_eq_zero (fun x hxW => ?_)).symm
      rw [hcol x hxW y hy, mul_zero]
  rw [key]
  exact Submodule.sum_mem _ (fun x _ =>
    Submodule.smul_mem _ _ (Submodule.starProjection_apply_mem _ _))

/-- **Coordinate of a truncation**: `(Σ_{a∈S} v_a e_a)_w = if w ∈ S then v_w else 0`. -/
theorem generalFlatBand_truncation_coord (S : Finset (Fin (M + 1)))
    (v : EuclideanSpace ℂ (Fin (M + 1))) (w : Fin (M + 1)) :
    WithLp.ofLp (∑ a ∈ S, v a • (EuclideanSpace.basisFun (Fin (M + 1)) ℂ a :
      EuclideanSpace ℂ (Fin (M + 1)))) w = if w ∈ S then v w else 0 := by
  have hbf : ∀ a b : Fin (M + 1),
      inner ℂ (EuclideanSpace.basisFun (Fin (M + 1)) ℂ a)
        (EuclideanSpace.basisFun (Fin (M + 1)) ℂ b : EuclideanSpace ℂ (Fin (M + 1)))
        = if a = b then (1 : ℂ) else 0 :=
    fun a b => orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin (M + 1)) ℂ).orthonormal a b
  have hcoord : WithLp.ofLp (∑ a ∈ S, v a • (EuclideanSpace.basisFun (Fin (M + 1)) ℂ a :
        EuclideanSpace ℂ (Fin (M + 1)))) w
      = inner ℂ (EuclideanSpace.basisFun (Fin (M + 1)) ℂ w)
          (∑ a ∈ S, v a • (EuclideanSpace.basisFun (Fin (M + 1)) ℂ a :
            EuclideanSpace ℂ (Fin (M + 1)))) := by
    rw [EuclideanSpace.basisFun_inner]
  rw [hcoord, inner_sum]
  rw [show (∑ a ∈ S, inner ℂ (EuclideanSpace.basisFun (Fin (M + 1)) ℂ w)
        (v a • (EuclideanSpace.basisFun (Fin (M + 1)) ℂ a :
          EuclideanSpace ℂ (Fin (M + 1)))))
      = ∑ a ∈ S, (if w = a then v a else 0) from
    Finset.sum_congr rfl (fun a _ => by
      rw [inner_smul_right, hbf w a]; split_ifs <;> simp)]
  rw [Finset.sum_ite_eq S w (fun a => v a)]

/-- **A special-basis vector confined to a `P₀`-block side**: for a coordinate cut `W` with no `P₀`
entries linking it to its complement (`(P₀)_{yx} = 0` for `x ∈ W`, `y ∉ W`), if the index `z ∈ I`
lies in `W` then `μ_z` is supported entirely in `W` (`μ_z(x) = 0` for `x ∉ W`).  Indeed the
truncation `1_{Wᶜ}·μ_z` is a kernel vector (`generalFlatBand_restrict_mem_kernel`) vanishing at every
index site (at `z` because `z ∈ W`, elsewhere by localisation `μ_z(z') = 0`), hence zero by
`generalFlatBand_kernel_coord_determined`.  So a basis vector cannot straddle a `P₀`-block cut. -/
theorem generalFlatBand_mu_confined_of_block {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (W : Finset (Fin (M + 1)))
    (hblock : ∀ x ∈ W, ∀ y ∉ W, generalFlatBandProjectionMatrix T y x = 0)
    {z : Fin (M + 1)} (hzI : z ∈ I) (hzW : z ∈ W) {x : Fin (M + 1)} (hxW : x ∉ W) :
    μ z x = 0 := by
  classical
  have hvmem : (WithLp.toLp 2 (μ z) : EuclideanSpace ℂ (Fin (M + 1))) ∈ generalFlatBandKernel T :=
    generalFlatBand_mu_mem_kernel T hbasis hzI
  -- symmetric block hypothesis for the complementary side
  have hblock' : ∀ a ∈ Wᶜ, ∀ b ∉ Wᶜ, generalFlatBandProjectionMatrix T b a = 0 := by
    intro a ha b hb
    rw [Finset.mem_compl] at ha
    simp only [Finset.mem_compl, not_not] at hb
    have h := hblock b hb a ha
    have hH := generalFlatBandProjectionMatrix_isHermitian T
    have h2 := hH.apply b a
    rw [h] at h2; simpa using h2.symm
  have hr_mem : (∑ a ∈ Wᶜ, (WithLp.toLp 2 (μ z) : EuclideanSpace ℂ (Fin (M + 1))) a •
      (EuclideanSpace.basisFun (Fin (M + 1)) ℂ a : EuclideanSpace ℂ (Fin (M + 1))))
      ∈ generalFlatBandKernel T :=
    generalFlatBand_restrict_mem_kernel T Wᶜ hblock' hvmem
  have hr0 : (∑ a ∈ Wᶜ, (WithLp.toLp 2 (μ z) : EuclideanSpace ℂ (Fin (M + 1))) a •
      (EuclideanSpace.basisFun (Fin (M + 1)) ℂ a : EuclideanSpace ℂ (Fin (M + 1)))) = 0 := by
    refine generalFlatBand_kernel_coord_determined T hbasis hr_mem (fun w hwI => ?_)
    rw [generalFlatBand_truncation_coord Wᶜ _ w]
    by_cases hwc : w ∈ Wᶜ
    · rw [if_pos hwc]
      have hwW : w ∉ W := Finset.mem_compl.mp hwc
      rcases eq_or_ne w z with rfl | hne
      · exact absurd hzW hwW
      · show (WithLp.toLp 2 (μ z) : EuclideanSpace ℂ (Fin (M + 1))) w = 0
        simpa using hbasis.2.2.2.2 z hzI w hwI hne.symm
    · rw [if_neg hwc]
  have hrx : WithLp.ofLp (∑ a ∈ Wᶜ, (WithLp.toLp 2 (μ z) : EuclideanSpace ℂ (Fin (M + 1))) a •
      (EuclideanSpace.basisFun (Fin (M + 1)) ℂ a : EuclideanSpace ℂ (Fin (M + 1)))) x = 0 := by
    rw [hr0]; rfl
  rw [generalFlatBand_truncation_coord Wᶜ _ x, if_pos (Finset.mem_compl.mpr hxW)] at hrx
  simpa using hrx

end LatticeSystem.Fermion
