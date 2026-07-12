import LatticeSystem.Quantum.SpinS.AndersonTowerRotationDeriv
import LatticeSystem.Quantum.SpinS.DysonLiebSimon
import LatticeSystem.Quantum.SpinS.AndersonTowerTanakaLowerBounds
import LatticeSystem.Quantum.SpinS.AndersonTowerTanakaFluctuation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Tasaki §4.2.2 Proposition 4.10: isotropy of the directional moment (sub-step L4b-iii)

For a total-spin singlet `Φ`, the rotation-derivative vanishing
`directionMoment_rotationPath_hasDerivAt_zero` (`AndersonTowerRotationDeriv`, sub-step L4b-ii) says
the directional moment `g(n) = ⟨Φ, (Ô_L^n)^{2M} Φ⟩` (`directionMoment`) has vanishing derivative
along every axis-`γ` rotation circle.  This module upgrades that infinitesimal statement to global
isotropy and passes it to the per-direction tower-term norm.

The route is three-stage:

1. **Arc constancy** (`directionMoment_rotationPath_const`): feeding the vanishing derivative to
   Mathlib's `is_const_of_deriv_eq_zero` makes `g` constant along any rotation circle.
2. **Sphere reachability** (`sphere_reachable_from_e3`): every unit vector `n ∈ S²` is reached from
   the north pole `e₃ = (0,0,1)` by two rotation arcs (a `γ=1` tilt by the polar angle
   `arccos n₂` followed by a `γ=2` spin by the azimuthal angle `arg⟨n₀,n₁⟩`).  Chaining arc
   constancy along the two arcs gives global isotropy `g(n) = g(e₃)`
   (`directionMoment_eq_e3`, `directionMoment_indep`).
3. **Norm consequence** (`directionTanakaTowerTerm_vecNormSqRe_eq`): the direction order operator is
   Hermitian (`directionStaggeredOp_isHermitian`), so the per-direction tower-term squared norm
   `‖(Ô_L^n)^M Φ‖²` equals `Re g(n)`, and its `n`-independence
   (`directionTanakaTowerTerm_vecNormSqRe_indep`) is the tip consumed by the sphere-average
   assembly (PR-6).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, eqs. (4.2.57)–(4.2.61), pp. 108–109; cf. Tasaki, arXiv:1807.05847.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ### Arc constancy of the directional moment -/

/-- The rotation path at `θ = 0` is the identity: `R_γ(0) n = n`.  Both sides agree coordinatewise
by the case split `fin_cases γ`, `fin_cases δ` with `Real.cos 0 = 1`, `Real.sin 0 = 0`. -/
theorem rotationPath_zero (γ : Fin 3) (n : EuclideanSpace ℝ (Fin 3)) :
    rotationPath γ n 0 = n := by
  ext δ
  fin_cases γ <;> fin_cases δ <;>
    simp only [rotationPath_apply, rotationCoords, Real.cos_zero, Real.sin_zero, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, mul_one, mul_zero, add_zero]

/-- **Arc constancy of the directional moment** (Prop 4.10 sub-step L4b-iii, stage 1).  For a
total-spin singlet `Φ`, the directional moment `g(n) = ⟨Φ, (Ô_L^n)^{2M} Φ⟩` is constant along any
axis-`γ` rotation circle: `g(R_γ(θ) n₀) = g(n₀)` for every `θ`.  The rotation-derivative vanishing
`directionMoment_rotationPath_hasDerivAt_zero` supplies both the differentiability and the zero
derivative to Mathlib's `is_const_of_deriv_eq_zero`; `rotationPath_zero` gives the base point. -/
theorem directionMoment_rotationPath_const (A : Λ → Bool) (γ : Fin 3)
    (n₀ : EuclideanSpace ℝ (Fin 3)) (M : ℕ) (Φ : (Λ → Fin (N + 1)) → ℂ)
    (h3 : (totalSpinSOp3 Λ N).mulVec Φ = 0) (h1 : (totalSpinSOp1 Λ N).mulVec Φ = 0) (θ : ℝ) :
    directionMoment A Φ M (rotationPath γ n₀ θ) = directionMoment A Φ M n₀ := by
  have hd : Differentiable ℝ (fun t => directionMoment A Φ M (rotationPath γ n₀ t)) :=
    fun x => (directionMoment_rotationPath_hasDerivAt_zero A γ n₀ M Φ h3 h1 x).differentiableAt
  have h := is_const_of_deriv_eq_zero hd
    (fun x => (directionMoment_rotationPath_hasDerivAt_zero A γ n₀ M Φ h3 h1 x).deriv) θ 0
  rwa [rotationPath_zero] at h

/-! ### Sphere reachability from the north pole -/

/-- The **north-pole unit vector** `e₃ = (0,0,1) ∈ S² ⊂ ℝ³`, taken as the reference direction from
which every unit vector is reached by two rotation arcs (`sphere_reachable_from_e3`). -/
noncomputable def e3vec : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![0, 0, 1]

/-- Coordinate access for the north pole: `(e₃)_δ = ![0,0,1]_δ`. -/
theorem e3vec_apply (δ : Fin 3) : e3vec δ = ![0, 0, 1] δ := rfl

/-- **Sphere reachability from the north pole** (Prop 4.10 sub-step L4b-iii, stage 2, crux).  Every
unit vector `n ∈ S²` is the image of the north pole `e₃` under a `γ=1` tilt by the polar angle
`θ = arccos n₂` followed by a `γ=2` spin by the azimuthal angle `φ = arg⟨n₀,n₁⟩`:
`n = R₂(φ) R₁(θ) e₃`.  The two arcs realise standard spherical coordinates
`(sinθ cosφ, sinθ sinφ, cosθ)`; the polar identities are `Real.cos_arccos`/`Real.sin_arccos` (with
`sinθ = √(n₀²+n₁²)` from `‖n‖ = 1`), and the azimuthal identities are `Complex.cos_arg`/
`Complex.sin_arg` for `z = n₀ + n₁ i`.  The degenerate pole `n₀ = n₁ = 0` (where `arg` is
ill-conditioned) is handled by a separate `r = 0` case. -/
theorem sphere_reachable_from_e3
    (n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∃ θ φ : ℝ, (n : EuclideanSpace ℝ (Fin 3))
      = rotationPath 2 (rotationPath 1 e3vec θ) φ := by
  obtain ⟨n, hn⟩ := n
  simp only [Metric.mem_sphere, dist_zero_right] at hn
  have hsum : (n 0) ^ 2 + (n 1) ^ 2 + (n 2) ^ 2 = 1 := by
    have hns : ‖n‖ ^ 2 = ∑ i : Fin 3, ‖n i‖ ^ 2 := EuclideanSpace.norm_sq_eq n
    rw [hn, one_pow, Fin.sum_univ_three] at hns
    simp only [Real.norm_eq_abs, sq_abs] at hns
    linarith [hns]
  have hn2le : n 2 ≤ 1 := by
    nlinarith [sq_nonneg (n 0), sq_nonneg (n 1), sq_nonneg (n 2 - 1)]
  have hn2ge : -1 ≤ n 2 := by
    nlinarith [sq_nonneg (n 0), sq_nonneg (n 1), sq_nonneg (n 2 + 1)]
  set r : ℝ := Real.sqrt ((n 0) ^ 2 + (n 1) ^ 2) with hr_def
  set z : ℂ := (↑(n 0) + ↑(n 1) * Complex.I : ℂ) with hz_def
  have hcos : Real.cos (Real.arccos (n 2)) = n 2 := Real.cos_arccos hn2ge hn2le
  have hsin : Real.sin (Real.arccos (n 2)) = r := by
    rw [Real.sin_arccos, hr_def]; congr 1; linarith [hsum]
  refine ⟨Real.arccos (n 2), Complex.arg z, ?_⟩
  have hrnn : 0 ≤ r := by rw [hr_def]; exact Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hrnn with hr0 | hrpos
  · -- Degenerate pole: `r = 0`, hence `n₀ = n₁ = 0`.
    have hrz : Real.sqrt ((n 0) ^ 2 + (n 1) ^ 2) = 0 := by rw [← hr_def]; exact hr0.symm
    have hle : (n 0) ^ 2 + (n 1) ^ 2 ≤ 0 := Real.sqrt_eq_zero'.mp hrz
    have hn0 : n 0 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (n 0), sq_nonneg (n 1)])
    have hn1 : n 1 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (n 0), sq_nonneg (n 1)])
    ext δ
    fin_cases δ <;>
      simp only [rotationPath_apply, rotationCoords, e3vec_apply, Fin.reduceFinMk, hcos, hsin,
        ← hr0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons, hn0, hn1, zero_mul, one_mul, mul_zero, neg_zero, add_zero,
        zero_add, neg_mul]
  · -- Generic direction: `r > 0`, so `z ≠ 0` and `arg z` is well-conditioned.
    have hznorm : ‖z‖ = r := by rw [hz_def, Complex.norm_add_mul_I, ← hr_def]
    have hzne : z ≠ 0 := by rw [← norm_pos_iff, hznorm]; exact hrpos
    have hzre : z.re = n 0 := by rw [hz_def]; simp
    have hzim : z.im = n 1 := by rw [hz_def]; simp
    have hrne : r ≠ 0 := ne_of_gt hrpos
    ext δ
    fin_cases δ
    · simp only [rotationPath_apply, rotationCoords, e3vec_apply, Fin.reduceFinMk, hcos, hsin,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons, zero_mul, one_mul, neg_zero, add_zero, zero_add, neg_mul]
      rw [Complex.cos_arg hzne, hzre, hznorm, ← mul_div_assoc, mul_div_cancel_left₀ _ hrne]
    · simp only [rotationPath_apply, rotationCoords, e3vec_apply, Fin.reduceFinMk, hcos, hsin,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons, zero_mul, one_mul, neg_zero, add_zero, zero_add, neg_mul]
      rw [Complex.sin_arg, hzim, hznorm, ← mul_div_assoc, mul_div_cancel_left₀ _ hrne]
    · simp only [rotationPath_apply, rotationCoords, e3vec_apply, Fin.reduceFinMk, hcos, hsin,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons, zero_mul, one_mul, neg_zero, add_zero, zero_add, neg_mul]

/-! ### Global isotropy -/

/-- **Global isotropy of the directional moment** (Prop 4.10 sub-step L4b-iii, stage 2 tip).  For a
total-spin singlet `Φ`, the directional moment agrees at every unit vector with its north-pole
value: `g(n) = g(e₃)` for all `n ∈ S²`.  Obtained by chaining arc constancy
(`directionMoment_rotationPath_const`) along the two arcs of `sphere_reachable_from_e3`. -/
theorem directionMoment_eq_e3 (A : Λ → Bool) (M : ℕ) (Φ : (Λ → Fin (N + 1)) → ℂ)
    (h3 : (totalSpinSOp3 Λ N).mulVec Φ = 0) (h1 : (totalSpinSOp1 Λ N).mulVec Φ = 0)
    (n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    directionMoment A Φ M (n : EuclideanSpace ℝ (Fin 3)) = directionMoment A Φ M e3vec := by
  obtain ⟨θ, φ, hn⟩ := sphere_reachable_from_e3 n
  rw [hn, directionMoment_rotationPath_const A 2 (rotationPath 1 e3vec θ) M Φ h3 h1 φ,
    directionMoment_rotationPath_const A 1 e3vec M Φ h3 h1 θ]

/-- **Two-point isotropy of the directional moment** (Prop 4.10 sub-step L4b-iii, stage 2, consumer
form).  For a total-spin singlet `Φ`, the directional moment is the same at any two unit vectors:
`g(n) = g(n')`.  Immediate from `directionMoment_eq_e3` at both points. -/
theorem directionMoment_indep (A : Λ → Bool) (M : ℕ) (Φ : (Λ → Fin (N + 1)) → ℂ)
    (h3 : (totalSpinSOp3 Λ N).mulVec Φ = 0) (h1 : (totalSpinSOp1 Λ N).mulVec Φ = 0)
    (n n' : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    directionMoment A Φ M (n : EuclideanSpace ℝ (Fin 3))
      = directionMoment A Φ M (n' : EuclideanSpace ℝ (Fin 3)) :=
  (directionMoment_eq_e3 A M Φ h3 h1 n).trans (directionMoment_eq_e3 A M Φ h3 h1 n').symm

/-! ### Per-direction tower-term norm -/

/-- **Hermiticity of the direction order operator.**  For a real unit vector `n`, the direction
order operator `Ô_L^n = Σ_α n_α ô^{(α)}` (`directionStaggeredOp`) is Hermitian: it is a
real-weighted sum of the three Hermitian staggered axis operators (`stagOpVec`), and each real
coordinate `(n_α : ℂ)` is self-adjoint (`Complex.conj_ofReal`). -/
theorem directionStaggeredOp_isHermitian (n : EuclideanSpace ℝ (Fin 3)) (A : Λ → Bool) (N : ℕ) :
    (directionStaggeredOp n A N).IsHermitian := by
  rw [directionStaggeredOp_eq_sum]
  refine Matrix.isHermitian_sum Finset.univ (fun α _ => ?_)
  refine Matrix.IsHermitian.smul ?_ ?_
  · fin_cases α
    · simpa only [stagOpVec, Matrix.cons_val_zero] using staggeredOrderOp1S_isHermitian A N
    · simpa only [stagOpVec, Matrix.cons_val_one, Matrix.head_cons] using
        staggeredOrderOp2S_isHermitian A N
    · simpa only [stagOpVec, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] using
        staggeredOrderOpS_isHermitian A N
  · change star ((n α : ℝ) : ℂ) = ((n α : ℝ) : ℂ)
    rw [Complex.star_def]; exact Complex.conj_ofReal _

/-- **The per-direction tower-term squared norm is the real part of the moment.**
`‖(Ô_L^n)^M Φ‖² = Re ⟨Φ, (Ô_L^n)^{2M} Φ⟩`.  Since `Ô_L^n` is Hermitian
(`directionStaggeredOp_isHermitian`), `star ((H^M) Φ) ⬝ᵥ (H^M) Φ = star Φ ⬝ᵥ H^{2M} Φ` by moving one
factor across the inner product (`Matrix.star_mulVec` and Hermiticity), regrouping
(`Matrix.dotProduct_mulVec`, `Matrix.vecMul_vecMul`) and folding `M + M = 2M`. -/
theorem directionTanakaTowerTerm_vecNormSqRe_eq (n : EuclideanSpace ℝ (Fin 3)) (A : Λ → Bool)
    (M : ℕ) (Φ : (Λ → Fin (N + 1)) → ℂ) :
    vecNormSqRe (directionTanakaTowerTerm n A N M Φ) = (directionMoment A Φ M n).re := by
  unfold vecNormSqRe directionTanakaTowerTerm directionMoment
  congr 1
  rw [Matrix.star_mulVec, ((directionStaggeredOp_isHermitian n A N).pow M).eq,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← pow_add, ← two_mul,
    ← Matrix.dotProduct_mulVec]

/-- **Isotropy of the per-direction tower-term squared norm** (Prop 4.10 sub-step L4b-iii tip).  For
a total-spin singlet `Φ`, the tower-term squared norm `‖(Ô_L^n)^M Φ‖²` is the same at any two unit
vectors.  Rewriting each side as `Re g(n)` (`directionTanakaTowerTerm_vecNormSqRe_eq`) and applying
the moment isotropy `directionMoment_indep` completes L4b (singlet isotropy); this constant is the
`c_M` consumed by the sphere-average assembly (PR-6). -/
theorem directionTanakaTowerTerm_vecNormSqRe_indep (A : Λ → Bool) (M : ℕ)
    (Φ : (Λ → Fin (N + 1)) → ℂ)
    (h3 : (totalSpinSOp3 Λ N).mulVec Φ = 0) (h1 : (totalSpinSOp1 Λ N).mulVec Φ = 0)
    (n n' : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    vecNormSqRe (directionTanakaTowerTerm (n : EuclideanSpace ℝ (Fin 3)) A N M Φ)
      = vecNormSqRe (directionTanakaTowerTerm (n' : EuclideanSpace ℝ (Fin 3)) A N M Φ) := by
  rw [directionTanakaTowerTerm_vecNormSqRe_eq, directionTanakaTowerTerm_vecNormSqRe_eq,
    directionMoment_indep A M Φ h3 h1 n n']

end LatticeSystem.Quantum
