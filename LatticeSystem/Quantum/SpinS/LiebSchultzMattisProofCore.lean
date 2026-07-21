import LatticeSystem.Quantum.SpinS.AndersonTower
import LatticeSystem.Quantum.SpinS.HermitianVariationalLowerBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import LatticeSystem.Quantum.SpinS.AxisSwapUnitarySSpinSCore
import LatticeSystem.Quantum.SpinS.Problem25cZAxisRotationInput
import LatticeSystem.Math.PosSemidef.Basics
import LatticeSystem.Math.ComplexVectorKernel
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed

/-!
# Tasaki §6.2: Lieb–Schultz–Mattis — generic operator/PSD foundations (Core)

Generic, model-independent helper lemmas shared by the §6.2 Lieb–Schultz–Mattis discharge:
positivity of the squared norm, the adjoint–vector dot-product identity, the
matrix-exponential/`onSiteS` commutation, the single-site `S²·1 − (Ŝ^a)²` positive-semidefinite
bounds, and the Cauchy–Schwarz bond expectation estimate.  Split out of
`LiebSchultzMattisProof.lean` for build-speed (these compile independently of the LSM-specific
twist-operator algebra).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §6.2, eqs. (6.2.1)–(6.2.19), pp. 158–162.
-/

namespace LatticeSystem.Quantum

open Matrix NormedSpace
open scoped ComplexOrder

/-- Complex exponentials multiply by adding exponents (forward rewrite helper, `a b` explicit so the
`Commute` witness is resolved inside the proof — avoids metavariable issues in `←` rewrites). -/
theorem cexp_mul_cexp (a b : ℂ) :
    NormedSpace.exp a * NormedSpace.exp b = NormedSpace.exp (a + b) :=
  (NormedSpace.exp_add_of_commute (Commute.all a b)).symm

/-- `onSiteS i` as a ring homomorphism. -/
noncomputable def onSiteSRingHom {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ} (i : Λ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ →+* ManyBodyOpS Λ N where
  toFun := fun A => onSiteS i A
  map_one' := onSiteS_one i
  map_mul' := fun A B => (onSiteS_mul_onSiteS_same i A B).symm
  map_zero' := onSiteS_zero i
  map_add' := fun A B => onSiteS_add i A B

/-- `onSiteS i` as a `ℂ`-linear map. -/
noncomputable def onSiteSLinearMap {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ} (i : Λ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ →ₗ[ℂ] ManyBodyOpS Λ N where
  toFun := fun A => onSiteS i A
  map_add' := fun A B => onSiteS_add i A B
  map_smul' := fun c A => onSiteS_smul i c A

/-- **`onSiteS i` commutes with the matrix exponential**: `onSiteS i (exp A) = exp(onSiteS i A)`.
Via `NormedSpace.map_exp` for the continuous ring hom `onSiteSRingHom i` (Frobenius norms). -/
theorem onSiteS_exp_eq_exp_onSiteS {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ} (i : Λ)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    onSiteS i (NormedSpace.exp A) = NormedSpace.exp (onSiteS i A : ManyBodyOpS Λ N) := by
  letI iAddSrc : NormedAddCommGroup (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :=
    Matrix.frobeniusNormedAddCommGroup
  letI _iSpaceSrc : NormedSpace ℂ (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :=
    Matrix.frobeniusNormedSpace
  letI iRingSrc : NormedRing (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :=
    Matrix.frobeniusNormedRing
  letI iAlgSrc : NormedAlgebra ℚ (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :=
    Matrix.frobeniusNormedAlgebra
  letI _iAddTgt : NormedAddCommGroup (ManyBodyOpS Λ N) := Matrix.frobeniusNormedAddCommGroup
  letI _iSpaceTgt : NormedSpace ℂ (ManyBodyOpS Λ N) := Matrix.frobeniusNormedSpace
  letI iRingTgt : NormedRing (ManyBodyOpS Λ N) := Matrix.frobeniusNormedRing
  letI iAlgTgt : Algebra ℚ (ManyBodyOpS Λ N) :=
    (Matrix.frobeniusNormedAlgebra (R := ℚ)).toAlgebra
  haveI iComplSrc : CompleteSpace (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :=
    FiniteDimensional.complete ℂ (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
  have hcont : Continuous (onSiteSRingHom (Λ := Λ) (N := N) i) :=
    (onSiteSLinearMap (Λ := Λ) (N := N) i).continuous_of_finiteDimensional
  exact @NormedSpace.map_exp (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (ManyBodyOpS Λ N)
    iRingSrc iAlgSrc iComplSrc iRingTgt iAlgTgt _ _ _
    (onSiteSRingHom (Λ := Λ) (N := N) i) hcont A

/-- **Generic PSD expectation bound**: if `b•1 − A` is positive semidefinite then the real
Rayleigh form of `A` is bounded by `b ‖ψ‖²`. -/
theorem dotProduct_mulVec_re_le_of_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} {b : ℝ}
    (hPSD : Matrix.PosSemidef (((b : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) - A)) (ψ : ι → ℂ) :
    (star ψ ⬝ᵥ A.mulVec ψ).re ≤ b * (star ψ ⬝ᵥ ψ).re := by
  have h := Matrix.PosSemidef.dotProduct_mulVec_nonneg hPSD ψ
  have hre : (0 : ℝ) ≤ (star ψ ⬝ᵥ ((((b : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) - A).mulVec ψ)).re :=
    (Complex.le_def.mp h).1
  have hkey : star ψ ⬝ᵥ ((((b : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) - A).mulVec ψ) =
      ((b : ℝ) : ℂ) * (star ψ ⬝ᵥ ψ) - star ψ ⬝ᵥ A.mulVec ψ := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      smul_eq_mul]
  rw [hkey, Complex.sub_re, Complex.re_ofReal_mul] at hre
  linarith

/-- `S²•1 − (Ŝ³)²` is positive semidefinite (`S=N/2`): `Ŝ³` is diagonal with eigenvalues
`N/2 − k ∈ [−S, S]`, so `(N/2)² − (N/2−k)² = k(N−k) ≥ 0`. -/
theorem spinSOp3_sq_posSemidef (N : ℕ) :
    Matrix.PosSemidef (((((N : ℝ) / 2) ^ 2 : ℝ) : ℂ) •
      (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) - spinSOp3 N * spinSOp3 N) := by
  have hdiag : ((((N : ℝ) / 2) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) -
        spinSOp3 N * spinSOp3 N =
      Matrix.diagonal (fun k : Fin (N + 1) => ((((N : ℝ) / 2) ^ 2 : ℝ) : ℂ) -
        ((N : ℂ) / 2 - (k.val : ℂ)) * ((N : ℂ) / 2 - (k.val : ℂ))) := by
    rw [spinSOp3_sq_eq_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq,
        smul_eq_mul]
    · simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hij,
        Matrix.diagonal_apply_ne _ hij]
  rw [hdiag]
  refine Matrix.PosSemidef.diagonal (fun k => ?_)
  have hk : (k.val : ℝ) ≤ N := (Nat.cast_le (α := ℝ)).mpr (Nat.lt_succ_iff.mp k.isLt)
  have hk0 : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
  rw [show ((((N : ℝ) / 2) ^ 2 : ℝ) : ℂ) -
        ((N : ℂ) / 2 - (k.val : ℂ)) * ((N : ℂ) / 2 - (k.val : ℂ)) =
      (((k.val : ℝ) * ((N : ℝ) - k.val) : ℝ) : ℂ) from by push_cast; ring]
  exact Complex.zero_le_real.mpr (mul_nonneg hk0 (by linarith))

/-- `S²•1 − (Ŝ²)²` is positive semidefinite: `Ŝ²` is unitarily equivalent to `Ŝ³` via the axis-swap
gauge (`Ŝ² = −U Ŝ³ U⁻¹`, `U = spinSRot1(π/2)` unitary), and conjugation by a unitary preserves the
positive-semidefinite order. -/
theorem spinSOp2_sq_posSemidef (N : ℕ) :
    Matrix.PosSemidef (((((N : ℝ) / 2) ^ 2 : ℝ) : ℂ) •
      (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) - spinSOp2 N * spinSOp2 N) := by
  set G := axisSwapUnitarySSpinS N with hG
  have hUinv : G.Uinv = Matrix.conjTranspose G.U := by
    simp only [hG, axisSwapUnitarySSpinS, spinSRot1_adjoint]
  have hS2sq : spinSOp2 N * spinSOp2 N = G.U * (spinSOp3 N * spinSOp3 N) * G.Uinv := by
    have hh : G.U * spinSOp3 N * G.Uinv = -spinSOp2 N := G.conj_spinSOp3
    have h2 : G.U * (spinSOp3 N * spinSOp3 N) * G.Uinv =
        (G.U * spinSOp3 N * G.Uinv) * (G.U * spinSOp3 N * G.Uinv) := by
      rw [show (G.U * spinSOp3 N * G.Uinv) * (G.U * spinSOp3 N * G.Uinv) =
          G.U * spinSOp3 N * (G.Uinv * G.U) * spinSOp3 N * G.Uinv from by noncomm_ring,
        G.Uinv_mul_U, Matrix.mul_one]
      noncomm_ring
    rw [h2, hh, neg_mul_neg]
  have hkey : ((((N : ℝ) / 2) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) -
        spinSOp2 N * spinSOp2 N =
      G.U * (((((N : ℝ) / 2) ^ 2 : ℝ) : ℂ) •
          (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) - spinSOp3 N * spinSOp3 N) *
        Matrix.conjTranspose G.U := by
    rw [hS2sq, hUinv, Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, ← hUinv, G.U_mul_Uinv]
  rw [hkey]
  exact (spinSOp3_sq_posSemidef N).mul_mul_conjTranspose_same G.U

/-- `S²•1 − (Ŝ¹)²` is positive semidefinite: `Ŝ¹ = R(−π/2) Ŝ² R(π/2)` is unitarily equivalent to
`Ŝ²` (hence to `Ŝ³`) via the `Ŝ³`-axis rotation `R = spinSRot3`, and conjugation by a unitary
preserves the positive-semidefinite order. -/
theorem spinSOp1_sq_posSemidef (N : ℕ) :
    Matrix.PosSemidef (((((N : ℝ) / 2) ^ 2 : ℝ) : ℂ) •
      (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) - spinSOp1 N * spinSOp1 N) := by
  have hS1sq : spinSOp1 N * spinSOp1 N =
      spinSRot3 N (-(Real.pi / 2)) * (spinSOp2 N * spinSOp2 N) * spinSRot3 N (Real.pi / 2) := by
    have hh : spinSRot3 N (-(Real.pi / 2)) * spinSOp2 N * spinSRot3 N (Real.pi / 2) =
        spinSOp1 N := spinSRot3_neg_pi_half_conj_spinSOp2 N
    have h2 : spinSRot3 N (-(Real.pi / 2)) * (spinSOp2 N * spinSOp2 N) * spinSRot3 N (Real.pi / 2) =
        (spinSRot3 N (-(Real.pi / 2)) * spinSOp2 N * spinSRot3 N (Real.pi / 2)) *
          (spinSRot3 N (-(Real.pi / 2)) * spinSOp2 N * spinSRot3 N (Real.pi / 2)) := by
      rw [show (spinSRot3 N (-(Real.pi / 2)) * spinSOp2 N * spinSRot3 N (Real.pi / 2)) *
            (spinSRot3 N (-(Real.pi / 2)) * spinSOp2 N * spinSRot3 N (Real.pi / 2)) =
          spinSRot3 N (-(Real.pi / 2)) * spinSOp2 N *
            (spinSRot3 N (Real.pi / 2) * spinSRot3 N (-(Real.pi / 2))) *
            spinSOp2 N * spinSRot3 N (Real.pi / 2) from by noncomm_ring,
        spinSRot3_mul_neg, Matrix.mul_one]
      noncomm_ring
    rw [h2, hh]
  have hadj : spinSRot3 N (Real.pi / 2) =
      Matrix.conjTranspose (spinSRot3 N (-(Real.pi / 2))) := by
    rw [spinSRot3_adjoint, neg_neg]
  have hkey : ((((N : ℝ) / 2) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) -
        spinSOp1 N * spinSOp1 N =
      spinSRot3 N (-(Real.pi / 2)) * (((((N : ℝ) / 2) ^ 2 : ℝ) : ℂ) •
        (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) - spinSOp2 N * spinSOp2 N) *
        Matrix.conjTranspose (spinSRot3 N (-(Real.pi / 2))) := by
    rw [hS1sq, hadj, Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, ← hadj, spinSRot3_neg_mul]
  rw [hkey]
  exact (spinSOp2_sq_posSemidef N).mul_mul_conjTranspose_same (spinSRot3 N (-(Real.pi / 2)))

/-- **`onSiteS` preserves positive-semidefiniteness**: embedding a single-site PSD operator at a
site gives a many-body PSD operator (via the factorisation `M = C*C` with `C ≥ 0`, so
`onSiteS x M = (onSiteS x C)ᴴ (onSiteS x C)`). -/
theorem onSiteS_posSemidef {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ} (x : Λ)
    {M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} (hM : M.PosSemidef) :
    Matrix.PosSemidef (onSiteS x M : ManyBodyOpS Λ N) := by
  obtain ⟨C, hC, hCC⟩ := LatticeSystem.Math.exists_posSemidef_sq_eq_of_posSemidef hM
  have hB : Matrix.conjTranspose (onSiteS x C : ManyBodyOpS Λ N) = onSiteS x C := by
    rw [onSiteS_conjTranspose, hC.isHermitian.eq]
  have hpsd := Matrix.posSemidef_conjTranspose_mul_self (onSiteS x C : ManyBodyOpS Λ N)
  rw [hB] at hpsd
  rwa [hCC, ← onSiteS_mul_onSiteS_same]

/-- **Many-body single-site square bound**: if `b•1 − A²` is positive semidefinite (single-site),
then `⟨Φ, (onSiteS x A)² Φ⟩.re ≤ b ‖Φ‖²`.  Applied with `A = Ŝ^a`, `b = S²` it gives
`‖(onSiteS x Ŝ^a) Φ‖² ≤ S² ‖Φ‖²` (`‖Ŝ^a‖ = S`). -/
theorem onSiteS_sq_dotProduct_re_le {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ} (x : Λ)
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} {b : ℝ}
    (hA : Matrix.PosSemidef (((b : ℝ) : ℂ) • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) - A * A))
    (Φ : (Λ → Fin (N + 1)) → ℂ) :
    (star Φ ⬝ᵥ (onSiteS x A * onSiteS x A : ManyBodyOpS Λ N).mulVec Φ).re ≤
      b * (star Φ ⬝ᵥ Φ).re := by
  rw [onSiteS_mul_onSiteS_same]
  refine dotProduct_mulVec_re_le_of_posSemidef ?_ Φ
  have heq : ((b : ℝ) : ℂ) • (1 : ManyBodyOpS Λ N) - onSiteS x (A * A) =
      onSiteS x (((b : ℝ) : ℂ) • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) - A * A) := by
    rw [onSiteS_sub, onSiteS_smul, onSiteS_one]
  rw [heq]
  exact onSiteS_posSemidef x hA

/-- The squared Euclidean (ℓ²) norm of a raw vector is `(star u ⬝ᵥ u).re = Σ|u_i|²`. -/
theorem euclidean_normSq_eq_dotProduct {ι : Type*} [Fintype ι] (u : ι → ℂ) :
    ‖(WithLp.toLp 2 u : EuclideanSpace ℂ ι)‖ ^ 2 = (star u ⬝ᵥ u).re := by
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) (WithLp.toLp 2 u : EuclideanSpace ℂ ι)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  rw [← h, dotProduct_comm]
  rfl

/-- **Cauchy–Schwarz for the (conjugate-linear-left) dot product** of finite ℂ-vectors:
`‖star u ⬝ᵥ v‖ ≤ ‖u‖ ‖v‖` (Euclidean norms). -/
theorem norm_star_dotProduct_le {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    ‖star u ⬝ᵥ v‖ ≤
      ‖(WithLp.toLp 2 u : EuclideanSpace ℂ ι)‖ * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ := by
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 u : EuclideanSpace ℂ ι)
    (WithLp.toLp 2 v : EuclideanSpace ℂ ι)
  rwa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm,
    show (star (WithLp.ofLp (WithLp.toLp 2 u)) : ι → ℂ) = star u from rfl,
    show (WithLp.ofLp (WithLp.toLp 2 v) : ι → ℂ) = v from rfl] at hcs

/-- **Bond expectation bound (Cauchy–Schwarz)**: for a Hermitian single-site `A` with `S²·1 − A²`
positive semidefinite (so `‖A‖ ≤ S`, `b = S²`),
`|⟨Φ, (onSiteS x A)(onSiteS y A) Φ⟩.re| ≤ b ‖Φ‖²`. -/
theorem onSiteS_mul_onSiteS_dotProduct_re_abs_le {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
    (x y : Λ) {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hAh : A.IsHermitian)
    (hA : Matrix.PosSemidef (((b : ℝ) : ℂ) • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) - A * A))
    (Φ : (Λ → Fin (N + 1)) → ℂ) :
    |(star Φ ⬝ᵥ (onSiteS x A * onSiteS y A : ManyBodyOpS Λ N).mulVec Φ).re| ≤
      b * (star Φ ⬝ᵥ Φ).re := by
  classical
  have hxh : (onSiteS x A : ManyBodyOpS Λ N).IsHermitian := onSiteS_isHermitian x hAh
  set u := (onSiteS x A : ManyBodyOpS Λ N).mulVec Φ with hu
  set v := (onSiteS y A : ManyBodyOpS Λ N).mulVec Φ with hv
  set p := (star Φ ⬝ᵥ Φ).re with hp
  have hpnn : 0 ≤ p := by
    rw [hp]; by_cases h : Φ = 0
    · simp [h]
    · exact (dotProduct_star_self_re_pos h).le
  -- the bond expectation is the inner product ⟨u, v⟩ = star u ⬝ᵥ v
  have hbond : star Φ ⬝ᵥ (onSiteS x A * onSiteS y A : ManyBodyOpS Λ N).mulVec Φ = star u ⬝ᵥ v := by
    rw [hu, hv, ← Matrix.mulVec_mulVec, star_mulVec_dotProduct, hxh.eq]
  -- ‖toLp u‖² = ⟨Φ, (onSiteS x A)² Φ⟩.re ≤ b·p, likewise for v
  have hnu2 : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖ ^ 2 ≤ b * p := by
    rw [euclidean_normSq_eq_dotProduct, hu, star_mulVec_dotProduct, hxh.eq, Matrix.mulVec_mulVec]
    exact onSiteS_sq_dotProduct_re_le x hA Φ
  have hnv2 : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖ ^ 2 ≤ b * p := by
    rw [euclidean_normSq_eq_dotProduct, hv, star_mulVec_dotProduct, (onSiteS_isHermitian y hAh).eq,
      Matrix.mulVec_mulVec]
    exact onSiteS_sq_dotProduct_re_le y hA Φ
  -- product of norms ≤ b·p
  have hbp : 0 ≤ b * p := mul_nonneg hb hpnn
  have hprod : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖ *
      ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖ ≤ b * p := by
    have hsq : (‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖ *
        ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖) ^ 2 ≤ (b * p) ^ 2 := by
      rw [mul_pow]
      calc _ ≤ (b * p) * (b * p) := mul_le_mul hnu2 hnv2 (sq_nonneg _) hbp
        _ = (b * p) ^ 2 := by ring
    have hlhs : 0 ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖ *
        ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith [hsq, hlhs, hbp]
  rw [hbond]
  have h1 : |(star u ⬝ᵥ v).re| ≤ ‖star u ⬝ᵥ v‖ := by
    simpa using RCLike.abs_re_le_norm (star u ⬝ᵥ v)
  have h2 := norm_star_dotProduct_le u v
  linarith [h1, h2, hprod]

/-- Elementary real bound `1 − cos x ≤ x²/2` (from `Real.one_sub_sq_div_two_le_cos`). -/
theorem one_sub_cos_le_half_sq (x : ℝ) : 1 - Real.cos x ≤ x ^ 2 / 2 := by
  have h := Real.one_sub_sq_div_two_le_cos (x := x)
  nlinarith [h]

/-- **The minimum eigenvalue lower-bounds every real Rayleigh quotient** (generic `Matrix ι ι ℂ`,
Hermitian `H`): `hermitianMinEigenvalue hH ≤ expectationRatioRe H v` for any nonzero `v`.  This is
the shared core of the variational lower bound; the minimality step (`E₀ ≤ hermitianMinEigenvalue`)
is supplied separately by each caller, so both the ground-energy (`IsGroundEnergy`) form
`groundEnergy_le_expectationRatioRe_general` and the spectral-minimizer form
`minimizerEigenvalue_le_expectationRatioRe` derive from it without repeating the
`hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec` chain. -/
theorem hermitianMinEigenvalue_le_expectationRatioRe {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {v : ι → ℂ} (hv : v ≠ 0) :
    hermitianMinEigenvalue hH ≤ expectationRatioRe H v := by
  have hpos : 0 < (star v ⬝ᵥ v).re := dotProduct_star_self_re_pos hv
  have hvar := hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec hH v
  unfold expectationRatioRe rayleighOnVec at *
  rw [le_div_iff₀ hpos]
  exact hvar

end LatticeSystem.Quantum
