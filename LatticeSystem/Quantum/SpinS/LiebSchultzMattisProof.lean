import LatticeSystem.Quantum.SpinS.LiebSchultzMattis
import LatticeSystem.Quantum.SpinS.LiebSchultzMattisProofCore
import LatticeSystem.Quantum.SpinS.OrderOperatorAlgebra
import LatticeSystem.Quantum.SpinS.HermitianVariationalLowerBound
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueEigenvector
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
# Tasaki §6.2: Lieb–Schultz–Mattis — discharge of the twist-operator lemmas

Foundations for discharging the §6.2 axioms `lsm_energy_bound` (Lemma 6.1),
`lsm_ground_twist_orthogonal` (Lemma 6.2), and `lieb_schultz_mattis_affleck_lieb` (Theorem 6.3).

This module first establishes that the **LSM twist operator** `Û_LSM = exp[−i Σ_x θ_x Ŝ³_x]`
(eq. (6.2.2)) is **unitary** — its Hermitian generator `G = Σ_x θ_x Ŝ³_x` gives
`Û_LSM† = exp[+i G]` and `Û_LSM† Û_LSM = 1` — so the twisted trial state has the same norm as the
ground state and `⟨Φ_LSM, Ĥ Φ_LSM⟩ = ⟨Φ_GS, Û_LSM† Ĥ Û_LSM Φ_GS⟩`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §6.2, eqs. (6.2.1)–(6.2.19), pp. 158–162.
-/

namespace LatticeSystem.Quantum

open Matrix NormedSpace
open scoped ComplexOrder

/-- The **LSM twist generator** `G = Σ_x θ_x Ŝ³_x` (`θ_x = 2π(x+1)/L`), the Hermitian operator
exponentiated (with `−i`) to form `lsmTwistOperator`. -/
noncomputable def lsmGenerator (L N : ℕ) : ManyBodyOpS (Fin L) N :=
  ∑ x : Fin L, (((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ) : ℝ) : ℂ) • spinSSiteOp3 x N

/-- `lsmTwistOperator = exp(−i • G)`. -/
theorem lsmTwistOperator_eq_exp (L N : ℕ) :
    lsmTwistOperator L N = NormedSpace.exp (-Complex.I • lsmGenerator L N) := rfl

/-- The twist generator is Hermitian (a real-coefficient sum of the Hermitian on-site `Ŝ³`). -/
theorem lsmGenerator_isHermitian (L N : ℕ) : (lsmGenerator L N).IsHermitian := by
  refine Matrix.isHermitian_sum Finset.univ (fun x _ => ?_)
  rw [spinSSiteOp3, Matrix.IsHermitian, Matrix.conjTranspose_smul]
  rw [(onSiteS_isHermitian x (spinSOp3_isHermitian N)).eq, Complex.star_def,
    Complex.conj_ofReal]

/-- The **twist operator is unitary**: `Û_LSM† = exp(+i G)` (the generic
`conjTranspose_exp_neg_I_smul_of_isHermitian`). -/
theorem lsmTwistOperator_conjTranspose (L N : ℕ) :
    (lsmTwistOperator L N).conjTranspose = NormedSpace.exp (Complex.I • lsmGenerator L N) := by
  rw [lsmTwistOperator_eq_exp]
  exact conjTranspose_exp_neg_I_smul_of_isHermitian (lsmGenerator_isHermitian L N)

/-- `Û_LSM† Û_LSM = 1` (the generic `conjTranspose_mul_exp_neg_I_smul_of_isHermitian`). -/
theorem lsmTwistOperator_unitary (L N : ℕ) :
    (lsmTwistOperator L N).conjTranspose * lsmTwistOperator L N = 1 := by
  rw [lsmTwistOperator_eq_exp]
  exact conjTranspose_mul_exp_neg_I_smul_of_isHermitian (lsmGenerator_isHermitian L N)

/-- `Û_LSM Û_LSM† = 1` (the companion unitarity identity, generic
`exp_neg_I_smul_mul_conjTranspose_of_isHermitian`). -/
theorem lsmTwistOperator_unitary' (L N : ℕ) :
    lsmTwistOperator L N * (lsmTwistOperator L N).conjTranspose = 1 := by
  rw [lsmTwistOperator_eq_exp]
  exact exp_neg_I_smul_mul_conjTranspose_of_isHermitian (lsmGenerator_isHermitian L N)

/-- **The twisted state's Rayleigh quotient equals the conjugated Hamiltonian's Rayleigh quotient.**
By unitarity of `Û_LSM`, `⟨Φ_LSM, Ĥ Φ_LSM⟩ / ⟨Φ_LSM, Φ_LSM⟩ = ⟨Φ_GS, Û† Ĥ Û Φ_GS⟩ / ⟨Φ_GS,
Φ_GS⟩`. -/
theorem expectationRatioRe_lsmTrialState (L N : ℕ) (Φ : (Fin L → Fin (N + 1)) → ℂ) :
    expectationRatioRe (afmHeisenbergChainHamiltonianS L N) (lsmTrialState L N Φ) =
      expectationRatioRe ((lsmTwistOperator L N).conjTranspose *
        afmHeisenbergChainHamiltonianS L N * lsmTwistOperator L N) Φ := by
  unfold expectationRatioRe lsmTrialState
  congr 2
  · rw [star_mulVec_dotProduct, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  · rw [star_mulVec_dotProduct, Matrix.mulVec_mulVec, lsmTwistOperator_unitary,
      Matrix.one_mulVec]

/-- The **LSM phase** `Σ_x θ_x (S − σ_x)` at a configuration `σ` (`θ_x = 2π(x+1)/L`), the diagonal
entry of the twist generator `G`. -/
noncomputable def lsmPhase (L N : ℕ) (σ : Fin L → Fin (N + 1)) : ℂ :=
  ∑ x : Fin L, (((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ) : ℝ) : ℂ) *
    ((N : ℂ) / 2 - (σ x).val)

/-- **LSM phase difference for a single-site move**: if `σ`, `τ` agree off site `x`, then
`φ_σ − φ_τ = θ_x · ((τ_x) − (σ_x))` (only the `x` term survives). -/
theorem lsmPhase_sub_of_single_site (L N : ℕ) (x : Fin L) {σ τ : Fin L → Fin (N + 1)}
    (hc : ∀ k, k ≠ x → σ k = τ k) :
    lsmPhase L N σ - lsmPhase L N τ =
      (((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ) : ℝ) : ℂ) * (((τ x).val : ℂ) - (σ x).val) := by
  unfold lsmPhase
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single x]
  · ring
  · intro z _ hz
    rw [hc z hz]
    ring
  · intro h
    exact absurd (Finset.mem_univ x) h
theorem lsmGenerator_eq_diagonal (L N : ℕ) :
    lsmGenerator L N = Matrix.diagonal (lsmPhase L N) := by
  ext σ' σ
  rw [lsmGenerator, Matrix.sum_apply, Matrix.diagonal_apply]
  by_cases h : σ' = σ
  · subst h
    rw [if_pos rfl, lsmPhase]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Matrix.smul_apply, spinSSiteOp3, onSiteS_apply, if_pos (fun _ _ => rfl), spinSOp3,
      Matrix.diagonal_apply_eq, smul_eq_mul]
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    rw [Matrix.smul_apply, spinSSiteOp3, onSiteS_apply]
    by_cases hk : ∀ k, k ≠ x → σ' k = σ k
    · rw [if_pos hk, spinSOp3]
      by_cases hx : σ' x = σ x
      · exact absurd (funext fun k => if hkx : k = x then hkx ▸ hx else hk k hkx) h
      · rw [Matrix.diagonal_apply_ne _ hx, smul_zero]
    · rw [if_neg hk, smul_zero]

/-- The **twist operator is diagonal**: `Û_LSM = diag(exp(−i · lsmPhase σ))`. -/
theorem lsmTwistOperator_eq_diagonal (L N : ℕ) :
    lsmTwistOperator L N =
      Matrix.diagonal (fun σ => NormedSpace.exp (-Complex.I • lsmPhase L N σ)) := by
  rw [lsmTwistOperator_eq_exp, lsmGenerator_eq_diagonal, ← Matrix.diagonal_smul,
    Matrix.exp_diagonal]
  ext σ' σ
  by_cases h : σ' = σ
  · subst h; simp only [Matrix.diagonal_apply_eq, Pi.coe_exp, Pi.smul_apply]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h]

/-- The **conjugate-transpose twist** is diagonal with the inverse phase (`Û† = exp(+i G)`). -/
theorem lsmTwistOperator_conjTranspose_eq_diagonal (L N : ℕ) :
    (lsmTwistOperator L N).conjTranspose =
      Matrix.diagonal (fun σ => NormedSpace.exp (Complex.I • lsmPhase L N σ)) := by
  rw [lsmTwistOperator_conjTranspose, lsmGenerator_eq_diagonal, ← Matrix.diagonal_smul,
    Matrix.exp_diagonal]
  ext σ' σ
  by_cases h : σ' = σ
  · subst h; simp only [Matrix.diagonal_apply_eq, Pi.coe_exp, Pi.smul_apply]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h]

/-- The single-site `Ŝ³`-rotation `spinSRot3 N θ = exp(−iθ Ŝ³)` is **diagonal** with entries
`exp(−iθ (N/2 − k))`. -/
private theorem spinSRot3_eq_diagonal (N : ℕ) (θ : ℝ) :
    spinSRot3 N θ = Matrix.diagonal (fun k : Fin (N + 1) =>
      NormedSpace.exp ((-((θ : ℂ) * Complex.I)) • ((N : ℂ) / 2 - (k.val : ℂ)))) := by
  rw [spinSRot3, spinSOp3, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  ext a b
  by_cases h : a = b
  · subst h; simp only [Matrix.diagonal_apply_eq, Pi.coe_exp, Pi.smul_apply]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h]

/-- **Single-site `Ŝ³`-rotation conjugation, matrix element**:
`(R(−θ) A R(θ))_{ab} = e^{iθ(b−a)} A_{ab}` (`R = spinSRot3`). -/
theorem spinSRot3_conj_apply (N : ℕ) (θ : ℝ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (a b : Fin (N + 1)) :
    (spinSRot3 N (-θ) * A * spinSRot3 N θ) a b =
      NormedSpace.exp (((θ : ℂ) * Complex.I) * ((b.val : ℂ) - (a.val : ℂ))) * A a b := by
  rw [spinSRot3_eq_diagonal, spinSRot3_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
    mul_right_comm, cexp_mul_cexp]
  congr 2
  simp only [smul_eq_mul]
  push_cast
  ring

/-- `R(−θ) Ŝ³ R(θ) = Ŝ³` (`R = spinSRot3`): the rotation about axis 3 fixes `Ŝ³`. -/
theorem spinSRot3_neg_conj_spinSOp3 (N : ℕ) (θ : ℝ) :
    spinSRot3 N (-θ) * spinSOp3 N * spinSRot3 N θ = spinSOp3 N := by
  ext a b
  rw [spinSRot3_conj_apply]
  by_cases h : a = b
  · subst h; simp
  · simp [spinSOp3, Matrix.diagonal_apply_ne _ h]

/-- `R(−θ) Ŝ⁺ R(θ) = e^{iθ} Ŝ⁺` (`R = spinSRot3`). -/
theorem spinSRot3_neg_conj_spinSOpPlus (N : ℕ) (θ : ℝ) :
    spinSRot3 N (-θ) * spinSOpPlus N * spinSRot3 N θ =
      Complex.exp ((θ : ℂ) * Complex.I) • spinSOpPlus N := by
  have h := spinSRot3_conj_spinSOpPlus N (-θ)
  rw [neg_neg] at h
  rw [h]
  congr 2
  push_cast
  ring

/-- `R(−θ) Ŝ⁻ R(θ) = e^{−iθ} Ŝ⁻` (`R = spinSRot3`). -/
theorem spinSRot3_neg_conj_spinSOpMinus (N : ℕ) (θ : ℝ) :
    spinSRot3 N (-θ) * spinSOpMinus N * spinSRot3 N θ =
      Complex.exp (-((θ : ℂ) * Complex.I)) • spinSOpMinus N := by
  have h := spinSRot3_conj_spinSOpMinus N (-θ)
  rw [neg_neg] at h
  rw [h]
  congr 2
  push_cast
  ring

/-- **Generic conjugation matrix element**: for *any* operator `M`, the twist multiplies each
matrix element by the phase `e^{i(φ_σ − φ_τ)}`: `(Û† M Û)_{στ} = e^{i(φ_σ − φ_τ)} M_{στ}`. -/
theorem lsmConj_apply (L N : ℕ) (M : ManyBodyOpS (Fin L) N) (σ τ : Fin L → Fin (N + 1)) :
    ((lsmTwistOperator L N).conjTranspose * M * lsmTwistOperator L N) σ τ =
      NormedSpace.exp (Complex.I • (lsmPhase L N σ - lsmPhase L N τ)) * M σ τ := by
  rw [lsmTwistOperator_conjTranspose_eq_diagonal, lsmTwistOperator_eq_diagonal,
    Matrix.mul_diagonal, Matrix.diagonal_mul,
    show Complex.I • (lsmPhase L N σ - lsmPhase L N τ) =
      Complex.I • lsmPhase L N σ + (-Complex.I) • lsmPhase L N τ by
        rw [smul_sub, sub_eq_add_neg, ← neg_smul],
    NormedSpace.exp_add_of_commute (Commute.all _ _)]
  ring

/-- **Single-site twist conjugation**: `Û†(onSiteS x A)Û = onSiteS x (R(−θ_x) A R(θ_x))`
(`R = spinSRot3`, `θ_x = 2π(x+1)/L`); only the `x`-factor of the twist acts. -/
theorem lsmConj_onSiteS (L N : ℕ) (x : Fin L)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (lsmTwistOperator L N).conjTranspose * onSiteS x A * lsmTwistOperator L N =
      onSiteS x (spinSRot3 N (-((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ))) * A *
        spinSRot3 N ((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ))) := by
  ext σ τ
  rw [lsmConj_apply, onSiteS_apply, onSiteS_apply]
  by_cases hc : ∀ k, k ≠ x → σ k = τ k
  · rw [if_pos hc, if_pos hc, spinSRot3_conj_apply, lsmPhase_sub_of_single_site L N x hc]
    congr 2
    simp only [smul_eq_mul]
    push_cast
    ring
  · rw [if_neg hc, if_neg hc, mul_zero]

/-- **Two-site twist conjugation**: the twist conjugates a product of two single-site operators
factor-by-factor, `Û†(onSiteS x A · onSiteS y B)Û = onSiteS x (R(−θ_x) A R(θ_x)) ·
onSiteS y (R(−θ_y) B R(θ_y))` (insert `Û Û† = 1` between the two factors). -/
theorem lsmConj_onSiteS_mul (L N : ℕ) (x y : Fin L)
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (lsmTwistOperator L N).conjTranspose * (onSiteS x A * onSiteS y B) * lsmTwistOperator L N =
      onSiteS x (spinSRot3 N (-((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ))) * A *
          spinSRot3 N ((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ))) *
        onSiteS y (spinSRot3 N (-((2 * Real.pi * ((y.val : ℝ) + 1)) / (L : ℝ))) * B *
          spinSRot3 N ((2 * Real.pi * ((y.val : ℝ) + 1)) / (L : ℝ))) := by
  have hUU := lsmTwistOperator_unitary' L N
  rw [show (lsmTwistOperator L N).conjTranspose * (onSiteS x A * onSiteS y B) *
        lsmTwistOperator L N =
      ((lsmTwistOperator L N).conjTranspose * onSiteS x A * lsmTwistOperator L N) *
        ((lsmTwistOperator L N).conjTranspose * onSiteS y B * lsmTwistOperator L N) from by
        rw [show ((lsmTwistOperator L N).conjTranspose * onSiteS x A * lsmTwistOperator L N) *
              ((lsmTwistOperator L N).conjTranspose * onSiteS y B * lsmTwistOperator L N) =
            (lsmTwistOperator L N).conjTranspose * onSiteS x A *
              (lsmTwistOperator L N * (lsmTwistOperator L N).conjTranspose) * onSiteS y B *
              lsmTwistOperator L N from by noncomm_ring, hUU, Matrix.mul_one]
        noncomm_ring,
    lsmConj_onSiteS, lsmConj_onSiteS]

/-- **Twist phase on a ladder bond term `Ŝ⁺_x Ŝ⁻_y`**: the twist multiplies it by the bond phase
`e^{i(θ_x − θ_y)}` (`θ_z = 2π(z+1)/L`).  This per-bond phase drives the energy estimate. -/
theorem lsmConj_onSiteS_plusMinus (L N : ℕ) (x y : Fin L) :
    (lsmTwistOperator L N).conjTranspose *
        (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)) * lsmTwistOperator L N =
      Complex.exp ((((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ) -
          (2 * Real.pi * ((y.val : ℝ) + 1)) / (L : ℝ) : ℝ) : ℂ) * Complex.I) •
        (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)) := by
  rw [lsmConj_onSiteS_mul, spinSRot3_neg_conj_spinSOpPlus, spinSRot3_neg_conj_spinSOpMinus,
    onSiteS_smul, onSiteS_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **Twist phase on a ladder bond term `Ŝ⁻_x Ŝ⁺_y`**: multiplied by `e^{−i(θ_x − θ_y)}`. -/
theorem lsmConj_onSiteS_minusPlus (L N : ℕ) (x y : Fin L) :
    (lsmTwistOperator L N).conjTranspose *
        (onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)) * lsmTwistOperator L N =
      Complex.exp (-((((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ) -
          (2 * Real.pi * ((y.val : ℝ) + 1)) / (L : ℝ) : ℝ) : ℂ) * Complex.I)) •
        (onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)) := by
  rw [lsmConj_onSiteS_mul, spinSRot3_neg_conj_spinSOpMinus, spinSRot3_neg_conj_spinSOpPlus,
    onSiteS_smul, onSiteS_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **Conjugated-Hamiltonian matrix element**: `(Û† Ĥ Û)_{στ} = e^{i(φ_σ − φ_τ)} Ĥ_{στ}` where
`φ = lsmPhase`.  The twist only multiplies each matrix element by a phase set by the two
configurations. -/
theorem lsmConjHamiltonian_apply (L N : ℕ) (σ τ : Fin L → Fin (N + 1)) :
    ((lsmTwistOperator L N).conjTranspose * afmHeisenbergChainHamiltonianS L N *
        lsmTwistOperator L N) σ τ =
      NormedSpace.exp (Complex.I • (lsmPhase L N σ - lsmPhase L N τ)) *
        afmHeisenbergChainHamiltonianS L N σ τ := by
  rw [lsmTwistOperator_conjTranspose_eq_diagonal, lsmTwistOperator_eq_diagonal,
    Matrix.mul_diagonal, Matrix.diagonal_mul,
    show Complex.I • (lsmPhase L N σ - lsmPhase L N τ) =
      Complex.I • lsmPhase L N σ + (-Complex.I) • lsmPhase L N τ by
        rw [smul_sub, sub_eq_add_neg, ← neg_smul],
    NormedSpace.exp_add_of_commute (Commute.all _ _)]
  ring

/-- **Energy-difference matrix element**: `(Û† Ĥ Û − Ĥ)_{στ} = (e^{i(φ_σ − φ_τ)} − 1) Ĥ_{στ}`. -/
theorem lsmConjHamiltonian_sub_apply (L N : ℕ) (σ τ : Fin L → Fin (N + 1)) :
    ((lsmTwistOperator L N).conjTranspose * afmHeisenbergChainHamiltonianS L N *
        lsmTwistOperator L N - afmHeisenbergChainHamiltonianS L N) σ τ =
      (NormedSpace.exp (Complex.I • (lsmPhase L N σ - lsmPhase L N τ)) - 1) *
        afmHeisenbergChainHamiltonianS L N σ τ := by
  rw [Matrix.sub_apply, lsmConjHamiltonian_apply, sub_one_mul]

/-- **Anti-conjugated-Hamiltonian matrix element** (the `−θ` twist): `(Û Ĥ Û†)_{στ} =
e^{−i(φ_σ − φ_τ)} Ĥ_{στ}`. -/
theorem lsmConjHamiltonianAnti_apply (L N : ℕ) (σ τ : Fin L → Fin (N + 1)) :
    (lsmTwistOperator L N * afmHeisenbergChainHamiltonianS L N *
        (lsmTwistOperator L N).conjTranspose) σ τ =
      NormedSpace.exp (-Complex.I • (lsmPhase L N σ - lsmPhase L N τ)) *
        afmHeisenbergChainHamiltonianS L N σ τ := by
  rw [lsmTwistOperator_conjTranspose_eq_diagonal, lsmTwistOperator_eq_diagonal,
    Matrix.mul_diagonal, Matrix.diagonal_mul,
    show -Complex.I • (lsmPhase L N σ - lsmPhase L N τ) =
      -Complex.I • lsmPhase L N σ + Complex.I • lsmPhase L N τ by
        rw [smul_sub, sub_eq_add_neg, ← neg_smul, neg_neg],
    NormedSpace.exp_add_of_commute (Commute.all _ _)]
  ring

/-- **Symmetrised energy-difference matrix element** (the `±θ` average): combining both twist
directions cancels the imaginary (current) part —
`(Û† Ĥ Û + Û Ĥ Û† − 2 Ĥ)_{στ} = (e^{i(φ_σ − φ_τ)} + e^{−i(φ_σ − φ_τ)} − 2) Ĥ_{στ}`. -/
theorem lsmConjHamiltonian_symm_sub_apply (L N : ℕ) (σ τ : Fin L → Fin (N + 1)) :
    ((lsmTwistOperator L N).conjTranspose * afmHeisenbergChainHamiltonianS L N *
          lsmTwistOperator L N +
        lsmTwistOperator L N * afmHeisenbergChainHamiltonianS L N *
          (lsmTwistOperator L N).conjTranspose -
        2 • afmHeisenbergChainHamiltonianS L N) σ τ =
      (NormedSpace.exp (Complex.I • (lsmPhase L N σ - lsmPhase L N τ)) +
          NormedSpace.exp (-Complex.I • (lsmPhase L N σ - lsmPhase L N τ)) - 2) *
        afmHeisenbergChainHamiltonianS L N σ τ := by
  rw [Matrix.sub_apply, Matrix.add_apply, lsmConjHamiltonian_apply, lsmConjHamiltonianAnti_apply,
    Matrix.smul_apply, nsmul_eq_mul]
  push_cast
  ring

/-- For a nonzero **eigenvector** `Φ` of the (real-eigenvalue) Hamiltonian at eigenvalue `E`, the
real Rayleigh quotient is exactly `E`. -/
theorem expectationRatioRe_of_eigenvector (L N : ℕ) (Φ : (Fin L → Fin (N + 1)) → ℂ) (E : ℝ)
    (hne : Φ ≠ 0)
    (heig : (afmHeisenbergChainHamiltonianS L N).mulVec Φ = (E : ℂ) • Φ) :
    expectationRatioRe (afmHeisenbergChainHamiltonianS L N) Φ = E := by
  have hpos : 0 < (star Φ ⬝ᵥ Φ).re :=
    dotProduct_star_self_re_pos hne
  unfold expectationRatioRe
  rw [heig, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul, mul_div_assoc,
    div_self (ne_of_gt hpos), mul_one]

/-- **Energy difference as a Rayleigh quotient of the conjugated minus bare Hamiltonian.**
For a ground-state eigenvector `Φ` at energy `E_GS`,
`expectationRatioRe Φ_LSM − E_GS = ⟨Φ, (Û† Ĥ Û − Ĥ) Φ⟩.re / ⟨Φ, Φ⟩.re`. -/
theorem expectationRatioRe_lsmTrialState_sub (L N : ℕ) (Φ : (Fin L → Fin (N + 1)) → ℂ) (E_GS : ℝ)
    (hne : Φ ≠ 0)
    (heig : (afmHeisenbergChainHamiltonianS L N).mulVec Φ = (E_GS : ℂ) • Φ) :
    expectationRatioRe (afmHeisenbergChainHamiltonianS L N) (lsmTrialState L N Φ) - E_GS =
      (star Φ ⬝ᵥ ((lsmTwistOperator L N).conjTranspose * afmHeisenbergChainHamiltonianS L N *
          lsmTwistOperator L N - afmHeisenbergChainHamiltonianS L N).mulVec Φ).re /
        (star Φ ⬝ᵥ Φ).re := by
  have hpos : 0 < (star Φ ⬝ᵥ Φ).re :=
    dotProduct_star_self_re_pos hne
  rw [expectationRatioRe_lsmTrialState, ← expectationRatioRe_of_eigenvector L N Φ E_GS hne heig]
  unfold expectationRatioRe
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, sub_div]

/-- **The anti-twisted state's Rayleigh quotient** (the `−θ` twist `Û† Φ`) equals the
anti-conjugated Hamiltonian's Rayleigh quotient. -/
theorem expectationRatioRe_lsmAntiTrialState (L N : ℕ) (Φ : (Fin L → Fin (N + 1)) → ℂ) :
    expectationRatioRe (afmHeisenbergChainHamiltonianS L N)
        ((lsmTwistOperator L N).conjTranspose.mulVec Φ) =
      expectationRatioRe (lsmTwistOperator L N * afmHeisenbergChainHamiltonianS L N *
        (lsmTwistOperator L N).conjTranspose) Φ := by
  unfold expectationRatioRe
  congr 2
  · rw [star_mulVec_dotProduct, Matrix.conjTranspose_conjTranspose, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
  · rw [star_mulVec_dotProduct, Matrix.conjTranspose_conjTranspose, Matrix.mulVec_mulVec,
      lsmTwistOperator_unitary', Matrix.one_mulVec]

/-- **Anti-twist energy difference** as a Rayleigh quotient: for a ground-state eigenvector `Φ`,
`expectationRatioRe (Û† Φ) − E_GS = ⟨Φ, (Û Ĥ Û† − Ĥ) Φ⟩.re / ⟨Φ, Φ⟩.re`. -/
theorem expectationRatioRe_lsmAntiTrialState_sub (L N : ℕ) (Φ : (Fin L → Fin (N + 1)) → ℂ)
    (E_GS : ℝ) (hne : Φ ≠ 0)
    (heig : (afmHeisenbergChainHamiltonianS L N).mulVec Φ = (E_GS : ℂ) • Φ) :
    expectationRatioRe (afmHeisenbergChainHamiltonianS L N)
        ((lsmTwistOperator L N).conjTranspose.mulVec Φ) - E_GS =
      (star Φ ⬝ᵥ (lsmTwistOperator L N * afmHeisenbergChainHamiltonianS L N *
          (lsmTwistOperator L N).conjTranspose - afmHeisenbergChainHamiltonianS L N).mulVec Φ).re /
        (star Φ ⬝ᵥ Φ).re := by
  rw [expectationRatioRe_lsmAntiTrialState, ← expectationRatioRe_of_eigenvector L N Φ E_GS hne heig]
  unfold expectationRatioRe
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, sub_div]

/-- **Symmetrised (`±θ` averaged) energy difference**: the sum of the two twist-direction energy
differences equals the Rayleigh quotient of the symmetrised operator `Û† Ĥ Û + Û Ĥ Û† − 2 Ĥ`,
in which the imaginary (current) contribution has cancelled. -/
theorem lsm_energy_diff_symm_sum (L N : ℕ) (Φ : (Fin L → Fin (N + 1)) → ℂ) (E_GS : ℝ)
    (hne : Φ ≠ 0)
    (heig : (afmHeisenbergChainHamiltonianS L N).mulVec Φ = (E_GS : ℂ) • Φ) :
    (expectationRatioRe (afmHeisenbergChainHamiltonianS L N) (lsmTrialState L N Φ) - E_GS) +
        (expectationRatioRe (afmHeisenbergChainHamiltonianS L N)
          ((lsmTwistOperator L N).conjTranspose.mulVec Φ) - E_GS) =
      (star Φ ⬝ᵥ ((lsmTwistOperator L N).conjTranspose * afmHeisenbergChainHamiltonianS L N *
            lsmTwistOperator L N +
          lsmTwistOperator L N * afmHeisenbergChainHamiltonianS L N *
            (lsmTwistOperator L N).conjTranspose -
          2 • afmHeisenbergChainHamiltonianS L N).mulVec Φ).re / (star Φ ⬝ᵥ Φ).re := by
  rw [expectationRatioRe_lsmTrialState_sub L N Φ E_GS hne heig,
    expectationRatioRe_lsmAntiTrialState_sub L N Φ E_GS hne heig, ← add_div]
  congr 1
  rw [← Complex.add_re, ← dotProduct_add, ← Matrix.add_mulVec]
  congr 3
  rw [two_smul]
  abel

/-- **Variational lower bound (`Δ₋ ≥ 0`)**: the ground energy lower-bounds the real Rayleigh
quotient of *any* nonzero vector.  Chains `E_GS ≤ hermitianMinEigenvalue ≤ expectationRatioRe`:
the minimum eigenvalue is in the spectrum (so `≥ E_GS` by minimality) and lower-bounds every
Rayleigh quotient. -/
theorem groundEnergy_le_expectationRatioRe (L N : ℕ) (E_GS : ℝ)
    (hmin : IsGroundEnergy (afmHeisenbergChainHamiltonianS L N) E_GS)
    {Ψ : (Fin L → Fin (N + 1)) → ℂ} (hΨ : Ψ ≠ 0) :
    E_GS ≤ expectationRatioRe (afmHeisenbergChainHamiltonianS L N) Ψ := by
  have hM : (afmHeisenbergChainHamiltonianS L N).IsHermitian :=
    afmHeisenbergChainHamiltonianS_isHermitian L N
  have hpos : 0 < (star Ψ ⬝ᵥ Ψ).re := dotProduct_star_self_re_pos hΨ
  have hvar := hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec hM Ψ
  have h1 : hermitianMinEigenvalue hM ≤
      expectationRatioRe (afmHeisenbergChainHamiltonianS L N) Ψ := by
    unfold expectationRatioRe rayleighOnVec at *
    rw [le_div_iff₀ hpos]
    exact hvar
  obtain ⟨v, hv0, hveig⟩ := exists_nonzero_eigenvector_hermitianMinEigenvalue hM
  exact le_trans (hmin.2 _ ⟨v, hv0, hveig⟩) h1

/-! ## P4: bond operator identity for the symmetrised twist -/

/-- **Anti-conjugation matrix element** (general `M`, the `Û · Û†` twist):
`(Û M Û†)_{στ} = e^{−i(φσ−φτ)} M_{στ}`.  Mirror of `lsmConj_apply` for the opposite twist. -/
theorem lsmConjAnti_apply (L N : ℕ) (M : ManyBodyOpS (Fin L) N) (σ τ : Fin L → Fin (N + 1)) :
    (lsmTwistOperator L N * M * (lsmTwistOperator L N).conjTranspose) σ τ =
      NormedSpace.exp (-Complex.I • (lsmPhase L N σ - lsmPhase L N τ)) * M σ τ := by
  rw [lsmTwistOperator_conjTranspose_eq_diagonal, lsmTwistOperator_eq_diagonal,
    Matrix.mul_diagonal, Matrix.diagonal_mul,
    show -Complex.I • (lsmPhase L N σ - lsmPhase L N τ) =
      -Complex.I • lsmPhase L N σ + Complex.I • lsmPhase L N τ by
        rw [smul_sub, sub_eq_add_neg, ← neg_smul, neg_neg],
    NormedSpace.exp_add_of_commute (Commute.all _ _)]
  ring

/-- **Single-site anti-conjugation**: `Û (onSiteS x A) Û† = onSiteS x (R(θ_x) A R(−θ_x))`
(`R = spinSRot3`, `θ_x = 2π(x+1)/L`); only the `x`-factor of the twist acts. -/
theorem lsmConjAnti_onSiteS (L N : ℕ) (x : Fin L)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    lsmTwistOperator L N * onSiteS x A * (lsmTwistOperator L N).conjTranspose =
      onSiteS x (spinSRot3 N ((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ)) * A *
        spinSRot3 N (-((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ)))) := by
  ext σ τ
  rw [lsmConjAnti_apply, onSiteS_apply, onSiteS_apply]
  by_cases hc : ∀ k, k ≠ x → σ k = τ k
  · rw [if_pos hc, if_pos hc,
      show spinSRot3 N ((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ)) * A *
          spinSRot3 N (-((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ))) =
        spinSRot3 N (-(-((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ)))) * A *
          spinSRot3 N (-((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ))) by rw [neg_neg],
      spinSRot3_conj_apply, lsmPhase_sub_of_single_site L N x hc]
    congr 2
    simp only [smul_eq_mul]
    push_cast
    ring
  · rw [if_neg hc, if_neg hc, mul_zero]

/-- **Two-site anti-conjugation**: the opposite twist conjugates a product factor-by-factor (insert
`Û† Û = 1` between the two factors). -/
theorem lsmConjAnti_onSiteS_mul (L N : ℕ) (x y : Fin L)
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    lsmTwistOperator L N * (onSiteS x A * onSiteS y B) * (lsmTwistOperator L N).conjTranspose =
      onSiteS x (spinSRot3 N ((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ)) * A *
          spinSRot3 N (-((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ)))) *
        onSiteS y (spinSRot3 N ((2 * Real.pi * ((y.val : ℝ) + 1)) / (L : ℝ)) * B *
          spinSRot3 N (-((2 * Real.pi * ((y.val : ℝ) + 1)) / (L : ℝ)))) := by
  have hUU := lsmTwistOperator_unitary L N
  rw [show lsmTwistOperator L N * (onSiteS x A * onSiteS y B) *
        (lsmTwistOperator L N).conjTranspose =
      (lsmTwistOperator L N * onSiteS x A * (lsmTwistOperator L N).conjTranspose) *
        (lsmTwistOperator L N * onSiteS y B * (lsmTwistOperator L N).conjTranspose) from by
        rw [show (lsmTwistOperator L N * onSiteS x A * (lsmTwistOperator L N).conjTranspose) *
              (lsmTwistOperator L N * onSiteS y B * (lsmTwistOperator L N).conjTranspose) =
            lsmTwistOperator L N * onSiteS x A *
              ((lsmTwistOperator L N).conjTranspose * lsmTwistOperator L N) * onSiteS y B *
              (lsmTwistOperator L N).conjTranspose from by noncomm_ring, hUU, Matrix.mul_one]
        noncomm_ring,
    lsmConjAnti_onSiteS, lsmConjAnti_onSiteS]

/-- **Anti-twist phase on `Ŝ⁺_x Ŝ⁻_y`**: `Û(Ŝ⁺_xŜ⁻_y)Û† = e^{−i(θ_x − θ_y)}(Ŝ⁺_xŜ⁻_y)`. -/
theorem lsmConjAnti_onSiteS_plusMinus (L N : ℕ) (x y : Fin L) :
    lsmTwistOperator L N *
        (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)) *
        (lsmTwistOperator L N).conjTranspose =
      Complex.exp (-((((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ) -
          (2 * Real.pi * ((y.val : ℝ) + 1)) / (L : ℝ) : ℝ) : ℂ) * Complex.I)) •
        (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)) := by
  rw [lsmConjAnti_onSiteS_mul, spinSRot3_conj_spinSOpPlus, spinSRot3_conj_spinSOpMinus,
    onSiteS_smul, onSiteS_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **Anti-twist phase on `Ŝ⁻_x Ŝ⁺_y`**: `Û(Ŝ⁻_xŜ⁺_y)Û† = e^{+i(θ_x − θ_y)}(Ŝ⁻_xŜ⁺_y)`. -/
theorem lsmConjAnti_onSiteS_minusPlus (L N : ℕ) (x y : Fin L) :
    lsmTwistOperator L N *
        (onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)) *
        (lsmTwistOperator L N).conjTranspose =
      Complex.exp (((((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ) -
          (2 * Real.pi * ((y.val : ℝ) + 1)) / (L : ℝ) : ℝ) : ℂ) * Complex.I)) •
        (onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)) := by
  rw [lsmConjAnti_onSiteS_mul, spinSRot3_conj_spinSOpMinus, spinSRot3_conj_spinSOpPlus,
    onSiteS_smul, onSiteS_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **`Ŝ³_x Ŝ³_y` is twist-invariant** (`Û†·Û` direction): the `Ŝ³`-rotation fixes `Ŝ³`. -/
theorem lsmConj_onSiteS_three (L N : ℕ) (x y : Fin L) :
    (lsmTwistOperator L N).conjTranspose *
        (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)) * lsmTwistOperator L N =
      onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N) := by
  rw [lsmConj_onSiteS_mul, spinSRot3_neg_conj_spinSOp3, spinSRot3_neg_conj_spinSOp3]

/-- **`Ŝ³_x Ŝ³_y` is twist-invariant** (`Û·Û†` direction). -/
theorem lsmConjAnti_onSiteS_three (L N : ℕ) (x y : Fin L) :
    lsmTwistOperator L N *
        (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)) * (lsmTwistOperator L N).conjTranspose =
      onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N) := by
  rw [lsmConjAnti_onSiteS_mul,
    show spinSRot3 N ((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ)) * spinSOp3 N *
        spinSRot3 N (-((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ))) =
      spinSRot3 N (-(-((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ)))) * spinSOp3 N *
        spinSRot3 N (-((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ))) by rw [neg_neg],
    show spinSRot3 N ((2 * Real.pi * ((y.val : ℝ) + 1)) / (L : ℝ)) * spinSOp3 N *
        spinSRot3 N (-((2 * Real.pi * ((y.val : ℝ) + 1)) / (L : ℝ))) =
      spinSRot3 N (-(-((2 * Real.pi * ((y.val : ℝ) + 1)) / (L : ℝ)))) * spinSOp3 N *
        spinSRot3 N (-((2 * Real.pi * ((y.val : ℝ) + 1)) / (L : ℝ))) by rw [neg_neg],
    spinSRot3_neg_conj_spinSOp3, spinSRot3_neg_conj_spinSOp3]

/-- The **two-site `XY` operator** `XY_{xy} = Ŝ¹_x Ŝ¹_y + Ŝ²_x Ŝ²_y` (the transverse part of the
spin dot product). -/
noncomputable def lsmXY (L N : ℕ) (x y : Fin L) : ManyBodyOpS (Fin L) N :=
  onSiteS x (spinSOp1 N) * onSiteS y (spinSOp1 N) +
    onSiteS x (spinSOp2 N) * onSiteS y (spinSOp2 N)

/-- **`XY` in the ladder basis**: `XY_{xy} = ½(Ŝ⁺_xŜ⁻_y + Ŝ⁻_xŜ⁺_y)`.  Obtained by subtracting the
`Ŝ³Ŝ³` part from both forms of `Ŝ_x · Ŝ_y` (`spinSDot_def` and `spinSDot_eq_plus_minus`). -/
theorem lsmXY_eq_ladder (L N : ℕ) (x y : Fin L) :
    lsmXY L N x y =
      (1 / 2 : ℂ) • (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) +
        onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)) := by
  have h := spinSDot_eq_plus_minus (Λ := Fin L) x y N
  rw [spinSDot_def] at h
  unfold lsmXY
  exact add_right_cancel h

/-- **Per-bond symmetrised twist identity** (the heart of Lemma 6.1).  Averaging the two twist
directions cancels the longitudinal (`Ŝ³Ŝ³`) part and the imaginary current, leaving
`Û†(Ŝ_x·Ŝ_y)Û + Û(Ŝ_x·Ŝ_y)Û† − 2(Ŝ_x·Ŝ_y) = 2(cos(θ_x − θ_y) − 1)·XY_{xy}`. -/
theorem lsmConj_spinSDot_symm (L N : ℕ) (x y : Fin L) :
    (lsmTwistOperator L N).conjTranspose * spinSDot x y N * lsmTwistOperator L N +
        lsmTwistOperator L N * spinSDot x y N * (lsmTwistOperator L N).conjTranspose -
        2 • spinSDot x y N =
      ((2 * Real.cos ((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ) -
          (2 * Real.pi * ((y.val : ℝ) + 1)) / (L : ℝ)) - 2 : ℝ) : ℂ) • lsmXY L N x y := by
  rw [spinSDot_eq_plus_minus]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add,
    lsmConj_onSiteS_three, lsmConjAnti_onSiteS_three,
    lsmConj_onSiteS_plusMinus, lsmConj_onSiteS_minusPlus,
    lsmConjAnti_onSiteS_plusMinus, lsmConjAnti_onSiteS_minusPlus]
  rw [lsmXY_eq_ladder]
  set β : ℝ := (2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ) -
    (2 * Real.pi * ((y.val : ℝ) + 1)) / (L : ℝ) with hβ
  have hcoef : ((2 * Real.cos β - 2 : ℝ) : ℂ) =
      (Complex.exp ((β : ℂ) * Complex.I) + Complex.exp (-((β : ℂ) * Complex.I))) - 2 := by
    have h2c := Complex.two_cos (β : ℂ)
    rw [neg_mul] at h2c
    push_cast
    linear_combination h2c
  rw [hcoef]
  module

/-- **Bond-sum form of the symmetrised twist Hamiltonian**: distributing the per-bond identity
`lsmConj_spinSDot_symm` over the periodic chain `Ĥ = Σ_{x,y} J(x,y) Ŝ_x·Ŝ_y` gives
`Û†ĤÛ + ÛĤÛ† − 2Ĥ = Σ_{x,y} J(x,y)·2(cos(θ_x−θ_y)−1)·XY_{xy}`. -/
theorem lsmHamiltonian_symm_eq_bondSum (L N : ℕ) :
    (lsmTwistOperator L N).conjTranspose * afmHeisenbergChainHamiltonianS L N *
          lsmTwistOperator L N +
        lsmTwistOperator L N * afmHeisenbergChainHamiltonianS L N *
          (lsmTwistOperator L N).conjTranspose -
        2 • afmHeisenbergChainHamiltonianS L N =
      ∑ x : Fin L, ∑ y : Fin L, ringCoupling L x y •
        (((2 * Real.cos ((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ) -
            (2 * Real.pi * ((y.val : ℝ) + 1)) / (L : ℝ)) - 2 : ℝ) : ℂ) • lsmXY L N x y) := by
  have key : ∀ x y : Fin L,
      (lsmTwistOperator L N).conjTranspose * (ringCoupling L x y • spinSDot x y N) *
            lsmTwistOperator L N +
          lsmTwistOperator L N * (ringCoupling L x y • spinSDot x y N) *
            (lsmTwistOperator L N).conjTranspose -
          2 • (ringCoupling L x y • spinSDot x y N) =
        ringCoupling L x y •
          (((2 * Real.cos ((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ) -
              (2 * Real.pi * ((y.val : ℝ) + 1)) / (L : ℝ)) - 2 : ℝ) : ℂ) • lsmXY L N x y) := by
    intro x y
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
      smul_comm (2 : ℕ) (ringCoupling L x y) (spinSDot x y N),
      ← smul_add, ← smul_sub, lsmConj_spinSDot_symm]
  unfold afmHeisenbergChainHamiltonianS heisenbergHamiltonianS
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  exact key x y

/-- **`XY` expectation bound**: `|⟨Φ, XY_{xy} Φ⟩.re| ≤ 2 S² ‖Φ‖²` (each of `Ŝ¹Ŝ¹`, `Ŝ²Ŝ²` is bounded
by `S²‖Φ‖²` via the per-axis Cauchy–Schwarz bond bound). -/
theorem lsmXY_dotProduct_re_abs_le (L N : ℕ) (x y : Fin L)
    (Φ : (Fin L → Fin (N + 1)) → ℂ) :
    |(star Φ ⬝ᵥ (lsmXY L N x y).mulVec Φ).re| ≤
      2 * ((N : ℝ) / 2) ^ 2 * (star Φ ⬝ᵥ Φ).re := by
  unfold lsmXY
  rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]
  have h1 := onSiteS_mul_onSiteS_dotProduct_re_abs_le x y (sq_nonneg ((N : ℝ) / 2))
    (spinSOp1_isHermitian N) (spinSOp1_sq_posSemidef N) Φ
  have h2 := onSiteS_mul_onSiteS_dotProduct_re_abs_le x y (sq_nonneg ((N : ℝ) / 2))
    (spinSOp2_isHermitian N) (spinSOp2_sq_posSemidef N) Φ
  obtain ⟨h1l, h1u⟩ := abs_le.1 h1
  obtain ⟨h2l, h2u⟩ := abs_le.1 h2
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- On the **support of the ring coupling** (`J(x,y) ≠ 0`, i.e. `y = x+1 mod L`) the bond angle has
the *same* cosine for every bond, `cos(θ_x − θ_y) = cos(2π/L)`: interior bonds give `θ_x − θ_y =
−2π/L`, and the wrap-around bond gives `2π − 2π/L`.  This uniformises the per-bond estimate. -/
theorem ringCoupling_cos_eq (L : ℕ) {x y : Fin L} (h : ringCoupling L x y ≠ 0) :
    Real.cos ((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ) -
        (2 * Real.pi * ((y.val : ℝ) + 1)) / (L : ℝ)) =
      Real.cos (2 * Real.pi / (L : ℝ)) := by
  have hLpos : 0 < L := lt_of_le_of_lt (Nat.zero_le x.val) x.isLt
  have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hLpos.ne'
  have hc : y.val = (x.val + 1) % L := by
    by_contra hne
    rw [ringCoupling, if_neg hne] at h
    exact h rfl
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt x.isLt) with heq | hlt
  · have heq' : x.val + 1 = L := heq
    have hy : y.val = 0 := by rw [hc, heq', Nat.mod_self]
    have hxL : ((x.val : ℝ) + 1) = (L : ℝ) := by
      have : ((x.val + 1 : ℕ) : ℝ) = (L : ℝ) := by exact_mod_cast heq'
      push_cast at this; linarith
    rw [hy,
      show (2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ) -
          (2 * Real.pi * (((0 : ℕ) : ℝ) + 1)) / (L : ℝ) =
        2 * Real.pi - 2 * Real.pi / (L : ℝ) by
          rw [hxL]; field_simp; ring,
      Real.cos_two_pi_sub]
  · have hlt' : x.val + 1 < L := hlt
    have hy : y.val = x.val + 1 := by rw [hc, Nat.mod_eq_of_lt hlt']
    rw [hy,
      show (2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ) -
          (2 * Real.pi * (((x.val + 1 : ℕ) : ℝ) + 1)) / (L : ℝ) =
        -(2 * Real.pi / (L : ℝ)) by push_cast; ring,
      Real.cos_neg]

/-! ## P5: assemble the energy bound (Tasaki Lemma 6.1) -/

/-- **Tasaki Lemma 6.1 (the twisted state has low energy).**  For the antiferromagnetic Heisenberg
chain of any spin `S = N/2` and length `L`, the LSM trial state `Φ_LSM` has energy above the ground
state bounded by `8π²S²/L` (eq. (6.2.5)):
`⟨Φ_LSM, Ĥ Φ_LSM⟩ / ⟨Φ_LSM, Φ_LSM⟩ − E_GS ≤ 8π²S²/L`.

Proof: `Δ₊ ≤ Δ₊ + Δ₋ = ⟨Φ, (Û†ĤÛ + ÛĤÛ† − 2Ĥ) Φ⟩/‖Φ‖²` (`Δ₋ ≥ 0` by the variational principle;
the imaginary current cancels in the `±θ` average).  The symmetrised operator equals
`Σ_bonds 2(cos(2π/L) − 1) XY_b`; each of the `L` bonds contributes
`≤ 2(1−cos(2π/L))·2S² ≤ (2π/L)²·2S² = 8π²S²/L²`, summing to `8π²S²/L`. -/
theorem lsm_energy_bound (L N : ℕ) (hL : 0 < L)
    (Φ_GS : (Fin L → Fin (N + 1)) → ℂ) (E_GS : ℝ) (hne : Φ_GS ≠ 0)
    (heig : (afmHeisenbergChainHamiltonianS L N).mulVec Φ_GS = (E_GS : ℂ) • Φ_GS)
    (hmin : IsGroundEnergy (afmHeisenbergChainHamiltonianS L N) E_GS) :
    expectationRatioRe (afmHeisenbergChainHamiltonianS L N) (lsmTrialState L N Φ_GS) - E_GS ≤
      8 * Real.pi ^ 2 * ((N : ℝ) / 2) ^ 2 / (L : ℝ) := by
  have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  have hppos : 0 < (star Φ_GS ⬝ᵥ Φ_GS).re := dotProduct_star_self_re_pos hne
  -- Δ₋ ≥ 0: the back-twisted state is nonzero (unitarity) and its Rayleigh quotient ≥ E_GS.
  have hΦ' : (lsmTwistOperator L N).conjTranspose.mulVec Φ_GS ≠ 0 := by
    intro hcon
    apply hne
    have h := lsmTwistOperator_unitary' L N
    calc Φ_GS = (1 : ManyBodyOpS (Fin L) N).mulVec Φ_GS := by rw [Matrix.one_mulVec]
      _ = (lsmTwistOperator L N * (lsmTwistOperator L N).conjTranspose).mulVec Φ_GS := by rw [h]
      _ = (lsmTwistOperator L N).mulVec
            ((lsmTwistOperator L N).conjTranspose.mulVec Φ_GS) := by rw [Matrix.mulVec_mulVec]
      _ = (lsmTwistOperator L N).mulVec 0 := by rw [hcon]
      _ = 0 := Matrix.mulVec_zero _
  have hΔm : 0 ≤ expectationRatioRe (afmHeisenbergChainHamiltonianS L N)
      ((lsmTwistOperator L N).conjTranspose.mulVec Φ_GS) - E_GS := by
    have := groundEnergy_le_expectationRatioRe L N E_GS hmin hΦ'
    linarith
  -- ⟨bond x ⟶ y⟩ ≤ J(x,y)·(8π²S²/L²)·‖Φ‖²; off-support it is 0.
  have hterm : ∀ x y : Fin L,
      (star Φ_GS ⬝ᵥ (ringCoupling L x y •
          ((((2 * Real.cos ((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ) -
              (2 * Real.pi * ((y.val : ℝ) + 1)) / (L : ℝ)) - 2 : ℝ)) : ℂ) •
            lsmXY L N x y)).mulVec Φ_GS).re ≤
        (ringCoupling L x y).re *
          (2 * (2 * Real.pi / (L : ℝ)) ^ 2 * ((N : ℝ) / 2) ^ 2 * (star Φ_GS ⬝ᵥ Φ_GS).re) := by
    intro x y
    by_cases hr : ringCoupling L x y = 0
    · simp [hr]
    · have hcond : y.val = (x.val + 1) % L := by
        by_contra hc
        rw [ringCoupling, if_neg hc] at hr
        exact hr rfl
      have h1 : ringCoupling L x y = 1 := by rw [ringCoupling, if_pos hcond]
      rw [h1, one_smul, Complex.one_re, one_mul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
        Complex.re_ofReal_mul, ringCoupling_cos_eq L hr]
      have hw := lsmXY_dotProduct_re_abs_le L N x y Φ_GS
      obtain ⟨hwl, hwu⟩ := abs_le.1 hw
      have hcos1 : Real.cos (2 * Real.pi / (L : ℝ)) ≤ 1 := Real.cos_le_one _
      have hcos2 : 1 - Real.cos (2 * Real.pi / (L : ℝ)) ≤ (2 * Real.pi / (L : ℝ)) ^ 2 / 2 :=
        one_sub_cos_le_half_sq _
      have hS2p : 0 ≤ ((N : ℝ) / 2) ^ 2 * (star Φ_GS ⬝ᵥ Φ_GS).re :=
        mul_nonneg (sq_nonneg _) hppos.le
      nlinarith [hwl, hwu, hcos1, hcos2, hS2p,
        mul_nonneg (sub_nonneg.2 hcos1)
          (show (0 : ℝ) ≤ 2 * ((N : ℝ) / 2) ^ 2 * (star Φ_GS ⬝ᵥ Φ_GS).re +
            (star Φ_GS ⬝ᵥ (lsmXY L N x y).mulVec Φ_GS).re by linarith),
        mul_nonneg (sub_nonneg.2 hcos2) hS2p]
  -- Σ_{x,y} J(x,y).re = L (each site has a unique successor).
  have hringsum : ∑ x : Fin L, ∑ y : Fin L, (ringCoupling L x y).re = (L : ℝ) := by
    have hinner : ∀ x : Fin L, ∑ y : Fin L, (ringCoupling L x y).re = 1 := by
      intro x
      have hy0lt : (x.val + 1) % L < L := Nat.mod_lt _ hL
      rw [Finset.sum_eq_single (a := (⟨(x.val + 1) % L, hy0lt⟩ : Fin L))
        (fun y _ hyne => by
          rw [ringCoupling, if_neg (fun hcond => hyne (Fin.ext hcond)), Complex.zero_re])
        (fun h => absurd (Finset.mem_univ _) h)]
      rw [ringCoupling, if_pos rfl, Complex.one_re]
    rw [Finset.sum_congr rfl (fun x _ => hinner x), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  -- Bound the symmetrised expectation by (8π²S²/L)·‖Φ‖².
  have hbound : (star Φ_GS ⬝ᵥ ((lsmTwistOperator L N).conjTranspose *
          afmHeisenbergChainHamiltonianS L N * lsmTwistOperator L N +
        lsmTwistOperator L N * afmHeisenbergChainHamiltonianS L N *
          (lsmTwistOperator L N).conjTranspose -
        2 • afmHeisenbergChainHamiltonianS L N).mulVec Φ_GS).re ≤
      (8 * Real.pi ^ 2 * ((N : ℝ) / 2) ^ 2 / (L : ℝ)) * (star Φ_GS ⬝ᵥ Φ_GS).re := by
    rw [lsmHamiltonian_symm_eq_bondSum]
    simp_rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
    refine le_trans (Finset.sum_le_sum (fun x _ =>
      Finset.sum_le_sum (fun y _ => hterm x y))) ?_
    have hcollapse :
        (∑ x : Fin L, ∑ y : Fin L, (ringCoupling L x y).re *
            (2 * (2 * Real.pi / (L : ℝ)) ^ 2 * ((N : ℝ) / 2) ^ 2 * (star Φ_GS ⬝ᵥ Φ_GS).re)) =
          (8 * Real.pi ^ 2 * ((N : ℝ) / 2) ^ 2 / (L : ℝ)) * (star Φ_GS ⬝ᵥ Φ_GS).re := by
      simp_rw [← Finset.sum_mul]
      rw [hringsum]
      field_simp
      ring
    exact le_of_eq hcollapse
  -- Δ₊ ≤ Δ₊ + Δ₋ = ⟨symm⟩/‖Φ‖² ≤ 8π²S²/L.
  have hsum := lsm_energy_diff_symm_sum L N Φ_GS E_GS hne heig
  have hcomb : (expectationRatioRe (afmHeisenbergChainHamiltonianS L N) (lsmTrialState L N Φ_GS) -
        E_GS) +
      (expectationRatioRe (afmHeisenbergChainHamiltonianS L N)
        ((lsmTwistOperator L N).conjTranspose.mulVec Φ_GS) - E_GS) ≤
      8 * Real.pi ^ 2 * ((N : ℝ) / 2) ^ 2 / (L : ℝ) := by
    rw [hsum, div_le_iff₀ hppos]
    exact hbound
  linarith [hΔm, hcomb]

end LatticeSystem.Quantum
