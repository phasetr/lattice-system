import LatticeSystem.Quantum.SpinS.AKLT
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Matrix product state definitions for Tasaki Theorem 7.5

This file defines the matrix product state data and the three conditions in Tasaki Theorem 7.5.
It also defines the dual transfer map and the faithful dual eigenmatrix hypothesis needed for the
corrected transfer-spectrum implication.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.2.2, Theorem 7.5, eqs. (7.2.41)–(7.2.42), pp. 202–203.
-/

namespace LatticeSystem.Quantum

open Matrix Module
open scoped ComplexOrder

variable {D N : ℕ}

/-- A collection of MPS matrices `(A^σ)_{σ = 0,…,N}` of bond dimension `D` for a spin-`S` site
(`N = 2S`): each `A^σ` is a `D × D` complex matrix. -/
abbrev MPSMatrices (D N : ℕ) : Type :=
  Fin (N + 1) → Matrix (Fin D) (Fin D) ℂ

/-- The transfer matrix `Ã` of an MPS, as defined in Tasaki eq. (7.2.42). -/
noncomputable def mpsTransferMatrix (A : MPSMatrices D N) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  Matrix.of fun p q => ∑ σ : Fin (N + 1), star (A σ p.1 q.1) * A σ p.2 q.2

/-- The ordered product `A^{σ_1} A^{σ_2} ⋯ A^{σ_ℓ}` of MPS matrices along a list of spin
labels. -/
noncomputable def orderedProd (A : MPSMatrices D N) :
    List (Fin (N + 1)) → Matrix (Fin D) (Fin D) ℂ
  | [] => 1
  | σ :: ss => A σ * orderedProd A ss

/-- The MPS matrices span at length `ℓ` when their ordered products of length `ℓ` span every
`D × D` matrix. -/
def mpsProductsSpanAt (A : MPSMatrices D N) (ℓ : ℕ) : Prop :=
  Submodule.span ℂ {M : Matrix (Fin D) (Fin D) ℂ |
    ∃ σs : List (Fin (N + 1)), σs.length = ℓ ∧ M = orderedProd A σs} = ⊤

/-- The normalization equation `Σ_σ A^σ (A^σ)† = λ I`, with `λ > 0`, from Tasaki
eq. (7.2.41). -/
def IsMPSNormalized (A : MPSMatrices D N) (lam : ℝ) : Prop :=
  0 < lam ∧
    (∑ σ : Fin (N + 1), A σ * (A σ).conjTranspose) =
      (lam : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ)

/-- Theorem 7.5(i): ordered products span all `D × D` matrices at some length. -/
def MPSSpansEventually (A : MPSMatrices D N) : Prop :=
  ∃ ℓ₀ : ℕ, mpsProductsSpanAt A ℓ₀

/-- Theorem 7.5(ii): ordered products span all `D × D` matrices at every sufficiently large
length. -/
def MPSSpansForAllLarge (A : MPSMatrices D N) : Prop :=
  ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ₀ ≤ ℓ → mpsProductsSpanAt A ℓ

/-- Theorem 7.5(iii): `λ` is a simple transfer-matrix eigenvalue and all other eigenvalues have
strictly smaller norm. -/
noncomputable def HasPrimitiveTransferSpectrum (A : MPSMatrices D N) (lam : ℝ) : Prop :=
  (lam : ℂ) ∈ spectrum ℂ (mpsTransferMatrix A) ∧
    finrank ℂ (LinearMap.ker
      ((mpsTransferMatrix A).mulVecLin - (lam : ℂ) • LinearMap.id)) = 1 ∧
    ∀ μ : ℂ, μ ∈ spectrum ℂ (mpsTransferMatrix A) →
      μ ≠ (lam : ℂ) → ‖μ‖ < lam

/-- A collection of MPS matrices is injective when it is normalized and satisfies all three
conditions in Tasaki Theorem 7.5. -/
def IsInjectiveMPS (A : MPSMatrices D N) (lam : ℝ) : Prop :=
  IsMPSNormalized A lam ∧ MPSSpansEventually A ∧ MPSSpansForAllLarge A ∧
    HasPrimitiveTransferSpectrum A lam

/-- The dual completely positive transfer map `ρ ↦ Σ_σ (A^σ)† ρ A^σ`. -/
noncomputable def mpsDualTransferMap (A : MPSMatrices D N)
    (ρ : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  ∑ σ : Fin (N + 1), (A σ).conjTranspose * ρ * A σ

/-- The dual transfer map has a positive-definite eigenmatrix with eigenvalue `λ`. -/
def HasFaithfulDualEigenmatrix (A : MPSMatrices D N) (lam : ℝ) : Prop :=
  ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
    ρ.PosDef ∧ mpsDualTransferMap A ρ = (lam : ℂ) • ρ

/-- Spanning at one length propagates to the next length under MPS normalization. -/
private theorem mpsProductsSpanAt_succ
    (A : MPSMatrices D N) (lam : ℝ) (ℓ : ℕ)
    (hnorm : IsMPSNormalized A lam) (hspan : mpsProductsSpanAt A ℓ) :
    mpsProductsSpanAt A (ℓ + 1) := by
  unfold mpsProductsSpanAt at hspan ⊢
  rw [Submodule.eq_top_iff'] at hspan ⊢
  intro M
  let W : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    Submodule.span ℂ {X : Matrix (Fin D) (Fin D) ℂ |
      ∃ σs : List (Fin (N + 1)), σs.length = ℓ + 1 ∧ X = orderedProd A σs}
  have hleft (σ : Fin (N + 1)) (X : Matrix (Fin D) (Fin D) ℂ) :
      A σ * X ∈ W := by
    have hX : X ∈ Submodule.span ℂ {P : Matrix (Fin D) (Fin D) ℂ |
        ∃ σs : List (Fin (N + 1)), σs.length = ℓ ∧ P = orderedProd A σs} :=
      hspan X
    induction hX using Submodule.span_induction with
    | mem P hP =>
        obtain ⟨σs, hlen, rfl⟩ := hP
        apply Submodule.subset_span
        refine ⟨σ :: σs, ?_, ?_⟩
        · simp [hlen]
        · rfl
    | zero =>
        simpa only [Matrix.mul_zero] using W.zero_mem
    | add X Y _ _ hX hY =>
        simpa [Matrix.mul_add] using W.add_mem hX hY
    | smul c X _ hX =>
        simpa [Matrix.mul_smul] using W.smul_mem c hX
  have hlam : (lam : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hnorm.1
  have hM :
      M = ∑ σ : Fin (N + 1),
        A σ * (((lam : ℂ)⁻¹) • ((A σ).conjTranspose * M)) := by
    calc
      M = (1 : Matrix (Fin D) (Fin D) ℂ) * M := by simp
      _ = (((lam : ℂ)⁻¹) •
          (∑ σ : Fin (N + 1), A σ * (A σ).conjTranspose)) * M := by
            rw [hnorm.2]
            rw [inv_smul_smul₀ hlam, one_mul]
      _ = ∑ σ : Fin (N + 1),
          A σ * (((lam : ℂ)⁻¹) • ((A σ).conjTranspose * M)) := by
            simp_rw [Matrix.smul_mul, Finset.sum_mul, Matrix.mul_assoc,
              Matrix.mul_smul]
            rw [Finset.smul_sum]
  rw [hM]
  exact Submodule.sum_mem W fun σ _ => hleft σ _

/-- Under normalization, Theorem 7.5(i) and Theorem 7.5(ii) are equivalent. -/
theorem mps_spans_eventually_iff_spans_for_all_large
    (A : MPSMatrices D N) (lam : ℝ) (hnorm : IsMPSNormalized A lam) :
    MPSSpansEventually A ↔ MPSSpansForAllLarge A := by
  constructor
  · rintro ⟨ℓ₀, hspan⟩
    refine ⟨ℓ₀, fun ℓ hℓ => ?_⟩
    induction ℓ, hℓ using Nat.le_induction with
    | base => exact hspan
    | succ k _ hk => exact mpsProductsSpanAt_succ A lam k hnorm hk
  · rintro ⟨ℓ₀, hspan⟩
    exact ⟨ℓ₀, hspan ℓ₀ le_rfl⟩

end LatticeSystem.Quantum
