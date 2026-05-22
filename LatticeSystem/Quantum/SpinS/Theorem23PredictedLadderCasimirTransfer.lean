import LatticeSystem.Quantum.SpinS.Theorem23PredictedLadder

/-!
# Tasaki §2.5 Theorem 2.3 predicted-ladder Casimir-transfer suffix

This module contains the real-scalar transfer and predicted-Casimir
preservation suffix split from `Theorem23PredictedLadder.lean`. The base
predicted-ladder module keeps the predicted-GS ladder closure and joint
sublattice-Casimir structure, while this module exposes the scalar-cancellation
and total-Casimir transfer wrappers consumed by the sector-existence and
dominance chains.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.

Tracked in Issue #412 (Tasaki §2.5: Marshall–Lieb–Mattis theorem).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS transfer across a non-zero
real scalar**: if a vector in the predicted toy ground-state subspace is
a non-zero real scalar multiple of another vector, then the second vector
also lies in the predicted toy ground-state subspace.

This is the membership analogue of
`tasaki23_totalSpinSSquared_predictedCasimirValue_of_real_smul_eq`, used
after the lowered ladder image is identified with the successor-sector
representative up to a positive real scalar. -/
theorem tasaki23_mem_bipartiteToyGroundStateSubspacePredicted_of_real_smul_eq
    (A : V → Bool) (N : ℕ) {r : ℝ}
    {Ψ Φ : (V → Fin (N + 1)) → ℂ}
    (hr : r ≠ 0)
    (hrel : Ψ = (r : ℂ) • Φ)
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    Φ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hsmul :
      (r : ℂ) • Φ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
    simpa [← hrel] using hΨ
  have hinv :
      ((r : ℂ)⁻¹) • ((r : ℂ) • Φ) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N :=
    Submodule.smul_mem _ _ hsmul
  have hscale : ((r : ℂ)⁻¹) • ((r : ℂ) • Φ) = Φ := by
    rw [smul_smul, inv_mul_cancel₀ hrC, one_smul]
  rwa [hscale] at hinv

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS lowered Casimir bridge**:
in the canonical orientation, a vector in the predicted toy ground-state
subspace has a total-lowering image with the Theorem 2.3 predicted
total-Casimir eigenvalue.

This combines predicted-GS lowering closure with the predicted-GS
total-Casimir bridge, so no separate Casimir hypothesis is needed for
the lowered ladder image. -/
theorem tasaki23_lowered_predictedCasimirValue_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (totalSpinSSquared V N).mulVec ((totalSpinSOpMinus V N).mulVec Ψ) =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
        ((totalSpinSOpMinus V N).mulVec Ψ) := by
  exact
    tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
      (V := V) A N hBA
      (tasaki23_totalSpinSOpMinus_mulVec_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ)

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS raised Casimir bridge**:
in the canonical orientation, a vector in the predicted toy ground-state
subspace has a total-raising image with the Theorem 2.3 predicted
total-Casimir eigenvalue.

This is the raising-direction companion to
`tasaki23_lowered_predictedCasimirValue_of_mem_bipartiteToyGroundStateSubspacePredicted`.
-/
theorem tasaki23_raised_predictedCasimirValue_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (totalSpinSSquared V N).mulVec ((totalSpinSOpPlus V N).mulVec Ψ) =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
        ((totalSpinSOpPlus V N).mulVec Ψ) := by
  exact
    tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
      (V := V) A N hBA
      (tasaki23_totalSpinSOpPlus_mulVec_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ)

/-- **Tasaki §2.5 Theorem 2.3 predicted-Casimir preservation under
lowering**: if a full spin-`S` vector has the Theorem 2.3 predicted
total-Casimir eigenvalue, then its image under `Ŝ^-_tot` has the same
total-Casimir eigenvalue.

This is the one-step Casimir stability needed when the admissible-sector
chain propagates Theorem 2.3 ground states by the total lowering
operator. -/
theorem tasaki23_totalSpinSOpMinus_preserves_predictedCasimirValue
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ_cas :
      (totalSpinSSquared V N).mulVec Ψ =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) • Ψ) :
    (totalSpinSSquared V N).mulVec ((totalSpinSOpMinus V N).mulVec Ψ) =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
        (totalSpinSOpMinus V N).mulVec Ψ := by
  have hcomm : totalSpinSSquared V N * totalSpinSOpMinus V N =
      totalSpinSOpMinus V N * totalSpinSSquared V N :=
    (totalSpinSSquared_commute_totalSpinSOpMinus (V := V) (N := N)).eq
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hΨ_cas, Matrix.mulVec_smul]

/-- **Tasaki §2.5 Theorem 2.3 predicted-Casimir preservation under
raising**: if a full spin-`S` vector has the Theorem 2.3 predicted
total-Casimir eigenvalue, then its image under `Ŝ^+_tot` has the same
total-Casimir eigenvalue.

This is the raising-direction companion to
`tasaki23_totalSpinSOpMinus_preserves_predictedCasimirValue`, used when
the admissible-sector chain is traversed toward smaller `magSumS`
sectors. -/
theorem tasaki23_totalSpinSOpPlus_preserves_predictedCasimirValue
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ_cas :
      (totalSpinSSquared V N).mulVec Ψ =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) • Ψ) :
    (totalSpinSSquared V N).mulVec ((totalSpinSOpPlus V N).mulVec Ψ) =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
        (totalSpinSOpPlus V N).mulVec Ψ := by
  have hcomm : totalSpinSSquared V N * totalSpinSOpPlus V N =
      totalSpinSOpPlus V N * totalSpinSSquared V N :=
    (totalSpinSSquared_commute_totalSpinSOpPlus (V := V) (N := N)).eq
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hΨ_cas, Matrix.mulVec_smul]

/-- **Tasaki §2.5 Theorem 2.3 sector-embedded predicted-Casimir
preservation under lowering**: if a Marshall-signed sector vector has the
Theorem 2.3 predicted total-Casimir eigenvalue after zero-extension to the
full spin-`S` Hilbert space, then its image under `Ŝ^-_tot` has the same
total-Casimir eigenvalue.

This is the sector-vector form used in the adjacent-sector chain, before the
lowered vector is compared with the target sector's Theorem 2.2
Marshall-positive representative. -/
theorem
    tasaki23_totalSpinSOpMinus_marshallSignedEmbedding_preserves_predictedCasimirValue
    (A : V → Bool) (N : ℕ) {M : ℕ} {v : magConfigS V N M → ℝ}
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) :
    (totalSpinSSquared V N).mulVec
        ((totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
        ((totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  exact
    tasaki23_totalSpinSOpMinus_preserves_predictedCasimirValue
      (V := V) A N hΦ_cas

/-- **Tasaki §2.5 Theorem 2.3 sector-embedded predicted-Casimir
preservation under raising**: if a Marshall-signed sector vector has the
Theorem 2.3 predicted total-Casimir eigenvalue after zero-extension to the
full spin-`S` Hilbert space, then its image under `Ŝ^+_tot` has the same
total-Casimir eigenvalue.

This is the raising-direction companion to
the corresponding lowering theorem above. -/
theorem
    tasaki23_totalSpinSOpPlus_marshallSignedEmbedding_preserves_predictedCasimirValue
    (A : V → Bool) (N : ℕ) {M : ℕ} {v : magConfigS V N M → ℝ}
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) :
    (totalSpinSSquared V N).mulVec
        ((totalSpinSOpPlus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
        ((totalSpinSOpPlus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  exact
    tasaki23_totalSpinSOpPlus_preserves_predictedCasimirValue
      (V := V) A N hΦ_cas

/-- **Tasaki §2.5 Theorem 2.3 predicted-Casimir transfer across a
non-zero real scalar**: if a vector with the predicted total-Casimir
eigenvalue is a non-zero real scalar multiple of another vector, then
the second vector has the same predicted total-Casimir eigenvalue.

This is the cancellation step used after identifying a lowered ladder
image with the adjacent-sector Marshall-positive representative up to a
positive real scalar. -/
theorem tasaki23_totalSpinSSquared_predictedCasimirValue_of_real_smul_eq
    (A : V → Bool) (N : ℕ) {r : ℝ}
    {Ψ Φ : (V → Fin (N + 1)) → ℂ}
    (hr : r ≠ 0)
    (hrel : Ψ = (r : ℂ) • Φ)
    (hΨ_cas :
      (totalSpinSSquared V N).mulVec Ψ =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) • Ψ) :
    (totalSpinSSquared V N).mulVec Φ =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) • Φ := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  rw [hrel, Matrix.mulVec_smul] at hΨ_cas
  funext σ
  have hσ := congrFun hΨ_cas σ
  change (r : ℂ) * ((totalSpinSSquared V N).mulVec Φ) σ =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) *
        ((r : ℂ) * Φ σ) at hσ
  change ((totalSpinSSquared V N).mulVec Φ) σ =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) * Φ σ
  have hσ' :
      (r : ℂ) * ((totalSpinSSquared V N).mulVec Φ) σ =
        (r : ℂ) * ((tasaki23PredictedCasimirValue (V := V) A N : ℂ) * Φ σ) := by
    calc
      (r : ℂ) * ((totalSpinSSquared V N).mulVec Φ) σ =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) *
            ((r : ℂ) * Φ σ) := hσ
      _ = (r : ℂ) * ((tasaki23PredictedCasimirValue (V := V) A N : ℂ) * Φ σ) := by
        ring
  exact mul_left_cancel₀ hrC hσ'

end LatticeSystem.Quantum
