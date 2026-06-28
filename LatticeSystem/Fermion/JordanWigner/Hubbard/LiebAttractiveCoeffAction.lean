import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveReflection
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractive
import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaTheoremCore

/-!
# The on-site interaction acts diagonally on the SRP coefficient matrix (Tasaki §10.2.1)

Second layer (PR2) toward discharging `theorem_10_2_lieb_attractive_unique_singlet`
(Lieb's theorem for the attractive Hubbard model). Building on the spin-reflection
coefficient-matrix language of `LiebAttractiveReflection.lean`, this file proves
that the on-site Hubbard interaction `Σ_x V_x n̂_{x↑} n̂_{x↓}` is **diagonal** in the
SRP coefficient matrix: applying it to a state and re-reading the coefficient
matrix multiplies each entry by the configuration-dependent interaction
eigenvalue. This is the interaction half of the operator-to-matrix translation in
which Lieb's spin-reflection-positivity proof is carried out.

## Main results

* `hubbardConfigInteractionWeight` — the diagonal interaction eigenvalue on a
  computational configuration.
* `hubbardOnSiteInteractionSite_mulVec_basisVec` /
  `hubbardOnSiteInteractionSite_mulVec_apply` — the interaction is diagonal on
  the computational basis, and its pointwise action on a general state.
* `spinReflectionCoeff_hubbardOnSiteInteractionSite` /
  `spinReflectionCoeff_attractiveHubbardInteraction` — the induced entrywise
  (Hadamard) action on the SRP coefficient matrix.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1, pp. 348–349; E. H. Lieb, *Phys. Rev. Lett.*
**62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- The diagonal interaction eigenvalue of `Σ_x V_x n̂_{x↑} n̂_{x↓}` on a
computational configuration `c`: `Σ_x V_x · n_{x↑}(c) · n_{x↓}(c)`. -/
noncomputable def hubbardConfigInteractionWeight (N : ℕ) (V : Fin (N + 1) → ℂ)
    (c : Fin (2 * N + 2) → Fin 2) : ℂ :=
  ∑ x : Fin (N + 1),
    V x * ((c (spinfulIndex N x 0)).val : ℂ) * ((c (spinfulIndex N x 1)).val : ℂ)

/-- The on-site interaction is **diagonal** on the computational basis:
`(Σ_x V_x n̂_{x↑} n̂_{x↓}) |c⟩ = (interaction eigenvalue at c) · |c⟩`. -/
theorem hubbardOnSiteInteractionSite_mulVec_basisVec (N : ℕ) (V : Fin (N + 1) → ℂ)
    (c : Fin (2 * N + 2) → Fin 2) :
    (hubbardOnSiteInteractionSite N V).mulVec (basisVec c)
      = hubbardConfigInteractionWeight N V c • basisVec c := by
  unfold hubbardOnSiteInteractionSite hubbardConfigInteractionWeight
  rw [Matrix.sum_mulVec, Finset.sum_smul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
  unfold fermionUpNumber fermionDownNumber
  rw [fermionMultiNumber_mulVec_basisVec, Matrix.mulVec_smul,
    fermionMultiNumber_mulVec_basisVec, smul_smul, smul_smul]
  congr 1
  ring

/-- The pointwise action of the on-site interaction on a general state:
`((Σ_x V_x n̂_{x↑} n̂_{x↓}) ψ) c' = (interaction eigenvalue at c') · ψ c'`
(diagonality). -/
theorem hubbardOnSiteInteractionSite_mulVec_apply (N : ℕ) (V : Fin (N + 1) → ℂ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) (c' : Fin (2 * N + 2) → Fin 2) :
    (hubbardOnSiteInteractionSite N V).mulVec ψ c'
      = hubbardConfigInteractionWeight N V c' * ψ c' := by
  have hentry : ∀ d, (hubbardOnSiteInteractionSite N V) c' d
      = hubbardConfigInteractionWeight N V d * basisVec d c' := by
    intro d
    have h := congrFun (hubbardOnSiteInteractionSite_mulVec_basisVec N V d) c'
    rw [Pi.smul_apply, smul_eq_mul] at h
    rw [← h]
    simp only [Matrix.mulVec, dotProduct]
    exact (sum_mul_basisVec d (fun k => (hubbardOnSiteInteractionSite N V) c' k)).symm
  simp only [Matrix.mulVec, dotProduct]
  calc ∑ d, (hubbardOnSiteInteractionSite N V) c' d * ψ d
      = ∑ d, hubbardConfigInteractionWeight N V d * basisVec d c' * ψ d := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [hentry d]
    _ = hubbardConfigInteractionWeight N V c' * ψ c' := by
        rw [Fintype.sum_eq_single c']
        · rw [basisVec_self, mul_one]
        · intro d hd
          rw [basisVec_of_ne (Ne.symm hd), mul_zero, zero_mul]

/-- The diagonal weight by which the on-site interaction acts on the SRP
coefficient matrix at entry `(u, h)`: the interaction eigenvalue on the
configuration `merge u (particle-hole h)`, namely
`Σ_x V_x · u_x · (1 − h_x)`. -/
noncomputable def hubbardOnSiteInteractionSiteReflectionCoeffWeight (N : ℕ)
    (V : Fin (N + 1) → ℂ) (u h : hubbardSpinConfig N) : ℂ :=
  ∑ x : Fin (N + 1),
    V x * ((u x).val : ℂ) * (((particleHoleConfig N h) x).val : ℂ)

/-- The induced entrywise (Hadamard) action of the on-site interaction on the SRP
coefficient matrix: `(action C) u h = weight_{u,h} · C u h`. -/
noncomputable def hubbardOnSiteInteractionSiteReflectionCoeffAction (N : ℕ)
    (V : Fin (N + 1) → ℂ)
    (C : Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ) :
    Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ :=
  fun u h => hubbardOnSiteInteractionSiteReflectionCoeffWeight N V u h * C u h

/-- **The on-site interaction acts diagonally (entrywise) on the SRP coefficient
matrix.** -/
theorem spinReflectionCoeff_hubbardOnSiteInteractionSite (N : ℕ)
    (V : Fin (N + 1) → ℂ) (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    spinReflectionCoeff N ((hubbardOnSiteInteractionSite N V).mulVec ψ)
      = hubbardOnSiteInteractionSiteReflectionCoeffAction N V
          (spinReflectionCoeff N ψ) := by
  funext u h
  simp only [spinReflectionCoeff, hubbardOnSiteInteractionSiteReflectionCoeffAction]
  rw [hubbardOnSiteInteractionSite_mulVec_apply]
  congr 1
  unfold hubbardOnSiteInteractionSiteReflectionCoeffWeight hubbardConfigInteractionWeight
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hubbardMergeConfig_spinfulIndex_zero, hubbardMergeConfig_spinfulIndex_one]

/-- The attractive specialization `V_x = −U_x` of the coefficient-matrix action. -/
noncomputable def attractiveHubbardInteractionReflectionCoeffAction (N : ℕ)
    (U : Fin (N + 1) → ℝ)
    (C : Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ) :
    Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ :=
  hubbardOnSiteInteractionSiteReflectionCoeffAction N (fun x => -(U x : ℂ)) C

/-- **The attractive on-site interaction acts diagonally on the SRP coefficient
matrix.** -/
theorem spinReflectionCoeff_attractiveHubbardInteraction (N : ℕ)
    (U : Fin (N + 1) → ℝ) (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    spinReflectionCoeff N ((attractiveHubbardInteraction N U).mulVec ψ)
      = attractiveHubbardInteractionReflectionCoeffAction N U
          (spinReflectionCoeff N ψ) := by
  unfold attractiveHubbardInteraction attractiveHubbardInteractionReflectionCoeffAction
  exact spinReflectionCoeff_hubbardOnSiteInteractionSite N (fun x => -(U x : ℂ)) ψ

end LatticeSystem.Fermion
