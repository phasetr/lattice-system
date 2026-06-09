import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandModeMonomial
import LatticeSystem.Fermion.JordanWigner.Hubbard.NonsingularAllUpAnnihilation

/-!
# Tasaki §11.3.1: mode-creation anticommutation and reordering

The mode creations all anticommute: `{Ĉ†_σ(w), Ĉ†_τ(w')} = 0` (from the spinful site
creation–creation anticommutation by bilinearity).  This is the algebraic input for reordering a
rotated Fock monomial into a canonical (sorted) order — used to turn the list-indexed spanning
family `flatBandModeMonomial` into an occupation-config-indexed basis.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1.  Tracked in Issue #4346.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {K : ℕ} {ν : ℝ}

/-- **Generic mode creation–creation anticommutation** `{Ĉ†_σ(w), Ĉ†_τ(w')} = 0`.  The bilinear
double sum of the spinful site anticommutations `{ĉ†_{x,σ}, ĉ†_{y,τ}} = 0` (all zero) vanishes
termwise.  Specialises to `{â†,â†}`, `{b̂†,b̂†}`, `{â†,b̂†}` all `= 0`. -/
theorem flatBandMode_creation_creation_anticomm (K : ℕ) (σ τ : Fin 2)
    (w w' : Fin (2 * K + 2) → ℂ) :
    flatBandModeCreation K σ w * flatBandModeCreation K τ w'
      + flatBandModeCreation K τ w' * flatBandModeCreation K σ w = 0 := by
  have hkey : flatBandModeCreation K σ w * flatBandModeCreation K τ w'
      + flatBandModeCreation K τ w' * flatBandModeCreation K σ w
      = ∑ x, ∑ y, (w x * w' y) •
          (fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ) *
              fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) y τ)
            + fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) y τ) *
              fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ)) := by
    simp only [flatBandModeCreation, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm _ (w' y), smul_mul_assoc,
      mul_smul_comm, smul_smul, mul_comm (w' y), ← smul_add]
  rw [hkey]
  refine Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero (fun y _ => ?_))
  rw [spinful_creation_creation_anticomm, smul_zero]

/-- Swapping the first two factors of a rotated Fock monomial negates it (the two leading creations
anticommute). -/
theorem flatBandModeMonomial_swap (x y : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2)
    (l : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2)) :
    flatBandModeMonomial K ν (y :: x :: l) = -flatBandModeMonomial K ν (x :: y :: l) := by
  unfold flatBandModeMonomial
  simp only [List.map_cons, List.prod_cons]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
    eq_neg_of_add_eq_zero_left
      (flatBandMode_creation_creation_anticomm K y.2 x.2 (flatBandBasis K ν y.1)
        (flatBandBasis K ν x.1)),
    Matrix.neg_mul, Matrix.neg_mulVec]

/-- **Reordering a rotated Fock monomial scales it.**  Permuting the creation list multiplies the
monomial by a (sign) scalar `z` — enough for the spanning/basis argument, where the explicit sign is
irrelevant.  Proved by induction on the permutation: `cons` keeps `z`, `swap` flips the sign,
`trans` multiplies. -/
theorem flatBandModeMonomial_perm {l l' : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2)}
    (h : l.Perm l') :
    ∃ z : ℂ, z ≠ 0 ∧ flatBandModeMonomial K ν l = z • flatBandModeMonomial K ν l' := by
  induction h with
  | nil => exact ⟨1, one_ne_zero, by rw [one_smul]⟩
  | cons x _ ih =>
    obtain ⟨z, hz0, hz⟩ := ih
    refine ⟨z, hz0, ?_⟩
    rw [← flatBandModeCreation_mulVec_monomial x.1 x.2, hz, Matrix.mulVec_smul,
      flatBandModeCreation_mulVec_monomial x.1 x.2]
  | swap x y l => exact ⟨-1, neg_ne_zero.mpr one_ne_zero, by rw [flatBandModeMonomial_swap,
      neg_one_smul]⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨z₁, hz₁0, hz₁⟩ := ih₁
    obtain ⟨z₂, hz₂0, hz₂⟩ := ih₂
    exact ⟨z₁ * z₂, mul_ne_zero hz₁0 hz₂0, by rw [hz₁, hz₂, smul_smul]⟩

/-- The square of a mode creation vanishes (`(Ĉ†)² = 0`). -/
theorem flatBandModeCreation_sq (i : Fin (K + 1) ⊕ Fin (K + 1)) (σ : Fin 2) :
    flatBandModeCreation K σ (flatBandBasis K ν i) *
      flatBandModeCreation K σ (flatBandBasis K ν i) = 0 := by
  have h2 := flatBandMode_creation_creation_anticomm K σ σ (flatBandBasis K ν i)
    (flatBandBasis K ν i)
  rw [← two_smul ℂ] at h2
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-- **Prepending an already-present mode to a monomial kills it.**  Splitting `l = s ++ q :: t`,
`q :: l` is a permutation of `q :: q :: (s ++ t)`, whose leading `(Ĉ†_q)² = 0`. -/
theorem flatBandModeMonomial_cons_mem_eq_zero
    (q : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2)
    (l : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2)) (hq : q ∈ l) :
    flatBandModeMonomial K ν (q :: l) = 0 := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hq
  obtain ⟨z, _, hz⟩ := flatBandModeMonomial_perm (K := K) (ν := ν)
    (List.perm_middle.cons q)
  rw [hz]
  have : flatBandModeMonomial K ν (q :: q :: (s ++ t)) = 0 := by
    unfold flatBandModeMonomial
    simp only [List.map_cons, List.prod_cons]
    rw [← Matrix.mul_assoc, flatBandModeCreation_sq, Matrix.zero_mul, Matrix.zero_mulVec]
  rw [this, smul_zero]

end LatticeSystem.Fermion
