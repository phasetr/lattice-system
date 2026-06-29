import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractivePermutation
import LatticeSystem.Fermion.JordanWigner.HopBasisVec

/-!
# The conjugated single-hop basis action (Tasaki §10.2.1)

Thirteenth layer (PR13) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model).

Using the unitary signed permutation operator `U = permutationOperator π` of PR12,
this file computes the basis action of a **conjugated single hopping term**
`U (ĉ†_p ĉ_q) Uᴴ` on a computational basis state, by chaining the basis actions of
`Uᴴ`, the bare hop, and `U`. The composite Jordan–Wigner / permutation sign is
kept explicit (a `def`); reducing it to an operator equality
`U Ĥ_block Uᴴ = Ĥ_interleaved` needs the JW sign cocycle identities, a later layer.

## Main results

* `permutationOperator_conjTranspose_mulVec_basisVec` — `Uᴴ |σ⟩ = ε(π, σ∘π) |σ∘π⟩`.
* `permutationOperator_hopping_conj_mulVec_basisVec` — the conjugated single-hop
  basis action with the explicit composite sign.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {M : ℕ}

/-- The basis action of the inverse (conjugate transpose) signed permutation
operator: `Uᴴ |σ⟩ = ε(π, σ∘π) |σ∘π⟩`. -/
theorem permutationOperator_conjTranspose_mulVec_basisVec (π : Equiv.Perm (Fin M))
    (σ : Fin M → Fin 2) :
    (permutationOperator π)ᴴ.mulVec (basisVec σ)
      = translationJwSign π (σ ∘ π) • basisVec (σ ∘ π) := by
  funext τ
  have h : (permutationOperator π)ᴴ.mulVec (basisVec σ) τ = (permutationOperator π)ᴴ τ σ :=
    sum_mul_basisVec σ (fun ρ => (permutationOperator π)ᴴ τ ρ)
  rw [h, Matrix.conjTranspose_apply, permutationOperator, Matrix.of_apply, Pi.smul_apply,
    smul_eq_mul, basisVec]
  by_cases hτ : σ = τ ∘ π.symm
  · have hτ' : τ = σ ∘ π := by
      funext x
      simpa [Function.comp_apply, Equiv.symm_apply_apply] using (congrFun hτ (π x)).symm
    rw [if_pos hτ, if_pos hτ', mul_one, translationJwSign_star, hτ']
  · have hτ' : τ ≠ σ ∘ π := by
      intro h; exact hτ (by funext x; rw [h]; simp [Equiv.apply_symm_apply])
    rw [if_neg hτ, star_zero, if_neg hτ', mul_zero]

/-- The explicit composite sign of the conjugated single-hop basis action. -/
noncomputable def permutationHopConjSign (π : Equiv.Perm (Fin (M + 1)))
    (p q : Fin (M + 1)) (σ : Fin (M + 1) → Fin 2) : ℂ :=
  translationJwSign π (σ ∘ π) *
    (jwSign M q (σ ∘ π) * jwSign M p (Function.update (σ ∘ π) q 0)) *
    translationJwSign π (Function.update (Function.update (σ ∘ π) q 0) p 1)

/-- The basis action of a conjugated single hopping term `U (ĉ†_p ĉ_q) Uᴴ`. -/
theorem permutationOperator_hopping_conj_mulVec_basisVec (π : Equiv.Perm (Fin (M + 1)))
    (p q : Fin (M + 1)) (σ : Fin (M + 1) → Fin 2) :
    ((permutationOperator π) *
        (fermionMultiCreation M p * fermionMultiAnnihilation M q) *
        (permutationOperator π)ᴴ).mulVec (basisVec σ)
      = if (σ ∘ π) q = 1 ∧ (Function.update (σ ∘ π) q 0) p = 0 then
          permutationHopConjSign π p q σ •
            basisVec ((Function.update (Function.update (σ ∘ π) q 0) p 1) ∘ π.symm)
        else 0 := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    permutationOperator_conjTranspose_mulVec_basisVec, Matrix.mulVec_smul,
    fermionMultiCreation_mul_Annihilation_mulVec_basisVec]
  by_cases hcond : (σ ∘ π) q = 1 ∧ (Function.update (σ ∘ π) q 0) p = 0
  · rw [if_pos hcond, Matrix.mulVec_smul, Matrix.mulVec_smul,
      permutationOperator_mulVec_basisVec, smul_smul, smul_smul, if_pos hcond,
      permutationHopConjSign]
  · rw [if_neg hcond, smul_zero, Matrix.mulVec_zero, if_neg hcond]

end LatticeSystem.Fermion
