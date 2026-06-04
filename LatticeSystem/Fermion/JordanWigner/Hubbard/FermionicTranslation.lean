import LatticeSystem.Fermion.JordanWigner.Hubbard.TranslationOperator

/-!
# Tasaki §11.4.2: the fermionic translation operator `τ̂_z` (eq. (11.4.30))

Building on the site-translation permutation (`siteTranslationPerm`), this file defines the
**fermionic translation operator** `τ̂_z` of eq. (11.4.30): the second-quantized lift of the
site shift to the Jordan–Wigner Fock space.

On the occupation basis `|σ⟩` the operator acts as a *signed* permutation,
`τ̂_z |σ⟩ = ε(π,σ) · |σ ∘ π⁻¹⟩`  (`π = siteTranslationPerm`),
where the Jordan–Wigner sign `ε(π,σ)` is the parity of the **occupied inversions** of `π`:
the number of pairs of occupied modes whose order is reversed by `π`,
`ε(π,σ) = (-1)^{#{(i,j) : i<j, σ_i=σ_j=1, π(j)<π(i)}}`.
This is the standard sign incurred when the shifted creation operators
`∏ ĉ†_{π(x_i)}` are reordered back to canonical mode order.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.4.2, eq. (11.4.30) (p. 423).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

variable {M : ℕ}

/-- **The Jordan–Wigner sign of a second-quantized permutation** `π` on a configuration
`σ`: `(-1)` to the number of *occupied inversions* of `π` (pairs of occupied modes whose
order `π` reverses).  This is the fermion sign incurred by reordering the shifted creation
operators to canonical mode order. -/
def translationJwSign (π : Equiv.Perm (Fin M)) (σ : Fin M → Fin 2) : ℂ :=
  (-1) ^ (Finset.univ.filter
    (fun p : Fin M × Fin M => p.1 < p.2 ∧ σ p.1 = 1 ∧ σ p.2 = 1 ∧ π p.2 < π p.1)).card

/-- The Jordan–Wigner sign is `±1`. -/
theorem translationJwSign_sq (π : Equiv.Perm (Fin M)) (σ : Fin M → Fin 2) :
    translationJwSign π σ * translationJwSign π σ = 1 := by
  unfold translationJwSign
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

/-- **The fermionic translation operator** `τ̂_z` (Tasaki eq. (11.4.30)): the second-quantized
lift of the `z`-cell site translation, acting on the occupation basis as the signed
permutation `|σ⟩ ↦ ε(π,σ) |σ ∘ π⁻¹⟩` with `π = siteTranslationPerm K z`. -/
noncomputable def translationOperator (K : ℕ) (z : Fin (K + 1)) :
    ManyBodyOp (Fin (2 * (2 * K + 1) + 2)) :=
  Matrix.of fun τ σ =>
    if τ = σ ∘ (siteTranslationPerm K z).symm then
      translationJwSign (siteTranslationPerm K z) σ
    else 0

/-- **The defining action of `τ̂_z` on basis states** (eq. (11.4.30)):
`τ̂_z |σ⟩ = ε(π,σ) · |σ ∘ π⁻¹⟩`. -/
theorem translationOperator_mulVec_basisVec (K : ℕ) (z : Fin (K + 1))
    (σ : Fin (2 * (2 * K + 1) + 2) → Fin 2) :
    (translationOperator K z).mulVec (basisVec σ)
      = translationJwSign (siteTranslationPerm K z) σ •
          basisVec (σ ∘ (siteTranslationPerm K z).symm) := by
  funext τ
  have h : (translationOperator K z).mulVec (basisVec σ) τ = translationOperator K z τ σ :=
    sum_mul_basisVec σ (fun ρ => translationOperator K z τ ρ)
  rw [h, translationOperator, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, basisVec]
  split_ifs with hτ <;> simp

/-- Translation by `z = 0` cells is the identity operator. -/
theorem translationOperator_zero (K : ℕ) :
    translationOperator K 0 = 1 := by
  ext τ σ
  have hsign : translationJwSign (Equiv.refl (Fin (2 * (2 * K + 1) + 2))) σ = 1 := by
    unfold translationJwSign
    rw [Finset.filter_false_of_mem, Finset.card_empty, pow_zero]
    rintro p _ ⟨hlt, -, -, hgt⟩
    exact absurd (hlt.trans hgt) (lt_irrefl _)
  rw [translationOperator, Matrix.of_apply, siteTranslationPerm_zero, Equiv.refl_symm,
    Equiv.coe_refl, Function.comp_id, hsign, Matrix.one_apply]

end LatticeSystem.Fermion
