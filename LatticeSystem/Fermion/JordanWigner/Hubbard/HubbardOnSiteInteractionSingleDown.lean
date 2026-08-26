import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveCoeffAction
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBalancedSectorGround

/-!
# The on-site interaction on the one-↓-electron sector (Tasaki §11.1.1)

The Roth trial state of the low-density impossibility argument is `Ψ̃ = P̂₀Ψ = (1 − ν̂)Ψ`, where
`ν̂ = Σ_x n̂_{x↑}n̂_{x↓}` counts doubly occupied sites and `Ψ` carries a single ↓ electron.  This
file supplies the operator content of that projection on the sector `N̂_↓Ψ = Ψ`, stated for an
arbitrary vector of the sector rather than for the trial state itself:

* `ν̂` is idempotent there, because a configuration with one ↓ electron has at most one doubly
  occupied site;
* the doubly occupied part `ν̂Ψ` stays inside the sector;
* the interaction annihilates `(1 − ν̂)Ψ` **for every coupling** `U`, which is the source of the
  `U`-independence of the variational bound;
* the norm of `(1 − ν̂)Ψ` is `‖Ψ‖² − ⟨Ψ, ν̂Ψ⟩`, the normalisation that turns the trial energy into
  a Rayleigh quotient.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §11.1.1, Theorem 11.4, eqs. (11.1.9)/(11.1.10), p. 376; the computation is Tasaki,
Prog. Theor. Phys. **99** (1998) 489, Theorem 3.3, Appendix F, p. 545, eqs. (F.1)/(F.2).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

open scoped BigOperators

/-- **The double-occupancy operator is idempotent on the one-↓-electron sector**: if
`N̂_↓v = v` then `ν̂(ν̂v) = ν̂v`, where `ν̂ = Σ_x n̂_{x↑}n̂_{x↓}` is `hubbardOnSiteInteraction M 1`,
the operator of eq. (F.1) in Tasaki, Prog. Theor. Phys. **99** (1998) 489, Appendix F, p. 545.
`ν̂` is diagonal with eigenvalue the number of doubly occupied sites, and a configuration with a
single ↓ electron has at most one such site, so that eigenvalue is `0` or `1`. -/
theorem hubbardOnSiteInteraction_mulVec_mulVec_of_downNumber_one (M : ℕ)
    {v : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hv : (fermionTotalDownNumber M).mulVec v = v) :
    (hubbardOnSiteInteraction M 1).mulVec ((hubbardOnSiteInteraction M 1).mulVec v)
      = (hubbardOnSiteInteraction M 1).mulVec v := by
  have hnu : ∀ (w : (Fin (2 * M + 2) → Fin 2) → ℂ) (c : Fin (2 * M + 2) → Fin 2),
      (hubbardOnSiteInteraction M 1).mulVec w c
        = ((∑ x : Fin (M + 1),
            (c (spinfulIndex M x 0)).val * (c (spinfulIndex M x 1)).val : ℕ) : ℂ) * w c := by
    intro w c
    rw [show hubbardOnSiteInteraction M 1 = hubbardOnSiteInteractionSite M (fun _ => 1) from rfl,
      hubbardOnSiteInteractionSite_mulVec_apply]
    congr 1
    simp only [hubbardConfigInteractionWeight, Nat.cast_sum, Nat.cast_mul, one_mul]
  funext c
  rw [hnu, hnu, ← mul_assoc]
  by_cases hc : (∑ x : Fin (M + 1), ((c (spinfulIndex M x 1)).val : ℂ)) = 1
  · have hcNat : (∑ x : Fin (M + 1), (c (spinfulIndex M x 1)).val) = 1 := by exact_mod_cast hc
    have hle : (∑ x : Fin (M + 1),
        (c (spinfulIndex M x 0)).val * (c (spinfulIndex M x 1)).val) ≤ 1 := by
      refine le_trans (Finset.sum_le_sum fun x _ => ?_) hcNat.le
      calc (c (spinfulIndex M x 0)).val * (c (spinfulIndex M x 1)).val
          ≤ 1 * (c (spinfulIndex M x 1)).val :=
            Nat.mul_le_mul (Fin.is_le (c (spinfulIndex M x 0))) (le_refl _)
        _ = (c (spinfulIndex M x 1)).val := one_mul _
    have hsq : (∑ x : Fin (M + 1),
          (c (spinfulIndex M x 0)).val * (c (spinfulIndex M x 1)).val)
        * (∑ x : Fin (M + 1),
          (c (spinfulIndex M x 0)).val * (c (spinfulIndex M x 1)).val)
        = ∑ x : Fin (M + 1),
          (c (spinfulIndex M x 0)).val * (c (spinfulIndex M x 1)).val := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h | h <;> rw [h]
    rw [← Nat.cast_mul, hsq]
  · have hvc : v c = 0 :=
      mulVec_apply_eq_zero_of_downNumber_ne v 1 (by rw [hv, one_smul]) c hc
    rw [hvc, mul_zero, mul_zero]

/-- **The doubly occupied part stays in the one-↓-electron sector**: if `N̂_↓v = v` then
`N̂_↓(ν̂v) = ν̂v`.  Both operators are diagonal, and on every configuration in the support of `v`
the ↓-count is `1`; off the support the `ν̂` entry already carries the vanishing factor `v c`. -/
theorem fermionTotalDownNumber_mulVec_hubbardOnSiteInteraction_mulVec_of_downNumber_one (M : ℕ)
    {v : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hv : (fermionTotalDownNumber M).mulVec v = v) :
    (fermionTotalDownNumber M).mulVec ((hubbardOnSiteInteraction M 1).mulVec v)
      = (hubbardOnSiteInteraction M 1).mulVec v := by
  funext c
  rw [fermionTotalDownNumber_mulVec_apply]
  by_cases hc : (∑ x : Fin (M + 1), ((c (spinfulIndex M x 1)).val : ℂ)) = 1
  · rw [hc, one_mul]
  · have hvc : v c = 0 :=
      mulVec_apply_eq_zero_of_downNumber_ne v 1 (by rw [hv, one_smul]) c hc
    rw [show hubbardOnSiteInteraction M 1 = hubbardOnSiteInteractionSite M (fun _ => 1) from rfl,
      hubbardOnSiteInteractionSite_mulVec_apply, hvc, mul_zero, mul_zero]

/-- **The Roth-projected vector minimizes the Coulomb interaction, at every coupling**: if
`N̂_↓v = v` then `Ĥ_int(U)(v − ν̂v) = 0` for every `U`.  This is eq. (F.1) of Tasaki,
Prog. Theor. Phys. **99** (1998) 489, Appendix F, p. 545, in the form used by the book
(eq. (11.1.9), p. 376): `Ĥ_int(U) = U ν̂`, so the statement is the idempotency of `ν̂` scaled by
`U`, and the interaction energy of `(1 − ν̂)v` vanishes independently of `U`. -/
theorem hubbardOnSiteInteraction_mulVec_sub_self_eq_zero_of_downNumber_one (M : ℕ) (U : ℂ)
    {v : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hv : (fermionTotalDownNumber M).mulVec v = v) :
    (hubbardOnSiteInteraction M U).mulVec (v - (hubbardOnSiteInteraction M 1).mulVec v) = 0 := by
  have hsmul : hubbardOnSiteInteraction M U = U • hubbardOnSiteInteraction M 1 := by
    unfold hubbardOnSiteInteraction
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_one]
  rw [hsmul, Matrix.smul_mulVec, Matrix.mulVec_sub,
    hubbardOnSiteInteraction_mulVec_mulVec_of_downNumber_one M hv, sub_self, smul_zero]

/-- **The norm of the Roth-projected vector**: if `N̂_↓v = v` then
`‖v − ν̂v‖² = ‖v‖² − ⟨v, ν̂v⟩` on real parts, which is eq. (F.2) of Tasaki,
Prog. Theor. Phys. **99** (1998) 489, Appendix F, p. 545 (`⟨Ψ̃,Ψ̃⟩ = ⟨Ψ,P̂₀Ψ⟩ = 1 − ⟨Ψ,ν̂Ψ⟩` for a
normalized `Ψ`).  The cross terms collapse because `ν̂` is Hermitian and idempotent on the sector;
real parts are taken because that is the shape the Rayleigh quotient consumes. -/
theorem dotProduct_star_self_sub_hubbardOnSiteInteraction_re_of_downNumber_one (M : ℕ)
    {v : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hv : (fermionTotalDownNumber M).mulVec v = v) :
    (dotProduct (star (v - (hubbardOnSiteInteraction M 1).mulVec v))
        (v - (hubbardOnSiteInteraction M 1).mulVec v)).re
      = (dotProduct (star v) v).re
        - (dotProduct (star v) ((hubbardOnSiteInteraction M 1).mulVec v)).re := by
  have hherm : (hubbardOnSiteInteraction M 1)ᴴ = hubbardOnSiteInteraction M 1 :=
    (hubbardOnSiteInteraction_isHermitian M (by simp)).eq
  have hmove : ∀ w : (Fin (2 * M + 2) → Fin 2) → ℂ,
      dotProduct (star ((hubbardOnSiteInteraction M 1).mulVec v)) w
        = dotProduct (star v) ((hubbardOnSiteInteraction M 1).mulVec w) := by
    intro w
    rw [Matrix.star_mulVec, hherm]
    exact (Matrix.dotProduct_mulVec _ _ _).symm
  have hexpand : dotProduct (star (v - (hubbardOnSiteInteraction M 1).mulVec v))
        (v - (hubbardOnSiteInteraction M 1).mulVec v)
      = dotProduct (star v) v
        - dotProduct (star v) ((hubbardOnSiteInteraction M 1).mulVec v) := by
    rw [star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hmove v,
      hmove ((hubbardOnSiteInteraction M 1).mulVec v),
      hubbardOnSiteInteraction_mulVec_mulVec_of_downNumber_one M hv]
    ring
  rw [hexpand, Complex.sub_re]

end LatticeSystem.Fermion
