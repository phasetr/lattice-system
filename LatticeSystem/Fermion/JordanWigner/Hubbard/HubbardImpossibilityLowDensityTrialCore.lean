import LatticeSystem.Fermion.JordanWigner.CreationNumberIdentities
import LatticeSystem.Fermion.JordanWigner.HoppingCommuteLadder
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardKineticSpinBounds

/-!
# Parity core of the spin-flip trial state (Tasaki §11.1.1)

The algebraic layer under the trial state `Ψ = Ĉ†_↓(v)Φ↑` of the low-density impossibility
argument, stated for an arbitrary fully polarized state `Φ` (`N̂_↓Φ = 0`) rather than for a
particular Slater determinant:

* an up-spin hopping bilinear commutes with the down-spin ladder operators, the spinful reading
  of the generic even-operator commutation of `HoppingCommuteLadder.lean`;
* the **one-↓ contraction** `n̂_{x↓}Ĉ†_↓(v)Φ = v_x ĉ†_{x↓}Φ`: with no down electron present, the
  down occupation at `x` selects exactly the `x` term of the smeared creator;
* the **δ factorisation** `⟨ĉ†_{y↓}Φ, X ĉ†_{x↓}Φ'⟩ = δ_{xy}⟨Φ, XΦ'⟩` for any `X` commuting with
  the down annihilations — the parity bookkeeping of Tasaki's computation, which needs no
  Jordan–Wigner string because the anticommutator remainders are killed by `ĉ_{y↓}Φ' = 0`;
* the norm `⟨Ĉ†_↓(v)Φ, Ĉ†_↓(v)Φ⟩ = (Σ_x |v_x|²)⟨Φ,Φ⟩`, the δ factorisation at `X = 1`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §11.1.1, Theorem 11.4, eqs. (11.1.6)/(11.1.9), pp. 375–376; the computation is the
unnumbered anticommutation bookkeeping of Tasaki, Prog. Theor. Phys. **99** (1998) 489,
Theorem 3.3, Appendix F — the substitution of eqs. (F.5)/(F.7) that yields eqs. (F.8)–(F.11),
pp. 545–546.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

open scoped BigOperators

variable {M : ℕ}

/-! ## Up hopping versus the down ladder -/

/-- **An up-spin hopping bilinear commutes with a down-spin creation**:
`Commute (ĉ†_{i↑}ĉ_{j↑}) ĉ†_{x↓}`.  The up and down channels sit at distinct Jordan–Wigner
modes, and the bilinear is even. -/
theorem upHopping_commute_fermionDownCreation (M : ℕ) (i j x : Fin (M + 1)) :
    Commute (fermionMultiCreation (2 * M + 1) (spinfulIndex M i 0) *
        fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j 0))
      (fermionDownCreation M x) :=
  fermionMultiHopping_commute_fermionMultiCreation_of_ne
    (spinfulIndex_up_ne_down M i x) (spinfulIndex_up_ne_down M j x)

/-- **An up-spin hopping bilinear commutes with a down-spin annihilation**:
`Commute (ĉ†_{i↑}ĉ_{j↑}) ĉ_{x↓}`.  This is the hypothesis shape consumed by the δ
factorisation below. -/
theorem upHopping_commute_fermionDownAnnihilation (M : ℕ) (i j x : Fin (M + 1)) :
    Commute (fermionMultiCreation (2 * M + 1) (spinfulIndex M i 0) *
        fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j 0))
      (fermionDownAnnihilation M x) :=
  fermionMultiHopping_commute_fermionMultiAnnihilation_of_ne
    (spinfulIndex_up_ne_down M i x) (spinfulIndex_up_ne_down M j x)

/-! ## The one-↓ contraction -/

/-- **The down occupation contracts the smeared down creator on the fully polarized sector**:
if `N̂_↓Φ = 0` then `n̂_{x↓}Ĉ†_↓(v)Φ = v_x ĉ†_{x↓}Φ`.  Only the `x` term of `Ĉ†_↓(v)` survives:
its own occupation is produced by `n̂_{x↓}ĉ†_{x↓} = ĉ†_{x↓}`, while every other term commutes
past `n̂_{x↓}`, which then annihilates `Φ`.  No parity sign appears. -/
theorem fermionDownNumber_mulVec_spinfulCreationFromVector_of_downNumber_zero
    (v : Fin (M + 1) → ℂ) (x : Fin (M + 1))
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : (fermionTotalDownNumber M).mulVec Φ = 0) :
    (fermionDownNumber M x).mulVec ((spinfulCreationFromVector M v 1).mulVec Φ)
      = v x • (fermionDownCreation M x).mulVec Φ := by
  have hnum : ∀ z : Fin (M + 1), (fermionDownNumber M z).mulVec Φ = 0 := by
    intro z
    rw [show fermionDownNumber M z
        = fermionDownCreation M z * fermionDownAnnihilation M z from rfl,
      ← Matrix.mulVec_mulVec, fermionDownAnnihilation_mulVec_eq_zero_of_downNumber_zero M z hΦ,
      Matrix.mulVec_zero]
  rw [Matrix.mulVec_mulVec, spinfulCreationFromVector, Finset.mul_sum, Matrix.sum_mulVec]
  rw [Finset.sum_eq_single x]
  · rw [mul_smul_comm, Matrix.smul_mulVec]
    congr 1
    rw [show fermionDownNumber M x * fermionMultiCreation (2 * M + 1) (spinfulIndex M x 1)
        = fermionDownCreation M x from
      fermionMultiNumber_mul_fermionMultiCreation_eq_fermionMultiCreation _ _]
  · intro y _ hyx
    have hne : spinfulIndex M x 1 ≠ spinfulIndex M y 1 := by
      intro h
      exact hyx (((spinfulIndex_eq_iff M x y 1 1).mp h).1).symm
    rw [mul_smul_comm, Matrix.smul_mulVec,
      show fermionDownNumber M x * fermionMultiCreation (2 * M + 1) (spinfulIndex M y 1)
        = fermionDownCreation M y * fermionDownNumber M x from
        (fermionMultiNumber_commute_fermionMultiCreation_of_ne hne).eq,
      ← Matrix.mulVec_mulVec, hnum x, Matrix.mulVec_zero, smul_zero]
  · intro hx
    exact absurd (Finset.mem_univ x) hx

/-! ## The δ factorisation -/

/-- **Parity factorisation of a matrix element between one-↓ states**: for `X` commuting with
every down annihilation and a fully polarized `Φ'` (`N̂_↓Φ' = 0`),
`⟨ĉ†_{y↓}Φ, X ĉ†_{x↓}Φ'⟩ = δ_{xy}⟨Φ, XΦ'⟩`.  Moving `ĉ†_{y↓}` across the inner product turns it
into `ĉ_{y↓}`, which passes through `X` and then meets `ĉ†_{x↓}` in the canonical
anticommutator; both remainder terms end in `ĉ_{y↓}Φ' = 0`.  The complex-valued (not real-part)
form is what the double sum over the trial vector's coefficients consumes. -/
theorem dotProduct_fermionDownCreation_sandwich (X : ManyBodyOp (Fin (2 * M + 2)))
    (hX : ∀ z : Fin (M + 1), Commute X (fermionDownAnnihilation M z))
    {Φ Φ' : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hΦ' : (fermionTotalDownNumber M).mulVec Φ' = 0) (x y : Fin (M + 1)) :
    star ((fermionDownCreation M y).mulVec Φ) ⬝ᵥ X.mulVec ((fermionDownCreation M x).mulVec Φ')
      = (if x = y then (1 : ℂ) else 0) * (star Φ ⬝ᵥ X.mulVec Φ') := by
  have hann : (fermionDownAnnihilation M y).mulVec Φ' = 0 :=
    fermionDownAnnihilation_mulVec_eq_zero_of_downNumber_zero M y hΦ'
  have hkey : (fermionDownAnnihilation M y).mulVec ((fermionDownCreation M x).mulVec Φ')
      = (if x = y then (1 : ℂ) else 0) • Φ' := by
    rw [Matrix.mulVec_mulVec]
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl, one_smul,
        show fermionDownAnnihilation M x * fermionDownCreation M x
          = 1 - fermionDownNumber M x from
          fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number _ _,
        Matrix.sub_mulVec, Matrix.one_mulVec,
        show fermionDownNumber M x = fermionDownCreation M x * fermionDownAnnihilation M x
          from rfl,
        ← Matrix.mulVec_mulVec, hann, Matrix.mulVec_zero, sub_zero]
    · have hne : spinfulIndex M y 1 ≠ spinfulIndex M x 1 := by
        intro h
        exact hxy (((spinfulIndex_eq_iff M y x 1 1).mp h).1).symm
      rw [if_neg hxy, zero_smul,
        show fermionDownAnnihilation M y * fermionDownCreation M x
          = -(fermionDownCreation M x * fermionDownAnnihilation M y) from
          eq_neg_of_add_eq_zero_left
            (fermionMultiAnnihilation_creation_anticomm_of_ne hne),
        Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, hann, Matrix.mulVec_zero, neg_zero]
  have hadj : (fermionDownCreation M y)ᴴ = fermionDownAnnihilation M y :=
    fermionMultiCreation_conjTranspose _ _
  rw [star_mulVec_dotProduct, hadj,
    Matrix.mulVec_mulVec, ← (hX y).eq, ← Matrix.mulVec_mulVec, hkey,
    Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/-! ## The norm of the trial vector -/

/-- **Norm of a smeared down creation on the fully polarized sector**: if `N̂_↓Φ = 0` then
`⟨Ĉ†_↓(v)Φ, Ĉ†_↓(v)Φ⟩ = (Σ_x conj(v_x)v_x)⟨Φ,Φ⟩`.  The double sum over the coefficient vector
collapses by the δ factorisation at `X = 1`. -/
theorem dotProduct_star_self_spinfulCreationFromVector_of_downNumber_zero
    (v : Fin (M + 1) → ℂ) {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hΦ : (fermionTotalDownNumber M).mulVec Φ = 0) :
    star ((spinfulCreationFromVector M v 1).mulVec Φ) ⬝ᵥ
        (spinfulCreationFromVector M v 1).mulVec Φ
      = (∑ x : Fin (M + 1), star (v x) * v x) * (star Φ ⬝ᵥ Φ) := by
  have hB : ∀ x y : Fin (M + 1),
      star ((fermionDownCreation M y).mulVec Φ) ⬝ᵥ (fermionDownCreation M x).mulVec Φ
        = (if x = y then (1 : ℂ) else 0) * (star Φ ⬝ᵥ Φ) := by
    intro x y
    have h := dotProduct_fermionDownCreation_sandwich (M := M) (Φ := Φ) (Φ' := Φ) 1
      (fun z => Commute.one_left _) hΦ x y
    rwa [Matrix.one_mulVec, Matrix.one_mulVec] at h
  have hexp : (spinfulCreationFromVector M v 1).mulVec Φ
      = ∑ x : Fin (M + 1), v x • (fermionDownCreation M x).mulVec Φ := by
    rw [spinfulCreationFromVector, Matrix.sum_mulVec]
    exact Finset.sum_congr rfl fun x _ => Matrix.smul_mulVec _ _ _
  rw [hexp, star_sum, sum_dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [dotProduct_sum, Finset.sum_eq_single y]
  · rw [star_smul, smul_dotProduct, dotProduct_smul, hB y y, if_pos rfl, one_mul,
      smul_eq_mul, smul_eq_mul, ← mul_assoc]
  · intro x _ hxy
    rw [star_smul, smul_dotProduct, dotProduct_smul, hB x y, if_neg hxy, zero_mul,
      smul_zero, smul_zero]
  · intro hy
    exact absurd (Finset.mem_univ y) hy

end LatticeSystem.Fermion
