import LatticeSystem.Quantum.MarshallLiebMattis.SublatticeCasimirNeelExpectations

/-!
# Spin-`1/2` `(Ŝ_tot)²` Casimir on arbitrary `basisVec σ`
(γ-4 step 216 onwards)

Extracted from `SublatticeCasimirNeel.lean` (build-speed refactor).
This file contains the **γ-4 step 216+** material — generalising
the constant-state Casimir formula (step 201) to arbitrary
`σ : Λ → Fin 2`, and the spin-`1/2` mirrors of the spin-`S`
sublattice-swap-invariance theorems.

Theorems:
- `basisVec_totalSpinHalfSquared_expectation_general` (step 216)
- `basisVec_totalSpinHalfOp12_sq_expectation_general` (step 219)
- `neelStateOf_totalSpinHalfSquared_expectation_via_general` (step 227)
- `basisVec_const_totalSpinHalfSquared_expectation_via_general` (step 228)
- `magnetization_neelConfigOf_complement_eq_neg` (step 232)
- `neelStateOf_totalSpinHalfSquared_complement_eq` (step 233)
- `neelStateOf_totalSpinHalfOp3_sq_complement_eq` (step 236)
- `neelStateOf_totalSpinHalfOp12_sq_complement_eq` (step 238)
- `neelStateOf_totalSpinHalfOp3_complement_eq_neg` (step 240)
- `neelStateOf_totalSpinHalfOp1_expectation` / `_Op2_` (step 242)
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- Helper: `(spinSign s)² = 1` for any `s : Fin 2`. -/
private theorem spinSign_sq (s : Fin 2) :
    (spinSign s : ℂ) * (spinSign s : ℂ) = 1 := by
  fin_cases s <;> simp [spinSign]

/-- Unified diagonal of `spinHalfDot x y` at `(σ, σ)`:
`(spinHalfDot x y) σ σ = (spinSign(σx))(spinSign(σy))/4 + (1/2)·[x=y]`.
Encodes the three cases (`x=y`, parallel `x≠y`, antiparallel `x≠y`) in
one closed form using the fact that `(spinSign s)² = 1` (γ-4 step 216). -/
private theorem spinHalfDot_apply_diag_unified
    (x y : Λ) (σ : Λ → Fin 2) :
    (spinHalfDot x y : ManyBodyOp Λ) σ σ =
      (spinSign (σ x) : ℂ) * (spinSign (σ y) : ℂ) / 4 +
        (if x = y then (1 / 2 : ℂ) else 0) := by
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, spinHalfDot_self]
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      spinSign_sq]
    ring
  · rw [if_neg hxy, add_zero]
    by_cases hpar : σ x = σ y
    · -- Parallel case: spinHalfDot σ σ = 1/4. Match m_x m_y / 4 = 1/4 since m² = 1.
      rw [spinHalfDot_apply_diag_of_ne_parallel hxy σ hpar, hpar, spinSign_sq]
    · rw [spinHalfDot_apply_diag_of_ne_antiparallel hxy σ hpar]
      have h_antipar : (spinSign (σ x) : ℂ) * (spinSign (σ y) : ℂ) = -1 := by
        unfold spinSign
        match hsx : σ x, hsy : σ y with
        | 0, 0 => exact absurd (hsx.trans hsy.symm) hpar
        | 0, 1 => push_cast; ring
        | 1, 0 => push_cast; ring
        | 1, 1 => exact absurd (hsx.trans hsy.symm) hpar
      rw [h_antipar]; ring

/-- **Spin-`1/2` `(Ŝ_tot)²` Casimir expectation on arbitrary `basisVec σ`**:
`<basisVec σ | (Ŝ_tot)² | basisVec σ> = |Λ|/2 + (M(σ)/2)²` for any
`σ : Λ → Fin 2`. Generalises γ-4 step 201 (the constant case where
`M(σ) = ±|Λ|` gives `|Λ|/2 + |Λ|²/4 = |Λ|·(|Λ|+2)/4`).

Proof: reduce to diagonal matrix element via `basisVec_expectation_eq_diagonal`,
expand `(Ŝ_tot)² = Σ_{x,y} spinHalfDot x y`, apply the unified
diagonal formula, then split the sum into the magnetization-squared
piece `(Σ_x spinSign(σ x))²/4 = M(σ)²/4` and the `(1/2)·[x=y]` piece
contributing `|Λ|/2` (γ-4 step 216). -/
theorem basisVec_totalSpinHalfSquared_expectation_general
    (σ : Λ → Fin 2) :
    dotProduct (star (basisVec σ))
        ((totalSpinHalfSquared Λ).mulVec (basisVec σ)) =
      (Fintype.card Λ : ℂ) / 2 + ((magnetization Λ σ : ℂ) / 2) ^ 2 := by
  rw [basisVec_expectation_eq_diagonal, totalSpinHalfSquared_eq_sum_dot]
  rw [Matrix.sum_apply]
  simp_rw [Matrix.sum_apply, spinHalfDot_apply_diag_unified]
  -- ∑ x, ∑ y, (m_x m_y / 4 + (if x = y then 1/2 else 0))
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_add_distrib)]
  rw [Finset.sum_add_distrib]
  -- Diagonal piece: ∑ x, ∑ y, (if x = y then 1/2 else 0) = |Λ|/2.
  have hDiag : (∑ x : Λ, ∑ y : Λ, (if x = y then (1/2 : ℂ) else 0)) =
      (Fintype.card Λ : ℂ) / 2 := by
    have hInner : ∀ x : Λ, (∑ y : Λ, (if x = y then (1/2 : ℂ) else 0)) = 1/2 := by
      intro x
      rw [Finset.sum_ite_eq Finset.univ x (fun _ => (1/2 : ℂ))]
      simp
    simp_rw [hInner]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hDiag]
  -- Off-diagonal piece: ∑ x, ∑ y, m_x m_y / 4 = M²/4.
  have hSepProd : ∀ a b : Λ → ℂ,
      (∑ x : Λ, ∑ y : Λ, a x * b y / 4) =
        (∑ x : Λ, a x) * (∑ y : Λ, b y) / 4 := fun a b => by
    rw [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, Finset.sum_div]
  rw [hSepProd]
  have hMag : (∑ x : Λ, (spinSign (σ x) : ℂ)) = (magnetization Λ σ : ℂ) := by
    unfold magnetization; push_cast; rfl
  rw [hMag]
  ring

/-- **Spin-`1/2` transverse Casimir `(Ŝ_tot^(1))² + (Ŝ_tot^(2))²` on
arbitrary `basisVec σ`** equals `|Λ|/2`, **independent of `σ`**.

Direct corollary of γ-4 step 216 (full Casimir) and γ-4 step 204
(z-axis squared): `(Ŝ_tot^(1))² + (Ŝ_tot^(2))² = (Ŝ_tot)² - (Ŝ_tot^(3))²`,
so the `M(σ)²/4` z-axis pieces cancel, leaving the constant `|Λ|/2`.

This expresses the per-state transverse contribution as a pure
combinatorial quantity (γ-4 step 219). -/
theorem basisVec_totalSpinHalfOp12_sq_expectation_general
    (σ : Λ → Fin 2) :
    dotProduct (star (basisVec σ))
        ((totalSpinHalfOp1 Λ * totalSpinHalfOp1 Λ +
            totalSpinHalfOp2 Λ * totalSpinHalfOp2 Λ).mulVec
          (basisVec σ)) =
      (Fintype.card Λ : ℂ) / 2 := by
  have hDecomp : totalSpinHalfOp1 Λ * totalSpinHalfOp1 Λ +
        totalSpinHalfOp2 Λ * totalSpinHalfOp2 Λ =
      totalSpinHalfSquared Λ -
        totalSpinHalfOp3 Λ * totalSpinHalfOp3 Λ := by
    unfold totalSpinHalfSquared; abel
  rw [hDecomp, Matrix.sub_mulVec, dotProduct_sub,
    basisVec_totalSpinHalfSquared_expectation_general,
    basisVec_totalSpinHalfOp3_sq_expectation]
  ring

/-- **Spin-`1/2` Néel Casimir** re-derived via the general
`basisVec σ` Casimir formula (γ-4 step 216):
`<Φ_Néel | (Ŝ_tot)² | Φ_Néel> = ((|A|−|¬A|)/2)² + |Λ|/2`.

Composition: γ-4 step 216 + `magnetization_neelConfigOf` + `ring`.

Direct corollary recovering the existing closed-form
`neelStateOf_totalSpinHalfSquared_expectation` from the general
framework (γ-4 step 227, spin-`1/2` mirror of γ-4 step 225). -/
theorem neelStateOf_totalSpinHalfSquared_expectation_via_general
    (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((totalSpinHalfSquared Λ).mulVec (neelStateOf A)) =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) /
          2) ^ 2 +
        (Fintype.card Λ : ℂ) / 2 := by
  unfold neelStateOf
  rw [basisVec_totalSpinHalfSquared_expectation_general,
    magnetization_neelConfigOf]
  push_cast
  ring

/-- **Spin-`1/2` const-state Casimir** re-derived via the general
`basisVec σ` formula (γ-4 step 216):
`<basisVec(const s) | (Ŝ_tot)² | basisVec(const s)> = |Λ|·(|Λ|+2)/4`
for any `s : Fin 2`. Composition of γ-4 step 216 +
`magnetization (const s) = ± |Λ|` + `(spinSign s)² = 1` + `ring`.
Recovers existing `basisVec_const_totalSpinHalfSquared_expectation`
(γ-4 step 201) from the general framework (γ-4 step 228, spin-`1/2`
mirror of γ-4 step 226). -/
theorem basisVec_const_totalSpinHalfSquared_expectation_via_general
    (s : Fin 2) :
    dotProduct (star (basisVec (fun _ : Λ => s)))
        ((totalSpinHalfSquared Λ).mulVec (basisVec (fun _ : Λ => s))) =
      (Fintype.card Λ : ℂ) * ((Fintype.card Λ : ℂ) + 2) / 4 := by
  rw [basisVec_totalSpinHalfSquared_expectation_general]
  have hMag : (magnetization Λ (fun _ : Λ => s) : ℂ) =
      (Fintype.card Λ : ℂ) * (spinSign s : ℂ) := by
    unfold magnetization
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    push_cast; ring
  rw [hMag]
  have hsq : (spinSign s : ℂ) * (spinSign s : ℂ) = 1 :=
    spinSign_sq s
  -- ((|Λ| · spinSign s) / 2)² = |Λ|²·(spinSign)²/4 = |Λ|²/4
  rw [show (((Fintype.card Λ : ℂ) * (spinSign s : ℂ)) / 2) ^ 2 =
      ((Fintype.card Λ : ℂ)) ^ 2 *
        ((spinSign s : ℂ) * (spinSign s : ℂ)) / 4 from by ring]
  rw [hsq]
  ring

/-- **Spin-`1/2` negation relation**:
`magnetization Λ (neelConfigOf (¬A)) = −magnetization Λ (neelConfigOf A)`.
Direct from `magnetization_neelConfigOf` + `magnetization_neelConfigOf_complement`
+ `ring`. Spin-`1/2` mirror of γ-4 step 231 (γ-4 step 232). -/
theorem magnetization_neelConfigOf_complement_eq_neg (A : Λ → Bool) :
    magnetization Λ (neelConfigOf (fun x : Λ => ! A x)) =
      -magnetization Λ (neelConfigOf A) := by
  rw [magnetization_neelConfigOf_complement, magnetization_neelConfigOf]
  ring

/-- **Spin-`1/2` Casimir is sublattice-swap invariant on Néel states**:
`<Φ_Néel(¬A) | (Ŝ_tot)² | Φ_Néel(¬A)> = <Φ_Néel(A) | (Ŝ_tot)² | Φ_Néel(A)>`.

Direct corollary of γ-4 step 227 (Casimir = `(M/2)² + |Λ|/2`) +
γ-4 step 232 (`M(¬A) = −M(A)`): the `M(σ)²` is invariant under
sign-flip, and `|Λ|/2` is `σ`-independent (γ-4 step 233). -/
theorem neelStateOf_totalSpinHalfSquared_complement_eq
    (A : Λ → Bool) :
    dotProduct (star (neelStateOf (fun x : Λ => ! A x)))
        ((totalSpinHalfSquared Λ).mulVec
          (neelStateOf (fun x : Λ => ! A x))) =
      dotProduct (star (neelStateOf A))
        ((totalSpinHalfSquared Λ).mulVec (neelStateOf A)) := by
  unfold neelStateOf
  rw [basisVec_totalSpinHalfSquared_expectation_general,
    basisVec_totalSpinHalfSquared_expectation_general,
    magnetization_neelConfigOf_complement_eq_neg]
  push_cast
  ring

/-- **Spin-`1/2` `(Ŝ_tot^(3))²` is sublattice-swap invariant on Néel
states**:
`<Φ_Néel(¬A) | (Ŝ_tot^(3))² | Φ_Néel(¬A)> = <Φ_Néel(A) | (Ŝ_tot^(3))² | Φ_Néel(A)>`.

Direct from γ-4 step 204 (`<basisVec σ|(Ŝ_tot^(3))²|basisVec σ>` =
`(M(σ)/2)²`) + γ-4 step 232 (`magnetization (¬A) = −(...)`):
the squared magnetization is sign-flip invariant. Spin-`1/2` mirror of
γ-4 step 235 (γ-4 step 236). -/
theorem neelStateOf_totalSpinHalfOp3_sq_complement_eq
    (A : Λ → Bool) :
    dotProduct (star (neelStateOf (fun x : Λ => ! A x)))
        ((totalSpinHalfOp3 Λ * totalSpinHalfOp3 Λ).mulVec
          (neelStateOf (fun x : Λ => ! A x))) =
      dotProduct (star (neelStateOf A))
        ((totalSpinHalfOp3 Λ * totalSpinHalfOp3 Λ).mulVec
          (neelStateOf A)) := by
  unfold neelStateOf
  rw [basisVec_totalSpinHalfOp3_sq_expectation,
    basisVec_totalSpinHalfOp3_sq_expectation,
    magnetization_neelConfigOf_complement_eq_neg]
  push_cast
  ring

/-- **Spin-`1/2` transverse Casimir `(Ŝ_tot^(1))²+(Ŝ_tot^(2))²` is
sublattice-swap invariant on Néel**:
both expectations equal `|Λ|/2` from γ-4 step 219 (which is
`σ`-independent). Spin-`1/2` mirror of γ-4 step 237 (γ-4 step 238). -/
theorem neelStateOf_totalSpinHalfOp12_sq_complement_eq
    (A : Λ → Bool) :
    dotProduct (star (neelStateOf (fun x : Λ => ! A x)))
        ((totalSpinHalfOp1 Λ * totalSpinHalfOp1 Λ +
            totalSpinHalfOp2 Λ * totalSpinHalfOp2 Λ).mulVec
          (neelStateOf (fun x : Λ => ! A x))) =
      dotProduct (star (neelStateOf A))
        ((totalSpinHalfOp1 Λ * totalSpinHalfOp1 Λ +
            totalSpinHalfOp2 Λ * totalSpinHalfOp2 Λ).mulVec
          (neelStateOf A)) := by
  unfold neelStateOf
  rw [basisVec_totalSpinHalfOp12_sq_expectation_general,
    basisVec_totalSpinHalfOp12_sq_expectation_general]

/-- **Spin-`1/2` linear `Ŝ_tot^(3)` expectation negation under sublattice swap**:
`<Φ_Néel(¬A) | Ŝ_tot^(3) | Φ_Néel(¬A)> = −<Φ_Néel(A) | Ŝ_tot^(3) | Φ_Néel(A)>`.

Direct from γ-4 step 207 + γ-4 step 232. Spin-`1/2` mirror of γ-4 step 239
(γ-4 step 240). -/
theorem neelStateOf_totalSpinHalfOp3_complement_eq_neg
    (A : Λ → Bool) :
    dotProduct (star (neelStateOf (fun x : Λ => ! A x)))
        ((totalSpinHalfOp3 Λ).mulVec (neelStateOf (fun x : Λ => ! A x))) =
      -dotProduct (star (neelStateOf A))
        ((totalSpinHalfOp3 Λ).mulVec (neelStateOf A)) := by
  unfold neelStateOf
  rw [basisVec_totalSpinHalfOp3_expectation,
    basisVec_totalSpinHalfOp3_expectation,
    magnetization_neelConfigOf_complement_eq_neg]
  push_cast
  ring

/-- **Spin-`1/2` `Ŝ_tot^(1)` zero expectation on Néel**:
`<Φ_Néel | Ŝ_tot^(1) | Φ_Néel> = 0`. Direct corollary of γ-4 step 215
applied to `σ = neelConfigOf A` (γ-4 step 242). -/
theorem neelStateOf_totalSpinHalfOp1_expectation (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((totalSpinHalfOp1 Λ).mulVec (neelStateOf A)) = 0 := by
  unfold neelStateOf
  exact basisVec_expectation_totalSpinHalfOp1 _

/-- **Spin-`1/2` `Ŝ_tot^(2)` zero expectation on Néel**:
`<Φ_Néel | Ŝ_tot^(2) | Φ_Néel> = 0`. Direct corollary of γ-4 step 215
applied to `σ = neelConfigOf A` (γ-4 step 242). -/
theorem neelStateOf_totalSpinHalfOp2_expectation (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((totalSpinHalfOp2 Λ).mulVec (neelStateOf A)) = 0 := by
  unfold neelStateOf
  exact basisVec_expectation_totalSpinHalfOp2 _

end LatticeSystem.Quantum
