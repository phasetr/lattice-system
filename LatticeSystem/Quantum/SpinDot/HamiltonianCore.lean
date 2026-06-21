import LatticeSystem.Quantum.SpinDot.Core
import LatticeSystem.Quantum.TotalSpin.Rotation

/-!
# Heisenberg-type Hamiltonian + Casimir + eigenvalue propagation

The bulk of the Tasaki §2.4 machinery built on top of `SpinDot`:
- Heisenberg-type SU(2)-invariant Hamiltonian definition,
- Casimir eigenvalue on all-up / all-down constants,
- Casimir invariance under `Ŝ_tot^±` on constant configs,
- Heisenberg Hamiltonian on the fully-polarised state (Tasaki
  §2.4 (2.4.5)),
- Eigenvalue propagation under `Ŝ_tot^±` (Tasaki §2.4 (2.4.7) /
  (2.4.9)),
- Commutativity with global rotation `Û^(α)_θ` (Tasaki §2.4
  (2.4.7)),
- Two-site singlet / triplet Casimir eigenvalues.

(Refactor Phase 2 PR 15 — first extraction from SpinDot.lean,
plan v4 §3.1.)
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Heisenberg-type SU(2)-invariant Hamiltonian (Tasaki §2.2 (2.2.13)) -/

/-- The general Heisenberg-type Hamiltonian
`H = Σ_{x,y} J(x,y) Ŝ_x · Ŝ_y`. Any choice of coupling `J` yields an
SU(2)-invariant operator (proved below). -/
noncomputable def heisenbergHamiltonian (J : Λ → Λ → ℂ) : ManyBodyOp Λ :=
  ∑ x : Λ, ∑ y : Λ, J x y • spinHalfDot x y

/-- A Heisenberg-type Hamiltonian commutes with `Ŝ_tot^(1)` (Tasaki
§2.2 SU(2)-invariance, eq. (2.2.13) for axis 1). -/
theorem heisenbergHamiltonian_commutator_totalSpinHalfOp1 (J : Λ → Λ → ℂ) :
    heisenbergHamiltonian J * totalSpinHalfOp1 Λ -
        totalSpinHalfOp1 Λ * heisenbergHamiltonian J = 0 := by
  unfold heisenbergHamiltonian
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  rw [spinHalfDot_commutator_totalSpinHalfOp1, smul_zero]

/-- A Heisenberg-type Hamiltonian commutes with `Ŝ_tot^(2)`. -/
theorem heisenbergHamiltonian_commutator_totalSpinHalfOp2 (J : Λ → Λ → ℂ) :
    heisenbergHamiltonian J * totalSpinHalfOp2 Λ -
        totalSpinHalfOp2 Λ * heisenbergHamiltonian J = 0 := by
  unfold heisenbergHamiltonian
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  rw [spinHalfDot_commutator_totalSpinHalfOp2, smul_zero]

/-- A Heisenberg-type Hamiltonian commutes with `Ŝ_tot^(3)`. -/
theorem heisenbergHamiltonian_commutator_totalSpinHalfOp3 (J : Λ → Λ → ℂ) :
    heisenbergHamiltonian J * totalSpinHalfOp3 Λ -
        totalSpinHalfOp3 Λ * heisenbergHamiltonian J = 0 := by
  unfold heisenbergHamiltonian
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  rw [spinHalfDot_commutator_totalSpinHalfOp3, smul_zero]

/-- A Heisenberg-type Hamiltonian commutes with `Ŝ^+_tot` (ladder
form of SU(2) invariance). -/
theorem heisenbergHamiltonian_commutator_totalSpinHalfOpPlus (J : Λ → Λ → ℂ) :
    heisenbergHamiltonian J * totalSpinHalfOpPlus Λ -
        totalSpinHalfOpPlus Λ * heisenbergHamiltonian J = 0 := by
  unfold heisenbergHamiltonian
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  rw [spinHalfDot_commutator_totalSpinHalfOpPlus, smul_zero]

/-- A Heisenberg-type Hamiltonian commutes with `Ŝ^-_tot`. -/
theorem heisenbergHamiltonian_commutator_totalSpinHalfOpMinus (J : Λ → Λ → ℂ) :
    heisenbergHamiltonian J * totalSpinHalfOpMinus Λ -
        totalSpinHalfOpMinus Λ * heisenbergHamiltonian J = 0 := by
  unfold heisenbergHamiltonian
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  rw [spinHalfDot_commutator_totalSpinHalfOpMinus, smul_zero]

/-- `Commute (heisenbergHamiltonian J) Ŝ^+_tot`. Reformulation of the
ladder commutator in `Commute` form. -/
theorem heisenbergHamiltonian_commute_totalSpinHalfOpPlus (J : Λ → Λ → ℂ) :
    Commute (heisenbergHamiltonian J) (totalSpinHalfOpPlus Λ) :=
  sub_eq_zero.mp (heisenbergHamiltonian_commutator_totalSpinHalfOpPlus J)

/-- `Commute (heisenbergHamiltonian J) Ŝ^-_tot`. -/
theorem heisenbergHamiltonian_commute_totalSpinHalfOpMinus (J : Λ → Λ → ℂ) :
    Commute (heisenbergHamiltonian J) (totalSpinHalfOpMinus Λ) :=
  sub_eq_zero.mp (heisenbergHamiltonian_commutator_totalSpinHalfOpMinus J)

/-- A Heisenberg-type Hamiltonian commutes with the Casimir `Ŝtot²`:
operator-level SU(2)/U(1) invariance at the Casimir level. Follows
from `[H, Ŝtot^α] = 0` for each axis via `Commute.mul_right` and
`Commute.add_right`. -/
theorem heisenbergHamiltonian_commute_totalSpinHalfSquared (J : Λ → Λ → ℂ) :
    Commute (heisenbergHamiltonian J) (totalSpinHalfSquared Λ) := by
  unfold totalSpinHalfSquared
  have h1 : Commute (heisenbergHamiltonian J) (totalSpinHalfOp1 Λ) :=
    sub_eq_zero.mp (heisenbergHamiltonian_commutator_totalSpinHalfOp1 J)
  have h2 : Commute (heisenbergHamiltonian J) (totalSpinHalfOp2 Λ) :=
    sub_eq_zero.mp (heisenbergHamiltonian_commutator_totalSpinHalfOp2 J)
  have h3 : Commute (heisenbergHamiltonian J) (totalSpinHalfOp3 Λ) :=
    sub_eq_zero.mp (heisenbergHamiltonian_commutator_totalSpinHalfOp3 J)
  exact ((h1.mul_right h1).add_right (h2.mul_right h2)).add_right (h3.mul_right h3)

/-- The Heisenberg Hamiltonian preserves `Ŝtot²` eigenvalues: if
`Ŝtot² · v = S · v`, then `Ŝtot² · (H · v) = S · (H · v)`. Operator-level
simultaneous diagonalisation of `H` and the SU(2) Casimir. -/
theorem heisenbergHamiltonian_mulVec_preserves_totalSpinHalfSquared_eigenvalue
    (J : Λ → Λ → ℂ) {S : ℂ} {v : (Λ → Fin 2) → ℂ}
    (hv : (totalSpinHalfSquared Λ).mulVec v = S • v) :
    (totalSpinHalfSquared Λ).mulVec ((heisenbergHamiltonian J).mulVec v) =
      S • (heisenbergHamiltonian J).mulVec v := by
  have hcomm : totalSpinHalfSquared Λ * heisenbergHamiltonian J =
      heisenbergHamiltonian J * totalSpinHalfSquared Λ :=
    (heisenbergHamiltonian_commute_totalSpinHalfSquared J).symm
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]

/-! ## Casimir eigenvalue on the all-up / all-down states -/

/-- `Ŝ_x · Ŝ_y` action on a uniformly-aligned basis state (constant `s`):
`(3/4) |s⟩` for `x = y`, `(1/4) |s⟩` for `x ≠ y`. -/
private theorem spinHalfDot_mulVec_const (s : Fin 2) (x y : Λ) :
    (spinHalfDot x y).mulVec (basisVec (fun _ : Λ => s)) =
      (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ)) •
        basisVec (fun _ : Λ => s) := by
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, spinHalfDot_self]
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  · rw [if_neg hxy]
    exact spinHalfDot_mulVec_basisVec_parallel hxy _ rfl

/-- Specialization to the all-up state. -/
private theorem spinHalfDot_mulVec_all_up (x y : Λ) :
    (spinHalfDot x y).mulVec (basisVec (fun _ : Λ => (0 : Fin 2))) =
      (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ)) •
        basisVec (fun _ : Λ => (0 : Fin 2)) :=
  spinHalfDot_mulVec_const 0 x y

/-- The Casimir eigenvalue on a uniformly-aligned basis state:
`Ŝ_tot² |s s … s⟩ = (N(N+2)/4) |s s … s⟩` where `N = |Λ|`. Both
the all-up and all-down states are eigenvectors with eigenvalue
`S(S+1) = (N/2)(N/2+1)`, the maximum total spin `S = N/2`. -/
theorem totalSpinHalfSquared_mulVec_basisVec_const (s : Fin 2) :
    (totalSpinHalfSquared Λ).mulVec (basisVec (fun _ : Λ => s)) =
      ((Fintype.card Λ : ℂ) * (Fintype.card Λ + 2) / 4) •
        basisVec (fun _ : Λ => s) := by
  rw [totalSpinHalfSquared_eq_sum_dot]
  rw [Matrix.sum_mulVec]
  simp_rw [Matrix.sum_mulVec, spinHalfDot_mulVec_const]
  simp_rw [← Finset.sum_smul]
  congr 1
  have hinner : ∀ x : Λ, (∑ y : Λ, (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ))) =
      (Fintype.card Λ : ℂ) / 4 + 1 / 2 := by
    intro x
    have hsplit : ∀ y : Λ, (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ)) =
        (1 / 4 : ℂ) + (if x = y then (1 / 2 : ℂ) else 0) := by
      intro y
      by_cases h : x = y
      · simp [h]; ring
      · simp [h]
    simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Finset.sum_ite_eq Finset.univ x (fun _ => (1 / 2 : ℂ))]
    rw [if_pos (Finset.mem_univ _)]
    ring
  simp_rw [hinner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- Specialization to the all-up state. -/
theorem totalSpinHalfSquared_mulVec_basisVec_all_up :
    (totalSpinHalfSquared Λ).mulVec (basisVec (fun _ : Λ => (0 : Fin 2))) =
      ((Fintype.card Λ : ℂ) * (Fintype.card Λ + 2) / 4) •
        basisVec (fun _ : Λ => (0 : Fin 2)) :=
  totalSpinHalfSquared_mulVec_basisVec_const 0

/-- Specialization to the all-down state. -/
theorem totalSpinHalfSquared_mulVec_basisVec_all_down :
    (totalSpinHalfSquared Λ).mulVec (basisVec (fun _ : Λ => (1 : Fin 2))) =
      ((Fintype.card Λ : ℂ) * (Fintype.card Λ + 2) / 4) •
        basisVec (fun _ : Λ => (1 : Fin 2)) :=
  totalSpinHalfSquared_mulVec_basisVec_const 1

/-- **`(Ŝ_tot)²` expectation on a constant-spin basis state** (spin-`1/2`):
`<basisVec(const s) | (Ŝ_tot)² | basisVec(const s)> = |Λ|·(|Λ|+2)/4`,
the maximum total-spin Casimir value (γ-4 step 201). -/
theorem basisVec_const_totalSpinHalfSquared_expectation (s : Fin 2) :
    dotProduct (star (basisVec (fun _ : Λ => s)))
        ((totalSpinHalfSquared Λ).mulVec (basisVec (fun _ : Λ => s))) =
      (Fintype.card Λ : ℂ) * (Fintype.card Λ + 2) / 4 := by
  rw [totalSpinHalfSquared_mulVec_basisVec_const]
  unfold dotProduct
  rw [Finset.sum_eq_single (fun _ : Λ => s)]
  · simp [Pi.star_apply, basisVec_self]
  · intros τ _ hτ
    simp [Pi.smul_apply, basisVec_of_ne hτ]
  · intro hempty
    exact (hempty (Finset.mem_univ _)).elim

/-- **`(Ŝ_tot^(3))²` expectation on a constant-spin basis state** (spin-`1/2`):
`<basisVec(const s) | (Ŝ_tot^(3))² | basisVec(const s)> = |Λ|²/4` for any `s : Fin 2`.
The constant state is an `Ŝ_tot^(3)`-eigenvector with eigenvalue `±|Λ|/2`,
whose square is `|Λ|²/4` (γ-4 step 203). -/
theorem basisVec_const_totalSpinHalfOp3_sq_expectation (s : Fin 2) :
    dotProduct (star (basisVec (fun _ : Λ => s)))
        ((totalSpinHalfOp3 Λ * totalSpinHalfOp3 Λ).mulVec
          (basisVec (fun _ : Λ => s))) =
      ((Fintype.card Λ : ℂ) / 2) ^ 2 := by
  rw [← Matrix.mulVec_mulVec, totalSpinHalfOp3_mulVec_basisVec_const,
    Matrix.mulVec_smul, totalSpinHalfOp3_mulVec_basisVec_const,
    smul_smul]
  unfold dotProduct
  rw [Finset.sum_eq_single (fun _ : Λ => s)]
  · simp only [Pi.star_apply, basisVec_self, star_one, Pi.smul_apply, smul_eq_mul,
      mul_one, one_mul]
    fin_cases s <;> simp [spinHalfSign] <;> ring
  · intros τ _ hτ
    simp [Pi.smul_apply, basisVec_of_ne hτ]
  · intro hempty
    exact (hempty (Finset.mem_univ _)).elim

/-- **`(Ŝ_tot^(3))²` expectation on an arbitrary basis state** (spin-`1/2`):
`<basisVec σ | (Ŝ_tot^(3))² | basisVec σ> = magnetization(σ)²/4` for any
`σ : Λ → Fin 2`. Direct from `totalSpinHalfOp3_mulVec_basisVec_eq_magnetization`
(eigenvector identity at eigenvalue `M(σ)/2`) applied twice via
`Matrix.mulVec_mulVec` (γ-4 step 204). The `_const` case (γ-4 step 203) is
the specialisation `σ = fun _ => s` whose magnetization is `±|Λ|`. -/
theorem basisVec_totalSpinHalfOp3_sq_expectation (σ : Λ → Fin 2) :
    dotProduct (star (basisVec σ))
        ((totalSpinHalfOp3 Λ * totalSpinHalfOp3 Λ).mulVec (basisVec σ)) =
      ((magnetization Λ σ : ℂ) / 2) ^ 2 := by
  rw [← Matrix.mulVec_mulVec, totalSpinHalfOp3_mulVec_basisVec_eq_magnetization,
    Matrix.mulVec_smul, totalSpinHalfOp3_mulVec_basisVec_eq_magnetization,
    smul_smul]
  unfold dotProduct
  rw [Finset.sum_eq_single σ]
  · simp only [Pi.star_apply, basisVec_self, star_one, Pi.smul_apply, smul_eq_mul,
      mul_one, one_mul]
    ring
  · intros τ _ hτ
    simp [Pi.smul_apply, basisVec_of_ne hτ]
  · intro hempty
    exact (hempty (Finset.mem_univ _)).elim

/-- **Linear `Ŝ_tot^(3)` expectation on an arbitrary basis state** (spin-`1/2`):
`<basisVec σ | Ŝ_tot^(3) | basisVec σ> = magnetization(σ)/2` for any
`σ : Λ → Fin 2`. Direct from `totalSpinHalfOp3_mulVec_basisVec_eq_magnetization`
(eigenvector identity at eigenvalue `M(σ)/2`) + dot-product right-linearity
(γ-4 step 207). -/
theorem basisVec_totalSpinHalfOp3_expectation (σ : Λ → Fin 2) :
    dotProduct (star (basisVec σ))
        ((totalSpinHalfOp3 Λ).mulVec (basisVec σ)) =
      (magnetization Λ σ : ℂ) / 2 := by
  rw [totalSpinHalfOp3_mulVec_basisVec_eq_magnetization]
  unfold dotProduct
  rw [Finset.sum_eq_single σ]
  · simp only [Pi.star_apply, basisVec_self, star_one, Pi.smul_apply, smul_eq_mul,
      mul_one, one_mul]
  · intros τ _ hτ
    simp [Pi.smul_apply, basisVec_of_ne hτ]
  · intro hempty
    exact (hempty (Finset.mem_univ _)).elim

/-- **`Ŝ_tot^(3)` zero-variance on `basisVec σ`** (spin-`1/2`):
`basisVec σ` is a sharp `Ŝ_tot^(3)`-eigenstate (zero variance):
`<(Ŝ_tot^(3))²> - <Ŝ_tot^(3)>² = 0` for any `σ : Λ → Fin 2`.
Direct corollary of γ-4 step 204 (squared, `M(σ)²/4`) and γ-4 step 207
(linear, `M(σ)/2`) (γ-4 step 208). -/
theorem basisVec_totalSpinHalfOp3_variance_eq_zero (σ : Λ → Fin 2) :
    dotProduct (star (basisVec σ))
        ((totalSpinHalfOp3 Λ * totalSpinHalfOp3 Λ).mulVec (basisVec σ)) -
      (dotProduct (star (basisVec σ))
        ((totalSpinHalfOp3 Λ).mulVec (basisVec σ))) ^ 2 = 0 := by
  rw [basisVec_totalSpinHalfOp3_sq_expectation,
    basisVec_totalSpinHalfOp3_expectation]
  ring

/-- **Off-diagonal `Ŝ_tot^(3)` matrix elements vanish** (spin-`1/2`):
for distinct basis configurations `σ ≠ τ`,
`<basisVec τ | Ŝ_tot^(3) | basisVec σ> = 0`. Witnesses that
`Ŝ_tot^(3)` is diagonal in the computational basis (γ-4 step 209). -/
theorem basisVec_off_diagonal_totalSpinHalfOp3 {σ τ : Λ → Fin 2}
    (hστ : τ ≠ σ) :
    dotProduct (star (basisVec τ))
        ((totalSpinHalfOp3 Λ).mulVec (basisVec σ)) = 0 := by
  have h0 : dotProduct (star (basisVec τ))
      (basisVec σ : (Λ → Fin 2) → ℂ) = 0 := by
    unfold dotProduct
    apply Finset.sum_eq_zero
    intros φ _
    by_cases hφ : φ = τ
    · subst hφ
      rw [Pi.star_apply, basisVec_self, star_one,
        basisVec_of_ne hστ, mul_zero]
    · rw [Pi.star_apply, basisVec_of_ne hφ, star_zero, zero_mul]
  rw [totalSpinHalfOp3_mulVec_basisVec_eq_magnetization, dotProduct_smul,
    smul_eq_mul, h0, mul_zero]

/-- **Spin-`1/2` basis states are pairwise orthogonal**: for `τ ≠ σ`,
`<basisVec τ | basisVec σ> = 0` (γ-4 step 210). -/
theorem basisVec_dotProduct_basisVec_of_ne {σ τ : Λ → Fin 2}
    (hστ : τ ≠ σ) :
    dotProduct (star (basisVec τ)) (basisVec σ : (Λ → Fin 2) → ℂ) = 0 := by
  unfold dotProduct
  apply Finset.sum_eq_zero
  intros φ _
  by_cases hφ : φ = τ
  · subst hφ
    rw [Pi.star_apply, basisVec_self, star_one,
      basisVec_of_ne hστ, mul_zero]
  · rw [Pi.star_apply, basisVec_of_ne hφ, star_zero, zero_mul]

/-- **Combined δ-form for spin-`1/2` basis dotProduct**:
`<basisVec τ | basisVec σ> = if τ = σ then 1 else 0` (γ-4 step 211). -/
theorem basisVec_dotProduct_basisVec (σ τ : Λ → Fin 2) :
    dotProduct (star (basisVec τ)) (basisVec σ : (Λ → Fin 2) → ℂ) =
      if τ = σ then 1 else 0 := by
  by_cases hτσ : τ = σ
  · subst hτσ
    rw [if_pos rfl]
    -- Diagonal case: <σ|σ> = 1.
    unfold dotProduct
    rw [Finset.sum_eq_single τ]
    · rw [Pi.star_apply, basisVec_self, star_one, mul_one]
    · intros φ _ hφ
      rw [Pi.star_apply, basisVec_of_ne hφ, star_zero, zero_mul]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · rw [if_neg hτσ, basisVec_dotProduct_basisVec_of_ne hτσ]

/-- **Spin-`1/2` combined δ-form for `Ŝ_tot^(3)` matrix elements**:
`<basisVec τ | Ŝ_tot^(3) | basisVec σ> = if τ = σ then magnetization(σ)/2 else 0`
(γ-4 step 212). -/
theorem basisVec_dotProduct_totalSpinHalfOp3_basisVec (σ τ : Λ → Fin 2) :
    dotProduct (star (basisVec τ))
        ((totalSpinHalfOp3 Λ).mulVec (basisVec σ)) =
      if τ = σ then (magnetization Λ σ : ℂ) / 2 else 0 := by
  by_cases hτσ : τ = σ
  · subst hτσ
    rw [if_pos rfl, basisVec_totalSpinHalfOp3_expectation]
  · rw [if_neg hτσ, basisVec_off_diagonal_totalSpinHalfOp3 hτσ]

/-- Off-diagonal spin-`1/2` `(Ŝ_tot^(3))²` matrix elements vanish for
`τ ≠ σ`: `<basisVec τ | (Ŝ_tot^(3))² | basisVec σ> = 0`
(γ-4 step 213). -/
theorem basisVec_off_diagonal_totalSpinHalfOp3_sq {σ τ : Λ → Fin 2}
    (hστ : τ ≠ σ) :
    dotProduct (star (basisVec τ))
        ((totalSpinHalfOp3 Λ * totalSpinHalfOp3 Λ).mulVec (basisVec σ)) = 0 := by
  have h0 : dotProduct (star (basisVec τ))
      (basisVec σ : (Λ → Fin 2) → ℂ) = 0 :=
    basisVec_dotProduct_basisVec_of_ne hστ
  rw [← Matrix.mulVec_mulVec, totalSpinHalfOp3_mulVec_basisVec_eq_magnetization,
    Matrix.mulVec_smul, totalSpinHalfOp3_mulVec_basisVec_eq_magnetization,
    smul_smul, dotProduct_smul, smul_eq_mul, h0, mul_zero]

/-- **Spin-`1/2` combined δ-form for `(Ŝ_tot^(3))²` matrix elements**:
`<basisVec τ | (Ŝ_tot^(3))² | basisVec σ> = if τ = σ then (magnetization(σ)/2)² else 0`
(γ-4 step 213). -/
theorem basisVec_dotProduct_totalSpinHalfOp3_sq_basisVec (σ τ : Λ → Fin 2) :
    dotProduct (star (basisVec τ))
        ((totalSpinHalfOp3 Λ * totalSpinHalfOp3 Λ).mulVec (basisVec σ)) =
      if τ = σ then ((magnetization Λ σ : ℂ) / 2) ^ 2 else 0 := by
  by_cases hτσ : τ = σ
  · subst hτσ
    rw [if_pos rfl, basisVec_totalSpinHalfOp3_sq_expectation]
  · rw [if_neg hτσ, basisVec_off_diagonal_totalSpinHalfOp3_sq hτσ]


end LatticeSystem.Quantum
