import LatticeSystem.Quantum.SpinDot.HamiltonianCore

/-!
# Heisenberg-type Hamiltonian §2.4 propagation — capstone

Continued from `SpinDot/HamiltonianCore.lean` (Heisenberg-type SU(2)-invariant
Hamiltonian definition, Casimir eigenvalue on all-up/all-down constants, and the
spin-`1/2` `(Ŝ_tot^(3))²` expectation machinery).  This file carries:
- spin-`1/2` total `Ŝ_tot^{(1,2)}` zero expectation (γ-4 step 215),
- Casimir invariance under `Ŝ_tot^±` on constant configs (Tasaki §2.4),
- Heisenberg Hamiltonian on the fully-polarised state (Tasaki §2.4 (2.4.5)),
- eigenvalue propagation under `Ŝ_tot^±` (Tasaki §2.4 (2.4.7)/(2.4.9)),
- commutativity with global rotation `Û^(α)_θ` (Tasaki §2.4 (2.4.7)),
- two-site singlet / triplet Casimir eigenvalues.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Spin-`1/2` total `Ŝ_tot^{(1,2)}` zero expectation (γ-4 step 215) -/

/-- Per-site spin-`1/2` `Ŝ^(1)_x` has zero expectation on every basis
state (γ-4 step 215). -/
private theorem basisVec_expectation_onSite_spinHalfOp1
    (x : Λ) (σ : Λ → Fin 2) :
    dotProduct (star (basisVec σ))
      ((onSite x spinHalfOp1 : ManyBodyOp Λ).mulVec (basisVec σ)) = 0 := by
  rw [basisVec_expectation_eq_diagonal]
  rw [onSite_apply, if_pos (fun _ _ => rfl)]
  unfold spinHalfOp1 pauliX
  match σ x with
  | 0 => simp
  | 1 => simp

/-- Per-site spin-`1/2` `Ŝ^(2)_x` has zero expectation on every basis
state (γ-4 step 215). -/
private theorem basisVec_expectation_onSite_spinHalfOp2
    (x : Λ) (σ : Λ → Fin 2) :
    dotProduct (star (basisVec σ))
      ((onSite x spinHalfOp2 : ManyBodyOp Λ).mulVec (basisVec σ)) = 0 := by
  rw [basisVec_expectation_eq_diagonal]
  rw [onSite_apply, if_pos (fun _ _ => rfl)]
  unfold spinHalfOp2 pauliY
  match σ x with
  | 0 => simp
  | 1 => simp

/-- The total `Ŝ_tot^(1)` (spin-`1/2`) has zero expectation on every
basis state (γ-4 step 215, mirror of γ-4 step 214 for spin-`S`). -/
theorem basisVec_expectation_totalSpinHalfOp1 (σ : Λ → Fin 2) :
    dotProduct (star (basisVec σ))
      ((totalSpinHalfOp1 Λ).mulVec (basisVec σ)) = 0 := by
  unfold totalSpinHalfOp1
  rw [Matrix.sum_mulVec, dotProduct_sum]
  apply Finset.sum_eq_zero
  intros x _
  exact basisVec_expectation_onSite_spinHalfOp1 x σ

/-- The total `Ŝ_tot^(2)` (spin-`1/2`) has zero expectation on every
basis state (γ-4 step 215). -/
theorem basisVec_expectation_totalSpinHalfOp2 (σ : Λ → Fin 2) :
    dotProduct (star (basisVec σ))
      ((totalSpinHalfOp2 Λ).mulVec (basisVec σ)) = 0 := by
  unfold totalSpinHalfOp2
  rw [Matrix.sum_mulVec, dotProduct_sum]
  apply Finset.sum_eq_zero
  intros x _
  exact basisVec_expectation_onSite_spinHalfOp2 x σ

/-! ## Casimir invariance under Ŝ_tot^± on constant configs (Tasaki §2.4)

`(Ŝ_tot)²` commutes with both `Ŝ_tot^+` and `Ŝ_tot^-`
(`totalSpinHalfSquared_commutator_totalSpinHalfOp{Plus,Minus}` in
`TotalSpin.lean`). Combined with the constant-config eigenvalue
`Ŝ_tot² · |s..s⟩ = (|Λ|·(|Λ|+2)/4) · |s..s⟩`, every iterate
`(Ŝ_tot^∓)^k · |s..s⟩` is a `Ŝ_tot²`-eigenvector with the same
maximum-spin eigenvalue `S_max(S_max+1)`. -/

/-- `Ŝ_tot² · (Ŝ_tot^-)^k · |s..s⟩ = (|Λ|·(|Λ|+2)/4) · (Ŝ_tot^-)^k · |s..s⟩`:
the lowering ladder iterates remain in the maximum-total-spin
SU(2) representation `S = S_max = |Λ|/2`. -/
theorem totalSpinHalfSquared_mulVec_totalSpinHalfOpMinus_pow_basisVec_const
    (s : Fin 2) (k : ℕ) :
    (totalSpinHalfSquared Λ).mulVec
        (((totalSpinHalfOpMinus Λ) ^ k).mulVec (basisVec (fun _ : Λ => s))) =
      ((Fintype.card Λ : ℂ) * (Fintype.card Λ + 2) / 4) •
        ((totalSpinHalfOpMinus Λ) ^ k).mulVec (basisVec (fun _ : Λ => s)) := by
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.one_mulVec]
    exact totalSpinHalfSquared_mulVec_basisVec_const s
  | succ k ih =>
    have hcomm : totalSpinHalfSquared Λ * totalSpinHalfOpMinus Λ =
        totalSpinHalfOpMinus Λ * totalSpinHalfSquared Λ :=
      sub_eq_zero.mp (totalSpinHalfSquared_commutator_totalSpinHalfOpMinus Λ)
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm,
      ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul]

/-- `Ŝ_tot² · (Ŝ_tot^+)^k · |s..s⟩ = (|Λ|·(|Λ|+2)/4) · (Ŝ_tot^+)^k · |s..s⟩`:
companion of the lowering version above. -/
theorem totalSpinHalfSquared_mulVec_totalSpinHalfOpPlus_pow_basisVec_const
    (s : Fin 2) (k : ℕ) :
    (totalSpinHalfSquared Λ).mulVec
        (((totalSpinHalfOpPlus Λ) ^ k).mulVec (basisVec (fun _ : Λ => s))) =
      ((Fintype.card Λ : ℂ) * (Fintype.card Λ + 2) / 4) •
        ((totalSpinHalfOpPlus Λ) ^ k).mulVec (basisVec (fun _ : Λ => s)) := by
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.one_mulVec]
    exact totalSpinHalfSquared_mulVec_basisVec_const s
  | succ k ih =>
    have hcomm : totalSpinHalfSquared Λ * totalSpinHalfOpPlus Λ =
        totalSpinHalfOpPlus Λ * totalSpinHalfSquared Λ :=
      sub_eq_zero.mp (totalSpinHalfSquared_commutator_totalSpinHalfOpPlus Λ)
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm,
      ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul]

/-! ## Heisenberg Hamiltonian on the fully-polarised state (Tasaki §2.4 (2.4.5))

Tasaki *Physics and Mathematics of Quantum Many-Body Systems* §2.4
"The Ferromagnetic Heisenberg Model", eq. (2.4.5), p. 32, asserts that
the fully-polarised state `|Φ↑⟩ = ⊗_x |ψ_x^S⟩` satisfies

```
- Ŝ_x · Ŝ_y |Φ↑⟩ = - Ŝ_x^(3) Ŝ_y^(3) |Φ↑⟩ = - S² |Φ↑⟩,
```

so each bond term contributes the minimum eigenvalue `-S²`. Summed over
the bond set `B`, this gives `E_GS = -|B| S²` (the ferromagnetic
ground-state energy).

For `S = 1/2` this lifts to: every Heisenberg-type Hamiltonian
`H = Σ_{x,y} J(x,y) Ŝ_x · Ŝ_y` acts on a constant-spin basis state
`|s s … s⟩` as a scalar, with eigenvalue determined entirely by `J`. -/

/-- Heisenberg Hamiltonian on a uniformly-aligned basis state (constant
spin configuration `s : Fin 2`): the state is a simultaneous eigenvector
of every Heisenberg-type Hamiltonian, and the eigenvalue is the
weighted bilinear sum of the couplings.

This is the bilinear-sum lift of Tasaki §2.4 eq. (2.4.5), p. 32, for
`S = 1/2`: each bond term `Ŝ_x · Ŝ_y` (for `x ≠ y`) contributes
`1/4 = S²` (the maximum eigenvalue of `Ŝ_x · Ŝ_y` for `S = 1/2`),
and each diagonal term `Ŝ_x · Ŝ_x` contributes `3/4 = S(S+1)`
(via `spinHalfDot_self`). The diagonal `3/4` summand is an
extension beyond Tasaki's bond-only statement (which only treats
`x ≠ y`). The eigenvalue equals the ground-state energy only for
suitable ferromagnetic `J`; that step is not asserted here. -/
theorem heisenbergHamiltonian_mulVec_basisVec_const
    (J : Λ → Λ → ℂ) (s : Fin 2) :
    (heisenbergHamiltonian J).mulVec (basisVec (fun _ : Λ => s)) =
      (∑ x : Λ, ∑ y : Λ,
          J x y * (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ))) •
        basisVec (fun _ : Λ => s) := by
  unfold heisenbergHamiltonian
  rw [Matrix.sum_mulVec]
  simp_rw [Matrix.sum_mulVec, Matrix.smul_mulVec,
    spinHalfDot_mulVec_const s, smul_smul]
  simp_rw [← Finset.sum_smul]

/-- Specialisation of `heisenbergHamiltonian_mulVec_basisVec_const`
to the all-up state (Tasaki §2.4 eq. (2.4.5), p. 32, for `S = 1/2`). -/
theorem heisenbergHamiltonian_mulVec_basisVec_all_up (J : Λ → Λ → ℂ) :
    (heisenbergHamiltonian J).mulVec (basisVec (fun _ : Λ => (0 : Fin 2))) =
      (∑ x : Λ, ∑ y : Λ,
          J x y * (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ))) •
        basisVec (fun _ : Λ => (0 : Fin 2)) :=
  heisenbergHamiltonian_mulVec_basisVec_const J 0

/-- Specialisation of `heisenbergHamiltonian_mulVec_basisVec_const`
to the all-down state (Tasaki §2.4 eq. (2.4.5), p. 32, for `S = 1/2`,
flipped). -/
theorem heisenbergHamiltonian_mulVec_basisVec_all_down (J : Λ → Λ → ℂ) :
    (heisenbergHamiltonian J).mulVec (basisVec (fun _ : Λ => (1 : Fin 2))) =
      (∑ x : Λ, ∑ y : Λ,
          J x y * (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ))) •
        basisVec (fun _ : Λ => (1 : Fin 2)) :=
  heisenbergHamiltonian_mulVec_basisVec_const J 1

/-! ## Eigenvalue propagation under Ŝ_tot^± (Tasaki §2.4 (2.4.7)/(2.4.9))

Since `[H, Ŝ_tot^±] = 0` for any Heisenberg-type Hamiltonian
(`heisenbergHamiltonian_commutator_totalSpinHalfOp{Plus,Minus}`), and
the constant configuration `|s s … s⟩` is an `H`-eigenvector
(`heisenbergHamiltonian_mulVec_basisVec_const`), the lowered state
`Ŝ_tot^- · |s s … s⟩` is again an `H`-eigenvector with the same
eigenvalue. Iterating gives the entire ferromagnetic ground-state
ladder `(Ŝ_tot^-)^k · |Φ↑⟩ ∝ |Φ_M⟩` of Tasaki eq. (2.4.9). -/

/-- Eigenvalue propagation under `Ŝ_tot^+`: applying the global raising
operator to a constant-spin basis state preserves the H-eigenvalue.
This is a direct corollary of the SU(2) invariance of every Heisenberg
Hamiltonian (Tasaki §2.4, eq. (2.4.7), p. 33). The companion `_Minus_`
result is the explicit lowering ladder Tasaki uses in eq. (2.4.9). -/
theorem heisenbergHamiltonian_mulVec_totalSpinHalfOpPlus_basisVec_const
    (J : Λ → Λ → ℂ) (s : Fin 2) :
    (heisenbergHamiltonian J).mulVec
        ((totalSpinHalfOpPlus Λ).mulVec (basisVec (fun _ : Λ => s))) =
      (∑ x : Λ, ∑ y : Λ,
          J x y * (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ))) •
        (totalSpinHalfOpPlus Λ).mulVec (basisVec (fun _ : Λ => s)) := by
  have hcomm := heisenbergHamiltonian_commutator_totalSpinHalfOpPlus J
  have hcomm' : heisenbergHamiltonian J * totalSpinHalfOpPlus Λ =
      totalSpinHalfOpPlus Λ * heisenbergHamiltonian J :=
    sub_eq_zero.mp hcomm
  rw [Matrix.mulVec_mulVec, hcomm', ← Matrix.mulVec_mulVec,
    heisenbergHamiltonian_mulVec_basisVec_const, Matrix.mulVec_smul]

/-- Eigenvalue propagation under `Ŝ_tot^-`: applying the global lowering
operator to a constant-spin basis state preserves the H-eigenvalue.
Tasaki §2.4 eqs. (2.4.7)/(2.4.9), p. 33, for `S = 1/2`. This is the
ladder step generating the ferromagnetic ground states `|Φ_M⟩` from
`|Φ↑⟩` in eq. (2.4.9). -/
theorem heisenbergHamiltonian_mulVec_totalSpinHalfOpMinus_basisVec_const
    (J : Λ → Λ → ℂ) (s : Fin 2) :
    (heisenbergHamiltonian J).mulVec
        ((totalSpinHalfOpMinus Λ).mulVec (basisVec (fun _ : Λ => s))) =
      (∑ x : Λ, ∑ y : Λ,
          J x y * (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ))) •
        (totalSpinHalfOpMinus Λ).mulVec (basisVec (fun _ : Λ => s)) := by
  have hcomm := heisenbergHamiltonian_commutator_totalSpinHalfOpMinus J
  have hcomm' : heisenbergHamiltonian J * totalSpinHalfOpMinus Λ =
      totalSpinHalfOpMinus Λ * heisenbergHamiltonian J :=
    sub_eq_zero.mp hcomm
  rw [Matrix.mulVec_mulVec, hcomm', ← Matrix.mulVec_mulVec,
    heisenbergHamiltonian_mulVec_basisVec_const, Matrix.mulVec_smul]

/-- Iterated form of
`heisenbergHamiltonian_mulVec_totalSpinHalfOpMinus_basisVec_const`:
for any constant `s : Fin 2` and every natural-number power `k`,
`(Ŝ_tot^-)^k · |s..s⟩` is an `H`-eigenvector with the same eigenvalue
as `|s..s⟩`. Specialised to `s = 0` (the all-up state `|Φ↑⟩`), this is
the unnormalised version of Tasaki §2.4 eq. (2.4.9), p. 33: the
ferromagnetic ground states `|Φ_M⟩ ∝ (Ŝ_tot^-)^{|Λ|S - M} · |Φ↑⟩` all
share the eigenvalue of `|Φ↑⟩`. -/
theorem heisenbergHamiltonian_mulVec_totalSpinHalfOpMinus_pow_basisVec_const
    (J : Λ → Λ → ℂ) (s : Fin 2) (k : ℕ) :
    (heisenbergHamiltonian J).mulVec
        (((totalSpinHalfOpMinus Λ) ^ k).mulVec (basisVec (fun _ : Λ => s))) =
      (∑ x : Λ, ∑ y : Λ,
          J x y * (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ))) •
        ((totalSpinHalfOpMinus Λ) ^ k).mulVec (basisVec (fun _ : Λ => s)) := by
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.one_mulVec]
    exact heisenbergHamiltonian_mulVec_basisVec_const J s
  | succ k ih =>
    have hcomm := heisenbergHamiltonian_commutator_totalSpinHalfOpMinus J
    have hcomm' : heisenbergHamiltonian J * totalSpinHalfOpMinus Λ =
        totalSpinHalfOpMinus Λ * heisenbergHamiltonian J :=
      sub_eq_zero.mp hcomm
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm',
      ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul]

/-- Iterated form of
`heisenbergHamiltonian_mulVec_totalSpinHalfOpPlus_basisVec_const`:
for any constant `s : Fin 2` and every `k : ℕ`,
`(Ŝ_tot^+)^k · |s..s⟩` is an `H`-eigenvector with the same eigenvalue
as `|s..s⟩`. Companion to the lowering version above; both are
direct corollaries of the SU(2) invariance of every Heisenberg
Hamiltonian (Tasaki §2.4, eq. (2.4.7), p. 33), iterated. -/
theorem heisenbergHamiltonian_mulVec_totalSpinHalfOpPlus_pow_basisVec_const
    (J : Λ → Λ → ℂ) (s : Fin 2) (k : ℕ) :
    (heisenbergHamiltonian J).mulVec
        (((totalSpinHalfOpPlus Λ) ^ k).mulVec (basisVec (fun _ : Λ => s))) =
      (∑ x : Λ, ∑ y : Λ,
          J x y * (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ))) •
        ((totalSpinHalfOpPlus Λ) ^ k).mulVec (basisVec (fun _ : Λ => s)) := by
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.one_mulVec]
    exact heisenbergHamiltonian_mulVec_basisVec_const J s
  | succ k ih =>
    have hcomm := heisenbergHamiltonian_commutator_totalSpinHalfOpPlus J
    have hcomm' : heisenbergHamiltonian J * totalSpinHalfOpPlus Λ =
        totalSpinHalfOpPlus Λ * heisenbergHamiltonian J :=
      sub_eq_zero.mp hcomm
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm',
      ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul]

/-! ## Commutativity with global rotation Û^(α)_θ (Tasaki §2.4 (2.4.7))

Combining `heisenbergHamiltonian_commutator_totalSpinHalfOp{1,2,3}`
with `totalSpinHalfRot{1,2,3}_commute_of_commute` gives that the
Heisenberg Hamiltonian commutes with every global rotation
`Û^(α)_θ = exp(-iθ Ŝ_tot^α)`. Composing with the constant-config
eigenvector `heisenbergHamiltonian_mulVec_basisVec_const` then shows
that the rotated state `Û^(α)_θ · |s..s⟩` shares the H-eigenvalue
with `|s..s⟩` (single-axis form). Composing axes 2 and 3 gives the
spin-coherent state `|Ξ_θ,ϕ⟩ = Û^(3)_ϕ · Û^(2)_θ · |Φ↑⟩` of Tasaki
eq. (2.4.6)/(2.4.7), formalised as
`heisenbergHamiltonian_mulVec_totalSpinHalfRot32_basisVec_const` below. -/

/-- The Heisenberg Hamiltonian commutes with the global rotation
`Û^(1)_θ = exp(-iθ Ŝ_tot^(1))` for any `θ : ℝ`. -/
theorem heisenbergHamiltonian_commute_totalSpinHalfRot1
    (J : Λ → Λ → ℂ) (θ : ℝ) :
    Commute (heisenbergHamiltonian J) (totalSpinHalfRot1 Λ θ) := by
  have hcomm : Commute (heisenbergHamiltonian J) (totalSpinHalfOp1 Λ) :=
    sub_eq_zero.mp (heisenbergHamiltonian_commutator_totalSpinHalfOp1 J)
  exact totalSpinHalfRot1_commute_of_commute Λ θ _ hcomm

/-- The Heisenberg Hamiltonian commutes with the global rotation
`Û^(2)_θ = exp(-iθ Ŝ_tot^(2))` for any `θ : ℝ`. -/
theorem heisenbergHamiltonian_commute_totalSpinHalfRot2
    (J : Λ → Λ → ℂ) (θ : ℝ) :
    Commute (heisenbergHamiltonian J) (totalSpinHalfRot2 Λ θ) := by
  have hcomm : Commute (heisenbergHamiltonian J) (totalSpinHalfOp2 Λ) :=
    sub_eq_zero.mp (heisenbergHamiltonian_commutator_totalSpinHalfOp2 J)
  exact totalSpinHalfRot2_commute_of_commute Λ θ _ hcomm

/-- The Heisenberg Hamiltonian commutes with the global rotation
`Û^(3)_θ = exp(-iθ Ŝ_tot^(3))` for any `θ : ℝ`. -/
theorem heisenbergHamiltonian_commute_totalSpinHalfRot3
    (J : Λ → Λ → ℂ) (θ : ℝ) :
    Commute (heisenbergHamiltonian J) (totalSpinHalfRot3 Λ θ) := by
  have hcomm : Commute (heisenbergHamiltonian J) (totalSpinHalfOp3 Λ) :=
    sub_eq_zero.mp (heisenbergHamiltonian_commutator_totalSpinHalfOp3 J)
  exact totalSpinHalfRot3_commute_of_commute Λ θ _ hcomm

/-- Rotated constant-spin state under axis-1 rotation shares the
H-eigenvalue with the original (Tasaki §2.4 (2.4.7), p. 33). -/
theorem heisenbergHamiltonian_mulVec_totalSpinHalfRot1_basisVec_const
    (J : Λ → Λ → ℂ) (θ : ℝ) (s : Fin 2) :
    (heisenbergHamiltonian J).mulVec
        ((totalSpinHalfRot1 Λ θ).mulVec (basisVec (fun _ : Λ => s))) =
      (∑ x : Λ, ∑ y : Λ,
          J x y * (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ))) •
        (totalSpinHalfRot1 Λ θ).mulVec (basisVec (fun _ : Λ => s)) := by
  rw [Matrix.mulVec_mulVec, (heisenbergHamiltonian_commute_totalSpinHalfRot1 J θ),
    ← Matrix.mulVec_mulVec, heisenbergHamiltonian_mulVec_basisVec_const,
    Matrix.mulVec_smul]

/-- Rotated constant-spin state under axis-2 rotation shares the
H-eigenvalue with the original (Tasaki §2.4 (2.4.7), p. 33). -/
theorem heisenbergHamiltonian_mulVec_totalSpinHalfRot2_basisVec_const
    (J : Λ → Λ → ℂ) (θ : ℝ) (s : Fin 2) :
    (heisenbergHamiltonian J).mulVec
        ((totalSpinHalfRot2 Λ θ).mulVec (basisVec (fun _ : Λ => s))) =
      (∑ x : Λ, ∑ y : Λ,
          J x y * (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ))) •
        (totalSpinHalfRot2 Λ θ).mulVec (basisVec (fun _ : Λ => s)) := by
  rw [Matrix.mulVec_mulVec, (heisenbergHamiltonian_commute_totalSpinHalfRot2 J θ),
    ← Matrix.mulVec_mulVec, heisenbergHamiltonian_mulVec_basisVec_const,
    Matrix.mulVec_smul]

/-- Rotated constant-spin state under axis-3 rotation shares the
H-eigenvalue with the original (Tasaki §2.4 (2.4.7), p. 33). -/
theorem heisenbergHamiltonian_mulVec_totalSpinHalfRot3_basisVec_const
    (J : Λ → Λ → ℂ) (θ : ℝ) (s : Fin 2) :
    (heisenbergHamiltonian J).mulVec
        ((totalSpinHalfRot3 Λ θ).mulVec (basisVec (fun _ : Λ => s))) =
      (∑ x : Λ, ∑ y : Λ,
          J x y * (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ))) •
        (totalSpinHalfRot3 Λ θ).mulVec (basisVec (fun _ : Λ => s)) := by
  rw [Matrix.mulVec_mulVec, (heisenbergHamiltonian_commute_totalSpinHalfRot3 J θ),
    ← Matrix.mulVec_mulVec, heisenbergHamiltonian_mulVec_basisVec_const,
    Matrix.mulVec_smul]

/-- Two-step rotated constant-spin state shares the H-eigenvalue: the
spin-coherent state of Tasaki §2.4 eq. (2.4.6), p. 33,
`|Ξ_θ,ϕ⟩ = Û^(3)_ϕ · Û^(2)_θ · |Φ↑⟩` (specialised at `s = 0`), is an
H-eigenvector with the same eigenvalue as the original constant
configuration. This is Tasaki eq. (2.4.7) for `S = 1/2`. -/
theorem heisenbergHamiltonian_mulVec_totalSpinHalfRot32_basisVec_const
    (J : Λ → Λ → ℂ) (θ ϕ : ℝ) (s : Fin 2) :
    (heisenbergHamiltonian J).mulVec
        ((totalSpinHalfRot3 Λ ϕ).mulVec
          ((totalSpinHalfRot2 Λ θ).mulVec (basisVec (fun _ : Λ => s)))) =
      (∑ x : Λ, ∑ y : Λ,
          J x y * (if x = y then (3 / 4 : ℂ) else (1 / 4 : ℂ))) •
        (totalSpinHalfRot3 Λ ϕ).mulVec
          ((totalSpinHalfRot2 Λ θ).mulVec (basisVec (fun _ : Λ => s))) := by
  rw [Matrix.mulVec_mulVec, (heisenbergHamiltonian_commute_totalSpinHalfRot3 J ϕ),
    ← Matrix.mulVec_mulVec,
    heisenbergHamiltonian_mulVec_totalSpinHalfRot2_basisVec_const,
    Matrix.mulVec_smul]

/-! ## Two-site singlet / triplet Casimir eigenvalues

For `Λ = Fin 2`, the natural anti-parallel basis state `|↑↓⟩` satisfies:

* `Ŝ_tot² (|↑↓⟩ - |↓↑⟩) = 0` (singlet, `S = 0`).
* `Ŝ_tot² (|↑↓⟩ + |↓↑⟩) = 2 (|↑↓⟩ + |↓↑⟩)` (triplet `m = 0`, `S = 1`).

Combined with the all-up/all-down statements, this exhausts the
`Ŝ_tot²` spectrum of two spin-1/2 particles. -/

/-- The two-site `↑↓` configuration (anti-parallel: site 0 up, site 1 down). -/
def upDown : Fin 2 → Fin 2
  | 0 => 0
  | 1 => 1

/-- `upDown` maps site 0 to spin-up. -/
lemma upDown_zero : upDown 0 = 0 := rfl
/-- `upDown` maps site 1 to spin-down. -/
lemma upDown_one : upDown 1 = 1 := rfl

/-- The two sites carry opposite spins under `upDown`. -/
lemma upDown_antiparallel : upDown 0 ≠ upDown 1 := by
  rw [upDown_zero, upDown_one]; exact zero_ne_one

/-- Explicit form of the swap of `upDown` at sites `0` and `1`. -/
lemma basisSwap_upDown :
    basisSwap upDown (0 : Fin 2) 1 = fun (i : Fin 2) =>
      match i with | 0 => 1 | 1 => 0 := by
  funext i
  unfold basisSwap upDown
  fin_cases i <;> simp

/-- Two-site singlet eigenvalue: `Ŝ_tot² (|↑↓⟩ - |↓↑⟩) = 0`. -/
theorem totalSpinHalfSquared_mulVec_two_site_singlet :
    (totalSpinHalfSquared (Fin 2)).mulVec
        (basisVec upDown - basisVec (basisSwap upDown 0 1)) = 0 := by
  rw [totalSpinHalfSquared_eq_sum_dot]
  have hzo : (0 : Fin 2) ≠ 1 := zero_ne_one
  have hoz : (1 : Fin 2) ≠ 0 := one_ne_zero
  have hud_swap : basisSwap upDown 1 0 = basisSwap upDown 0 1 := by
    funext i; unfold basisSwap upDown
    fin_cases i <;> simp
  -- Distribute the double sum into 4 terms
  rw [show (∑ x : Fin 2, ∑ y : Fin 2, spinHalfDot x y :) =
      spinHalfDot 0 0 + spinHalfDot 0 1 + spinHalfDot 1 0 + spinHalfDot 1 1 from by
    simp [Fin.sum_univ_two]; abel]
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec]
  -- Each diagonal term = (3/4)·1, off-diagonal terms = -(3/4)
  rw [spinHalfDot_self, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [spinHalfDot_self, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [spinHalfDot_mulVec_singlet hzo upDown upDown_antiparallel]
  rw [spinHalfDot_comm 1 0]
  rw [spinHalfDot_mulVec_singlet hzo upDown upDown_antiparallel]
  -- Now: (3/4)·v + -(3/4)·v + -(3/4)·v + (3/4)·v = 0
  set v : (Fin 2 → Fin 2) → ℂ := basisVec upDown - basisVec (basisSwap upDown 0 1)
  change (3 / 4 : ℂ) • v + -(3 / 4 : ℂ) • v + -(3 / 4 : ℂ) • v + (3 / 4 : ℂ) • v = 0
  module

/-- Two-site triplet `m = 0` eigenvalue: `Ŝ_tot² (|↑↓⟩ + |↓↑⟩) = 2 (|↑↓⟩ + |↓↑⟩)`. -/
theorem totalSpinHalfSquared_mulVec_two_site_triplet_zero :
    (totalSpinHalfSquared (Fin 2)).mulVec
        (basisVec upDown + basisVec (basisSwap upDown 0 1)) =
      (2 : ℂ) • (basisVec upDown + basisVec (basisSwap upDown 0 1)) := by
  rw [totalSpinHalfSquared_eq_sum_dot]
  have hzo : (0 : Fin 2) ≠ 1 := zero_ne_one
  rw [show (∑ x : Fin 2, ∑ y : Fin 2, spinHalfDot x y :) =
      spinHalfDot 0 0 + spinHalfDot 0 1 + spinHalfDot 1 0 + spinHalfDot 1 1 from by
    simp [Fin.sum_univ_two]; abel]
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec]
  rw [spinHalfDot_self, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [spinHalfDot_self, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [spinHalfDot_mulVec_triplet_anti hzo upDown upDown_antiparallel]
  rw [spinHalfDot_comm 1 0]
  rw [spinHalfDot_mulVec_triplet_anti hzo upDown upDown_antiparallel]
  set v : (Fin 2 → Fin 2) → ℂ := basisVec upDown + basisVec (basisSwap upDown 0 1)
  change (3 / 4 : ℂ) • v + (1 / 4 : ℂ) • v + (1 / 4 : ℂ) • v + (3 / 4 : ℂ) • v =
       (2 : ℂ) • v
  module

/-- The two-site singlet is annihilated by `Ŝ_tot^(3)`: zero magnetization. -/
theorem totalSpinHalfOp3_mulVec_two_site_singlet :
    (totalSpinHalfOp3 (Fin 2)).mulVec
        (basisVec upDown - basisVec (basisSwap upDown 0 1)) = 0 := by
  rw [Matrix.mulVec_sub]
  rw [totalSpinHalfOp3_mulVec_basisVec]
  rw [totalSpinHalfOp3_mulVec_basisVec]
  -- Σ spinHalfSign upDown = (1/2) + (-1/2) = 0
  have h_ud : ∑ x : Fin 2, spinHalfSign (upDown x) = 0 := by
    rw [Fin.sum_univ_two]
    simp [upDown_zero, upDown_one, spinHalfSign]
  -- For swap σ x = 1, swap σ y = 0: Σ spinHalfSign = (-1/2) + (1/2) = 0
  have h_swap : ∑ x : Fin 2, spinHalfSign (basisSwap upDown 0 1 x) = 0 := by
    rw [Fin.sum_univ_two]
    rw [basisSwap_upDown]; simp [spinHalfSign]
  rw [h_ud, h_swap, zero_smul, zero_smul, sub_self]


end LatticeSystem.Quantum
