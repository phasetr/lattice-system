import LatticeSystem.Quantum.SpinS.Theorem23Local


/-!
# Tasaki §2.5 Theorem 2.3 predicted data bridges

This file contains the predicted-Casimir, predicted-GS, and cross-ladder
bridge layer used by the adjacent-sector chain for
Tasaki §2.5 Theorem 2.3.

It is split from `Theorem23.lean` so the adjacent common-energy chain
can import the predicted-data API without keeping these bridge proofs in
the same elaboration unit. The predicted-GS ladder-closure and
scalar-cancellation suffix is split into `Theorem23PredictedLadder.lean`,
and the source-weight / lowering-predecessor suffix is split into
`Theorem23PredictedSourceWeight.lean`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.

Tracked in Issue #412 (Tasaki §2.5: Marshall–Lieb–Mattis theorem).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 real lowering endpoint inequality**:
inside the spin interval and strictly above the lowest weight, the
lowering-kernel value is strictly below `S(S+1)`. -/
private theorem tasaki23_lowering_kernel_lt_predicted_of_m_interval {S m : ℝ}
    (hleft : -S < m) (hright : m ≤ S) :
    m * (m - 1) < S * (S + 1) := by
  have hpos_left : 0 < S + m := by nlinarith
  have hpos_right : 0 < S - m + 1 := by nlinarith
  have hprod : 0 < (S + m) * (S - m + 1) :=
    mul_pos hpos_left hpos_right
  have hdiff : S * (S + 1) - m * (m - 1) =
      (S + m) * (S - m + 1) := by
    ring
  nlinarith

/-- **Tasaki §2.5 Theorem 2.3 real raising endpoint inequality**:
inside the spin interval and strictly below the highest weight, the
raising-kernel value is strictly below `S(S+1)`. -/
private theorem tasaki23_raising_kernel_lt_predicted_of_m_interval {S m : ℝ}
    (hleft : -S ≤ m) (hright : m < S) :
    m * (m + 1) < S * (S + 1) := by
  have hpos_left : 0 < S - m := by nlinarith
  have hpos_right : 0 < S + m + 1 := by nlinarith
  have hprod : 0 < (S - m) * (S + m + 1) :=
    mul_pos hpos_left hpos_right
  have hdiff : S * (S + 1) - m * (m + 1) =
      (S - m) * (S + m + 1) := by
    ring
  nlinarith

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 lowering endpoint mismatch, real form**:
for every admissible sector strictly before the right endpoint, the
lowering-kernel Casimir value is strictly smaller than the predicted
Casimir `S_tot(S_tot+1)`. -/
theorem tasaki23_lowering_kernel_value_lt_predictedCasimirValue_of_mem_of_lt_right
    (A : V → Bool) (N : ℕ) {M : ℕ}
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N) :
    (((Fintype.card V : ℝ) * (N : ℝ) / 2 - (M : ℝ)) *
        (((Fintype.card V : ℝ) * (N : ℝ) / 2 - (M : ℝ)) - 1)) <
      tasaki23PredictedCasimirValue (V := V) A N := by
  classical
  let cA := (Finset.univ.filter (fun x : V => A x = true)).card
  let cB := (Finset.univ.filter (fun x : V => (! A x) = true)).card
  let left := min cA cB * N
  let right := max cA cB * N
  let S := tasaki23PredictedTotalSpin (V := V) A N
  let m := ((Fintype.card V : ℝ) * (N : ℝ) / 2 - (M : ℝ))
  have hbounds := (tasaki23GroundStateSectors_mem_iff (V := V) A N M).mp hM
  have hleft_le_M : left ≤ M := by simpa [left, cA, cB] using hbounds.1
  have hleft_le_right : left ≤ right := by
    exact Nat.mul_le_mul_right N min_le_max
  have hS_eq_nat : S = (((right - left : ℕ) : ℝ) / 2) := by
    simpa [S, left, right, cA, cB] using
      tasaki23PredictedTotalSpin_eq_sector_half_width (V := V) A N
  have hS_eq : S = ((right : ℝ) - (left : ℝ)) / 2 := by
    have hsub_cast : ((right - left : ℕ) : ℝ) = (right : ℝ) - (left : ℝ) := by
      have hsub_add : ((right - left : ℕ) : ℝ) + (left : ℝ) = (right : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel hleft_le_right
      nlinarith
    rw [hS_eq_nat, hsub_cast]
  have hcard_sum : cA + cB = Fintype.card V := by
    simpa [cA, cB] using tasaki23_card_filter_A_add_card_notA (V := V) A
  have hminmax : min cA cB + max cA cB = cA + cB := min_add_max cA cB
  have hcard_mul : Fintype.card V * N = left + right := by
    calc
      Fintype.card V * N = (cA + cB) * N := by rw [hcard_sum]
      _ = (min cA cB + max cA cB) * N := by rw [hminmax]
      _ = left + right := by rw [Nat.add_mul]
  have hcenter : (Fintype.card V : ℝ) * (N : ℝ) / 2 =
      ((left : ℝ) + (right : ℝ)) / 2 := by
    have hcast : ((Fintype.card V * N : ℕ) : ℝ) = ((left + right : ℕ) : ℝ) := by
      exact_mod_cast hcard_mul
    rw [← Nat.cast_mul, hcast, Nat.cast_add]
  have hleft_le_M_real : (left : ℝ) ≤ (M : ℝ) := by exact_mod_cast hleft_le_M
  have hM_lt_right_real : (M : ℝ) < (right : ℝ) := by
    simpa [right, cA, cB] using (show (M : ℝ) <
      (max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N : ℝ) from
        (by exact_mod_cast hMlt))
  have hm_le_S : m ≤ S := by
    dsimp [m]
    rw [hcenter, hS_eq]
    nlinarith
  have hnegS_lt_m : -S < m := by
    dsimp [m]
    rw [hcenter, hS_eq]
    nlinarith
  have hlt := tasaki23_lowering_kernel_lt_predicted_of_m_interval
    (S := S) (m := m) hnegS_lt_m hm_le_S
  simpa [tasaki23PredictedCasimirValue, S, m] using hlt

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 raising endpoint mismatch, real form**:
for every admissible source sector strictly above the left endpoint, the
raising-kernel Casimir value is strictly smaller than the predicted
Casimir `S_tot(S_tot+1)`. -/
theorem tasaki23_raising_kernel_value_lt_predictedCasimirValue_of_mem_of_left_lt
    (A : V → Bool) (N : ℕ) {M : ℕ}
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1) :
    (((Fintype.card V : ℝ) * (N : ℝ) / 2 - ((M + 1 : ℕ) : ℝ)) *
        (((Fintype.card V : ℝ) * (N : ℝ) / 2 - ((M + 1 : ℕ) : ℝ)) + 1)) <
      tasaki23PredictedCasimirValue (V := V) A N := by
  classical
  let cA := (Finset.univ.filter (fun x : V => A x = true)).card
  let cB := (Finset.univ.filter (fun x : V => (! A x) = true)).card
  let left := min cA cB * N
  let right := max cA cB * N
  let S := tasaki23PredictedTotalSpin (V := V) A N
  let m := ((Fintype.card V : ℝ) * (N : ℝ) / 2 - ((M + 1 : ℕ) : ℝ))
  have hbounds := (tasaki23GroundStateSectors_mem_iff (V := V) A N (M + 1)).mp hM
  have hM_le_right : M + 1 ≤ right := by simpa [right, cA, cB] using hbounds.2
  have hleft_le_right : left ≤ right := by
    exact Nat.mul_le_mul_right N min_le_max
  have hS_eq_nat : S = (((right - left : ℕ) : ℝ) / 2) := by
    simpa [S, left, right, cA, cB] using
      tasaki23PredictedTotalSpin_eq_sector_half_width (V := V) A N
  have hS_eq : S = ((right : ℝ) - (left : ℝ)) / 2 := by
    have hsub_cast : ((right - left : ℕ) : ℝ) = (right : ℝ) - (left : ℝ) := by
      have hsub_add : ((right - left : ℕ) : ℝ) + (left : ℝ) = (right : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel hleft_le_right
      nlinarith
    rw [hS_eq_nat, hsub_cast]
  have hcard_sum : cA + cB = Fintype.card V := by
    simpa [cA, cB] using tasaki23_card_filter_A_add_card_notA (V := V) A
  have hminmax : min cA cB + max cA cB = cA + cB := min_add_max cA cB
  have hcard_mul : Fintype.card V * N = left + right := by
    calc
      Fintype.card V * N = (cA + cB) * N := by rw [hcard_sum]
      _ = (min cA cB + max cA cB) * N := by rw [hminmax]
      _ = left + right := by rw [Nat.add_mul]
  have hcenter : (Fintype.card V : ℝ) * (N : ℝ) / 2 =
      ((left : ℝ) + (right : ℝ)) / 2 := by
    have hcast : ((Fintype.card V * N : ℕ) : ℝ) = ((left + right : ℕ) : ℝ) := by
      exact_mod_cast hcard_mul
    rw [← Nat.cast_mul, hcast, Nat.cast_add]
  have hM_le_right_real : ((M + 1 : ℕ) : ℝ) ≤ (right : ℝ) := by
    exact_mod_cast hM_le_right
  have hleft_lt_M_real : (left : ℝ) < ((M + 1 : ℕ) : ℝ) := by
    simpa [left, cA, cB] using (show
      (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N : ℝ) <
          ((M + 1 : ℕ) : ℝ) from
        (by exact_mod_cast hMlt))
  have hnegS_le_m : -S ≤ m := by
    dsimp [m]
    rw [hcenter, hS_eq]
    nlinarith
  have hm_lt_S : m < S := by
    dsimp [m]
    rw [hcenter, hS_eq]
    nlinarith
  have hlt := tasaki23_raising_kernel_lt_predicted_of_m_interval
    (S := S) (m := m) hnegS_le_m hm_lt_S
  simpa [tasaki23PredictedCasimirValue, S, m] using hlt

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 lowering endpoint mismatch, complex form**:
the predicted Casimir value is not the lowering-kernel value in any
admissible sector strictly before the right endpoint. This is the
`hγ_ne` form used by the Casimir non-vanishing successor wrapper. -/
theorem tasaki23_predictedCasimirValue_ne_lowering_kernel_value_of_mem_of_lt_right
    (A : V → Bool) (N : ℕ) {M : ℕ}
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N) :
    (tasaki23PredictedCasimirValue (V := V) A N : ℂ) ≠
      ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) *
        ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) - 1)) := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre
  have hlt :=
    tasaki23_lowering_kernel_value_lt_predictedCasimirValue_of_mem_of_lt_right
      (V := V) A N hM hMlt
  nlinarith

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 raising endpoint mismatch, complex form**:
the predicted Casimir value is not the raising-kernel value in any
admissible source sector strictly above the left endpoint. This is the
`hγ_ne` form used by the Casimir non-vanishing predecessor wrapper. -/
theorem tasaki23_predictedCasimirValue_ne_raising_kernel_value_of_mem_of_left_lt
    (A : V → Bool) (N : ℕ) {M : ℕ}
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1) :
    (tasaki23PredictedCasimirValue (V := V) A N : ℂ) ≠
      ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) *
        ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) + 1)) := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre
  have hlt :=
    tasaki23_raising_kernel_value_lt_predictedCasimirValue_of_mem_of_left_lt
      (V := V) A N hM hMlt
  have hM1 : (((M + 1 : ℕ) : ℝ)) = (M : ℝ) + 1 := by norm_num
  rw [hM1] at hlt
  nlinarith

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 predicted Casimir value, canonical
orientation**: if the complement sublattice is no larger than `A`, then
the absolute value in `tasaki23PredictedTotalSpin` drops to
`|A| - |¬A|`, and `tasaki23PredictedCasimirValue` is the canonical
joint-Casimir target used in `bipartiteToyGroundStateSubspacePredicted`.
-/
theorem tasaki23PredictedCasimirValue_eq_canonical_of_card_notA_le_cardA
    (A : V → Bool) (N : ℕ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card) :
    tasaki23PredictedCasimirValue (V := V) A N =
      ((((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) *
              ((N : ℝ) / 2) -
            ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) *
              ((N : ℝ) / 2)) *
        ((((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) *
              ((N : ℝ) / 2) -
            ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) *
              ((N : ℝ) / 2)) + 1)) := by
  have hnonneg :
      0 ≤ ((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hBA)
  unfold tasaki23PredictedCasimirValue tasaki23PredictedTotalSpin
  rw [abs_of_nonneg hnonneg]
  ring

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS total-Casimir bridge**:
in the canonical orientation `|¬A| ≤ |A|`, membership in the predicted
toy ground-state subspace gives exactly the
`tasaki23PredictedCasimirValue` total-Casimir eigenvector hypothesis.

This packages the definitional total-Casimir component of
`bipartiteToyGroundStateSubspacePredicted` in the form used by the
adjacent-sector Theorem 2.3 chain. -/
theorem tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (totalSpinSSquared V N).mulVec Ψ =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) • Ψ := by
  have hmem :=
    bipartiteToyGroundStateSubspacePredicted_le_totalSpinSSquaredEigenspace
      (Λ := V) A N hΨ
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hmem
  rw [tasaki23PredictedCasimirValue_eq_canonical_of_card_notA_le_cardA
    (V := V) A N hBA]
  simpa using hmem

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS `A`-sublattice Casimir
bridge**: membership in the predicted toy ground-state subspace gives
the maximum `A`-sublattice Casimir eigenvector identity.

This packages the definitional `(Ŝ_A)^2` component of
`bipartiteToyGroundStateSubspacePredicted` for the later sublattice
ladder comparison. -/
theorem tasaki23_sublatticeSpinSquaredS_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSquaredS N A).mulVec Ψ =
      ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) • Ψ := by
  have hmem :=
    bipartiteToyGroundStateSubspacePredicted_le_sublatticeSpinSquaredSEigenspace
      (Λ := V) A N hΨ
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hmem
  simpa using hmem

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS complement-sublattice Casimir
bridge**: membership in the predicted toy ground-state subspace gives
the maximum `¬A`-sublattice Casimir eigenvector identity.

This is the complement companion to
`tasaki23_sublatticeSpinSquaredS_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted`. -/
theorem tasaki23_sublatticeSpinSquaredS_complement_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSquaredS N (fun x => !A x)).mulVec Ψ =
      ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) • Ψ := by
  have hmem :=
    bipartiteToyGroundStateSubspacePredicted_le_sublatticeSpinSquaredS_complementEigenspace
      (Λ := V) A N hΨ
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hmem
  simpa using hmem

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS toy-Hamiltonian bridge**:
membership in the predicted toy ground-state subspace gives the
predicted toy-Hamiltonian eigenvector identity.

This packages the Casimir-decomposition eigenspace inclusion in pointwise
`mulVec` form, so the later sublattice comparison can use the cross
spin-dot part of the toy Hamiltonian without reopening the joint
eigenspace definition. -/
theorem tasaki23_heisenbergToyHamiltonianS_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (heisenbergToyHamiltonianS (Λ := V) A N).mulVec Ψ =
      bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ := by
  have hmem :=
    bipartiteToyGroundStateSubspacePredicted_le_heisenbergToyHamiltonianS_eigenspace
      (Λ := V) A N hΨ
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hmem
  simpa using hmem

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS cross-dot bridge**:
membership in the predicted toy ground-state subspace gives the pointwise
eigenvector identity for `2 • Ŝ_A · Ŝ_¬A`.

Together with the ladder expansion of `Ŝ_A · Ŝ_¬A`, this is the operator
identity that connects the predicted-GS Casimir structure to the
remaining comparison between the `A` and `¬A` lowering components. -/
theorem tasaki23_two_sublatticeSpinSDot_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    ((2 : ℂ) • sublatticeSpinSDot N A (fun x => ! A x)).mulVec Ψ =
      bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ := by
  rw [← heisenbergToyHamiltonianS_eq_two_sublatticeSpinSDot (Λ := V) (N := N) A]
  exact
    tasaki23_heisenbergToyHamiltonianS_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
      (V := V) A N hΨ

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS cross-ladder bridge**:
membership in the predicted toy ground-state subspace gives the pointwise
eigenvector identity for twice the ladder-expanded cross spin-dot
operator.

This is the exact operator form used to separate the `Ŝ_A^+ Ŝ_¬A^-` and
`Ŝ_A^- Ŝ_¬A^+` terms in the remaining sublattice lowering comparison. -/
theorem tasaki23_two_cross_ladder_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    ((2 : ℂ) •
      (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x) +
        (1 / 2 : ℂ) •
          (sublatticeSpinSOpPlus N A * sublatticeSpinSOpMinus N (fun x => ! A x) +
            sublatticeSpinSOpMinus N A *
              sublatticeSpinSOpPlus N (fun x => ! A x)))).mulVec Ψ =
      bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ := by
  rw [← sublatticeSpinSDot_eq_op3_add_ladder (Λ := V) (N := N) A (fun x => ! A x)]
  exact
    tasaki23_two_sublatticeSpinSDot_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
      (V := V) A N hΨ

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS cross-ladder isolation**:
membership in the predicted toy ground-state subspace isolates the sum
of the two cross-ladder products as the predicted toy energy term minus
twice the `S^3_A S^3_¬A` contribution.

This is the algebraic form used after the cross-dot bridge: the remaining
component comparison can now refer directly to
`Ŝ_A^+ Ŝ_¬A^- + Ŝ_A^- Ŝ_¬A^+` instead of the full dot product. -/
theorem
    tasaki23_cross_ladder_sum_mulVec_eq_energy_sub_two_op3_of_predictedGS
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSOpPlus N A * sublatticeSpinSOpMinus N (fun x => ! A x) +
        sublatticeSpinSOpMinus N A * sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec Ψ =
      bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
        ((2 : ℂ) •
          (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ := by
  let Z : ManyBodyOpS V N :=
    sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x)
  let L : ManyBodyOpS V N :=
    sublatticeSpinSOpPlus N A * sublatticeSpinSOpMinus N (fun x => ! A x) +
      sublatticeSpinSOpMinus N A * sublatticeSpinSOpPlus N (fun x => ! A x)
  change L.mulVec Ψ =
    bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ - ((2 : ℂ) • Z).mulVec Ψ
  have hbridge :
      ((2 : ℂ) • (Z + (1 / 2 : ℂ) • L)).mulVec Ψ =
        bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ := by
    dsimp [Z, L]
    exact
      tasaki23_two_cross_ladder_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ
  rw [← hbridge]
  have hop : (2 : ℂ) • (Z + (1 / 2 : ℂ) • L) = (2 : ℂ) • Z + L := by
    ext σ τ
    simp [Z, L]
    ring
  rw [hop]
  ext σ
  rw [Matrix.add_mulVec]
  rw [Matrix.add_mulVec]
  rw [Matrix.add_mulVec]
  simp [Matrix.smul_mulVec]

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS sequential cross-ladder
identity**: the isolated cross-ladder sum can be read as the sum of the
two sequential actions `Ŝ_A^+ (Ŝ_¬A^- Ψ)` and
`Ŝ_A^- (Ŝ_¬A^+ Ψ)`.

This is the component-comparison form of the predicted-GS cross-ladder
constraint: it exposes the two lowered pieces that the remaining
Marshall-positivity argument compares. -/
theorem
    tasaki23_cross_ladder_sequential_mulVec_eq_energy_sub_two_op3_of_predictedGS
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSOpPlus N A).mulVec
        ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) +
      (sublatticeSpinSOpMinus N A).mulVec
        ((sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec Ψ) =
      bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
        ((2 : ℂ) •
          (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ := by
  rw [← tasaki23_cross_ladder_sum_mulVec_eq_energy_sub_two_op3_of_predictedGS
    (V := V) A N hΨ]
  ext σ
  rw [Matrix.add_mulVec]
  rw [Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_mulVec]

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS raised-lowered component
identity**: the sequential cross-ladder identity can be read as applying
the opposite sublattice raising operators to the two lowered components
`Ŝ_¬A^- Ψ` and `Ŝ_A^- Ψ`.

This is the component-comparison form used before the remaining
Marshall-positivity step: both summands now act directly on one of the
two lowered sublattice components whose pointwise sizes must be compared.
-/
theorem
    tasaki23_cross_ladder_raised_lowered_components_eq_energy_sub_two_op3_of_predictedGS
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSOpPlus N A).mulVec
        ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) +
      (sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec
        ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
      bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
        ((2 : ℂ) •
          (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ := by
  rw [← tasaki23_cross_ladder_sequential_mulVec_eq_energy_sub_two_op3_of_predictedGS
    (V := V) A N hΨ]
  have hterm :
      (sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec
          ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
        (sublatticeSpinSOpMinus N A).mulVec
          ((sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec Ψ) := by
    have hcomm :
        sublatticeSpinSOpMinus N A * sublatticeSpinSOpPlus N (fun x => ! A x) =
          sublatticeSpinSOpPlus N (fun x => ! A x) * sublatticeSpinSOpMinus N A :=
      (sublatticeSpinSOpMinus_cross_commute_plus N A).eq
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [← hcomm]
  rw [hterm]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 re-embedded source-sector cross-ladder
site sums**: after the two lowered components are known to lie in the
successor magnetization eigenspace, re-embed their sector restrictions
and evaluate the raised-lowered cross-ladder identity at a source-sector
configuration.

The left-hand side is now expressed as the on-`A` and off-`A`
single-site raising sums applied to the sector restrictions of
`Ŝ_¬A^- Ψ` and `Ŝ_A^- Ψ`.  This is the component form needed before the
remaining local Marshall-signed coefficient comparison. -/
theorem
    tasaki23_cross_ladder_reembedded_source_site_sum_eq_energy_sub_two_op3_of_predictedGS
    (A : V → Bool) (N : ℕ) {M : ℕ} {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hA_mag :
      ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)))
    (hB_mag :
      ((sublatticeSpinSOpMinus N (fun x => !A x)).mulVec Ψ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)))
    (σ : magConfigS V N M) :
    (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding
            (magSectorRestriction (M := M + 1)
              ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)))) σ.1) +
      ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding
            (magSectorRestriction (M := M + 1)
              ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) σ.1 =
      (bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
        ((2 : ℂ) •
          (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ)
        σ.1 := by
  have hcross :=
    tasaki23_cross_ladder_raised_lowered_components_eq_energy_sub_two_op3_of_predictedGS
      (V := V) A N hΨ
  have hA_embed :
      magSectorEmbedding
          (magSectorRestriction (M := M + 1)
            ((sublatticeSpinSOpMinus N A).mulVec Ψ)) =
        (sublatticeSpinSOpMinus N A).mulVec Ψ :=
    magSectorEmbedding_magSectorRestriction_of_mem_magSubspaceS
      (V := V) (N := N) (M := M + 1) hA_mag
  have hB_embed :
      magSectorEmbedding
          (magSectorRestriction (M := M + 1)
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)) =
        (sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ :=
    magSectorEmbedding_magSectorRestriction_of_mem_magSubspaceS
      (V := V) (N := N) (M := M + 1) hB_mag
  have hcomponent := congrFun hcross σ.1
  rw [← hB_embed, ← hA_embed] at hcomponent
  rw [Pi.add_apply] at hcomponent
  rw [sublatticeSpinSOpPlus_mulVec_magSectorEmbedding_apply_eq_onA_site_sum,
    sublatticeSpinSOpPlus_complement_mulVec_magSectorEmbedding_apply_eq_offA_site_sum]
    at hcomponent
  simpa [Pi.add_apply] using hcomponent

end LatticeSystem.Quantum
