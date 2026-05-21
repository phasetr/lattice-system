import LatticeSystem.Quantum.SpinS.Theorem23Local


/-!
# Tasaki §2.5 Theorem 2.3 predicted data bridges

This file contains the predicted-Casimir, predicted-GS, cross-ladder,
source-weight, and sector-embedded predicted-Casimir bridge layer used
by the adjacent-sector chain for Tasaki §2.5 Theorem 2.3.

It is split from `Theorem23.lean` so the adjacent common-energy chain
can import the predicted-data API without keeping these bridge proofs in
the same elaboration unit.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.

Tracked in Issue #412 (Tasaki §2.5: Marshall–Lieb–Mattis theorem).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 single-site lowering predecessor**:
if a target configuration `τ` in sector `M + 1` has positive local
value at `x`, lowering that local value by one gives a configuration
in sector `M`.

This private copy keeps the interval-chain module from exporting the
local bookkeeping lemma while preserving the moved local module's public
API surface. -/
private theorem magSumS_single_site_lowering_predecessor {M : ℕ}
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val) :
    magSumS
        (Function.update τ.1 x
          ⟨(τ.1 x).val - 1, by omega⟩) = M := by
  classical
  have hsum_succ :
      magSumS
          (Function.update τ.1 x
            ⟨(τ.1 x).val - 1, by omega⟩) + 1 = magSumS τ.1 := by
    unfold magSumS
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ x)]
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ x)]
    simp only [Function.update_self]
    have hrest :
        (∑ y ∈ (Finset.univ : Finset V) \ {x},
            (Function.update τ.1 x
              ⟨(τ.1 x).val - 1, by omega⟩ y).val) =
          ∑ y ∈ (Finset.univ : Finset V) \ {x}, (τ.1 y).val := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyx : y ≠ x := by
        simpa using hy
      rw [Function.update_of_ne hyx]
    rw [hrest]
    have hpred_val :
        (⟨(τ.1 x).val - 1, by
          omega⟩ : Fin (N + 1)).val + 1 = (τ.1 x).val := by
      simp
      omega
    omega
  have hτ : magSumS τ.1 = M + 1 := τ.2
  omega

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

/-- **Tasaki §2.5 Theorem 2.3 single-site `S^3` source weight**:
the diagonal on-site `Ŝ_x^3` action multiplies an arbitrary vector by the
local source weight `N / 2 - σ x` at configuration `σ`.

This is the local diagonal-action bridge needed to evaluate the
`Ŝ_A^3 Ŝ_¬A^3` term in the re-embedded cross-ladder identity. -/
theorem onSiteS_spinSOp3_mulVec_apply
    (x : V) (N : ℕ) (Φ : (V → Fin (N + 1)) → ℂ) (σ : V → Fin (N + 1)) :
    ((onSiteS x (spinSOp3 N) : ManyBodyOpS V N).mulVec Φ) σ =
      ((N : ℂ) / 2 - ((σ x).val : ℂ)) * Φ σ := by
  classical
  change ∑ τ, (onSiteS x (spinSOp3 N) : ManyBodyOpS V N) σ τ * Φ τ =
    ((N : ℂ) / 2 - ((σ x).val : ℂ)) * Φ σ
  rw [Finset.sum_eq_single σ]
  · rw [onSiteS_apply_diag, spinSOp3_apply_diag]
  · intro τ _hτ hτσ
    rw [onSiteS_apply]
    by_cases hoff : ∀ k, k ≠ x → σ k = τ k
    · rw [if_pos hoff]
      have hx : σ x ≠ τ x := by
        intro hxeq
        apply hτσ
        funext k
        by_cases hk : k = x
        · subst k
          exact hxeq.symm
        · exact (hoff k hk).symm
      simp [spinSOp3_apply_offdiag N hx]
    · rw [if_neg hoff, zero_mul]
  · intro hσ
    simp at hσ

/-- **Tasaki §2.5 Theorem 2.3 sublattice `S^3` source weight**:
the on-`A` sublattice `Ŝ_A^3` action multiplies an arbitrary vector by the
sum of the local `S^3` weights over sites in `A`.

This is the sublattice diagonal-action bridge used to evaluate the
right-hand side of the re-embedded cross-ladder identity at source-sector
configurations. -/
theorem sublatticeSpinSOp3_mulVec_apply_eq_onA_weight
    (A : V → Bool) (N : ℕ) (Φ : (V → Fin (N + 1)) → ℂ)
    (σ : V → Fin (N + 1)) :
    ((sublatticeSpinSOp3 N A).mulVec Φ) σ =
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        ((N : ℂ) / 2 - ((σ x).val : ℂ))) * Φ σ := by
  classical
  rw [sublatticeSpinSOp3, Matrix.sum_mulVec, Finset.sum_apply]
  calc
    (∑ c : V,
      Matrix.mulVec (if A c = true then onSiteS c (spinSOp3 N) else 0) Φ σ) =
        ∑ c : V, if A c = true then
          ((N : ℂ) / 2 - ((σ c).val : ℂ)) * Φ σ
        else 0 := by
          apply Finset.sum_congr rfl
          intro x _hx
          by_cases hA : A x = true
          · simp [hA, onSiteS_spinSOp3_mulVec_apply]
          · cases hx : A x <;> simp [hx] at hA ⊢
    _ = ∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        ((N : ℂ) / 2 - ((σ x).val : ℂ)) * Φ σ := by
          rw [Finset.sum_filter]
    _ = (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        ((N : ℂ) / 2 - ((σ x).val : ℂ))) * Φ σ := by
          rw [Finset.sum_mul]

/-- **Tasaki §2.5 Theorem 2.3 complement sublattice `S^3` source weight**:
the `Ŝ_¬A^3` action multiplies an arbitrary vector by the sum of the local
`S^3` weights over sites outside `A`.

This packages the complement sublattice with the `A x = false` filter used
by the local coefficient comparison. -/
theorem sublatticeSpinSOp3_complement_mulVec_apply_eq_offA_weight
    (A : V → Bool) (N : ℕ) (Φ : (V → Fin (N + 1)) → ℂ)
    (σ : V → Fin (N + 1)) :
    ((sublatticeSpinSOp3 N (fun x => ! A x)).mulVec Φ) σ =
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        ((N : ℂ) / 2 - ((σ x).val : ℂ))) * Φ σ := by
  classical
  rw [sublatticeSpinSOp3_mulVec_apply_eq_onA_weight]
  congr 1
  apply Finset.sum_congr
  · ext x
    cases A x <;> simp
  · intro x _hx
    rfl

/-- **Tasaki §2.5 Theorem 2.3 cross-sublattice `S^3` source weight**:
the diagonal product `Ŝ_A^3 Ŝ_¬A^3` multiplies an arbitrary vector by the
product of the on-`A` and off-`A` local `S^3` weight sums.

This is the right-hand-side evaluation bridge for the re-embedded
cross-ladder source-sector identity. -/
theorem
    sublatticeSpinSOp3_mul_complement_mulVec_apply_eq_onA_offA_weight
    (A : V → Bool) (N : ℕ) (Φ : (V → Fin (N + 1)) → ℂ)
    (σ : V → Fin (N + 1)) :
    ((sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x)).mulVec Φ) σ =
      ((∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
          ((N : ℂ) / 2 - ((σ x).val : ℂ))) *
        (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
          ((N : ℂ) / 2 - ((σ x).val : ℂ)))) * Φ σ := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinSOp3_mulVec_apply_eq_onA_weight]
  rw [sublatticeSpinSOp3_complement_mulVec_apply_eq_offA_weight]
  ring

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 re-embedded cross-ladder source-weight RHS**:
the re-embedded source-sector cross-ladder site-sum identity can be
rewritten with the explicit `Ŝ_A^3 Ŝ_¬A^3` source-weight product on the
right-hand side.

This substitutes the diagonal `S^3` source-weight evaluation into the
non-ladder term, leaving a scalar multiple of the source coefficient
`Ψ σ`. -/
theorem
    tasaki23_cross_ladder_reembedded_source_site_sum_eq_energy_sub_two_sublattice_weight_product_of_predictedGS
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
      (bipartiteToyMinEnergyPredicted (Λ := V) A N -
        (2 : ℂ) *
          ((∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
              ((N : ℂ) / 2 - ((σ.1 x).val : ℂ))) *
            (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
              ((N : ℂ) / 2 - ((σ.1 x).val : ℂ))))) * Ψ σ.1 := by
  rw [tasaki23_cross_ladder_reembedded_source_site_sum_eq_energy_sub_two_op3_of_predictedGS
    (V := V) A N hΨ hA_mag hB_mag σ]
  rw [Pi.sub_apply, Pi.smul_apply, Matrix.smul_mulVec, Pi.smul_apply]
  rw [sublatticeSpinSOp3_mul_complement_mulVec_apply_eq_onA_offA_weight]
  simp [smul_eq_mul]
  ring_nf

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 source-weight identity at a lowering
predecessor**: the re-embedded scalar cross-ladder identity can be
specialized to the source-sector predecessor obtained from a successor
configuration `τ` by lowering a site `x`.

This aligns the source-weight equation with the exact predecessor
configuration used in `tasaki23LoweringPredecessorSignedCoefficient`. -/
theorem
    tasaki23_cross_ladder_reembedded_source_weight_eq_lowering_predecessor_of_predictedGS
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
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val) :
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    (∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
        ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding
            (magSectorRestriction (M := M + 1)
              ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
      ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
        ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding
            (magSectorRestriction (M := M + 1)
              ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred =
      (bipartiteToyMinEnergyPredicted (Λ := V) A N -
        (2 : ℂ) *
          ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
              ((N : ℂ) / 2 - ((pred y).val : ℂ))) *
            (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
              ((N : ℂ) / 2 - ((pred y).val : ℂ))))) * Ψ pred := by
  classical
  dsimp only
  exact
    tasaki23_cross_ladder_reembedded_source_site_sum_eq_energy_sub_two_sublattice_weight_product_of_predictedGS
      (V := V) A N hΨ hA_mag hB_mag
      ⟨Function.update τ.1 x ⟨(τ.1 x).val - 1, by omega⟩,
        magSumS_single_site_lowering_predecessor τ x hx⟩

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 real source-weight RHS at a lowering
predecessor**: for a Marshall-positive sector embedding, the real part
of the predecessor source-weight right-hand side is the real predicted
toy energy minus twice the real on-`A`/off-`A` source-weight product,
times the signed positive sector coefficient at the predecessor.

This is the real-valued form of the scalar RHS exposed by
`tasaki23_cross_ladder_reembedded_source_weight_eq_lowering_predecessor_of_predictedGS`.
-/
theorem
    tasaki23_cross_ladder_reembedded_source_weight_lowering_predecessor_rhs_re_eq
    (A : V → Bool) (N : ℕ) {M : ℕ} {v : magConfigS V N M → ℝ}
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ_eq :
      Ψ =
        magSectorEmbedding
          (fun ρ : magConfigS V N M =>
            (((marshallSignS A ρ.1).re * v ρ : ℝ) : ℂ)))
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val) :
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    (((bipartiteToyMinEnergyPredicted (Λ := V) A N -
        (2 : ℂ) *
          ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
              ((N : ℂ) / 2 - ((pred y).val : ℂ))) *
            (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
              ((N : ℂ) / 2 - ((pred y).val : ℂ))))) * Ψ pred).re =
      ((bipartiteToyMinEnergyPredicted (Λ := V) A N).re -
          2 *
            ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                ((N : ℝ) / 2 - ((pred y).val : ℝ))) *
              (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                ((N : ℝ) / 2 - ((pred y).val : ℝ))))) *
        ((marshallSignS A pred).re *
          v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩)) := by
  classical
  dsimp only
  subst Ψ
  rw [magSectorEmbedding_apply_of_mem _
    (magSumS_single_site_lowering_predecessor τ x hx)]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  simp only [mul_zero, sub_zero]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.re_sum, Complex.im_sum, Complex.natCast_re, Complex.natCast_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.div_re, Complex.div_im,
    zero_mul, mul_zero, sub_zero]
  norm_num [Complex.normSq]
  ring_nf
  exact Or.inl trivial

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 real predecessor source-weight identity**:
the complex predecessor source-weight equality can be read on the real
axis for a Marshall-positive sector embedding.

This combines `Complex.re` of the predecessor-specialized cross-ladder
equation with
`tasaki23_cross_ladder_reembedded_source_weight_lowering_predecessor_rhs_re_eq`,
so the remaining local comparison may use the real scalar coefficient
directly. -/
theorem
    tasaki23_cross_ladder_reembedded_source_weight_lowering_predecessor_re_eq
    (A : V → Bool) (N : ℕ) {M : ℕ} {v : magConfigS V N M → ℝ}
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ_eq :
      Ψ =
        magSectorEmbedding
          (fun ρ : magConfigS V N M =>
            (((marshallSignS A ρ.1).re * v ρ : ℝ) : ℂ)))
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val)
    (hpred :
      let predVal : Fin (N + 1) :=
        ⟨(τ.1 x).val - 1, by omega⟩
      let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
      (∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
          ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
            (magSectorEmbedding
              (magSectorRestriction (M := M + 1)
                ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
        ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
          ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
            (magSectorEmbedding
              (magSectorRestriction (M := M + 1)
                ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred =
        (bipartiteToyMinEnergyPredicted (Λ := V) A N -
          (2 : ℂ) *
            ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                ((N : ℂ) / 2 - ((pred y).val : ℂ))) *
              (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                ((N : ℂ) / 2 - ((pred y).val : ℂ))))) * Ψ pred) :
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
        ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding
            (magSectorRestriction (M := M + 1)
              ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
      ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
        ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding
            (magSectorRestriction (M := M + 1)
              ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred).re =
      ((bipartiteToyMinEnergyPredicted (Λ := V) A N).re -
          2 *
            ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                ((N : ℝ) / 2 - ((pred y).val : ℝ))) *
              (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                ((N : ℝ) / 2 - ((pred y).val : ℝ))))) *
        ((marshallSignS A pred).re *
          v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩) := by
  classical
  dsimp only at hpred ⊢
  have hre := congrArg Complex.re hpred
  rw [
    tasaki23_cross_ladder_reembedded_source_weight_lowering_predecessor_rhs_re_eq
      (V := V) A N hΨ_eq τ x hx] at hre
  exact hre

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS lowering closure**:
if a full spin-`S` vector lies in the predicted toy ground-state
subspace, then its total-lowering image also lies in that subspace.

This packages the existing predicted-GS ladder invariance in the
pointwise form used by the adjacent-sector Theorem 2.3 chain, without
adding a new membership hypothesis for the lowered vector. -/
theorem tasaki23_totalSpinSOpMinus_mulVec_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (totalSpinSOpMinus V N).mulVec Ψ ∈
      bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
  exact
    bipartiteToyGroundStateSubspacePredicted_totalSpinSOpMinus_invariant
      (Λ := V) A N ⟨Ψ, hΨ, by simp⟩

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS raising closure**:
if a full spin-`S` vector lies in the predicted toy ground-state
subspace, then its total-raising image also lies in that subspace.

This is the raising-direction companion to
`tasaki23_totalSpinSOpMinus_mulVec_mem_bipartiteToyGroundStateSubspacePredicted`.
-/
theorem tasaki23_totalSpinSOpPlus_mulVec_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (totalSpinSOpPlus V N).mulVec Ψ ∈
      bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
  exact
    bipartiteToyGroundStateSubspacePredicted_totalSpinSOpPlus_invariant
      (Λ := V) A N ⟨Ψ, hΨ, by simp⟩

/-- **Tasaki §2.5 Theorem 2.3 lowered predicted-GS `A`-sublattice
Casimir bridge**: the total-lowering image of a predicted toy ground
state still has the maximum `A`-sublattice Casimir eigenvalue.

This combines predicted-GS lowering closure with the `A`-sublattice
Casimir bridge. -/
theorem tasaki23_lowered_sublatticeSpinSquaredS_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSquaredS N A).mulVec ((totalSpinSOpMinus V N).mulVec Ψ) =
      ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) • ((totalSpinSOpMinus V N).mulVec Ψ) := by
  exact
    tasaki23_sublatticeSpinSquaredS_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
      (V := V) A N
      (tasaki23_totalSpinSOpMinus_mulVec_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered predicted-GS complement-sublattice
Casimir bridge**: the total-lowering image of a predicted toy ground
state still has the maximum `¬A`-sublattice Casimir eigenvalue.

This is the complement companion to
`tasaki23_lowered_sublatticeSpinSquaredS_of_mem_bipartiteToyGroundStateSubspacePredicted`. -/
theorem tasaki23_lowered_sublatticeSpinSquaredS_complement_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSquaredS N (fun x => !A x)).mulVec
        ((totalSpinSOpMinus V N).mulVec Ψ) =
      ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) • ((totalSpinSOpMinus V N).mulVec Ψ) := by
  exact
    tasaki23_sublatticeSpinSquaredS_complement_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
      (V := V) A N
      (tasaki23_totalSpinSOpMinus_mulVec_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS `A`-lowered
sublattice-Casimir bridge**: the `A`-sublattice lowering component of
a predicted toy ground state remains in the maximum `A`-sublattice
Casimir eigenspace.

This is the component-level version needed for comparing
`Ŝ_A^- Ψ` with `Ŝ_¬A^- Ψ` in the remaining lowered-Marshall positivity
argument. -/
theorem
    tasaki23_sublatticeSpinSquaredS_sublatticeSpinSOpMinus_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSquaredS N A).mulVec ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
      ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) • ((sublatticeSpinSOpMinus N A).mulVec Ψ) := by
  exact
    mulVec_preserves_eigenvalue_of_commuteS_ladder
      N
      (sublatticeSpinSquaredS_commute_sublatticeSpinSOpMinus N A)
      (tasaki23_sublatticeSpinSquaredS_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS complement-lowered
sublattice-Casimir bridge**: the `¬A`-sublattice lowering component of
a predicted toy ground state remains in the maximum complement
sublattice-Casimir eigenspace.

This is the complement companion to
`tasaki23_sublatticeSpinSquaredS_sublatticeSpinSOpMinus_of_mem_bipartiteToyGroundStateSubspacePredicted`. -/
theorem
    tasaki23_sublatticeSpinSquaredS_complement_sublatticeSpinSOpMinus_complement_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSquaredS N (fun x => !A x)).mulVec
        ((sublatticeSpinSOpMinus N (fun x => !A x)).mulVec Ψ) =
      ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) •
        ((sublatticeSpinSOpMinus N (fun x => !A x)).mulVec Ψ) := by
  exact
    mulVec_preserves_eigenvalue_of_commuteS_ladder
      N
      (sublatticeSpinSquaredS_commute_sublatticeSpinSOpMinus N (fun x => !A x))
      (tasaki23_sublatticeSpinSquaredS_complement_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS `A`-lowered complement
sublattice-Casimir bridge**: the `A`-sublattice lowering component of
a predicted toy ground state also remains in the maximum complement
sublattice-Casimir eigenspace.

Together with
`tasaki23_sublatticeSpinSquaredS_sublatticeSpinSOpMinus_of_mem_bipartiteToyGroundStateSubspacePredicted`,
this places `Ŝ_A^- Ψ` in the joint maximum sublattice-Casimir
eigenspace needed for the remaining component comparison. -/
theorem
    tasaki23_sublatticeSpinSquaredS_complement_sublatticeSpinSOpMinus_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSquaredS N (fun x => !A x)).mulVec
        ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
      ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) • ((sublatticeSpinSOpMinus N A).mulVec Ψ) := by
  have hcomm :
      Commute (sublatticeSpinSquaredS N (fun x => ! A x))
        (sublatticeSpinSOpMinus N A) := by
    simpa using
      (sublatticeSpinSquaredS_commute_sublatticeSpinSOpMinus_complement
        N (fun x : V => ! A x))
  exact
    mulVec_preserves_eigenvalue_of_commuteS_ladder
      N hcomm
      (tasaki23_sublatticeSpinSquaredS_complement_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS complement-lowered `A`
sublattice-Casimir bridge**: the `¬A`-sublattice lowering component of
a predicted toy ground state also remains in the maximum `A`-sublattice
Casimir eigenspace.

Together with
`tasaki23_sublatticeSpinSquaredS_complement_sublatticeSpinSOpMinus_complement_of_mem_bipartiteToyGroundStateSubspacePredicted`,
this places `Ŝ_¬A^- Ψ` in the joint maximum sublattice-Casimir
eigenspace needed for the remaining component comparison. -/
theorem
    tasaki23_sublatticeSpinSquaredS_sublatticeSpinSOpMinus_complement_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSquaredS N A).mulVec
        ((sublatticeSpinSOpMinus N (fun x => !A x)).mulVec Ψ) =
      ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) •
        ((sublatticeSpinSOpMinus N (fun x => !A x)).mulVec Ψ) := by
  exact
    mulVec_preserves_eigenvalue_of_commuteS_ladder
      N
      (sublatticeSpinSquaredS_commute_sublatticeSpinSOpMinus_complement N A)
      (tasaki23_sublatticeSpinSquaredS_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 joint sublattice-Casimir eigenspace**:
the intersection of the maximum `A`- and `¬A`-sublattice Casimir
eigenspaces.

This names the structural target used by the component-lowering chain,
where both `Ŝ_A^- Ψ` and `Ŝ_¬A^- Ψ` are compared after being shown to
remain in the joint maximum sublattice-Casimir eigenspace. -/
noncomputable def tasaki23JointSublatticeCasimirEigenspace
    (A : V → Bool) (N : ℕ) : Submodule ℂ ((V → Fin (N + 1)) → ℂ) :=
  Module.End.eigenspace (sublatticeSpinSquaredS N A).mulVecLin
      ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
        ((N : ℂ) / 2)) *
      ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
        ((N : ℂ) / 2)) + 1))
    ⊓ Module.End.eigenspace
        (sublatticeSpinSquaredS N (fun x => ! A x)).mulVecLin
        ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS `A`-lowered joint
sublattice-Casimir eigenspace bridge**: the `A`-sublattice lowering
component of a predicted toy ground state lies in the joint maximum
sublattice-Casimir eigenspace.

This packages the same-side and cross-side Casimir identities for
`Ŝ_A^- Ψ` in the exact intersection form needed by the remaining
component comparison. -/
theorem
    tasaki23_sublatticeSpinSOpMinus_mem_joint_sublattice_casimir_eigenspace_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
      tasaki23JointSublatticeCasimirEigenspace (V := V) A N := by
  unfold tasaki23JointSublatticeCasimirEigenspace
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact
      tasaki23_sublatticeSpinSquaredS_sublatticeSpinSOpMinus_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact
      tasaki23_sublatticeSpinSquaredS_complement_sublatticeSpinSOpMinus_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS complement-lowered joint
sublattice-Casimir eigenspace bridge**: the complement-sublattice
lowering component of a predicted toy ground state lies in the joint
maximum sublattice-Casimir eigenspace.

This packages the same-side and cross-side Casimir identities for
`Ŝ_¬A^- Ψ` in the exact intersection form needed by the remaining
component comparison. -/
theorem
    tasaki23_sublatticeSpinSOpMinus_complement_mem_joint_sublattice_casimir_eigenspace_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
      tasaki23JointSublatticeCasimirEigenspace (V := V) A N := by
  unfold tasaki23JointSublatticeCasimirEigenspace
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact
      tasaki23_sublatticeSpinSquaredS_sublatticeSpinSOpMinus_complement_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact
      tasaki23_sublatticeSpinSquaredS_complement_sublatticeSpinSOpMinus_complement_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered component joint-magnetization
subspace**: the structural target for a lowered component of a
sector-`M` source vector.

It combines the joint maximum sublattice-Casimir eigenspace with the
successor magnetization subspace `magSumS = M + 1`, in centered
magnetization units.  The remaining comparison can then use one
submodule membership carrying both the Casimir and sector-support
facts for the lowered components. -/
noncomputable def tasaki23LoweredJointMagSubspace
    (A : V → Bool) (N M : ℕ) : Submodule ℂ ((V → Fin (N + 1)) → ℂ) :=
  tasaki23JointSublatticeCasimirEigenspace (V := V) A N ⊓
    magSubspaceS V N
      (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 `A`-lowered joint-magnetization bridge**:
if a sector-`M` representative is in the predicted toy ground-state
subspace, then its `A`-sublattice lowering component lies in the
combined joint-Casimir and successor-sector subspace.

This packages the PR #3408 joint-Casimir membership together with the
standard sublattice-lowering magnetization shift. -/
theorem
    tasaki23_sublatticeSpinSOpMinus_mem_lowered_joint_magSubspace_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {M : ℕ} {Φ : magConfigS V N M → ℂ}
    (hΦ : magSectorEmbedding Φ ∈
      bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    ((sublatticeSpinSOpMinus N A).mulVec (magSectorEmbedding Φ)) ∈
      tasaki23LoweredJointMagSubspace (V := V) A N M := by
  unfold tasaki23LoweredJointMagSubspace
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · exact
      tasaki23_sublatticeSpinSOpMinus_mem_joint_sublattice_casimir_eigenspace_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΦ
  · have hshift :
        (sublatticeSpinSOpMinus N A).mulVec (magSectorEmbedding Φ) ∈
          magSubspaceS V N
            ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) - 1) :=
      sublatticeSpinSOpMinus_mulVec_mem_magSubspaceS_of_mem
        N A (magSectorEmbedding_mem_magSubspaceS Φ)
    convert hshift using 1
    norm_num
    ring_nf

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 complement-lowered joint-magnetization
bridge**: if a sector-`M` representative is in the predicted toy
ground-state subspace, then its complement-sublattice lowering component
lies in the combined joint-Casimir and successor-sector subspace.

This is the complement component version of
`tasaki23_sublatticeSpinSOpMinus_mem_lowered_joint_magSubspace_of_mem_bipartiteToyGroundStateSubspacePredicted`.
-/
theorem
    tasaki23_sublatticeSpinSOpMinus_complement_mem_lowered_joint_magSubspace_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {M : ℕ} {Φ : magConfigS V N M → ℂ}
    (hΦ : magSectorEmbedding Φ ∈
      bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
        (magSectorEmbedding Φ)) ∈
      tasaki23LoweredJointMagSubspace (V := V) A N M := by
  unfold tasaki23LoweredJointMagSubspace
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · exact
      tasaki23_sublatticeSpinSOpMinus_complement_mem_joint_sublattice_casimir_eigenspace_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΦ
  · have hshift :
        (sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
            (magSectorEmbedding Φ) ∈
          magSubspaceS V N
            ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) - 1) :=
      sublatticeSpinSOpMinus_mulVec_mem_magSubspaceS_of_mem
        N (fun x => ! A x) (magSectorEmbedding_mem_magSubspaceS Φ)
    convert hshift using 1
    norm_num
    ring_nf

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered joint-magnetization Casimir
projection**: membership in `tasaki23LoweredJointMagSubspace` exposes
the joint maximum sublattice-Casimir component.

This is an unpacking lemma for the cross-ladder comparison callback. -/
theorem tasaki23_mem_joint_sublattice_casimir_eigenspace_of_mem_lowered_joint_magSubspace
    (A : V → Bool) (N M : ℕ) {w : (V → Fin (N + 1)) → ℂ}
    (hw : w ∈ tasaki23LoweredJointMagSubspace (V := V) A N M) :
    w ∈ tasaki23JointSublatticeCasimirEigenspace (V := V) A N := by
  unfold tasaki23LoweredJointMagSubspace at hw
  exact (Submodule.mem_inf.mp hw).1

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered joint-magnetization sector
projection**: membership in `tasaki23LoweredJointMagSubspace` exposes
the successor magnetization support.

This is the sector-support companion to
`tasaki23_mem_joint_sublattice_casimir_eigenspace_of_mem_lowered_joint_magSubspace`. -/
theorem tasaki23_mem_magSubspaceS_of_mem_lowered_joint_magSubspace
    (A : V → Bool) (N M : ℕ) {w : (V → Fin (N + 1)) → ℂ}
    (hw : w ∈ tasaki23LoweredJointMagSubspace (V := V) A N M) :
    w ∈ magSubspaceS V N
      (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) := by
  unfold tasaki23LoweredJointMagSubspace at hw
  exact (Submodule.mem_inf.mp hw).2

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered joint-magnetization `A`-Casimir
equation**: a vector in `tasaki23LoweredJointMagSubspace` satisfies the
maximum `A`-sublattice Casimir eigenvector identity.

This turns the packed subspace membership used by the interval chain
into the explicit equation needed by the remaining representation-
theoretic comparison. -/
theorem tasaki23_sublatticeSpinSquaredS_eq_of_mem_lowered_joint_magSubspace
    (A : V → Bool) (N M : ℕ) {w : (V → Fin (N + 1)) → ℂ}
    (hw : w ∈ tasaki23LoweredJointMagSubspace (V := V) A N M) :
    (sublatticeSpinSquaredS N A).mulVec w =
      ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) • w := by
  have hjoint :=
    tasaki23_mem_joint_sublattice_casimir_eigenspace_of_mem_lowered_joint_magSubspace
      (V := V) A N M hw
  unfold tasaki23JointSublatticeCasimirEigenspace at hjoint
  have hA := (Submodule.mem_inf.mp hjoint).1
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hA
  exact hA

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered joint-magnetization complement
Casimir equation**: a vector in `tasaki23LoweredJointMagSubspace`
satisfies the maximum `¬A`-sublattice Casimir eigenvector identity.

This is the complement-sublattice companion to
`tasaki23_sublatticeSpinSquaredS_eq_of_mem_lowered_joint_magSubspace`. -/
theorem tasaki23_sublatticeSpinSquaredS_complement_eq_of_mem_lowered_joint_magSubspace
    (A : V → Bool) (N M : ℕ) {w : (V → Fin (N + 1)) → ℂ}
    (hw : w ∈ tasaki23LoweredJointMagSubspace (V := V) A N M) :
    (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec w =
      ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) • w := by
  have hjoint :=
    tasaki23_mem_joint_sublattice_casimir_eigenspace_of_mem_lowered_joint_magSubspace
      (V := V) A N M hw
  unfold tasaki23JointSublatticeCasimirEigenspace at hjoint
  have hB := (Submodule.mem_inf.mp hjoint).2
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hB
  exact hB

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS transfer across a non-zero
real scalar**: if a vector in the predicted toy ground-state subspace is
a non-zero real scalar multiple of another vector, then the second vector
also lies in the predicted toy ground-state subspace.

This is the membership analogue of
`tasaki23_totalSpinSSquared_predictedCasimirValue_of_real_smul_eq`, used
after the lowered ladder image is identified with the successor-sector
representative up to a positive real scalar. -/
theorem tasaki23_mem_bipartiteToyGroundStateSubspacePredicted_of_real_smul_eq
    (A : V → Bool) (N : ℕ) {r : ℝ}
    {Ψ Φ : (V → Fin (N + 1)) → ℂ}
    (hr : r ≠ 0)
    (hrel : Ψ = (r : ℂ) • Φ)
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    Φ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hsmul :
      (r : ℂ) • Φ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
    simpa [← hrel] using hΨ
  have hinv :
      ((r : ℂ)⁻¹) • ((r : ℂ) • Φ) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N :=
    Submodule.smul_mem _ _ hsmul
  have hscale : ((r : ℂ)⁻¹) • ((r : ℂ) • Φ) = Φ := by
    rw [smul_smul, inv_mul_cancel₀ hrC, one_smul]
  rwa [hscale] at hinv

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS lowered Casimir bridge**:
in the canonical orientation, a vector in the predicted toy ground-state
subspace has a total-lowering image with the Theorem 2.3 predicted
total-Casimir eigenvalue.

This combines predicted-GS lowering closure with the predicted-GS
total-Casimir bridge, so no separate Casimir hypothesis is needed for
the lowered ladder image. -/
theorem tasaki23_lowered_predictedCasimirValue_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (totalSpinSSquared V N).mulVec ((totalSpinSOpMinus V N).mulVec Ψ) =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
        ((totalSpinSOpMinus V N).mulVec Ψ) := by
  exact
    tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
      (V := V) A N hBA
      (tasaki23_totalSpinSOpMinus_mulVec_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ)

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS raised Casimir bridge**:
in the canonical orientation, a vector in the predicted toy ground-state
subspace has a total-raising image with the Theorem 2.3 predicted
total-Casimir eigenvalue.

This is the raising-direction companion to
`tasaki23_lowered_predictedCasimirValue_of_mem_bipartiteToyGroundStateSubspacePredicted`.
-/
theorem tasaki23_raised_predictedCasimirValue_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (totalSpinSSquared V N).mulVec ((totalSpinSOpPlus V N).mulVec Ψ) =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
        ((totalSpinSOpPlus V N).mulVec Ψ) := by
  exact
    tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
      (V := V) A N hBA
      (tasaki23_totalSpinSOpPlus_mulVec_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ)

/-- **Tasaki §2.5 Theorem 2.3 predicted-Casimir preservation under
lowering**: if a full spin-`S` vector has the Theorem 2.3 predicted
total-Casimir eigenvalue, then its image under `Ŝ^-_tot` has the same
total-Casimir eigenvalue.

This is the one-step Casimir stability needed when the admissible-sector
chain propagates Theorem 2.3 ground states by the total lowering
operator. -/
theorem tasaki23_totalSpinSOpMinus_preserves_predictedCasimirValue
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ_cas :
      (totalSpinSSquared V N).mulVec Ψ =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) • Ψ) :
    (totalSpinSSquared V N).mulVec ((totalSpinSOpMinus V N).mulVec Ψ) =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
        (totalSpinSOpMinus V N).mulVec Ψ := by
  have hcomm : totalSpinSSquared V N * totalSpinSOpMinus V N =
      totalSpinSOpMinus V N * totalSpinSSquared V N :=
    (totalSpinSSquared_commute_totalSpinSOpMinus (V := V) (N := N)).eq
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hΨ_cas, Matrix.mulVec_smul]

/-- **Tasaki §2.5 Theorem 2.3 predicted-Casimir preservation under
raising**: if a full spin-`S` vector has the Theorem 2.3 predicted
total-Casimir eigenvalue, then its image under `Ŝ^+_tot` has the same
total-Casimir eigenvalue.

This is the raising-direction companion to
`tasaki23_totalSpinSOpMinus_preserves_predictedCasimirValue`, used when
the admissible-sector chain is traversed toward smaller `magSumS`
sectors. -/
theorem tasaki23_totalSpinSOpPlus_preserves_predictedCasimirValue
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ_cas :
      (totalSpinSSquared V N).mulVec Ψ =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) • Ψ) :
    (totalSpinSSquared V N).mulVec ((totalSpinSOpPlus V N).mulVec Ψ) =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
        (totalSpinSOpPlus V N).mulVec Ψ := by
  have hcomm : totalSpinSSquared V N * totalSpinSOpPlus V N =
      totalSpinSOpPlus V N * totalSpinSSquared V N :=
    (totalSpinSSquared_commute_totalSpinSOpPlus (V := V) (N := N)).eq
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hΨ_cas, Matrix.mulVec_smul]

/-- **Tasaki §2.5 Theorem 2.3 sector-embedded predicted-Casimir
preservation under lowering**: if a Marshall-signed sector vector has the
Theorem 2.3 predicted total-Casimir eigenvalue after zero-extension to the
full spin-`S` Hilbert space, then its image under `Ŝ^-_tot` has the same
total-Casimir eigenvalue.

This is the sector-vector form used in the adjacent-sector chain, before the
lowered vector is compared with the target sector's Theorem 2.2
Marshall-positive representative. -/
theorem
    tasaki23_totalSpinSOpMinus_marshallSignedEmbedding_preserves_predictedCasimirValue
    (A : V → Bool) (N : ℕ) {M : ℕ} {v : magConfigS V N M → ℝ}
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) :
    (totalSpinSSquared V N).mulVec
        ((totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
        ((totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  exact
    tasaki23_totalSpinSOpMinus_preserves_predictedCasimirValue
      (V := V) A N hΦ_cas

/-- **Tasaki §2.5 Theorem 2.3 sector-embedded predicted-Casimir
preservation under raising**: if a Marshall-signed sector vector has the
Theorem 2.3 predicted total-Casimir eigenvalue after zero-extension to the
full spin-`S` Hilbert space, then its image under `Ŝ^+_tot` has the same
total-Casimir eigenvalue.

This is the raising-direction companion to
the corresponding lowering theorem above. -/
theorem
    tasaki23_totalSpinSOpPlus_marshallSignedEmbedding_preserves_predictedCasimirValue
    (A : V → Bool) (N : ℕ) {M : ℕ} {v : magConfigS V N M → ℝ}
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) :
    (totalSpinSSquared V N).mulVec
        ((totalSpinSOpPlus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
        ((totalSpinSOpPlus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  exact
    tasaki23_totalSpinSOpPlus_preserves_predictedCasimirValue
      (V := V) A N hΦ_cas

/-- **Tasaki §2.5 Theorem 2.3 predicted-Casimir transfer across a
non-zero real scalar**: if a vector with the predicted total-Casimir
eigenvalue is a non-zero real scalar multiple of another vector, then
the second vector has the same predicted total-Casimir eigenvalue.

This is the cancellation step used after identifying a lowered ladder
image with the adjacent-sector Marshall-positive representative up to a
positive real scalar. -/
theorem tasaki23_totalSpinSSquared_predictedCasimirValue_of_real_smul_eq
    (A : V → Bool) (N : ℕ) {r : ℝ}
    {Ψ Φ : (V → Fin (N + 1)) → ℂ}
    (hr : r ≠ 0)
    (hrel : Ψ = (r : ℂ) • Φ)
    (hΨ_cas :
      (totalSpinSSquared V N).mulVec Ψ =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) • Ψ) :
    (totalSpinSSquared V N).mulVec Φ =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) • Φ := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  rw [hrel, Matrix.mulVec_smul] at hΨ_cas
  funext σ
  have hσ := congrFun hΨ_cas σ
  change (r : ℂ) * ((totalSpinSSquared V N).mulVec Φ) σ =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) *
        ((r : ℂ) * Φ σ) at hσ
  change ((totalSpinSSquared V N).mulVec Φ) σ =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) * Φ σ
  have hσ' :
      (r : ℂ) * ((totalSpinSSquared V N).mulVec Φ) σ =
        (r : ℂ) * ((tasaki23PredictedCasimirValue (V := V) A N : ℂ) * Φ σ) := by
    calc
      (r : ℂ) * ((totalSpinSSquared V N).mulVec Φ) σ =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) *
            ((r : ℂ) * Φ σ) := hσ
      _ = (r : ℂ) * ((tasaki23PredictedCasimirValue (V := V) A N : ℂ) * Φ σ) := by
        ring
  exact mul_left_cancel₀ hrC hσ'

end LatticeSystem.Quantum
