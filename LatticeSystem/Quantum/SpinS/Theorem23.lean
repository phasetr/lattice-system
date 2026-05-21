import LatticeSystem.Quantum.SpinS.Theorem23Local


/-!
# Tasaki §2.5 Theorem 2.3 — Marshall–Lieb–Mattis, general spin-S, `|A| ≠ |¬A|`

This file states the final form of Tasaki §2.5 Theorem 2.3 (p. 42):

> Let `(Λ, B)` be a connected bipartite lattice with `|A| ≥ 1` and
> `|B| ≥ 1`. Then the ground states have total spin
>   `S_tot = ||A| − |B|| · S`,
> and are `2 S_tot + 1` fold degenerate. The ground states are
> expanded as in (2.5.4) with the restriction `σ = 0` replaced by
> `σ = M`, where `M = −S_tot, …, S_tot − 1, S_tot`.

The statement is encoded as a `Prop`-valued definition
`tasaki_2_5_theorem_2_3` whose hypothesis bundle and conclusion
match the per-sector bundled Theorem 2.2
`marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full`
(file `MagSectorEmbedding.lean`, PR #869), iterated across the range
of admissible magnetization sectors
`M ∈ tasaki23GroundStateSectors A N` (= the closed integer interval
`[min(|A|, |¬A|)·N, max(|A|, |¬A|)·N]` in `magSumS` units; centered
units `m = M − |V|·N/2 ∈ {−S_tot, …, S_tot}`).

Per Tasaki ("essentially a straightforward modification of that of
Theorem 2.2"), the proof reuses the Marshall sign + Perron–Frobenius
+ toy-Hamiltonian argument with `H_M` replacing `H_0` to obtain
`2 S_tot + 1` sector-unique ground states sharing energy `μ`.

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

/-- **Tasaki §2.5 Theorem 2.3 adjacent common-energy successor step**:
inside the admissible sector interval, a source-sector
Marshall-positive eigenvector in sector `M`, together with the lowered
site-sum positivity input, produces a Marshall-positive eigenvector in
the successor sector `M + 1` at the same eigenvalue.

This is the one-step chain link for the final Theorem 2.3 proof.  The
interval hypotheses prove that `M + 1` is still an admissible sector,
and the previously established lowered site-sum package identifies the
successor-sector Theorem 2.2 eigenvalue with the source eigenvalue. -/
theorem tasaki23_successor_sector_common_energy_of_site_sum_pos
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hlowered_site_sum_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  have hsucc_mem :
      M + 1 ∈ tasaki23GroundStateSectors (V := V) A N :=
    tasaki23GroundStateSectors_succ_mem_of_mem_of_lt_right A N hM hMlt
  obtain ⟨hlowered_ne, μ_succ, v_succ, hμ_succ_lt, hv_succ_pos,
      hmul_succ, hμ_eq, r, hr_pos, hrel⟩ :=
    tasaki23_lowering_identifies_adjacent_sector_energy_of_site_sum_pos
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hΦ hlowered_site_sum_pos
  subst μ_succ
  exact ⟨hsucc_mem, hμ_lt, hv_pos, hΦ, hlowered_ne, v_succ,
    hμ_succ_lt, hv_succ_pos, hmul_succ, r, hr_pos, hrel⟩

/-- **Tasaki §2.5 Theorem 2.3 adjacent common-energy successor step from
Casimir non-vanishing**: inside the admissible sector interval, a
Marshall-positive source-sector Casimir eigenvector whose Casimir value
is not the lowering endpoint value has a non-zero lowered image, and a
site-sum positivity proof identifies the successor-sector ground-state
energy with the source energy.

This connects the Casimir endpoint obstruction to the one-step
successor link used in the final Theorem 2.3 chain. -/
theorem tasaki23_successor_sector_common_energy_of_site_sum_pos_of_casimir_ne_kernel_value
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {γ : ℂ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        γ • magSectorEmbedding
          (fun τ : magConfigS V N M => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hγ_ne :
      γ ≠
        ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) *
          ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) - 1)))
    (hlowered_site_sum_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  have hsucc_mem :
      M + 1 ∈ tasaki23GroundStateSectors (V := V) A N :=
    tasaki23GroundStateSectors_succ_mem_of_mem_of_lt_right A N hM hMlt
  obtain ⟨hlowered_ne, μ_succ, v_succ, hμ_succ_lt, hv_succ_pos,
      hmul_succ, hμ_eq, r, hr_pos, hrel⟩ :=
    tasaki23_lowering_identifies_adjacent_sector_energy_with_casimir_nonzero
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hΦ_cas hγ_ne hv_pos hΦ
      (tasaki23_lowered_marshall_pos_of_site_sum_pos A
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
        hlowered_site_sum_pos)
  subst μ_succ
  exact ⟨hsucc_mem, hμ_lt, hv_pos, hΦ, hlowered_ne, v_succ,
    hμ_succ_lt, hv_succ_pos, hmul_succ, r, hr_pos, hrel⟩

/-- **Tasaki §2.5 Theorem 2.3 adjacent common-energy predecessor step**:
inside the admissible sector interval, a source-sector
Marshall-positive eigenvector in sector `M + 1`, together with the
raised site-sum positivity input, produces a Marshall-positive
eigenvector in the predecessor sector `M` at the same eigenvalue.

This is the raising-direction interval wrapper corresponding to
`tasaki23_successor_sector_common_energy_of_site_sum_pos`. -/
theorem tasaki23_predecessor_sector_common_energy_of_site_sum_pos
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hraised_site_sum_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    M ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpPlus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_pred : magConfigS V N M → ℝ,
      μ < c ∧ (∀ τ, 0 < v_pred τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N M,
          (((totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_pred τ) := by
  have hpred_mem_raw :
      (M + 1) - 1 ∈ tasaki23GroundStateSectors (V := V) A N :=
    tasaki23GroundStateSectors_pred_mem_of_left_lt_of_mem A N hMlt hM
  have hpred_mem : M ∈ tasaki23GroundStateSectors (V := V) A N := by
    simpa using hpred_mem_raw
  obtain ⟨hraised_ne, μ_pred, v_pred, hμ_pred_lt, hv_pred_pos,
      hmul_pred, hμ_eq, r, hr_pos, hrel⟩ :=
    tasaki23_raising_identifies_adjacent_sector_energy_of_site_sum_pos
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hΦ hraised_site_sum_pos
  subst μ_pred
  exact ⟨hpred_mem, hμ_lt, hv_pos, hΦ, hraised_ne, v_pred,
    hμ_pred_lt, hv_pred_pos, hmul_pred, r, hr_pos, hrel⟩

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 adjacent common-energy predecessor step
from Casimir non-vanishing**: inside the admissible sector interval, a
Marshall-positive source-sector Casimir eigenvector whose Casimir value
is not the raising endpoint value has a non-zero raised image, and a
site-sum positivity proof identifies the predecessor-sector ground-state
energy with the source energy.

This is the raising-direction interval wrapper corresponding to
`tasaki23_successor_sector_common_energy_of_site_sum_pos_of_casimir_ne_kernel_value`. -/
theorem tasaki23_predecessor_sector_common_energy_of_site_sum_pos_of_casimir_ne_kernel_value
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    {μ : ℝ} {γ : ℂ} {v : magConfigS V N (M + 1) → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        γ • magSectorEmbedding
          (fun τ : magConfigS V N (M + 1) =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hγ_ne :
      γ ≠
        ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) *
          ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) + 1)))
    (hraised_site_sum_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    M ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpPlus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_pred : magConfigS V N M → ℝ,
      μ < c ∧ (∀ τ, 0 < v_pred τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N M,
          (((totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_pred τ) := by
  have hpred_mem_raw :
      (M + 1) - 1 ∈ tasaki23GroundStateSectors (V := V) A N :=
    tasaki23GroundStateSectors_pred_mem_of_left_lt_of_mem A N hMlt hM
  have hpred_mem : M ∈ tasaki23GroundStateSectors (V := V) A N := by
    simpa using hpred_mem_raw
  obtain ⟨hraised_ne, μ_pred, v_pred, hμ_pred_lt, hv_pred_pos,
      hmul_pred, hμ_eq, r, hr_pos, hrel⟩ :=
    tasaki23_raising_identifies_adjacent_sector_energy_with_casimir_nonzero
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hΦ_cas hγ_ne hv_pos hΦ
      (tasaki23_raised_marshall_pos_of_site_sum_pos A
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
        hraised_site_sum_pos)
  subst μ_pred
  exact ⟨hpred_mem, hμ_lt, hv_pos, hΦ, hraised_ne, v_pred,
    hμ_pred_lt, hv_pred_pos, hmul_pred, r, hr_pos, hrel⟩

/-- **Tasaki §2.5 Theorem 2.3 adjacent common-energy successor step from
the predicted Casimir value**: inside the admissible sector interval, a
Marshall-positive source vector whose total-Casimir eigenvalue is the
Theorem 2.3 predicted value has a non-zero lowered image away from the
right endpoint, and the site-sum positivity input identifies the
successor-sector ground-state energy with the source energy.

This specializes
`tasaki23_successor_sector_common_energy_of_site_sum_pos_of_casimir_ne_kernel_value`
by discharging its endpoint-mismatch hypothesis with the
predicted-Casimir mismatch lemma. -/
theorem tasaki23_successor_sector_common_energy_of_site_sum_pos_of_predictedCasimirValue
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hlowered_site_sum_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  exact
    tasaki23_successor_sector_common_energy_of_site_sum_pos_of_casimir_ne_kernel_value
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ hΦ_cas
      (tasaki23_predictedCasimirValue_ne_lowering_kernel_value_of_mem_of_lt_right
        (V := V) A N hM hMlt)
      hlowered_site_sum_pos

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 adjacent common-energy predecessor step from
the predicted Casimir value**: inside the admissible sector interval, a
Marshall-positive source vector in sector `M + 1` whose total-Casimir
eigenvalue is the Theorem 2.3 predicted value has a non-zero raised
image away from the left endpoint, and the site-sum positivity input
identifies the predecessor-sector ground-state energy with the source
energy.

This specializes
`tasaki23_predecessor_sector_common_energy_of_site_sum_pos_of_casimir_ne_kernel_value`
by discharging its endpoint-mismatch hypothesis with the
predicted-Casimir mismatch lemma. -/
theorem tasaki23_predecessor_sector_common_energy_of_site_sum_pos_of_predictedCasimirValue
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hraised_site_sum_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    M ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpPlus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_pred : magConfigS V N M → ℝ,
      μ < c ∧ (∀ τ, 0 < v_pred τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N M,
          (((totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_pred τ) := by
  exact
    tasaki23_predecessor_sector_common_energy_of_site_sum_pos_of_casimir_ne_kernel_value
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ hΦ_cas
      (tasaki23_predictedCasimirValue_ne_raising_kernel_value_of_mem_of_left_lt
        (V := V) A N hM hMlt)
      hraised_site_sum_pos

/-- **Tasaki §2.5 Theorem 2.3 successor step with lowered predicted
Casimir image**: the predicted-Casimir successor common-energy wrapper also
returns that the actual lowered full-space ladder image has the predicted
total-Casimir eigenvalue.

This packages the adjacent-sector energy comparison with
`tasaki23_totalSpinSOpMinus_marshallSignedEmbedding_preserves_predictedCasimirValue`.
-/
theorem tasaki23_successor_common_energy_with_lowered_predictedCasimir
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hlowered_site_sum_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    (M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
      μ < c ∧ (∀ τ, 0 < v τ) ∧
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
      (totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
      ∃ v_succ : magConfigS V N (M + 1) → ℝ,
        μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
        (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
        ∃ r : ℝ, 0 < r ∧
          ∀ τ : magConfigS V N (M + 1),
            (((totalSpinSOpMinus V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
              r * ((marshallSignS A τ.1).re * v_succ τ)) ∧
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
  constructor
  · exact
      tasaki23_successor_sector_common_energy_of_site_sum_pos_of_predictedCasimirValue
        A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
        hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ hΦ_cas
        hlowered_site_sum_pos
  · exact
      tasaki23_totalSpinSOpMinus_marshallSignedEmbedding_preserves_predictedCasimirValue
        (V := V) A N hΦ_cas

/-- **Tasaki §2.5 Theorem 2.3 predecessor step with raised predicted
Casimir image**: the predicted-Casimir predecessor common-energy wrapper
also returns that the actual raised full-space ladder image has the
predicted total-Casimir eigenvalue.

This is the raising-direction companion to
`tasaki23_successor_common_energy_with_lowered_predictedCasimir`. -/
theorem tasaki23_predecessor_common_energy_with_raised_predictedCasimir
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hraised_site_sum_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    (M ∈ tasaki23GroundStateSectors (V := V) A N ∧
      μ < c ∧ (∀ τ, 0 < v τ) ∧
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
      (totalSpinSOpPlus V N).mulVec
          (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
      ∃ v_pred : magConfigS V N M → ℝ,
        μ < c ∧ (∀ τ, 0 < v_pred τ) ∧
        (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
        ∃ r : ℝ, 0 < r ∧
          ∀ τ : magConfigS V N M,
            (((totalSpinSOpPlus V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
              r * ((marshallSignS A τ.1).re * v_pred τ)) ∧
      (totalSpinSSquared V N).mulVec
          ((totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N (M + 1) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          ((totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N (M + 1) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  constructor
  · exact
      tasaki23_predecessor_sector_common_energy_of_site_sum_pos_of_predictedCasimirValue
        A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
        hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ hΦ_cas
        hraised_site_sum_pos
  · exact
      tasaki23_totalSpinSOpPlus_marshallSignedEmbedding_preserves_predictedCasimirValue
        (V := V) A N hΦ_cas

/-- **Tasaki §2.5 Theorem 2.3 adjacent common-energy successor step from
lowered dominance**: inside the admissible sector interval, the pointwise
dominance of the off-`A` lowered signed sum over the negative on-`A`
signed sum supplies the strict site-sum positivity input and hence
produces the successor-sector common-energy conclusion.

This is the dominance-form wrapper around
`tasaki23_successor_sector_common_energy_of_site_sum_pos`.  The
substantive remaining proof obligation is the dominance hypothesis
itself. -/
theorem tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hdominates :
      ∀ τ : magConfigS V N (M + 1),
        -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23SignedLoweringSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23SignedLoweringSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  exact tasaki23_successor_sector_common_energy_of_site_sum_pos
    A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
    hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ
    (fun τ =>
      tasaki23_signed_lowering_site_sum_pos_of_onA_neg_lt_offA
        A (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
        τ (hdominates τ))

/-- **Tasaki §2.5 Theorem 2.3 adjacent common-energy predecessor step from
raised dominance**: inside the admissible sector interval, the pointwise
dominance of the off-`A` raised signed sum over the negative on-`A`
signed sum supplies the strict site-sum positivity input and hence
produces the predecessor-sector common-energy conclusion.

This is the raising-direction dominance-form wrapper around
`tasaki23_predecessor_sector_common_energy_of_site_sum_pos`. The
substantive remaining proof obligation is the dominance hypothesis
itself. -/
theorem tasaki23_predecessor_sector_common_energy_of_onA_neg_lt_offA
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hdominates :
      ∀ τ : magConfigS V N M,
        -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23SignedRaisingSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23SignedRaisingSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    M ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpPlus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_pred : magConfigS V N M → ℝ,
      μ < c ∧ (∀ τ, 0 < v_pred τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N M,
          (((totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_pred τ) := by
  exact tasaki23_predecessor_sector_common_energy_of_site_sum_pos
    A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
    hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ
    (fun τ =>
      tasaki23_signed_raising_site_sum_pos_of_onA_neg_lt_offA
        A (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
        τ (hdominates τ))

/-- **Tasaki §2.5 Theorem 2.3 adjacent predicted-Casimir successor step
from lowered dominance**: the lowered dominance hypothesis supplies the
strict site-sum positivity input for the predicted-Casimir successor
common-energy wrapper.

This is the predicted-Casimir analogue of
`tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA`; the
substantive dominance estimate remains an explicit hypothesis. -/
theorem
    tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_predictedCasimirValue
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hdominates :
      ∀ τ : magConfigS V N (M + 1),
        -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23SignedLoweringSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23SignedLoweringSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  exact
    tasaki23_successor_sector_common_energy_of_site_sum_pos_of_predictedCasimirValue
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ hΦ_cas
      (fun τ =>
        tasaki23_signed_lowering_site_sum_pos_of_onA_neg_lt_offA
          A (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
          τ (hdominates τ))

/-- **Tasaki §2.5 Theorem 2.3 adjacent predicted-Casimir successor step
with successor Casimir**: the lowered dominance common-energy wrapper also
transfers the predicted total-Casimir identity to the successor-sector
Marshall-positive representative.

This is the source-vector form of the interval-threading step: once the
source sector carries the predicted Casimir, the adjacent successor returned
by Theorem 2.2 uniqueness carries it as well, so later interval induction does
not need a fresh source-Casimir callback at the successor sector. -/
theorem
    tasaki23_successor_sector_common_energy_with_successor_predictedCasimir_of_onA_neg_lt_offA
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hdominates :
      ∀ τ : magConfigS V N (M + 1),
        -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23SignedLoweringSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23SignedLoweringSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  have hstep :=
    tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_predictedCasimirValue
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ hΦ_cas hdominates
  rcases hstep with ⟨hsucc_mem, hμ_lt', hv_pos', hΦ', hne,
    v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, r, hr_pos, hrel⟩
  have hcas_lowered :
      (totalSpinSSquared V N).mulVec
          ((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          ((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) :=
    tasaki23_totalSpinSOpMinus_marshallSignedEmbedding_preserves_predictedCasimirValue
      A N hΦ_cas
  have hsmul :
      (totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (r : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) :=
    totalSpinSOpMinus_marshallSignedEmbedding_eq_smul_successor_of_re
      A hrel
  have hsucc_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) :=
    tasaki23_totalSpinSSquared_predictedCasimirValue_of_real_smul_eq
      A N (ne_of_gt hr_pos) hsmul hcas_lowered
  exact ⟨hsucc_mem, hμ_lt', hv_pos', hΦ', hne,
    ⟨v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_cas,
      ⟨r, hr_pos, hrel⟩⟩⟩

/-- **Tasaki §2.5 Theorem 2.3 adjacent predicted-Casimir successor step
with successor Casimir from lowered site-sum positivity**: the direct
lowered site-sum positivity common-energy wrapper also transfers the
predicted total-Casimir identity to the successor-sector Marshall-positive
representative.

This is the site-sum form of
`tasaki23_successor_sector_common_energy_with_successor_predictedCasimir_of_onA_neg_lt_offA`.
-/
theorem
    tasaki23_successor_sector_common_energy_with_successor_predictedCasimir_of_site_sum_pos
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hlowered_site_sum_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  have hstep :=
    tasaki23_successor_sector_common_energy_of_site_sum_pos_of_predictedCasimirValue
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ hΦ_cas
      hlowered_site_sum_pos
  rcases hstep with ⟨hsucc_mem, hμ_lt', hv_pos', hΦ', hne,
    v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, r, hr_pos, hrel⟩
  have hcas_lowered :
      (totalSpinSSquared V N).mulVec
          ((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          ((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) :=
    tasaki23_totalSpinSOpMinus_marshallSignedEmbedding_preserves_predictedCasimirValue
      A N hΦ_cas
  have hsmul :
      (totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (r : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) :=
    totalSpinSOpMinus_marshallSignedEmbedding_eq_smul_successor_of_re
      A hrel
  have hsucc_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) :=
    tasaki23_totalSpinSSquared_predictedCasimirValue_of_real_smul_eq
      A N (ne_of_gt hr_pos) hsmul hcas_lowered
  exact ⟨hsucc_mem, hμ_lt', hv_pos', hΦ', hne,
    ⟨v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_cas,
      ⟨r, hr_pos, hrel⟩⟩⟩

/-- **Tasaki §2.5 Theorem 2.3 adjacent predicted-Casimir predecessor step
from raised dominance**: the raised dominance hypothesis supplies the
strict site-sum positivity input for the predicted-Casimir predecessor
common-energy wrapper.

This is the raising-direction companion to
`tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_predictedCasimirValue`.
-/
theorem
    tasaki23_predecessor_sector_common_energy_of_onA_neg_lt_offA_of_predictedCasimirValue
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hdominates :
      ∀ τ : magConfigS V N M,
        -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23SignedRaisingSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23SignedRaisingSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    M ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpPlus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_pred : magConfigS V N M → ℝ,
      μ < c ∧ (∀ τ, 0 < v_pred τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N M,
          (((totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_pred τ) := by
  exact
    tasaki23_predecessor_sector_common_energy_of_site_sum_pos_of_predictedCasimirValue
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ hΦ_cas
      (fun τ =>
        tasaki23_signed_raising_site_sum_pos_of_onA_neg_lt_offA
          A (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
          τ (hdominates τ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 adjacent predicted-GS successor step from
lowered dominance**: in the canonical orientation `|¬A| ≤ |A|`,
membership of the source-sector vector in the predicted toy
ground-state subspace supplies the predicted-Casimir hypothesis needed
by the lowered dominance common-energy wrapper.

The dominance estimate remains explicit; this theorem only replaces the
source total-Casimir input by predicted-GS membership. -/
theorem
    tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_pred :
      magSectorEmbedding
          (fun τ : magConfigS V N M =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hdominates :
      ∀ τ : magConfigS V N (M + 1),
        -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23SignedLoweringSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23SignedLoweringSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  exact
    tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_predictedCasimirValue
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ
      (tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
        A N hBA hΦ_pred)
      hdominates

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 adjacent predicted-GS successor step from
lowered site-sum positivity**: in the canonical orientation `|¬A| ≤ |A|`,
membership of the source-sector vector in the predicted toy ground-state
subspace supplies the predicted-Casimir hypothesis, while the direct
lowered site-sum positivity hypothesis supplies Marshall positivity of
the lowered vector.

This is the site-sum analogue of
`tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_mem_bipartiteToyGroundStateSubspacePredicted`.
-/
theorem
    tasaki23_successor_sector_common_energy_of_site_sum_pos_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_pred :
      magSectorEmbedding
          (fun τ : magConfigS V N M =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hlowered_site_sum_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  exact
    tasaki23_successor_sector_common_energy_of_site_sum_pos_of_predictedCasimirValue
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ
      (tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
        A N hBA hΦ_pred)
      hlowered_site_sum_pos

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 adjacent successor step with successor
predicted-GS membership from lowered site-sum positivity**: if the source
representative lies in the predicted toy ground-state subspace, then the
successor representative produced by the lowered adjacent-sector step
lies in the same predicted subspace.

The proof uses predicted-GS invariance under `Ŝ^-_tot` and then cancels
the positive real scalar relating the lowered image to the successor
Marshall-positive representative. -/
theorem
    tasaki23_successor_sector_common_energy_with_successor_predictedGS_of_site_sum_pos
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_pred :
      magSectorEmbedding
          (fun τ : magConfigS V N M =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hlowered_site_sum_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      magSectorEmbedding
          (fun τ : magConfigS V N (M + 1) =>
            (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  have hstep :=
    tasaki23_successor_sector_common_energy_of_site_sum_pos_of_mem_bipartiteToyGroundStateSubspacePredicted
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hM hMlt hμ_lt hv_pos hΦ hΦ_pred
      hlowered_site_sum_pos
  rcases hstep with ⟨hsucc_mem, hμ_lt', hv_pos', hΦ', hlowered_ne,
    v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, r, hr_pos, hrel⟩
  have hsmul :
      (totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (r : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) :=
    totalSpinSOpMinus_marshallSignedEmbedding_eq_smul_successor_of_re
      A hrel
  have hlowered_pred :
      (totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N :=
    tasaki23_totalSpinSOpMinus_mulVec_mem_bipartiteToyGroundStateSubspacePredicted
      A N hΦ_pred
  have hsucc_pred :
      magSectorEmbedding
          (fun τ : magConfigS V N (M + 1) =>
            (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N :=
    tasaki23_mem_bipartiteToyGroundStateSubspacePredicted_of_real_smul_eq
      A N (ne_of_gt hr_pos) hsmul hlowered_pred
  exact ⟨hsucc_mem, hμ_lt', hv_pos', hΦ', hlowered_ne,
    v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_pred,
    r, hr_pos, hrel⟩

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 adjacent predicted-GS predecessor step from
raised dominance**: in the canonical orientation `|¬A| ≤ |A|`,
membership of the sector-`M+1` source vector in the predicted toy
ground-state subspace supplies the predicted-Casimir hypothesis needed
by the raised dominance common-energy wrapper.

This is the raising-direction companion to
`tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_mem_bipartiteToyGroundStateSubspacePredicted`.
-/
theorem
    tasaki23_predecessor_sector_common_energy_of_onA_neg_lt_offA_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_pred :
      magSectorEmbedding
          (fun τ : magConfigS V N (M + 1) =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hdominates :
      ∀ τ : magConfigS V N M,
        -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23SignedRaisingSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23SignedRaisingSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    M ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpPlus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_pred : magConfigS V N M → ℝ,
      μ < c ∧ (∀ τ, 0 < v_pred τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N M,
          (((totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_pred τ) := by
  exact
    tasaki23_predecessor_sector_common_energy_of_onA_neg_lt_offA_of_predictedCasimirValue
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ
      (tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
        A N hBA hΦ_pred)
      hdominates

/-- **Tasaki §2.5 Theorem 2.3 (Marshall–Lieb–Mattis general spin-S), final
statement** as a `Prop`.

The hypothesis bundle matches the per-sector bundled Theorem 2.2
`marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full`
(PR #869) exactly. Given:
- real symmetric coupling `J` (`(J x y).im = 0`, `star (J x y) = J x y`,
  `J x y = J y x`, `0 ≤ (J x y).re`);
- bipartite support (`A x = A y → J x y = 0`);
- positive on the bipartite complete graph (`Adj → 0 < (J x y).re`);
- non-empty sublattices (`|A| ≥ 1`, `|¬A| ≥ 1`);
- a uniform spectral shift `c` strictly above the dressed diagonal;
- the intermediate-existence hypothesis from Theorem 2.2 (#869);
- each admissible sector `M` is non-empty;

the conclusion asserts existence of a common ground-state energy `μ`
realised on every admissible sector by a Marshall-positive
eigenvector (Tasaki (2.5.4) with `σ = M`), with within-sector
uniqueness up to positive scalar, plus global minimality of `μ`.

The proof iterates #869 sector-by-sector across
`tasaki23GroundStateSectors A N`. -/
def tasaki_2_5_theorem_2_3
    (A : V → Bool) (N : ℕ) (J : V → V → ℂ) (c : ℝ) : Prop :=
  -- Coupling hypotheses (matching #869's bundle).
  (∀ x y, (J x y).im = 0) →
  (∀ x y, star (J x y) = J x y) →
  (∀ x y, J x y = J y x) →
  (∀ x y, 0 ≤ (J x y).re) →
  (∀ x y, A x = A y → J x y = 0) →
  (∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re) →
  -- Spectral shift strictly above the dressed diagonal (matching #869).
  (∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c) →
  -- Intermediate-existence hypothesis (matching #869).
  (∀ τ : V → Fin (N + 1), ∀ x : V, ∃ z, A z ≠ A x ∧ (τ z).val < N) →
  -- Non-empty sublattices (Tasaki Theorem 2.3 hypothesis `|A| ≥ 1`, `|¬A| ≥ 1`).
  (1 ≤ (Finset.univ.filter (fun x : V => A x = true)).card) →
  (1 ≤ (Finset.univ.filter (fun x : V => (! A x) = true)).card) →
  -- Conclusion.
  ∃ μ : ℝ,
    -- (Existence + Marshall expansion + sector uniqueness) per admissible sector.
    (∀ M ∈ tasaki23GroundStateSectors (V := V) A N,
      [Nonempty (magConfigS V N M)] →
      ∃ v : magConfigS V N M → ℝ,
        μ < c ∧ (∀ σ, 0 < v σ) ∧
        (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
          (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
          (∀ σ, magSumS σ ≠ M → Ψ' σ = 0) →
          (∀ τ : magConfigS V N M, 0 < (marshallSignS A τ.1).re * (Ψ' τ.1).re) →
          μ' = μ ∧ ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N M,
              (Ψ' τ.1).re = r * ((marshallSignS A τ.1).re * v τ))) ∧
    -- Global minimality of μ across all eigenvalues.
    (∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
      Ψ' ≠ 0 →
      (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
      μ ≤ μ')

/-- **Per-sector existence step (toward Tasaki §2.5 Theorem 2.3 proof)**.

For each admissible magnetization sector `M ∈ tasaki23GroundStateSectors A N`
with `Nonempty (magConfigS V N M)`, the per-sector bundled Theorem 2.2
`marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full` (#869)
gives a Marshall-positive ground state of the spin-`S` antiferromagnetic
Heisenberg Hamiltonian (Tasaki (2.5.4) with `σ = M`) at some sector
eigenvalue `μ_M < c`, plus within-sector uniqueness up to positive scalar.

This is the first step of the Tasaki §2.5 Theorem 2.3 proof
("essentially a straightforward modification of that of Theorem 2.2"):
the proof of `tasaki_2_5_theorem_2_3` then iterates this per-sector
existence across the admissible range and shows the sector eigenvalues
`μ_M` coincide (constancy via the SU(2) ladder
`heisenbergHamiltonianS_commute_totalSpinSOpMinus`) and that the common
value is the global minimum.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42. -/
theorem tasaki_2_5_theorem_2_3_sector_existence
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      μ < c ∧ (∀ σ, 0 < v σ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
      (∀ σ, magSumS σ ≠ M →
        magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) σ = 0) ∧
      (∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
        (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
        (∀ σ, magSumS σ ≠ M → Ψ' σ = 0) →
        (∀ τ : magConfigS V N M, 0 < (marshallSignS A τ.1).re * (Ψ' τ.1).re) →
        μ' = μ ∧ ∃ r : ℝ, 0 < r ∧
          ∀ τ : magConfigS V N M,
            (Ψ' τ.1).re = r * ((marshallSignS A τ.1).re * v τ)) :=
  marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full
    A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate

/-- **Tasaki §2.5 Theorem 2.3 sector-existence successor chain link
with predicted Casimir**: choose the source-sector Marshall-positive
ground-state vector from the per-sector Theorem 2.2 wrapper, then apply
the adjacent ladder-image predicted-Casimir successor package.

The remaining hypotheses are exactly the two mathematical inputs still
needed for the chosen Theorem 2.2 sector vector: predicted total-Casimir
eigenvalue and lowered site-sum positivity. -/
theorem tasaki23_successor_sector_existence_with_lowered_predictedCasimir
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    (hsource_cas :
      ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        (totalSpinSSquared V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_site_sum :
      ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        ∀ τ : magConfigS V N (M + 1),
          0 < (marshallSignS A τ.1).re *
            (∑ x : V,
              (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      (M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
        μ < c ∧ (∀ τ, 0 < v τ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
        ∃ v_succ : magConfigS V N (M + 1) → ℝ,
          μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
          (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
          ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N (M + 1),
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
                r * ((marshallSignS A τ.1).re * v_succ τ)) ∧
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
  obtain ⟨μ, v, hμ_lt, hv_pos, hΦ, _hsupport, _huniq⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := M) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  exact ⟨μ, v,
    tasaki23_successor_common_energy_with_lowered_predictedCasimir
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ
      (hsource_cas hμ_lt hv_pos hΦ)
      (hsource_site_sum hμ_lt hv_pos hΦ)⟩

/-- **Tasaki §2.5 Theorem 2.3 successor predicted-Casimir
propagation**: in the lowering-direction sector-existence step, the
successor representative returned by the adjacent-sector comparison also
has the Theorem 2.3 predicted total-Casimir eigenvalue.

The existing package already proves that the lowered source vector has
the predicted Casimir eigenvalue and that its real parts are a positive
real scalar multiple of the successor representative in Marshall
coordinates.  Since both vectors are real and supported in the successor
sector, this is a full scalar equality, so the Casimir eigenvector
equation cancels the scalar. -/
theorem
    tasaki23_successor_sector_existence_with_successor_predictedCasimir
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    (hsource_cas :
      ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        (totalSpinSSquared V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_site_sum :
      ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        ∀ τ : magConfigS V N (M + 1),
          0 < (marshallSignS A τ.1).re *
            (∑ x : V,
              (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      (M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
        μ < c ∧ (∀ τ, 0 < v τ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
        ∃ v_succ : magConfigS V N (M + 1) → ℝ,
          μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
          (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
          (totalSpinSSquared V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N (M + 1) =>
                (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ : magConfigS V N (M + 1) =>
                  (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
          ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N (M + 1),
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
                r * ((marshallSignS A τ.1).re * v_succ τ)) ∧
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
  obtain ⟨μ, v, hpack⟩ :=
    tasaki23_successor_sector_existence_with_lowered_predictedCasimir
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hsource_cas hsource_site_sum
  have hM_succ := hpack.1.1
  have hμ_lt := hpack.1.2.1
  have hv_pos := hpack.1.2.2.1
  have hΦ := hpack.1.2.2.2.1
  have hlowered_ne := hpack.1.2.2.2.2.1
  have hsucc := hpack.1.2.2.2.2.2
  have hcas_lowered := hpack.2
  obtain ⟨v_succ, hsucc_pack⟩ := hsucc
  have hμ_succ_lt := hsucc_pack.1
  have hv_succ_pos := hsucc_pack.2.1
  have hΦ_succ := hsucc_pack.2.2.1
  obtain ⟨r, hr_pos, hrel⟩ := hsucc_pack.2.2.2
  have hsmul :
      (totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (r : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) :=
    totalSpinSOpMinus_marshallSignedEmbedding_eq_smul_successor_of_re
      A hrel
  have hsucc_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) :=
    tasaki23_totalSpinSSquared_predictedCasimirValue_of_real_smul_eq
      A N (ne_of_gt hr_pos) hsmul hcas_lowered
  exact ⟨μ, v,
    ⟨hM_succ, hμ_lt, hv_pos, hΦ, hlowered_ne,
      ⟨v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_cas,
        ⟨r, hr_pos, hrel⟩⟩⟩,
    hcas_lowered⟩

/-- **Tasaki §2.5 Theorem 2.3 sector-existence predecessor chain link
with predicted Casimir**: choose the sector-`M+1` Marshall-positive
ground-state vector from the per-sector Theorem 2.2 wrapper, then apply
the adjacent ladder-image predicted-Casimir predecessor package.

This is the raising-direction companion to
`tasaki23_successor_sector_existence_with_lowered_predictedCasimir`. -/
theorem tasaki23_predecessor_sector_existence_with_raised_predictedCasimir
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    (hsource_cas :
      ∀ {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        (totalSpinSSquared V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N (M + 1) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            magSectorEmbedding
              (fun τ : magConfigS V N (M + 1) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_site_sum :
      ∀ {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        ∀ τ : magConfigS V N M,
          0 < (marshallSignS A τ.1).re *
            (∑ x : V,
              (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    ∃ (μ : ℝ) (v : magConfigS V N (M + 1) → ℝ),
      (M ∈ tasaki23GroundStateSectors (V := V) A N ∧
        μ < c ∧ (∀ τ, 0 < v τ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
        ∃ v_pred : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v_pred τ) ∧
          (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
          ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N M,
              (((totalSpinSOpPlus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
                r * ((marshallSignS A τ.1).re * v_pred τ)) ∧
        (totalSpinSSquared V N).mulVec
            ((totalSpinSOpPlus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N (M + 1) =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            ((totalSpinSOpPlus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N (M + 1) =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  obtain ⟨μ, v, hμ_lt, hv_pos, hΦ, _hsupport, _huniq⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := M + 1) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym
      hJ_bipartite hc_strict h_intermediate
  exact ⟨μ, v,
    tasaki23_predecessor_common_energy_with_raised_predictedCasimir
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ
      (hsource_cas hμ_lt hv_pos hΦ)
      (hsource_site_sum hμ_lt hv_pos hΦ)⟩

/-- **Tasaki §2.5 Theorem 2.3 sector-existence successor chain link
with predicted Casimir from lowered dominance**: choose the source-sector
Marshall-positive ground-state vector from the per-sector Theorem 2.2
wrapper, convert the lowered off-`A` dominance hypothesis into strict
lowered site-sum positivity, then apply the predicted-Casimir successor
package.

The dominance estimate remains an explicit hypothesis; this theorem only
connects that estimate to the sector-existence adjacent-chain wrapper. -/
theorem
    tasaki23_successor_sector_existence_with_lowered_predictedCasimir_of_onA_neg_lt_offA
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    (hsource_cas :
      ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        (totalSpinSSquared V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_dominance :
      ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        ∀ τ : magConfigS V N (M + 1),
          -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
              tasaki23SignedLoweringSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
            ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
              tasaki23SignedLoweringSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      (M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
        μ < c ∧ (∀ τ, 0 < v τ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
        ∃ v_succ : magConfigS V N (M + 1) → ℝ,
          μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
          (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
          ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N (M + 1),
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
                r * ((marshallSignS A τ.1).re * v_succ τ)) ∧
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
    tasaki23_successor_sector_existence_with_lowered_predictedCasimir
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hsource_cas
      (fun {μ : ℝ} {v : magConfigS V N M → ℝ} hμ_lt hv_pos hΦ τ =>
        tasaki23_signed_lowering_site_sum_pos_of_onA_neg_lt_offA
          A (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
          τ (hsource_dominance hμ_lt hv_pos hΦ τ))

/-- **Tasaki §2.5 Theorem 2.3 sector-existence predecessor chain link
with predicted Casimir from raised dominance**: choose the sector-`M+1`
Marshall-positive ground-state vector from the per-sector Theorem 2.2
wrapper, convert the raised off-`A` dominance hypothesis into strict
raised site-sum positivity, then apply the predicted-Casimir predecessor
package.

This is the raising-direction companion to the lowered dominance wrapper
above. -/
theorem
    tasaki23_predecessor_sector_existence_with_raised_predictedCasimir_of_onA_neg_lt_offA
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    (hsource_cas :
      ∀ {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        (totalSpinSSquared V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N (M + 1) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            magSectorEmbedding
              (fun τ : magConfigS V N (M + 1) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_dominance :
      ∀ {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        ∀ τ : magConfigS V N M,
          -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
              tasaki23SignedRaisingSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
            ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
              tasaki23SignedRaisingSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    ∃ (μ : ℝ) (v : magConfigS V N (M + 1) → ℝ),
      (M ∈ tasaki23GroundStateSectors (V := V) A N ∧
        μ < c ∧ (∀ τ, 0 < v τ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
        ∃ v_pred : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v_pred τ) ∧
          (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
          ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N M,
              (((totalSpinSOpPlus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
                r * ((marshallSignS A τ.1).re * v_pred τ)) ∧
        (totalSpinSSquared V N).mulVec
            ((totalSpinSOpPlus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N (M + 1) =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            ((totalSpinSOpPlus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N (M + 1) =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  exact
    tasaki23_predecessor_sector_existence_with_raised_predictedCasimir
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hsource_cas
      (fun {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ} hμ_lt hv_pos hΦ τ =>
        tasaki23_signed_raising_site_sum_pos_of_onA_neg_lt_offA
          A (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
          τ (hsource_dominance hμ_lt hv_pos hΦ τ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 sector-existence successor chain link
with predicted-GS membership from lowered dominance**: in the canonical
orientation `|¬A| ≤ |A|`, choose the source-sector Marshall-positive
ground-state vector from the per-sector Theorem 2.2 wrapper, use
predicted-GS membership to supply the predicted-Casimir input, and
convert the lowered off-`A` dominance hypothesis into the strict
site-sum positivity input.

The membership and dominance estimates remain explicit callbacks for the
chosen source-sector vector. -/
theorem
    tasaki23_successor_sector_existence_with_lowered_predictedGS_of_onA_neg_lt_offA
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    (hsource_pred :
      ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
          bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_dominance :
      ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        ∀ τ : magConfigS V N (M + 1),
          -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
              tasaki23SignedLoweringSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
            ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
              tasaki23SignedLoweringSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      (M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
        μ < c ∧ (∀ τ, 0 < v τ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
        ∃ v_succ : magConfigS V N (M + 1) → ℝ,
          μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
          (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
          ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N (M + 1),
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
                r * ((marshallSignS A τ.1).re * v_succ τ)) ∧
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
    tasaki23_successor_sector_existence_with_lowered_predictedCasimir_of_onA_neg_lt_offA
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt
      (fun {μ : ℝ} {v : magConfigS V N M → ℝ} hμ_lt hv_pos hΦ =>
        tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
          A N hBA (hsource_pred hμ_lt hv_pos hΦ))
      hsource_dominance

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 sector-existence predecessor chain link
with predicted-GS membership from raised dominance**: in the canonical
orientation `|¬A| ≤ |A|`, choose the sector-`M+1`
Marshall-positive ground-state vector from the per-sector Theorem 2.2
wrapper, use predicted-GS membership to supply the predicted-Casimir
input, and convert the raised off-`A` dominance hypothesis into the
strict site-sum positivity input.

This is the raising-direction companion to the lowered predicted-GS
sector-existence wrapper. -/
theorem
    tasaki23_predecessor_sector_existence_with_raised_predictedGS_of_onA_neg_lt_offA
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    (hsource_pred :
      ∀ {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
          bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_dominance :
      ∀ {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        ∀ τ : magConfigS V N M,
          -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
              tasaki23SignedRaisingSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
            ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
              tasaki23SignedRaisingSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    ∃ (μ : ℝ) (v : magConfigS V N (M + 1) → ℝ),
      (M ∈ tasaki23GroundStateSectors (V := V) A N ∧
        μ < c ∧ (∀ τ, 0 < v τ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
        ∃ v_pred : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v_pred τ) ∧
          (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
          ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N M,
              (((totalSpinSOpPlus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
                r * ((marshallSignS A τ.1).re * v_pred τ)) ∧
        (totalSpinSSquared V N).mulVec
            ((totalSpinSOpPlus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N (M + 1) =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            ((totalSpinSOpPlus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N (M + 1) =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  exact
    tasaki23_predecessor_sector_existence_with_raised_predictedCasimir_of_onA_neg_lt_offA
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt
      (fun {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ} hμ_lt hv_pos hΦ =>
        tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
          A N hBA (hsource_pred hμ_lt hv_pos hΦ))
      hsource_dominance

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS energy interval chain**:
in the canonical orientation `|¬A| ≤ |A|`, choose the left endpoint
sector by the per-sector Theorem 2.2 wrapper and propagate its energy
through the whole admissible interval by the predicted-GS lowered
dominance common-energy step.

The theorem deliberately keeps the two remaining mathematical inputs as
callbacks for each currently chosen source vector: membership in
`bipartiteToyGroundStateSubspacePredicted A N` and the lowered off-`A`
dominance estimate. It isolates the discrete interval induction needed
for the final Theorem 2.3 proof. -/
theorem tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_onA_neg_lt_offA
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_pred :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_dominance :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
              ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
  let left : ℕ :=
    min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  let right : ℕ :=
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  have hleft_mem : left ∈ tasaki23GroundStateSectors (V := V) A N := by
    simpa [left] using tasaki23GroundStateSectors_left_mem (V := V) A N
  letI : Nonempty (magConfigS V N left) := hsector_nonempty left hleft_mem
  obtain ⟨μ, v_left, hμ_left_lt, hv_left_pos, hΦ_left, _hsupport, _huniq⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := left) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  refine ⟨μ, ?_⟩
  have hchain :
      ∀ M, left ≤ M → M ≤ right →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
    intro M hleft_le hright_le
    induction M, hleft_le using Nat.le_induction with
    | base =>
        exact ⟨v_left, hμ_left_lt, hv_left_pos, hΦ_left⟩
    | succ M hleft_le ih =>
        have hM_le_right : M ≤ right := Nat.le_of_succ_le hright_le
        have hMlt : M < right := Nat.lt_of_succ_le hright_le
        have hM_mem : M ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          simpa [left, right] using And.intro hleft_le hM_le_right
        have hsucc_mem : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          have hleft_succ : left ≤ M + 1 := hleft_le.trans (Nat.le_succ M)
          simpa [left, right] using And.intro hleft_succ hright_le
        letI : Nonempty (magConfigS V N M) :=
          hsector_nonempty M hM_mem
        letI : Nonempty (magConfigS V N (M + 1)) :=
          hsector_nonempty (M + 1) hsucc_mem
        obtain ⟨v, hμ_lt, hv_pos, hΦ⟩ := ih hM_le_right
        have hstep :=
          tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_mem_bipartiteToyGroundStateSubspacePredicted
            A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
            hc_strict h_intermediate hBA hM_mem (by simpa [right] using hMlt)
            hμ_lt hv_pos hΦ
            (hsource_pred hM_mem (by simpa [right] using hMlt) hμ_lt hv_pos hΦ)
            (hsource_dominance hM_mem (by simpa [right] using hMlt) hμ_lt hv_pos hΦ)
        rcases hstep with ⟨_hsucc_mem, _hμ_lt, _hv_pos, _hΦ, _hne,
          v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, _hr⟩
        exact ⟨v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ⟩
  intro M hM
  have hbounds := (tasaki23GroundStateSectors_mem_iff (V := V) A N M).mp hM
  exact hchain M (by simpa [left] using hbounds.1) (by simpa [right] using hbounds.2)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS energy interval chain from
lowered site-sum positivity**: in the canonical orientation `|¬A| ≤ |A|`,
choose the left endpoint sector by the per-sector Theorem 2.2 wrapper and
propagate its energy through the whole admissible interval using the
direct lowered site-sum positivity successor step.

Compared with
`tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_onA_neg_lt_offA`,
this version keeps the actual Marshall-positivity input for
`S^-_{\mathrm{tot}}` as a strict site-sum positivity callback, without
packaging it first as an off-`A`/on-`A` dominance inequality. -/
theorem tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_lowered_site_sum_pos
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_pred :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_site_sum_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (∑ x : V,
                (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
                  (magSectorEmbedding
                    (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
  let left : ℕ :=
    min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  let right : ℕ :=
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  have hleft_mem : left ∈ tasaki23GroundStateSectors (V := V) A N := by
    simpa [left] using tasaki23GroundStateSectors_left_mem (V := V) A N
  letI : Nonempty (magConfigS V N left) := hsector_nonempty left hleft_mem
  obtain ⟨μ, v_left, hμ_left_lt, hv_left_pos, hΦ_left, _hsupport, _huniq⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := left) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  refine ⟨μ, ?_⟩
  have hchain :
      ∀ M, left ≤ M → M ≤ right →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
    intro M hleft_le hright_le
    induction M, hleft_le using Nat.le_induction with
    | base =>
        exact ⟨v_left, hμ_left_lt, hv_left_pos, hΦ_left⟩
    | succ M hleft_le ih =>
        have hM_le_right : M ≤ right := Nat.le_of_succ_le hright_le
        have hMlt : M < right := Nat.lt_of_succ_le hright_le
        have hM_mem : M ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          simpa [left, right] using And.intro hleft_le hM_le_right
        have hsucc_mem : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          have hleft_succ : left ≤ M + 1 := hleft_le.trans (Nat.le_succ M)
          simpa [left, right] using And.intro hleft_succ hright_le
        letI : Nonempty (magConfigS V N M) :=
          hsector_nonempty M hM_mem
        letI : Nonempty (magConfigS V N (M + 1)) :=
          hsector_nonempty (M + 1) hsucc_mem
        obtain ⟨v, hμ_lt, hv_pos, hΦ⟩ := ih hM_le_right
        have hstep :=
          tasaki23_successor_sector_common_energy_of_site_sum_pos_of_mem_bipartiteToyGroundStateSubspacePredicted
            A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
            hc_strict h_intermediate hBA hM_mem (by simpa [right] using hMlt)
            hμ_lt hv_pos hΦ
            (hsource_pred hM_mem (by simpa [right] using hMlt) hμ_lt hv_pos hΦ)
            (hsource_site_sum_pos hM_mem (by simpa [right] using hMlt) hμ_lt hv_pos hΦ)
        rcases hstep with ⟨_hsucc_mem, _hμ_lt, _hv_pos, _hΦ, _hne,
          v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, _hr⟩
        exact ⟨v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ⟩
  intro M hM
  have hbounds := (tasaki23GroundStateSectors_mem_iff (V := V) A N M).mp hM
  exact hchain M (by simpa [left] using hbounds.1) (by simpa [right] using hbounds.2)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS energy interval chain from
lowered vector Marshall positivity**: in the canonical orientation
`|¬A| ≤ |A|`, choose the left endpoint sector by the per-sector
Theorem 2.2 wrapper and propagate its energy through the admissible
interval using the actual Marshall positivity of the lowered ladder
image.

This is the vector-positivity version of
`tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_lowered_site_sum_pos`.
The source-form bridge
`tasaki23_lowered_site_sum_pos_of_source_lowered_marshall_pos` converts
the Marshall-signed positive real representative input into the site-sum
callback consumed by the existing successor step. -/
theorem tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_lowered_marshall_pos
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_pred :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_lowered_marshall_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
  exact
    tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_lowered_site_sum_pos
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hsource_pred
      (fun {M : ℕ} hM hMlt {μ : ℝ} {v : magConfigS V N M → ℝ}
          hμ_lt hv_pos hΦ =>
        tasaki23_lowered_site_sum_pos_of_source_lowered_marshall_pos A v
          (hsource_lowered_marshall_pos hM hMlt hμ_lt hv_pos hΦ))

end LatticeSystem.Quantum
