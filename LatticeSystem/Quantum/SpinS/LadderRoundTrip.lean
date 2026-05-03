import LatticeSystem.Quantum.SpinS.IterateInductiveNonvanishingPlus

/-!
# Round-trip identity on the saturated-ferromagnet ladder

For `[Nonempty V]`, applying `(Ŝ^-_{tot})^{|V|·N}` followed by
`(Ŝ^+_{tot})^{|V|·N}` to the all-up state returns a non-zero
multiple of the all-up state — and symmetrically for the
opposite-order round-trip starting from the all-down state.

Combines PR #909 (lowering reaches `c1 · |σ_⊥⟩`) with PR #910
(raising from `|σ_⊥⟩` reaches `c2 · |σ_⊤⟩`) to give the round-trip
scalar `c1 · c2 ≠ 0`.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Round-trip lowering then raising** returns a non-zero multiple
of `|σ_⊤⟩`:

  `(Ŝ^+_{tot})^{|V|·N} · (Ŝ^-_{tot})^{|V|·N} · |σ_⊤⟩ = c · |σ_⊤⟩`

for some non-zero scalar `c`.

Proof: chain PR #909
(`(Ŝ^-_{tot})^{|V|·N} · |σ_⊤⟩ = c₁ · |σ_⊥⟩`, `c₁ ≠ 0`) with
PR #910 (`(Ŝ^+_{tot})^{|V|·N} · |σ_⊥⟩ = c₂ · |σ_⊤⟩`, `c₂ ≠ 0`).
The composite scalar `c = c₁ · c₂` is non-zero. -/
theorem totalSpinSOpPlus_pow_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero_eq_smul
    [Nonempty V] :
    ∃ c : ℂ, c ≠ 0 ∧
      ((totalSpinSOpPlus V N) ^ (Fintype.card V * N)).mulVec
        (((totalSpinSOpMinus V N) ^ (Fintype.card V * N)).mulVec
          (allAlignedStateS V N (0 : Fin (N + 1)))) =
        c • allAlignedStateS V N (0 : Fin (N + 1)) := by
  obtain ⟨c1, hc1_ne, hc1⟩ :=
    totalSpinSOpMinus_pow_card_mul_N_allAlignedStateS_zero_eq_smul_last
      (V := V) (N := N)
  obtain ⟨c2, hc2_ne, hc2⟩ :=
    totalSpinSOpPlus_pow_card_mul_N_allAlignedStateS_last_eq_smul_zero
      (V := V) (N := N)
  refine ⟨c1 * c2, mul_ne_zero hc1_ne hc2_ne, ?_⟩
  rw [hc1, Matrix.mulVec_smul, hc2, smul_smul, mul_comm c1 c2]

/-- Symmetric round-trip raising then lowering on `|σ_⊥⟩`:

  `(Ŝ^-_{tot})^{|V|·N} · (Ŝ^+_{tot})^{|V|·N} · |σ_⊥⟩ = c · |σ_⊥⟩`

for some non-zero scalar `c`. -/
theorem totalSpinSOpMinus_pow_mulVec_totalSpinSOpPlus_pow_allAlignedStateS_last_eq_smul
    [Nonempty V] :
    ∃ c : ℂ, c ≠ 0 ∧
      ((totalSpinSOpMinus V N) ^ (Fintype.card V * N)).mulVec
        (((totalSpinSOpPlus V N) ^ (Fintype.card V * N)).mulVec
          (allAlignedStateS V N (Fin.last N))) =
        c • allAlignedStateS V N (Fin.last N) := by
  obtain ⟨c1, hc1_ne, hc1⟩ :=
    totalSpinSOpPlus_pow_card_mul_N_allAlignedStateS_last_eq_smul_zero
      (V := V) (N := N)
  obtain ⟨c2, hc2_ne, hc2⟩ :=
    totalSpinSOpMinus_pow_card_mul_N_allAlignedStateS_zero_eq_smul_last
      (V := V) (N := N)
  refine ⟨c1 * c2, mul_ne_zero hc1_ne hc2_ne, ?_⟩
  rw [hc1, Matrix.mulVec_smul, hc2, smul_smul, mul_comm c1 c2]

end LatticeSystem.Quantum
