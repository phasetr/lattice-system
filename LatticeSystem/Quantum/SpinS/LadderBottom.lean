import LatticeSystem.Quantum.SpinS.MagSubspaceExtremalDim
import LatticeSystem.Quantum.SpinS.IterateInductiveNonvanishing

/-!
# The maximal-lowering iterate is a non-zero multiple of `|σ_⊥⟩`

For `[Nonempty V]`, the iterate
`(Ŝ^-_{tot})^{|V|·N} · |σ_⊤⟩` lies on the line through the all-down
state `|σ_⊥⟩`, with non-zero coefficient. This identifies the
"ladder reaches the bottom" boundary of the saturated-ferromagnet
ladder explicitly with the all-down basis state.

Argument:
- PR #887 places the iterate in the `Ŝ^z_{tot}`-eigenspace at
  `m_max - |V|·N = -m_max`.
- PR #908 identifies `magSubspaceS V N (-m_max) = span {|σ_⊥⟩}`.
- Hence the iterate is a scalar multiple of `|σ_⊥⟩`.
- PR #895 ensures the iterate is non-zero, so the scalar is non-zero.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Maximal-lowering iterate is a multiple of `|σ_⊥⟩` -/

/-- The iterate `(Ŝ^-_{tot})^{|V|·N} · |σ_⊤⟩` lies in the line
through the all-down state. -/
theorem totalSpinSOpMinus_pow_card_mul_N_allAlignedStateS_zero_mem_span_last
    [Nonempty V] :
    ((totalSpinSOpMinus V N) ^ (Fintype.card V * N)).mulVec
        (allAlignedStateS V N (0 : Fin (N + 1))) ∈
      Submodule.span ℂ {(allAlignedStateS V N (Fin.last N) :
        (V → Fin (N + 1)) → ℂ)} := by
  set v := ((totalSpinSOpMinus V N) ^ (Fintype.card V * N)).mulVec
    (allAlignedStateS V N (0 : Fin (N + 1)))
  -- v is an Ŝ^z_tot eigenvector at -m_max.
  have h_eigen : (totalSpinSOp3 V N).mulVec v =
      (-((Fintype.card V : ℂ) * (N : ℂ) / 2)) • v := by
    have h := totalSpinSOp3_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero
      (V := V) (N := N) (Fintype.card V * N)
    convert h using 2
    push_cast
    ring
  have hv_mem : v ∈ magSubspaceS V N (-((Fintype.card V : ℂ) * (N : ℂ) / 2)) := by
    rw [mem_magSubspaceS_iff]
    exact h_eigen
  rw [magSubspaceS_neg_mMax_eq_span_allAlignedStateS_last] at hv_mem
  exact hv_mem

/-- **Maximal-lowering iterate identification**: there exists a
**non-zero** scalar `c : ℂ` with
`(Ŝ^-_{tot})^{|V|·N} · |σ_⊤⟩ = c • |σ_⊥⟩`. -/
theorem totalSpinSOpMinus_pow_card_mul_N_allAlignedStateS_zero_eq_smul_last
    [Nonempty V] :
    ∃ c : ℂ, c ≠ 0 ∧
      ((totalSpinSOpMinus V N) ^ (Fintype.card V * N)).mulVec
          (allAlignedStateS V N (0 : Fin (N + 1))) =
        c • allAlignedStateS V N (Fin.last N) := by
  obtain ⟨c, hc⟩ :=
    Submodule.mem_span_singleton.mp
      (totalSpinSOpMinus_pow_card_mul_N_allAlignedStateS_zero_mem_span_last
        (V := V) (N := N))
  refine ⟨c, ?_, hc.symm⟩
  -- The iterate is non-zero (PR #895), so c ≠ 0.
  intro hc_zero
  rw [hc_zero, zero_smul] at hc
  have h_ne :=
    totalSpinSOpMinus_pow_allAlignedStateS_zero_ne_zero (V := V) (N := N)
      (k := Fintype.card V * N) le_rfl
  exact h_ne hc.symm

/-! ## Maximal-raising iterate is a multiple of `|σ_⊤⟩` (symmetric) -/

/-- The iterate `(Ŝ^+_{tot})^{|V|·N} · |σ_⊥⟩` lies in the line
through the all-up state. -/
theorem totalSpinSOpPlus_pow_card_mul_N_allAlignedStateS_last_mem_span_zero
    [Nonempty V] :
    ((totalSpinSOpPlus V N) ^ (Fintype.card V * N)).mulVec
        (allAlignedStateS V N (Fin.last N)) ∈
      Submodule.span ℂ {(allAlignedStateS V N (0 : Fin (N + 1)) :
        (V → Fin (N + 1)) → ℂ)} := by
  set v := ((totalSpinSOpPlus V N) ^ (Fintype.card V * N)).mulVec
    (allAlignedStateS V N (Fin.last N))
  have h_eigen : (totalSpinSOp3 V N).mulVec v =
      ((Fintype.card V : ℂ) * (N : ℂ) / 2) • v := by
    have h := totalSpinSOp3_mulVec_totalSpinSOpPlus_pow_allAlignedStateS_last
      (V := V) (N := N) (Fintype.card V * N)
    convert h using 2
    push_cast
    ring
  have hv_mem : v ∈ magSubspaceS V N ((Fintype.card V : ℂ) * (N : ℂ) / 2) := by
    rw [mem_magSubspaceS_iff]
    exact h_eigen
  rw [magSubspaceS_mMax_eq_span_allAlignedStateS_zero] at hv_mem
  exact hv_mem

end LatticeSystem.Quantum
