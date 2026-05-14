import LatticeSystem.Quantum.SpinS.IterateInductiveNonvanishing
import LatticeSystem.Quantum.SpinS.AllAlignedStateMagShift
import LatticeSystem.Quantum.SpinS.LadderBottom

/-!
# Symmetric inductive non-vanishing of `(Ŝ^+_{tot})^k · |σ_⊥⟩`

Mirror of PR #895 for the raising side: for `[Nonempty V]` and
every `k ≤ |V|·N`, `(Ŝ^+_{tot})^k · |σ_⊥⟩ ≠ 0`.

Same Casimir-rearrangement strategy, but using PR #894's
**MinusPlus** identity `Ŝ^-_{tot} Ŝ^+_{tot} = Ŝ_{tot}² − (Ŝ^z_{tot})² − Ŝ^z_{tot}`
applied at the lowest-weight state. The identical scalar
`(k+1)(2m_max − k)` arises in the eigenvalue identity, with the
`Ŝ^z_{tot}` eigenvalue `−m_max + k` (from PR #887 raising side).

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Eigenvalue identity from Casimir rearrangement (raising side) -/

/-- Mirror of PR #895's eigenvalue identity for the raising side:
for every `k : ℕ`,

  `Ŝ^-_{tot} · ((Ŝ^+_{tot})^{k+1} · |σ_⊥⟩) =
    ((k+1) · (|V|·N − k)) • ((Ŝ^+_{tot})^k · |σ_⊥⟩)`. -/
theorem totalSpinSOpMinus_mulVec_totalSpinSOpPlus_pow_succ_allAlignedStateS_last
    [Nonempty V] (k : ℕ) :
    (totalSpinSOpMinus V N).mulVec
      (((totalSpinSOpPlus V N) ^ (k + 1)).mulVec
        (allAlignedStateS V N (Fin.last N))) =
      (((k + 1 : ℕ) : ℂ) *
          ((Fintype.card V : ℂ) * (N : ℂ) - (k : ℂ))) •
        ((totalSpinSOpPlus V N) ^ k).mulVec
          (allAlignedStateS V N (Fin.last N)) := by
  set v_k := ((totalSpinSOpPlus V N) ^ k).mulVec
    (allAlignedStateS V N (Fin.last N))
  rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  -- Apply Casimir MinusPlus rearrangement.
  rw [totalSpinSOpMinus_mul_totalSpinSOpPlus_eq_casimir_minus_z_sq_sub_z]
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec]
  -- Casimir eigenvalue: m_max(m_max+1).
  have h_casimir : (totalSpinSSquared V N).mulVec v_k =
      ((Fintype.card V : ℂ) * (N : ℂ) / 2 *
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 + 1)) • v_k := by
    exact totalSpinSSquared_mulVec_totalSpinSOpPlus_pow_allAlignedStateS_last k
  -- Ŝ^z eigenvalue: -m_max + k.
  have h_z : (totalSpinSOp3 V N).mulVec v_k =
      (-((Fintype.card V : ℂ) * (N : ℂ) / 2) + (k : ℂ)) • v_k := by
    exact totalSpinSOp3_mulVec_totalSpinSOpPlus_pow_allAlignedStateS_last k
  -- (Ŝ^z)² eigenvalue: (-m_max + k)².
  have h_z_sq : ((totalSpinSOp3 V N : ManyBodyOpS V N) *
      totalSpinSOp3 V N).mulVec v_k =
      ((-((Fintype.card V : ℂ) * (N : ℂ) / 2) + (k : ℂ)) *
        (-((Fintype.card V : ℂ) * (N : ℂ) / 2) + (k : ℂ))) • v_k := by
    rw [← Matrix.mulVec_mulVec, h_z, Matrix.mulVec_smul, h_z, smul_smul]
  rw [h_casimir, h_z_sq, h_z]
  rw [← sub_smul, ← sub_smul]
  congr 1
  push_cast
  ring

/-! ## Inductive non-vanishing (raising side) -/

/-- **Inductive non-vanishing of the saturated-ferromagnet ladder
(raising side)**: for every `k ≤ |V|·N`, the iterate
`(Ŝ^+_{tot})^k · |σ_⊥⟩` is non-zero.

Mirror of PR #895; same inductive scheme using the Casimir
rearrangement (raising-side eigenvalue identity above). -/
theorem totalSpinSOpPlus_pow_allAlignedStateS_last_ne_zero
    [Nonempty V] {k : ℕ} (hk : k ≤ Fintype.card V * N) :
    ((totalSpinSOpPlus V N) ^ k).mulVec
        (allAlignedStateS V N (Fin.last N)) ≠ 0 := by
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.one_mulVec]
    exact allAlignedStateS_ne_zero _
  | succ k ih =>
    have hk_lt : k < Fintype.card V * N := hk
    have hk_le : k ≤ Fintype.card V * N := Nat.le_of_lt hk_lt
    have h_vk_ne : ((totalSpinSOpPlus V N) ^ k).mulVec
        (allAlignedStateS V N (Fin.last N)) ≠ 0 := ih hk_le
    intro h_vk_succ_zero
    have h_eigen :=
      totalSpinSOpMinus_mulVec_totalSpinSOpPlus_pow_succ_allAlignedStateS_last
        (V := V) (N := N) k
    rw [h_vk_succ_zero, Matrix.mulVec_zero] at h_eigen
    have h_scalar_ne : (((k + 1 : ℕ) : ℂ) *
        ((Fintype.card V : ℂ) * (N : ℂ) - (k : ℂ))) ≠ 0 := by
      apply mul_ne_zero
      · exact_mod_cast (Nat.succ_ne_zero k)
      · intro h_eq
        have hcN : ((Fintype.card V : ℂ) * (N : ℂ)) = (k : ℂ) :=
          sub_eq_zero.mp h_eq
        have hcN' : ((Fintype.card V * N : ℕ) : ℂ) = ((k : ℕ) : ℂ) := by
          push_cast; exact hcN
        have : (Fintype.card V * N : ℕ) = k := by
          exact_mod_cast hcN'
        omega
    have h_vk_zero := (smul_eq_zero.mp h_eigen.symm).resolve_left h_scalar_ne
    exact h_vk_ne h_vk_zero

/-! ## Symmetric maximal-raising iterate identification (with non-zero scalar) -/

/-- **Maximal-raising iterate identification** (extension of #909
raising side): there exists a **non-zero** scalar `c : ℂ` with
`(Ŝ^+_{tot})^{|V|·N} · |σ_⊥⟩ = c • |σ_⊤⟩`. -/
theorem totalSpinSOpPlus_pow_card_mul_N_allAlignedStateS_last_eq_smul_zero
    [Nonempty V] :
    ∃ c : ℂ, c ≠ 0 ∧
      ((totalSpinSOpPlus V N) ^ (Fintype.card V * N)).mulVec
          (allAlignedStateS V N (Fin.last N)) =
        c • allAlignedStateS V N (0 : Fin (N + 1)) := by
  obtain ⟨c, hc⟩ :=
    Submodule.mem_span_singleton.mp
      (totalSpinSOpPlus_pow_card_mul_N_allAlignedStateS_last_mem_span_zero
        (V := V) (N := N))
  refine ⟨c, ?_, hc.symm⟩
  intro hc_zero
  rw [hc_zero, zero_smul] at hc
  have h_ne :=
    totalSpinSOpPlus_pow_allAlignedStateS_last_ne_zero (V := V) (N := N)
      (k := Fintype.card V * N) le_rfl
  exact h_ne hc.symm

end LatticeSystem.Quantum
