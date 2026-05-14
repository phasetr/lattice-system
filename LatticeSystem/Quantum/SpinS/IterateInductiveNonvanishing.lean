import LatticeSystem.Quantum.SpinS.CasimirRearrangement
import LatticeSystem.Quantum.SpinS.AllAlignedStateMagShift
import LatticeSystem.Quantum.SpinS.SaturatedPairLinearIndependent

/-!
# Inductive non-vanishing of `(Ŝ^-_{tot})^k · |σ_⊤⟩` for `k ≤ 2m_max`

Building on PRs #882, #887, #890, #891, #894, this file proves that
the saturated-ferromagnet ladder iterates
`(Ŝ^-_{tot})^k · |σ_⊤⟩` are non-zero for every `k ≤ |V|·N` (i.e.,
`k ≤ 2m_max`).

The argument is a clean inductive use of the Casimir rearrangement:
on any `Ŝ^z_{tot}` eigenvector `v_k` at eigenvalue `m_max − k` that
is also a `(Ŝ_{tot})²` eigenvector at `m_max(m_max + 1)`,

  `Ŝ^+_{tot} Ŝ^-_{tot} v_k =
    ((Ŝ_{tot})² − (Ŝ^z_{tot})² + Ŝ^z_{tot}) v_k =
    (m_max(m_max + 1) − (m_max − k)² + (m_max − k)) v_k =
    (k + 1)(2m_max − k) v_k`.

For `k < 2m_max`, the scalar `(k+1)(2m_max − k)` is non-zero, so
`Ŝ^+_{tot}` applied to `v_{k+1} := Ŝ^-_{tot} v_k` gives a non-zero
multiple of `v_k`. Hence `v_{k+1} ≠ 0` (since otherwise
`Ŝ^+_{tot} 0 = 0` would force `v_k = 0`, contradicting the IH).

This is the technical hurdle that turns PR #891 (pair LI) into the
full `(2m_max + 1)`-vector LI on the saturated-ferromagnet ladder
(deferred to a follow-up textbook unit).

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Eigenvalue identity from Casimir rearrangement -/

/-- The eigenvalue identity at the iterates: for every `k : ℕ`,

  `Ŝ^+_{tot} · ((Ŝ^-_{tot})^{k+1} · |σ_⊤⟩) =
    ((k+1) · (|V|·N − k)) • ((Ŝ^-_{tot})^k · |σ_⊤⟩)`.

Proof: write `(Ŝ^-_{tot})^{k+1} = Ŝ^-_{tot} · (Ŝ^-_{tot})^k` so the
LHS becomes `(Ŝ^+ Ŝ^-).mulVec v_k`. Apply the Casimir rearrangement
(`totalSpinSOpPlus_mul_totalSpinSOpMinus_eq_casimir_minus_z_sq_add_z`,
PR #894) and the iterate eigenvalue identities (PR #882 for `Ŝ²`,
PR #887 for `Ŝ^z`, applied twice for `(Ŝ^z)²`). -/
theorem totalSpinSOpPlus_mulVec_totalSpinSOpMinus_pow_succ_allAlignedStateS_zero
    [Nonempty V] (k : ℕ) :
    (totalSpinSOpPlus V N).mulVec
      (((totalSpinSOpMinus V N) ^ (k + 1)).mulVec
        (allAlignedStateS V N (0 : Fin (N + 1)))) =
      (((k + 1 : ℕ) : ℂ) *
          ((Fintype.card V : ℂ) * (N : ℂ) - (k : ℂ))) •
        ((totalSpinSOpMinus V N) ^ k).mulVec
          (allAlignedStateS V N (0 : Fin (N + 1))) := by
  set v_k := ((totalSpinSOpMinus V N) ^ k).mulVec
    (allAlignedStateS V N (0 : Fin (N + 1)))
  -- Step 1: rewrite (Ŝ^-)^(k+1) = Ŝ^- * (Ŝ^-)^k and combine to (Ŝ^+ * Ŝ^-).
  rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  -- Step 2: apply Casimir rearrangement.
  rw [totalSpinSOpPlus_mul_totalSpinSOpMinus_eq_casimir_minus_z_sq_add_z]
  -- Now: (Ŝ_tot² - Ŝ^z * Ŝ^z + Ŝ^z).mulVec v_k.
  rw [Matrix.add_mulVec, Matrix.sub_mulVec]
  -- Compute Ŝ_tot² · v_k = m_max(m_max+1) • v_k (PR #882).
  have h_casimir : (totalSpinSSquared V N).mulVec v_k =
      ((Fintype.card V : ℂ) * (N : ℂ) / 2 *
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 + 1)) • v_k := by
    exact totalSpinSSquared_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero k
  -- Compute Ŝ^z · v_k = (m_max - k) • v_k (PR #887).
  have h_z : (totalSpinSOp3 V N).mulVec v_k =
      ((Fintype.card V : ℂ) * (N : ℂ) / 2 - (k : ℂ)) • v_k := by
    exact totalSpinSOp3_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero k
  -- Compute (Ŝ^z * Ŝ^z) · v_k = (m_max - k)² • v_k (apply Ŝ^z twice).
  have h_z_sq : ((totalSpinSOp3 V N : ManyBodyOpS V N) *
      totalSpinSOp3 V N).mulVec v_k =
      (((Fintype.card V : ℂ) * (N : ℂ) / 2 - (k : ℂ)) *
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 - (k : ℂ))) • v_k := by
    rw [← Matrix.mulVec_mulVec, h_z, Matrix.mulVec_smul, h_z, smul_smul]
  rw [h_casimir, h_z_sq, h_z]
  -- Combine the smuls and simplify.
  rw [← sub_smul, ← add_smul]
  congr 1
  push_cast
  ring

/-! ## Inductive non-vanishing -/

/-- **Inductive non-vanishing of the saturated-ferromagnet ladder**:
for every `k ≤ |V|·N` (i.e., `k ≤ 2m_max`), the iterate
`(Ŝ^-_{tot})^k · |σ_⊤⟩` is non-zero.

Proof by strong induction on `k`. Base: `k = 0` — `|σ_⊤⟩ ≠ 0` (PR #891).
Step: from `v_k ≠ 0` and `k < 2m_max`, derive `v_{k+1} ≠ 0` via
`Ŝ^+_{tot} v_{k+1} = (k+1)(2m_max − k) v_k ≠ 0`. -/
theorem totalSpinSOpMinus_pow_allAlignedStateS_zero_ne_zero
    [Nonempty V] {k : ℕ} (hk : k ≤ Fintype.card V * N) :
    ((totalSpinSOpMinus V N) ^ k).mulVec
        (allAlignedStateS V N (0 : Fin (N + 1))) ≠ 0 := by
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.one_mulVec]
    exact allAlignedStateS_ne_zero _
  | succ k ih =>
    have hk_lt : k < Fintype.card V * N := hk
    have hk_le : k ≤ Fintype.card V * N := Nat.le_of_lt hk_lt
    have h_vk_ne : ((totalSpinSOpMinus V N) ^ k).mulVec
        (allAlignedStateS V N (0 : Fin (N + 1))) ≠ 0 := ih hk_le
    -- Apply the eigenvalue identity to deduce v_{k+1} ≠ 0.
    intro h_vk_succ_zero
    have h_eigen :=
      totalSpinSOpPlus_mulVec_totalSpinSOpMinus_pow_succ_allAlignedStateS_zero
        (V := V) (N := N) k
    rw [h_vk_succ_zero, Matrix.mulVec_zero] at h_eigen
    -- h_eigen: 0 = ((k+1) * (|V|·N - k)) • v_k.
    -- Since (k+1) * (|V|·N - k) ≠ 0 in ℂ for k < |V|·N, v_k = 0, contradiction.
    have h_scalar_ne : (((k + 1 : ℕ) : ℂ) *
        ((Fintype.card V : ℂ) * (N : ℂ) - (k : ℂ))) ≠ 0 := by
      apply mul_ne_zero
      · -- (k + 1 : ℕ) : ℂ ≠ 0 since k + 1 ≥ 1.
        exact_mod_cast (Nat.succ_ne_zero k)
      · -- (|V|·N : ℂ) - (k : ℂ) ≠ 0 for k < |V|·N.
        intro h_eq
        have hcN : ((Fintype.card V : ℂ) * (N : ℂ)) = (k : ℂ) :=
          sub_eq_zero.mp h_eq
        have hcN' : ((Fintype.card V * N : ℕ) : ℂ) = ((k : ℕ) : ℂ) := by
          push_cast; exact hcN
        have : (Fintype.card V * N : ℕ) = k := by
          exact_mod_cast hcN'
        omega
    have h_vk_zero := (smul_eq_zero.mp h_eigen.symm).resolve_left h_scalar_ne
    exact h_vk_ne h_vk_zero

end LatticeSystem.Quantum
