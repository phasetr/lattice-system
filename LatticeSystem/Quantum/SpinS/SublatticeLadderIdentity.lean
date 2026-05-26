import LatticeSystem.Quantum.SpinS.SublatticeLadderIterateMag

/-!
# Sublattice raising-of-lowering identity on the all-up state

Scaffold for the minimal-total-spin joint eigenstate (Issue #3687 / #3674, the
final obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

The `su(2)` ladder identity for the `A`-sublattice on the all-up state:
`Ŝ_A^+ (Ŝ_A^-)^{k+1} |σ_⊤⟩ = (k+1)(|A|·N − k) (Ŝ_A^-)^k |σ_⊤⟩`.
This is the sublattice analogue of
`totalSpinSOpPlus_mulVec_totalSpinSOpMinus_pow_succ_allAlignedStateS_zero` (§2.4),
derived from the sublattice Cartan identity `Ŝ_A^+ Ŝ_A^- = (Ŝ_A)² − (Ŝ_A^(3))² +
Ŝ_A^(3)`, the maximal sublattice Casimir value (#3691) and the sublattice
magnetization `s_A − k` of the iterate (#3692).  Since the scalar
`(k+1)(|A|·N − k) ≠ 0` for `k < |A|·N`, this drives the inductive non-vanishing
of the iterates.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Sublattice raising-of-lowering identity**:
`Ŝ_A^+ (Ŝ_A^-)^{k+1} |σ_⊤⟩ = (k+1)(|A|·N − k) (Ŝ_A^-)^k |σ_⊤⟩`. -/
theorem sublatticeSpinSOpPlus_mulVec_sublatticeLadderIterateDownS_succ (A : Λ → Bool) (k : ℕ) :
    (sublatticeSpinSOpPlus N A).mulVec (sublatticeLadderIterateDownS A N (k + 1)) =
      (((k + 1 : ℕ) : ℂ) *
          ((Finset.univ.filter (fun x : Λ => A x = true)).card * (N : ℂ) - (k : ℂ))) •
        sublatticeLadderIterateDownS A N k := by
  set cA : ℂ := ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) with hcA
  set v_k := sublatticeLadderIterateDownS A N k with hv_k
  -- (Ŝ_A^-)^{k+1} = Ŝ_A^- * (Ŝ_A^-)^k, then combine Ŝ_A^+ · Ŝ_A^-.
  have hiter : sublatticeLadderIterateDownS A N (k + 1) =
      (sublatticeSpinSOpMinus N A).mulVec v_k := by
    simp only [hv_k, sublatticeLadderIterateDownS, pow_succ']
    rw [Matrix.mulVec_mulVec]
  rw [hiter, Matrix.mulVec_mulVec]
  -- Sublattice Cartan: Ŝ_A^+ Ŝ_A^- = (Ŝ_A)² − Ŝ_A^(3)·Ŝ_A^(3) + Ŝ_A^(3).
  have hcartan : sublatticeSpinSOpPlus N A * sublatticeSpinSOpMinus N A =
      sublatticeSpinSquaredS N A
        - sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N A
        + sublatticeSpinSOp3 N A := by
    rw [sublatticeSpinSOpPlus_mul_sublatticeSpinSOpMinus_eq, sublatticeSpinSquaredS_def]
    abel
  rw [hcartan, Matrix.add_mulVec, Matrix.sub_mulVec]
  -- (Ŝ_A)² v_k = s_A(s_A+1) • v_k.
  have h_casimir : (sublatticeSpinSquaredS N A).mulVec v_k =
      (cA * ((N : ℂ) / 2) * (cA * ((N : ℂ) / 2) + 1)) • v_k :=
    sublatticeSpinSquaredS_mulVec_sublatticeLadderIterateDownS A k
  -- Ŝ_A^(3) v_k = (s_A − k) • v_k.
  have h_z : (sublatticeSpinSOp3 N A).mulVec v_k = (cA * (N : ℂ) / 2 - (k : ℂ)) • v_k := by
    have hmem := sublatticeLadderIterateDownS_mem_sublatticeMagSubspaceS (N := N) A k
    rwa [mem_sublatticeMagSubspaceS_iff] at hmem
  -- (Ŝ_A^(3))² v_k = (s_A − k)² • v_k.
  have h_z_sq : (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N A).mulVec v_k =
      ((cA * (N : ℂ) / 2 - (k : ℂ)) * (cA * (N : ℂ) / 2 - (k : ℂ))) • v_k := by
    rw [← Matrix.mulVec_mulVec, h_z, Matrix.mulVec_smul, h_z, smul_smul]
  rw [h_casimir, h_z_sq, h_z]
  rw [← sub_smul, ← add_smul]
  congr 1
  push_cast
  ring

end LatticeSystem.Quantum
