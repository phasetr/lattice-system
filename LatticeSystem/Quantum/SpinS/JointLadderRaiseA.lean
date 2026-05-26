import LatticeSystem.Quantum.SpinS.JointLadderIterateSublatticeMag

/-!
# Raising the `A`-index of the joint ladder iterate

Scaffold for the minimal-total-spin joint eigenstate (Issue #3687 / #3674, the
final obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

`Ŝ_A^+` lowers the `A`-ladder index of the joint iterate:
`Ŝ_A^+ (Ŝ_A^-)^{k_A+1} (Ŝ_¬A^-)^{k_B} |σ_⊤⟩ =
  (k_A+1)(|A|·N − k_A) · (Ŝ_A^-)^{k_A} (Ŝ_¬A^-)^{k_B} |σ_⊤⟩`.

This generalizes the single-sublattice ladder identity (#3693) to the joint iterate
(whose `A`-block is the highest weight): it uses the joint maximal `A`-Casimir
(#3698) and the joint `A`-magnetization `s_A − k_A` (#3700).  Together with the
`¬A`-version it shows `Ŝ⁺_tot` maps the diagonal family into the span of the
lower-index diagonal family, the key step of the rank–nullity argument producing
the minimal-total-spin highest-weight state.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Raising the `A`-index**: `Ŝ_A^+ · jointIterate (k_A+1) k_B =
(k_A+1)(|A|·N − k_A) · jointIterate k_A k_B`. -/
theorem sublatticeSpinSOpPlus_mulVec_jointLadderIterateDownS_succA (A : Λ → Bool) (kA kB : ℕ) :
    (sublatticeSpinSOpPlus N A).mulVec (jointLadderIterateDownS A N (kA + 1) kB) =
      (((kA + 1 : ℕ) : ℂ) *
          ((Finset.univ.filter (fun x : Λ => A x = true)).card * (N : ℂ) - (kA : ℂ))) •
        jointLadderIterateDownS A N kA kB := by
  set cA : ℂ := ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) with hcA
  -- jointIterate (kA+1) kB = Ŝ_A^- · jointIterate kA kB.
  have hiter : jointLadderIterateDownS A N (kA + 1) kB =
      (sublatticeSpinSOpMinus N A).mulVec (jointLadderIterateDownS A N kA kB) := by
    unfold jointLadderIterateDownS
    rw [pow_succ', ← Matrix.mulVec_mulVec]
  rw [hiter]
  set v_k := jointLadderIterateDownS A N kA kB with hv_k
  rw [Matrix.mulVec_mulVec]
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
    sublatticeSpinSquaredS_mulVec_jointLadderIterateDownS A kA kB
  -- Ŝ_A^(3) v_k = (s_A − kA) • v_k.
  have h_z : (sublatticeSpinSOp3 N A).mulVec v_k = (cA * (N : ℂ) / 2 - (kA : ℂ)) • v_k := by
    have hmem := jointLadderIterateDownS_mem_sublatticeMagSubspaceS (N := N) A kA kB
    rwa [mem_sublatticeMagSubspaceS_iff] at hmem
  -- (Ŝ_A^(3))² v_k = (s_A − kA)² • v_k.
  have h_z_sq : (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N A).mulVec v_k =
      ((cA * (N : ℂ) / 2 - (kA : ℂ)) * (cA * (N : ℂ) / 2 - (kA : ℂ))) • v_k := by
    rw [← Matrix.mulVec_mulVec, h_z, Matrix.mulVec_smul, h_z, smul_smul]
  rw [h_casimir, h_z_sq, h_z]
  rw [← sub_smul, ← add_smul]
  congr 1
  push_cast
  ring

end LatticeSystem.Quantum
