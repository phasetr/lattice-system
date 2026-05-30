import LatticeSystem.Quantum.SpinS.JointLadderRaiseA
import LatticeSystem.Quantum.SpinS.SublatticeLadderIterateNonvanishing

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Non-vanishing of the joint ladder iterates

Scaffold for the minimal-total-spin joint eigenstate (Issue #3687 / #3674, the
final obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

For `k_A ≤ |A|·N` and `k_B ≤ |¬A|·N`, the joint iterate
`(Ŝ_A^-)^{k_A} (Ŝ_¬A^-)^{k_B} · |σ_⊤⟩` is non-zero.  Inductive proof on `k_A`: the
base `k_A = 0` is the single-sublattice `¬A`-iterate non-vanishing (#3694 at `¬A`);
the step uses the `A`-raising identity (#3701) — if `v_{k_A+1} = 0` then
`Ŝ_A^+ v_{k_A+1} = (k_A+1)(|A|·N − k_A) v_{k_A} = 0` with a non-zero scalar for
`k_A < |A|·N`, forcing `v_{k_A} = 0` against the induction hypothesis.

With the joint `A`-magnetization (#3700), the diagonal-family members are non-zero
eigenvectors at distinct `A`-magnetizations, hence linearly independent.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Non-vanishing of the joint ladder iterates**: for `k_A ≤ |A|·N` and
`k_B ≤ |¬A|·N`, `(Ŝ_A^-)^{k_A} (Ŝ_¬A^-)^{k_B} · |σ_⊤⟩ ≠ 0`. -/
theorem jointLadderIterateDownS_ne_zero (A : Λ → Bool) {kA kB : ℕ}
    (hkA : kA ≤ (Finset.univ.filter (fun x : Λ => A x = true)).card * N)
    (hkB : kB ≤ (Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N) :
    jointLadderIterateDownS A N kA kB ≠ 0 := by
  induction kA with
  | zero =>
    -- jointIterate 0 kB = (Ŝ_¬A^-)^kB |σ_⊤⟩ = the ¬A-iterate.
    have heq : jointLadderIterateDownS A N 0 kB =
        sublatticeLadderIterateDownS (fun x => ! A x) N kB := by
      simp [jointLadderIterateDownS, sublatticeLadderIterateDownS]
    rw [heq]
    exact sublatticeLadderIterateDownS_ne_zero (fun x => ! A x) hkB
  | succ kA ih =>
    have hkA_lt : kA < (Finset.univ.filter (fun x : Λ => A x = true)).card * N := hkA
    have h_vk_ne := ih (Nat.le_of_lt hkA_lt)
    intro h_vk_succ_zero
    have h_eigen :=
      sublatticeSpinSOpPlus_mulVec_jointLadderIterateDownS_succA (Λ := Λ) (N := N) A kA kB
    rw [h_vk_succ_zero, Matrix.mulVec_zero] at h_eigen
    have h_scalar_ne : (((kA + 1 : ℕ) : ℂ) *
        ((Finset.univ.filter (fun x : Λ => A x = true)).card * (N : ℂ) - (kA : ℂ))) ≠ 0 := by
      apply mul_ne_zero
      · exact_mod_cast Nat.succ_ne_zero kA
      · intro h_eq
        have hcN : (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ)) = (kA : ℂ) :=
          sub_eq_zero.mp h_eq
        have hcN' : (((Finset.univ.filter (fun x : Λ => A x = true)).card * N : ℕ) : ℂ) =
            ((kA : ℕ) : ℂ) := by push_cast; exact hcN
        have : ((Finset.univ.filter (fun x : Λ => A x = true)).card * N : ℕ) = kA := by
          exact_mod_cast hcN'
        omega
    have h_vk_zero := (smul_eq_zero.mp h_eigen.symm).resolve_left h_scalar_ne
    exact h_vk_ne h_vk_zero

end LatticeSystem.Quantum
