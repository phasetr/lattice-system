import LatticeSystem.Quantum.SpinS.SublatticeLadderIdentity

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Non-vanishing of the sublattice ladder iterates

Scaffold for the minimal-total-spin joint eigenstate (Issue #3687 / #3674, the
final obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

For every `k ≤ |A|·N`, the sublattice ladder iterate `(Ŝ_A^-)^k · |σ_⊤⟩` is
non-zero.  Inductive proof (sublattice analogue of
`totalSpinSOpMinus_pow_allAlignedStateS_zero_ne_zero`, §2.4): if `v_{k+1} = 0` then
`Ŝ_A^+ v_{k+1} = (k+1)(|A|·N − k) v_k = 0` (the ladder identity #3693), and the
scalar is non-zero for `k < |A|·N`, forcing `v_k = 0` against the hypothesis.

Combined with the distinct sublattice magnetizations (#3692), the iterates
`(Ŝ_A^-)^k |σ_⊤⟩` for `k = 0, …, |A|·N` are linearly independent — the
`(|A|·N + 1)`-dimensional spanning family of the A-symmetric subspace.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Non-vanishing of the sublattice ladder iterates**: for `k ≤ |A|·N`,
`(Ŝ_A^-)^k · |σ_⊤⟩ ≠ 0`. -/
theorem sublatticeLadderIterateDownS_ne_zero (A : Λ → Bool) {k : ℕ}
    (hk : k ≤ (Finset.univ.filter (fun x : Λ => A x = true)).card * N) :
    sublatticeLadderIterateDownS A N k ≠ 0 := by
  induction k with
  | zero =>
    simp only [sublatticeLadderIterateDownS, pow_zero, Matrix.one_mulVec]
    exact allAlignedStateS_ne_zero _
  | succ k ih =>
    have hk_lt : k < (Finset.univ.filter (fun x : Λ => A x = true)).card * N := hk
    have h_vk_ne := ih (Nat.le_of_lt hk_lt)
    intro h_vk_succ_zero
    have h_eigen := sublatticeSpinSOpPlus_mulVec_sublatticeLadderIterateDownS_succ (Λ := Λ) (N :=
        N) A k
    rw [h_vk_succ_zero, Matrix.mulVec_zero] at h_eigen
    have h_scalar_ne : (((k + 1 : ℕ) : ℂ) *
        ((Finset.univ.filter (fun x : Λ => A x = true)).card * (N : ℂ) - (k : ℂ))) ≠ 0 := by
      apply mul_ne_zero
      · exact_mod_cast Nat.succ_ne_zero k
      · intro h_eq
        have hcN : (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ)) = (k : ℂ)
            :=
          sub_eq_zero.mp h_eq
        have hcN' : (((Finset.univ.filter (fun x : Λ => A x = true)).card * N : ℕ) : ℂ) =
            ((k : ℕ) : ℂ) := by push_cast; exact hcN
        have : ((Finset.univ.filter (fun x : Λ => A x = true)).card * N : ℕ) = k := by
          exact_mod_cast hcN'
        omega
    have h_vk_zero := (smul_eq_zero.mp h_eigen.symm).resolve_left h_scalar_ne
    exact h_vk_ne h_vk_zero

end LatticeSystem.Quantum
