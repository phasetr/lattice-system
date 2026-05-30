import LatticeSystem.Quantum.SpinS.AxisSwapBondParity
import LatticeSystem.Quantum.SpinS.SingleIonOffDiag
import LatticeSystem.Quantum.SpinS.DressedAxisSwapOffDiag

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Parity block-diagonality of the axis-swapped Hamiltonian

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Every off-diagonal move of `Ĥ'` changes the total occupation `magSumS σ = Σ_x (σ_x)` by an even
amount, so `Ĥ'_{σ' σ} = 0` whenever `magSumS σ'` and `magSumS σ` have different parities.  Thus
`Ĥ'` is block-diagonal with respect to the **even/odd magnetization parity** — the decomposition
on which the parity-sector Perron–Frobenius degeneracy bound runs (PR5).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- For configurations agreeing off `{x, y}`, the global occupation parity matches the local
`{x, y}` parity. -/
theorem magSumS_add_parity_eq_of_agree_off_two_site
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (magSumS σ' + magSumS σ) % 2 =
      ((σ' x).val + (σ x).val + ((σ' y).val + (σ y).val)) % 2 := by
  have hsum : magSumS σ' + magSumS σ = ∑ k : Λ, ((σ' k).val + (σ k).val) := by
    rw [magSumS_def, magSumS_def, ← Finset.sum_add_distrib]
  rw [hsum,
    ← Finset.add_sum_erase _ (fun k => (σ' k).val + (σ k).val) (Finset.mem_univ x),
    ← Finset.add_sum_erase _ (fun k => (σ' k).val + (σ k).val)
      (Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_univ y⟩)]
  have hrest : ∑ k ∈ (Finset.univ.erase x).erase y, ((σ' k).val + (σ k).val) =
      ∑ k ∈ (Finset.univ.erase x).erase y, 2 * (σ k).val := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hkx : k ≠ x := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hk)).1
    have hky : k ≠ y := (Finset.mem_erase.mp hk).1
    rw [h k hkx hky]; ring
  rw [hrest, ← Finset.mul_sum]
  omega

/-- For configurations agreeing off a single site `x`, the global occupation parity matches the
local `x` parity. -/
theorem magSumS_add_parity_eq_of_agree_off_site
    (x : Λ) {σ' σ : Λ → Fin (N + 1)} (h : ∀ k, k ≠ x → σ' k = σ k) :
    (magSumS σ' + magSumS σ) % 2 = ((σ' x).val + (σ x).val) % 2 := by
  have hsum : magSumS σ' + magSumS σ = ∑ k : Λ, ((σ' k).val + (σ k).val) := by
    rw [magSumS_def, magSumS_def, ← Finset.sum_add_distrib]
  rw [hsum, ← Finset.add_sum_erase _ (fun k => (σ' k).val + (σ k).val) (Finset.mem_univ x)]
  have hrest : ∑ k ∈ Finset.univ.erase x, ((σ' k).val + (σ k).val) =
      ∑ k ∈ Finset.univ.erase x, 2 * (σ k).val := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [h k (Finset.mem_erase.mp hk).1]; ring
  rw [hrest, ← Finset.mul_sum]
  omega

/-- The axis-swapped bond vanishes across magnetization-parity classes. -/
theorem spinSDotXXZSwap_apply_eq_zero_of_magSum_parity_ne
    {x y : Λ} (hxy : x ≠ y) (lam : ℂ) {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (hpar : Odd (magSumS σ' + magSumS σ)) :
    spinSDotXXZSwap x y lam N σ' σ = 0 := by
  by_cases hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k
  · refine spinSDotXXZSwap_apply_eq_zero_of_local_odd hxy lam hne ?_
    have hh := magSumS_add_parity_eq_of_agree_off_two_site hxy hagree
    rw [Nat.odd_iff] at hpar ⊢
    omega
  · exact spinSDotXXZSwap_apply_eq_zero_of_not_agree hxy lam hagree

/-- The single-ion site term vanishes across magnetization-parity classes. -/
theorem onSiteS_spinSOp2_sq_apply_eq_zero_of_magSum_parity_ne
    (x : Λ) {σ' σ : Λ → Fin (N + 1)}
    (hpar : Odd (magSumS σ' + magSumS σ)) :
    (onSiteS x (spinSOp2 N * spinSOp2 N)) σ' σ = 0 := by
  rw [onSiteS_apply]
  by_cases hagree : ∀ k, k ≠ x → σ' k = σ k
  · rw [if_pos hagree]
    apply spinSOp2_mul_spinSOp2_apply_eq_zero_of_odd
    have hh := magSumS_add_parity_eq_of_agree_off_site x hagree
    rw [Nat.odd_iff] at hpar ⊢
    omega
  · rw [if_neg hagree]

/-- **Parity block-diagonality of `Ĥ'`** (no self-bonds): the off-diagonal entry vanishes when
`σ'` and `σ` lie in different magnetization-parity classes. -/
theorem axisSwappedAnisotropicHeisenbergS_apply_eq_zero_of_magSum_parity_ne
    {J : Λ → Λ → ℂ} (hJself : ∀ x, J x x = 0) (lam D : ℂ)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (hpar : Odd (magSumS σ' + magSumS σ)) :
    axisSwappedAnisotropicHeisenbergS J lam D N σ' σ = 0 := by
  rw [axisSwappedAnisotropicHeisenbergS_def, Matrix.add_apply]
  have hbond : (∑ x : Λ, ∑ y : Λ, J x y • spinSDotXXZSwap x y lam N : ManyBodyOpS Λ N) σ' σ
      = 0 := by
    rw [Matrix.sum_apply]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    rw [Matrix.sum_apply]
    refine Finset.sum_eq_zero (fun y _ => ?_)
    rw [Matrix.smul_apply, smul_eq_mul]
    by_cases hxy : x = y
    · subst hxy; rw [hJself x, zero_mul]
    · rw [spinSDotXXZSwap_apply_eq_zero_of_magSum_parity_ne hxy lam hne hpar, mul_zero]
  have hsingle : singleIonAnisotropyS2 D N σ' σ = 0 := by
    rw [singleIonAnisotropyS2, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
      Finset.sum_eq_zero (fun x _ => by
        rw [onSiteS_mul_onSiteS_same]
        exact onSiteS_spinSOp2_sq_apply_eq_zero_of_magSum_parity_ne x hpar), mul_zero]
  rw [hbond, hsingle, add_zero]
