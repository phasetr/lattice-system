import LatticeSystem.Quantum.SpinS.MultiSiteDot

/-!
# Matrix entries of the spin-1 (`N = 2`) operators on a two-site chain

This module collects the elementary **entry-level formulas** for the spin-1 (`N = 2S = 2`)
operators on the two-site index type `Λ = Fin 2`, i.e. on `ℂ³ ⊗ ℂ³`:

* the enumeration of a sum over the nine two-site configurations `Fin 2 → Fin 3`
  (`sum_fin2_fin3`);
* the single-site ladder and `Ŝ^{(3)}` entries at `N = 2` (`spinSOpPlus_two_apply`,
  `spinSOpMinus_two_apply`, `spinSOp3_two_apply`);
* the two-site dot product `Ŝ_0 · Ŝ_1` as a plain tensor of single-site operators
  (`spinSDot_fin2_apply`) and in its imaginary-free ladder form
  `½ (Ŝ⁺ ⊗ Ŝ⁻ + Ŝ⁻ ⊗ Ŝ⁺) + Ŝ^{(3)} ⊗ Ŝ^{(3)}` (`spinSDot_fin2_apply'`).

The statements are pure finite-dimensional linear algebra about the spin-1 operators; nothing
here refers to any particular model or Hamiltonian.  They are the common computational base for
the explicit `9 × 9` bond computations of the `S = 1` chain — the AKLT bond spin-2 projection
(`AKLTBondProjection.lean`) and the Knabe-type finite-size gap estimates alike — so they live in
their own module rather than as private helpers of a single consumer.

Reference (for the spin-1 conventions, `Ŝ^± = Ŝ^{(1)} ± i Ŝ^{(2)}` and the ladder entries
`√2`): Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.2, pp. 30–34.
-/

namespace LatticeSystem.Quantum

open Matrix

/-- Enumeration of a sum over the `9` two-site configurations `Fin 2 → Fin 3`. -/
lemma sum_fin2_fin3 (f : (Fin 2 → Fin 3) → ℂ) :
    ∑ σ : Fin 2 → Fin 3, f σ =
      f ![0, 0] + f ![0, 1] + f ![0, 2] + f ![1, 0] + f ![1, 1] + f ![1, 2]
        + f ![2, 0] + f ![2, 1] + f ![2, 2] := by
  rw [← (finTwoArrowEquiv (Fin 3)).symm.sum_comp f, Fintype.sum_prod_type,
    Fin.sum_univ_three]
  simp only [Fin.sum_univ_three, finTwoArrowEquiv_symm_apply]
  ring

/-- On `Λ = Fin 2` the off-bond delta of the two-site dot product is vacuous, so
`Ŝ_0 · Ŝ_1` is the plain tensor `∑_α Ŝ^{(α)} ⊗ Ŝ^{(α)}` of single-site operators. -/
lemma spinSDot_fin2_apply (σ' σ : Fin 2 → Fin 3) :
    spinSDot (0 : Fin 2) 1 2 σ' σ =
      spinSOp1 2 (σ' 0) (σ 0) * spinSOp1 2 (σ' 1) (σ 1)
        + spinSOp2 2 (σ' 0) (σ 0) * spinSOp2 2 (σ' 1) (σ 1)
        + spinSOp3 2 (σ' 0) (σ 0) * spinSOp3 2 (σ' 1) (σ 1) := by
  have hne : (0 : Fin 2) ≠ 1 := by decide
  have hvac : ∀ k : Fin 2, k ≠ 0 → k ≠ 1 → σ' k = σ k := by
    intro k h0 h1; fin_cases k
    · exact absurd rfl h0
    · exact absurd rfl h1
  rw [spinSDot_def]
  simp only [Matrix.add_apply]
  rw [onSiteS_mul_onSiteS_apply_eq hne, onSiteS_mul_onSiteS_apply_eq hne,
    onSiteS_mul_onSiteS_apply_eq hne]
  simp only [if_pos hvac]

/-- Raising-operator entries at `N = 2` (`Ŝ^+` on the spin-1 ladder): `√2` on the two raising
pairs, `0` otherwise. -/
lemma spinSOpPlus_two_apply (i j : Fin 3) :
    spinSOpPlus 2 i j =
      if i.val + 1 = j.val then ((Real.sqrt 2 : ℝ) : ℂ) else 0 := by
  by_cases h : i.val + 1 = j.val
  · rw [spinSOpPlus_apply_raise 2 h, if_pos h]
    have hj : j.val = 1 ∨ j.val = 2 := by omega
    rcases hj with hj | hj <;> rw [hj] <;> norm_num
  · rw [spinSOpPlus_apply_other 2 h, if_neg h]

/-- Lowering-operator entries at `N = 2` (`Ŝ^-` on the spin-1 ladder): `√2` on the two lowering
pairs, `0` otherwise. -/
lemma spinSOpMinus_two_apply (i j : Fin 3) :
    spinSOpMinus 2 i j =
      if j.val + 1 = i.val then ((Real.sqrt 2 : ℝ) : ℂ) else 0 := by
  by_cases h : j.val + 1 = i.val
  · rw [spinSOpMinus_apply_lower 2 h, if_pos h]
    have hj : j.val = 0 ∨ j.val = 1 := by omega
    rcases hj with hj | hj <;> rw [hj] <;> norm_num
  · rw [spinSOpMinus_apply_other 2 h, if_neg h]

/-- `Ŝ^{(3)}` entries at `N = 2`: diagonal `1 − k` (magnetic quantum
number), off-diagonal `0`. -/
lemma spinSOp3_two_apply (i j : Fin 3) :
    spinSOp3 2 i j = if i = j then (1 : ℂ) - (i.val : ℂ) else 0 := by
  unfold spinSOp3
  rw [Matrix.diagonal_apply]
  split
  · norm_num
  · rfl

/-- Imaginary-free form of the two-site dot product on `Fin 2`:
`Ŝ_0 · Ŝ_1 = ½ (Ŝ^+ ⊗ Ŝ^- + Ŝ^- ⊗ Ŝ^+) + Ŝ^{(3)} ⊗ Ŝ^{(3)}`,
eliminating `Ŝ^{(1)}, Ŝ^{(2)}` (and hence `I`) so the kernel computation
stays over rational multiples of `√2`. -/
lemma spinSDot_fin2_apply' (σ' σ : Fin 2 → Fin 3) :
    spinSDot (0 : Fin 2) 1 2 σ' σ =
      (1 / 2 : ℂ) * (spinSOpPlus 2 (σ' 0) (σ 0) * spinSOpMinus 2 (σ' 1) (σ 1)
        + spinSOpMinus 2 (σ' 0) (σ 0) * spinSOpPlus 2 (σ' 1) (σ 1))
        + spinSOp3 2 (σ' 0) (σ 0) * spinSOp3 2 (σ' 1) (σ 1) := by
  rw [spinSDot_fin2_apply, spinSOp1, spinSOp2]
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  have hI : (1 : ℂ) / (2 * Complex.I) = -Complex.I / 2 := by
    rw [mul_comm, ← div_div, Complex.div_I]; ring
  rw [hI]
  ring_nf
  rw [Complex.I_sq]
  ring

end LatticeSystem.Quantum
