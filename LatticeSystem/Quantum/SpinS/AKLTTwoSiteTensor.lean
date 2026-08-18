import LatticeSystem.Quantum.SpinS.AKLTBondProjection
import LatticeSystem.Quantum.SpinS.AKLTStringOrderDefs

/-!
# The two-site AKLT tensor and the VBS bond subspace

The whole valence-bond-solid structure of the `S = 1` AKLT matrix-product state sits in a single
`2 × 2` table: the two-site tensor `A^{a_0} A^{a_1}` of the AKLT matrices (Tasaki eqs.
(7.2.12)–(7.2.14)) has each of its four components proportional to one VBS bond vector `Ψ_{σσ'}`
of eqs. (7.1.19)–(7.1.20),

`A^{a_0}A^{a_1} = !![¼ Ψ_{↓↑}(a), s Ψ_{↓↓}(a); −s Ψ_{↑↑}(a), −¼ Ψ_{↑↓}(a)]`,  `s = (√2)⁻¹`.

Consequently **every linear functional of the two-site tensor** lies in the four-dimensional VBS
bond subspace `W` (eq. (7.1.21)).  That is the shared core of frustration-freeness for the periodic
and for the open AKLT chain: a bond slice of the periodic trace state is the functional with
coefficients `c i j = R j i` (the remainder matrix `R`), and a bond slice of the open chain state
is the functional with coefficients `c i j = P p i · Q j q` (the prefix/suffix products at the
boundary indices `p, q`).  Both then land in `W` through the same lemma, and Lemma 7.4 turns that
into annihilation by the bond spin-2 projection.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.1.3, eqs. (7.1.19)–(7.1.21), pp. 186–187, and §7.2.2, eqs. (7.2.12)–(7.2.14),
pp. 195–196.
-/

namespace LatticeSystem.Quantum

open Matrix

/-- **The two-site AKLT tensor table.**  Entry by entry, each component of `A^{a_0}A^{a_1}` is a
multiple of one VBS bond vector `Ψ_{σσ'}` of Tasaki eqs. (7.1.19)–(7.1.20), with `s = (√2)⁻¹`:
`A^{a_0}A^{a_1} = !![¼ Ψ_{↓↑}(a), s Ψ_{↓↓}(a); −s Ψ_{↑↑}(a), −¼ Ψ_{↑↓}(a)]`.
The only irrational input is `(√2)⁻¹ (√2)⁻¹ = ½`, used once. -/
theorem akltTwoSiteTensor_eq (a : Fin 2 → Fin 3) :
    akltVBSMatrices (a 0) * akltVBSMatrices (a 1) =
      !![(1 / 4 : ℂ) * vbsBondVec 1 0 a, ((Real.sqrt 2 : ℂ))⁻¹ * vbsBondVec 1 1 a;
        -((Real.sqrt 2 : ℂ))⁻¹ * vbsBondVec 0 0 a, (-1 / 4 : ℂ) * vbsBondVec 0 1 a] := by
  have hs : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = (1 / 2 : ℂ) := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  simp only [vbsBondVec, akltVBSMatrices]
  obtain ⟨u, hu⟩ : ∃ u, a 0 = u := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, a 1 = v := ⟨_, rfl⟩
  rw [hu, hv]
  fin_cases u <;> fin_cases v <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp +decide [Matrix.mul_apply, Fin.sum_univ_two, hs] <;>
    ring

/-- **Every linear functional of the two-site AKLT tensor lies in the VBS bond subspace `W`.**
If `v a = ∑_{i,j} c_{ij} (A^{a_0}A^{a_1})_{ij}` for a coefficient table `c` independent of the bond
configuration `a`, then `v ∈ W` (Tasaki eq. (7.1.21)): by the tensor table each of the four
components is a multiple of a generator `Ψ_{σσ'}`, so `v` is a linear combination of the four
generators.  Both the periodic trace state (`c i j = R j i`) and the open chain state
(`c i j = P p i · Q j q`) produce their bond slices in this form. -/
theorem mem_vbsBondSubspace_of_twoSiteTensor (c : Fin 2 → Fin 2 → ℂ) (v : (Fin 2 → Fin 3) → ℂ)
    (hv : ∀ a : Fin 2 → Fin 3, v a
      = ∑ i : Fin 2, ∑ j : Fin 2, c i j * (akltVBSMatrices (a 0) * akltVBSMatrices (a 1)) i j) :
    v ∈ vbsBondSubspace := by
  have hmem : ∀ p q : Fin 2, vbsBondVec p q ∈ vbsBondSubspace := by
    intro p q
    simp only [vbsBondSubspace]
    exact Submodule.subset_span ⟨(p, q), rfl⟩
  have hv' : v = (c 0 0 * (1 / 4 : ℂ)) • vbsBondVec 1 0
      + (c 0 1 * ((Real.sqrt 2 : ℂ))⁻¹) • vbsBondVec 1 1
      + (c 1 0 * -((Real.sqrt 2 : ℂ))⁻¹) • vbsBondVec 0 0
      + (c 1 1 * (-1 / 4 : ℂ)) • vbsBondVec 0 1 := by
    funext a
    rw [hv a, akltTwoSiteTensor_eq a]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hv']
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (hmem 1 0)) (Submodule.smul_mem _ _ (hmem 1 1)))
    (Submodule.smul_mem _ _ (hmem 0 0))) (Submodule.smul_mem _ _ (hmem 0 1))

end LatticeSystem.Quantum
