import LatticeSystem.Quantum.SpinS.HeisenbergRaiseLower

/-!
# Tasaki §2.4, p. 34: off-diagonal signs of the ferromagnetic Heisenberg matrix

The Perron-Frobenius input to Theorem 2.1: in the configuration basis `|Ψ^σ⟩` the ferromagnetic
Heisenberg matrix has non-positive off-diagonal entries, strictly negative on the ladder steps
`Ŝ⁺_x Ŝ⁻_y` along an edge.  These are hypotheses (i) and (ii) of Tasaki's Perron-Frobenius
Theorem A.18 (p. 475); the book reaches them in the Proof of Theorem 2.2 (properties (i)-(iii),
pp. 40-42) and refers to that argument for Theorem 2.1 in the solution of Problem 2.4.a (p. 496).

The bare bond bound is stated **sign-free** (`spinSDot_apply_re_nonneg_of_ne`): the ladder factors
`√(σ_x (N - σ_x + 1))` are non-negative whatever the coupling is, so at the Hamiltonian level they
only have to be weighted by `(J x y).re ≤ 0` and the configuration case analysis is not repeated.
Unlike the antiferromagnetic Theorem 2.2, the ferromagnetic case needs **no** Marshall sign
dressing (the `∏_{x ∈ B} (-1)^{σ_x - S}` prefactor of eq. (2.5.8), p. 40): a non-positive coupling
already puts the off-diagonal entries on the required side of zero.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.4 Theorem 2.1, p. 34; Proof of Theorem 2.2, properties (i)-(iii), pp. 40-42; solution of
Problem 2.4.a, p. 496; Theorem A.18, p. 475.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Sign-free off-diagonal bond bound** (Tasaki §2.4, p. 34; the `Ŝ_x·Ŝ_y` half of property (i)
in the Proof of Theorem 2.2, p. 40).  For `x ≠ y` and `σ' ≠ σ`, the matrix element of the bare
bond operator `Ŝ_x·Ŝ_y` has non-negative real part.

No coupling and no ferromagnetic hypothesis enter: the entry is either zero (whenever `σ'` and `σ`
differ away from `{x, y}`, differ at a single site, or differ at `x` by other than one ladder
step) or a product of the non-negative ladder factors of `Ŝ⁺_x Ŝ⁻_y` / `Ŝ⁻_x Ŝ⁺_y`. -/
theorem spinSDot_apply_re_nonneg_of_ne
    {x y : V} (hxy : x ≠ y) {σ' σ : V → Fin (N + 1)} (hne : σ' ≠ σ) :
    0 ≤ ((spinSDot x y N : ManyBodyOpS V N) σ' σ).re := by
  classical
  by_cases hout : ∃ z, z ≠ x ∧ z ≠ y ∧ σ' z ≠ σ z
  · obtain ⟨z, hzx, hzy, hz⟩ := hout
    rw [spinSDot_apply_eq_zero_of_diff_outside_pair hxy N hzx hzy hz]
    simp
  · have hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k := by
      intro k hkx hky
      by_contra hk
      exact hout ⟨k, hkx, hky, hk⟩
    by_cases hσx : σ' x = σ x
    · -- The difference is confined to `y`, so the two-site entry vanishes.
      have hσy : σ' y ≠ σ y := by
        intro hy
        refine hne (funext fun k => ?_)
        by_cases hkx : k = x
        · exact hkx ▸ hσx
        · by_cases hky : k = y
          · exact hky ▸ hy
          · exact hagree k hkx hky
      have hagree_y : ∀ k, k ≠ y → σ' k = σ k := by
        intro k hky
        by_cases hkx : k = x
        · exact hkx ▸ hσx
        · exact hagree k hkx hky
      rw [spinSDot_apply_eq_zero_of_one_site_diff hxy N hagree_y hσy]
      simp
    · by_cases hraise : (σ' x).val + 1 = (σ x).val
      · exact spinSDot_apply_re_nonneg_of_raising_lowering_x hxy N hagree hraise
      · by_cases hlower : (σ x).val + 1 = (σ' x).val
        · exact spinSDot_apply_re_nonneg_of_raising_lowering_y hxy N hagree hlower
        · rw [spinSDot_apply_eq_zero_of_off_two_site_agree_diff_at_x_not_pm1 hxy N hagree hσx
            hraise hlower]
          simp

/-- **Off-diagonal non-positivity of the ferromagnetic Heisenberg matrix** (Tasaki, Proof of
Theorem 2.2 property (i), p. 40, read in the ferromagnetic sign convention; hypothesis (i) of
Theorem A.18, p. 475).  For a real coupling with `(J x y).re ≤ 0`, every off-diagonal entry
`⟨Ψ^{σ'}|Ĥ|Ψ^σ⟩` has non-positive real part.

Entrywise `Re (Ĥ)_{σ'σ} = ∑_{x,y} (J x y).re · Re (Ŝ_x·Ŝ_y)_{σ'σ}`: the same-site pairs `x = y`
contribute nothing on `σ' ≠ σ`, and every other summand is a non-positive weight times the
non-negative bond entry of `spinSDot_apply_re_nonneg_of_ne`. -/
theorem heisenbergHamiltonianS_apply_re_nonpos_of_ne
    {J : V → V → ℂ} (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_nonpos : ∀ x y, (J x y).re ≤ 0)
    {σ' σ : V → Fin (N + 1)} (hne : σ' ≠ σ) :
    ((heisenbergHamiltonianS (Λ := V) J N) σ' σ).re ≤ 0 := by
  classical
  obtain ⟨z, hz⟩ := Function.ne_iff.mp hne
  rw [heisenbergHamiltonianS_apply, Complex.re_sum]
  refine Finset.sum_nonpos fun x _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_nonpos fun y _ => ?_
  rw [Complex.mul_re, hJ_real x y, zero_mul, sub_zero]
  by_cases hxy : x = y
  · subst hxy
    rw [spinSDot_self_apply_eq_zero_of_diff_at x N hz]
    simp
  · exact mul_nonpos_iff.mpr (Or.inr ⟨hJ_nonpos x y, spinSDot_apply_re_nonneg_of_ne hxy hne⟩)

end LatticeSystem.Quantum
