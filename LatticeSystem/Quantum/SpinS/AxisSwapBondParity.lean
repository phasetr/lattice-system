import LatticeSystem.Quantum.SpinS.AxisSwapBondOffDiag

/-!
# Parity preservation of the axis-swapped bond at the matrix-entry level

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Every ladder term of the axis-swapped bond raises/lowers each of `x, y` by exactly one unit, so
each non-vanishing off-diagonal contribution changes the local occupation sum
`(σ'_x + σ_x) + (σ'_y + σ_y)` by an even amount.  Hence the bond entry vanishes whenever that sum
is **odd** — the matrix-entry form of "bond moves preserve the magnetization parity", the input to
the parity-block decomposition of the Marshall-dressed `Ĥ'` (PR5).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- `Ŝ⁺_{i j}` vanishes when `i.val + j.val` is even (raising flips the parity). -/
theorem spinSOpPlus_apply_eq_zero_of_even (N : ℕ) {i j : Fin (N + 1)}
    (h : Even (i.val + j.val)) : spinSOpPlus N i j = 0 := by
  apply spinSOpPlus_apply_other
  obtain ⟨m, hm⟩ := h
  omega

/-- `Ŝ⁻_{i j}` vanishes when `i.val + j.val` is even. -/
theorem spinSOpMinus_apply_eq_zero_of_even (N : ℕ) {i j : Fin (N + 1)}
    (h : Even (i.val + j.val)) : spinSOpMinus N i j = 0 := by
  apply spinSOpMinus_apply_other
  obtain ⟨m, hm⟩ := h
  omega

/-- **Parity preservation of the axis-swapped bond** (matrix-entry form): the bond entry vanishes
when the local occupation parity `(σ'_x + σ_x) + (σ'_y + σ_y)` is odd. -/
theorem spinSDotXXZSwap_apply_eq_zero_of_local_odd
    {x y : Λ} (hxy : x ≠ y) (lam : ℂ) {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (hodd : Odd ((σ' x).val + (σ x).val + ((σ' y).val + (σ y).val))) :
    spinSDotXXZSwap x y lam N σ' σ = 0 := by
  have hcase : Even ((σ' x).val + (σ x).val) ∨ Even ((σ' y).val + (σ y).val) := by
    rcases Nat.even_or_odd ((σ' x).val + (σ x).val) with hx | hx
    · exact Or.inl hx
    · refine Or.inr ?_
      rcases Nat.even_or_odd ((σ' y).val + (σ y).val) with hy | hy
      · exact hy
      · obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy; obtain ⟨c, hc⟩ := hodd; omega
  have hladder := congrFun (congrFun (spinSDotXXZSwap_ladder_form (Λ := Λ) x y lam) σ') σ
  rw [hladder, Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
    smul_eq_mul, smul_eq_mul,
    onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_eq_zero_of_ne hxy hne, add_zero]
  rw [Matrix.add_apply, Matrix.add_apply,
    onSiteS_mul_onSiteS_apply_eq hxy, onSiteS_mul_onSiteS_apply_eq hxy,
    onSiteS_mul_onSiteS_apply_eq hxy, onSiteS_mul_onSiteS_apply_eq hxy]
  rcases hcase with hx | hy
  · rw [spinSOpPlus_apply_eq_zero_of_even N hx, spinSOpMinus_apply_eq_zero_of_even N hx]
    simp
  · rw [spinSOpMinus_apply_eq_zero_of_even N hy, spinSOpPlus_apply_eq_zero_of_even N hy]
    simp

end LatticeSystem.Quantum
