import LatticeSystem.Quantum.SpinS.AnisotropicEdgeStates
import LatticeSystem.Quantum.SpinS.AnisotropicEdgeStringOrder
import LatticeSystem.Quantum.SpinS.MagParityOperator

/-!
# Tasaki §8.1.3: the `Z₂ × Z₂` half turns of the open anisotropic chain

The essential assumption of the §8.1.3 argument is that each local term of the Hamiltonian is
invariant under the three global `π` rotations `Û_π^{(α)}`, which for integer spin generate a
`Z₂ × Z₂` (Klein four-group) symmetry (Tasaki (2.1.29)–(2.1.30), p. 19).  Two generators suffice,
and this module takes the two already available global operators

* `manyBodyReversalS (Fin L) 2` — the axis-1 half turn, acting site-wise by `u_1 = -F`;
* `magParityDiagS (Fin L) 2` — the axis-3 half turn, acting site-wise by `u_3 = diag(-1,1,-1)`.

Each differs from Tasaki's normalisation `∏_x û_α^{(x)}` only by the global scalar `(-1)^L`, which
is invisible to conjugation and to the `δ² = 1` character argument, so no exact-phase equivalence
is needed.

The module proves the site-wise conjugation tables, the resulting character law (8.1.12) for the
string operator, and the invariance of the open chain Hamiltonian.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.1, eqs. (2.1.16), (2.1.21), (2.1.23)–(2.1.25) and (2.1.29)–(2.1.30), pp. 16–19; §8.1.3,
eq. (8.1.12), p. 238.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {L : ℕ}

/-! ## The site-wise conjugation tables of the two generators -/

/-- **The many-body reversal acts site-wise by the axis-1 half turn**: `Θ A_z Θ = (u_1 A u_1)_z`.
The two minus signs of `u_1 = -F` cancel, so this is the already-proved conjugation by the
single-site reversal. -/
theorem manyBodyReversalS_conj_onSiteS_halfTurn (z : Fin L) (A : Matrix (Fin 3) (Fin 3) ℂ) :
    manyBodyReversalS (Fin L) 2 * onSiteS z A * manyBodyReversalS (Fin L) 2
      = onSiteS z (spinOneHalfTurnS 0 * A * spinOneHalfTurnS 0) := by
  rw [manyBodyReversalS_conj_onSiteS, spinOneHalfTurnS_zero_eq]
  congr 1
  noncomm_ring

/-- Entrywise conjugation by the axis-3 half turn: `(u_3 A u_3)_{ij} = (-1)^{i+j} A_{ij}`. -/
private theorem spinOneHalfTurnS_two_conj_apply (A : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
    (spinOneHalfTurnS 2 * A * spinOneHalfTurnS 2) i j
      = (-1 : ℂ) ^ i.val * ((-1 : ℂ) ^ j.val * A i j) := by
  have hdiag : spinOneHalfTurnS 2 = Matrix.diagonal (fun k : Fin 3 => -((-1 : ℂ) ^ k.val)) := by
    rw [spinOneHalfTurnS_two_eq]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.diagonal, spinOnePiRot3]
  rw [hdiag, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

/-- **The magnetization parity acts site-wise by the axis-3 half turn**: `P A_z P = (u_3 A u_3)_z`.
Both sides multiply the matrix element by `(-1)^{σ'_z + σ_z}`, because the configurations agree off
the site `z` and the off-site contributions to the magnetization parity cancel in pairs. -/
theorem magParityDiagS_conj_onSiteS (z : Fin L) (A : Matrix (Fin 3) (Fin 3) ℂ) :
    magParityDiagS (Fin L) 2 * onSiteS z A * magParityDiagS (Fin L) 2
      = onSiteS z (spinOneHalfTurnS 2 * A * spinOneHalfTurnS 2) := by
  ext σ' σ
  rw [magParityDiagS, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : ∀ k, k ≠ z → σ' k = σ k
  · rw [onSiteS_apply_of_off_site_agree z A h, onSiteS_apply_of_off_site_agree z _ h,
      spinOneHalfTurnS_two_conj_apply]
    have htail : ∑ x ∈ Finset.univ.erase z, (σ' x).val
        = ∑ x ∈ Finset.univ.erase z, (σ x).val :=
      Finset.sum_congr rfl fun x hx => by rw [h x (Finset.ne_of_mem_erase hx)]
    have hsplit' : magSumS σ' = (σ' z).val + ∑ x ∈ Finset.univ.erase z, (σ' x).val :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ z)).symm
    have hsplit : magSumS σ = (σ z).val + ∑ x ∈ Finset.univ.erase z, (σ x).val :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ z)).symm
    rw [hsplit', hsplit, htail, pow_add, pow_add]
    have hT : ((-1 : ℂ) ^ (∑ x ∈ Finset.univ.erase z, (σ x).val)) *
        ((-1 : ℂ) ^ (∑ x ∈ Finset.univ.erase z, (σ x).val)) = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow ⟨_, rfl⟩
    calc ((-1 : ℂ) ^ (σ' z).val * (-1 : ℂ) ^ (∑ x ∈ Finset.univ.erase z, (σ x).val)) *
          A (σ' z) (σ z) *
          ((-1 : ℂ) ^ (σ z).val * (-1 : ℂ) ^ (∑ x ∈ Finset.univ.erase z, (σ x).val))
        = ((-1 : ℂ) ^ (σ' z).val * ((-1 : ℂ) ^ (σ z).val * A (σ' z) (σ z))) *
            (((-1 : ℂ) ^ (∑ x ∈ Finset.univ.erase z, (σ x).val)) *
              ((-1 : ℂ) ^ (∑ x ∈ Finset.univ.erase z, (σ x).val))) := by ring
      _ = _ := by rw [hT, mul_one]
  · rw [onSiteS_apply_eq_zero_of_off_site_diff z A h,
      onSiteS_apply_eq_zero_of_off_site_diff z _ h]
    ring

/-! ## The character law (8.1.12) for the string operator -/

/-- **(8.1.12) for the axis-1 generator**: `Θ Ô^{(α)}_string Θ = ±Ô^{(α)}_string`, with `+` exactly
at `α = 1`. -/
theorem manyBodyReversalS_conj_edgeStringOrderOpS (L : ℕ) (alpha : Fin 3) :
    manyBodyReversalS (Fin L) 2 * edgeStringOrderOpS L alpha * manyBodyReversalS (Fin L) 2
      = (if (0 : Fin 3) = alpha then (1 : ℂ) else -1) • edgeStringOrderOpS L alpha :=
  edgeStringOrderOpS_conj L alpha _ (spinOneHalfTurnS 0) _
    (manyBodyReversalS_mul_self (Fin L) 2) (spinOneHalfTurnS_mul_self 0)
    (spinOneHalfTurnS_conj_spinOneHalfTurnS 0 alpha)
    (spinOneHalfTurnS_conj_spinOneAxisS 0 alpha)
    manyBodyReversalS_conj_onSiteS_halfTurn

/-- **(8.1.12) for the axis-3 generator**: `P Ô^{(α)}_string P = ±Ô^{(α)}_string`, with `+` exactly
at `α = 3`. -/
theorem magParityDiagS_conj_edgeStringOrderOpS (L : ℕ) (alpha : Fin 3) :
    magParityDiagS (Fin L) 2 * edgeStringOrderOpS L alpha * magParityDiagS (Fin L) 2
      = (if (2 : Fin 3) = alpha then (1 : ℂ) else -1) • edgeStringOrderOpS L alpha :=
  edgeStringOrderOpS_conj L alpha _ (spinOneHalfTurnS 2) _
    magParityDiagS_mul_self (spinOneHalfTurnS_mul_self 2)
    (spinOneHalfTurnS_conj_spinOneHalfTurnS 2 alpha)
    (spinOneHalfTurnS_conj_spinOneAxisS 2 alpha)
    magParityDiagS_conj_onSiteS

/-! ## Invariance of the open chain Hamiltonian -/

/-- **A half turn conjugating both sites of a bond fixes the Heisenberg coupling**, because each
axis factor picks up the same sign twice.  Stated site-locally so that it also applies to a prefix
rotation, which conjugates only the sites it covers. -/
theorem spinSDot_conj_of_onSiteS_conj (nu : Fin 3) {U : ManyBodyOpS (Fin L) 2}
    (hU : U * U = 1) {x y : Fin L}
    (hx : ∀ A : Matrix (Fin 3) (Fin 3) ℂ,
      U * onSiteS x A * U = onSiteS x (spinOneHalfTurnS nu * A * spinOneHalfTurnS nu))
    (hy : ∀ A : Matrix (Fin 3) (Fin 3) ℂ,
      U * onSiteS y A * U = onSiteS y (spinOneHalfTurnS nu * A * spinOneHalfTurnS nu)) :
    U * spinSDot x y 2 * U = spinSDot x y 2 := by
  have hax : ∀ beta : Fin 3, U * onSiteS x (spinOneAxisS beta) * U
      = (if nu = beta then (1 : ℂ) else -1) • onSiteS x (spinOneAxisS beta) := by
    intro beta
    rw [hx, spinOneHalfTurnS_conj_spinOneAxisS, onSiteS_smul]
  have hay : ∀ beta : Fin 3, U * onSiteS y (spinOneAxisS beta) * U
      = (if nu = beta then (1 : ℂ) else -1) • onSiteS y (spinOneAxisS beta) := by
    intro beta
    rw [hy, spinOneHalfTurnS_conj_spinOneAxisS, onSiteS_smul]
  have hterm : ∀ beta : Fin 3,
      U * (onSiteS x (spinOneAxisS beta) * onSiteS y (spinOneAxisS beta)) * U
        = onSiteS x (spinOneAxisS beta) * onSiteS y (spinOneAxisS beta) := by
    intro beta
    rw [conj_mul_of_mul_self hU, hax, hay, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    by_cases hb : nu = beta <;> simp [hb]
  rw [spinSDot, Matrix.mul_add, Matrix.add_mul, Matrix.mul_add, Matrix.add_mul]
  rw [show (onSiteS x (spinSOp1 2) : ManyBodyOpS (Fin L) 2) = onSiteS x (spinOneAxisS 0) from rfl,
    show (onSiteS y (spinSOp1 2) : ManyBodyOpS (Fin L) 2) = onSiteS y (spinOneAxisS 0) from rfl,
    show (onSiteS x (spinSOp2 2) : ManyBodyOpS (Fin L) 2) = onSiteS x (spinOneAxisS 1) from rfl,
    show (onSiteS y (spinSOp2 2) : ManyBodyOpS (Fin L) 2) = onSiteS y (spinOneAxisS 1) from rfl,
    show (onSiteS x (spinSOp3 2) : ManyBodyOpS (Fin L) 2) = onSiteS x (spinOneAxisS 2) from rfl,
    show (onSiteS y (spinSOp3 2) : ManyBodyOpS (Fin L) 2) = onSiteS y (spinOneAxisS 2) from rfl,
    hterm 0, hterm 1, hterm 2]

/-- **A half turn conjugating a site fixes the on-site anisotropy term** `(Ŝ^{(3)}_x)²`, again by
sign squaring. -/
theorem spinSSiteOp3_sq_conj_of_onSiteS_conj (nu : Fin 3) {U : ManyBodyOpS (Fin L) 2}
    (hU : U * U = 1) {x : Fin L}
    (hx : ∀ A : Matrix (Fin 3) (Fin 3) ℂ,
      U * onSiteS x A * U = onSiteS x (spinOneHalfTurnS nu * A * spinOneHalfTurnS nu)) :
    U * (spinSSiteOp3 x 2 * spinSSiteOp3 x 2) * U = spinSSiteOp3 x 2 * spinSSiteOp3 x 2 := by
  have hax : U * onSiteS x (spinOneAxisS 2) * U
      = (if nu = 2 then (1 : ℂ) else -1) • onSiteS x (spinOneAxisS 2) := by
    rw [hx, spinOneHalfTurnS_conj_spinOneAxisS, onSiteS_smul]
  rw [show (spinSSiteOp3 x 2 : ManyBodyOpS (Fin L) 2) = onSiteS x (spinOneAxisS 2) from rfl,
    conj_mul_of_mul_self hU, hax, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  by_cases hb : nu = 2 <;> simp [hb]

/-- **The open chain Hamiltonian is invariant under every global half turn** (Tasaki p. 238: this
`Z₂ × Z₂` invariance of each local term is the essential assumption of the argument). -/
private theorem conj_openAnisotropicChainHamiltonianS (L : ℕ) (D : ℝ) (nu : Fin 3)
    {U : ManyBodyOpS (Fin L) 2} (hU : U * U = 1)
    (hconj : ∀ (z : Fin L) (A : Matrix (Fin 3) (Fin 3) ℂ),
      U * onSiteS z A * U = onSiteS z (spinOneHalfTurnS nu * A * spinOneHalfTurnS nu)) :
    U * openAnisotropicChainHamiltonianS L D * U = openAnisotropicChainHamiltonianS L D := by
  rw [openAnisotropicChainHamiltonianS, Matrix.mul_add, Matrix.add_mul, heisenbergHamiltonianS,
    Matrix.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum,
    Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul,
      spinSDot_conj_of_onSiteS_conj nu hU (fun A => hconj x A) (fun A => hconj y A)]
  · congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    exact spinSSiteOp3_sq_conj_of_onSiteS_conj nu hU (fun A => hconj x A)

/-- **The axis-1 half turn commutes with the open chain Hamiltonian.** -/
theorem manyBodyReversalS_commute_openAnisotropicChainHamiltonianS (L : ℕ) (D : ℝ) :
    Commute (manyBodyReversalS (Fin L) 2) (openAnisotropicChainHamiltonianS L D) := by
  have hU := manyBodyReversalS_mul_self (Fin L) 2
  have h := conj_openAnisotropicChainHamiltonianS L D 0 hU manyBodyReversalS_conj_onSiteS_halfTurn
  have hstep := congrArg (fun M => M * manyBodyReversalS (Fin L) 2) h
  simp only [mul_assoc, hU, mul_one] at hstep
  exact hstep

/-- **The axis-3 half turn commutes with the open chain Hamiltonian.** -/
theorem magParityDiagS_commute_openAnisotropicChainHamiltonianS (L : ℕ) (D : ℝ) :
    Commute (magParityDiagS (Fin L) 2) (openAnisotropicChainHamiltonianS L D) := by
  have hU : magParityDiagS (Fin L) 2 * magParityDiagS (Fin L) 2 = 1 := magParityDiagS_mul_self
  have h := conj_openAnisotropicChainHamiltonianS L D 2 hU magParityDiagS_conj_onSiteS
  have hstep := congrArg (fun M => M * magParityDiagS (Fin L) 2) h
  simp only [mul_assoc, hU, mul_one] at hstep
  exact hstep

end LatticeSystem.Quantum
