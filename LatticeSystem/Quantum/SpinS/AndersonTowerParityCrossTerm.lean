/-
Tasaki §4.2.2 Theorem 4.8 (Tanaka symmetry-breaking state), arc PR3 [N4] — the parity cross-term
vanishing (eq. (4.2.69)).

The Tanaka state `Ξ = (u_M + u_{M+1})/√2` (with `u_k = (Ô_L^{(1)})^k Φ / ‖·‖`) has energy
`⟨Ξ, Ĥ Ξ⟩ = ½(⟨u_M, Ĥ u_M⟩ + ⟨u_{M+1}, Ĥ u_{M+1}⟩)` because the cross term
`⟨u_M, Ĥ u_{M+1}⟩` vanishes (Tasaki eq. (4.2.69), the `Û_π^{(3)}` invariance).  Physically: the two
tower terms lie in opposite magnetization-parity subspaces (their `Ŝ_tot^{(3)}`-charge content is
`≡ M` resp. `≡ M+1` mod `2` when `Φ` is a singlet), and `Ĥ` preserves the charge, so the cross term
pairs orthogonal parity subspaces.

We formalize this with the diagonal π-rotation parity operator `Û = exp(iπ Ŝ_tot^{(3)})` about axis
`3`.  It is diagonal in the computational basis (`Ŝ_tot^{(3)}` is), and:
* `Û Ô_L^{(1)} = -Ô_L^{(1)} Û` (the `1`-axis order operator shifts the charge by `±1`, so `Û`
  changes its sign), obtained entrywise from the sector commutators `[Ŝ_tot^{(3)}, Ô_L^±] = ±Ô_L^±`;
* `Û Ĥ = Ĥ Û` (charge conservation `[Ĥ, Ŝ_tot^{(3)}] = 0`);
* `Û Φ = Φ` for a total-spin-`3`-singlet `Φ`.
Hence `Û (Ô_L^{(1)})^k Φ = (-1)^k (Ô_L^{(1)})^k Φ`, so `(Ô_L^{(1)})^M Φ` and
`Ĥ (Ô_L^{(1)})^{M+1} Φ` are `Û`-eigenvectors with distinct eigenvalues `(-1)^M ≠ (-1)^{M+1}`; a
diagonal operator's eigenvectors with distinct eigenvalues have disjoint support, so their inner
product — the cross term — is zero.

This file is downstream of `AndersonTowerSameSignDecay` (arc PR2) and reuses the diagonal form of
`Ŝ_tot^{(3)}` from `Problem25cZAxisRotationCommutation`.  It touches no crux ([N2], the 1-axis
numerator's binomial cancellation) — only the reusable parity layer.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, eq. (4.2.69), pp. 111–112 (Tanaka [62]).
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerSameSignDecay
import LatticeSystem.Quantum.SpinS.Problem25cZAxisRotationCommutation

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ### The magnetization-parity sign and its diagonal operator -/

/-- The **magnetization-parity sign** `exp(iπ · magEigenvalueS σ)`, the diagonal entry of the
π-rotation `Û = exp(iπ Ŝ_tot^{(3)})` about axis `3` at the basis configuration `σ`.  Its defining
property is that a `+1` charge step (`magEigenvalueS σ = magEigenvalueS τ + 1`) flips the sign. -/
noncomputable def magParitySignS (σ : Λ → Fin (N + 1)) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * magEigenvalueS σ)

omit [DecidableEq Λ] in
/-- A `+1` charge step flips the parity sign: `magParitySignS σ = -magParitySignS τ` when
`magEigenvalueS σ = magEigenvalueS τ + 1` (`exp(iπ(x+1)) = -exp(iπx)`). -/
theorem magParitySignS_of_magEig_add_one {σ τ : Λ → Fin (N + 1)}
    (h : magEigenvalueS σ = magEigenvalueS τ + 1) :
    magParitySignS σ = -magParitySignS τ := by
  simp only [magParitySignS, h]
  rw [mul_add, mul_one, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]

omit [DecidableEq Λ] in
/-- The parity sign is `1` on the zero-charge sector: `magEigenvalueS σ = 0 → magParitySignS σ = 1`
(`exp(0) = 1`). -/
theorem magParitySignS_of_magEig_eq_zero {σ : Λ → Fin (N + 1)} (h : magEigenvalueS σ = 0) :
    magParitySignS σ = 1 := by
  simp only [magParitySignS, h, mul_zero, Complex.exp_zero]

omit [DecidableEq Λ] in
/-- The parity sign depends only on the charge: equal `magEigenvalueS` gives equal sign. -/
theorem magParitySignS_congr {σ τ : Λ → Fin (N + 1)}
    (h : magEigenvalueS σ = magEigenvalueS τ) : magParitySignS σ = magParitySignS τ := by
  simp only [magParitySignS, h]

/-! ### The parity operator anticommutes with `Ô_L^{(1)}` and commutes with `Ĥ` -/

/-- `Û Ô_L⁺ = -Ô_L⁺ Û`: the raising order operator shifts the `Ŝ_tot^{(3)}`-charge by `+1`, obtained
entrywise from the sector commutator `[Ŝ_tot^{(3)}, Ô_L⁺] = Ô_L⁺`. -/
theorem diagonal_magParitySignS_mul_staggeredRaisingOpS (A : Λ → Bool) :
    Matrix.diagonal (magParitySignS (Λ := Λ) (N := N)) * staggeredRaisingOpS A N
      = -(staggeredRaisingOpS A N * Matrix.diagonal (magParitySignS (Λ := Λ) (N := N))) := by
  have hcomm := totalSpinSOp3_commutator_staggeredRaisingOpS (N := N) A
  rw [totalSpinSOp3_eq_diagonal_magEigenvalueS] at hcomm
  ext σ τ
  have hst := congrFun (congrFun hcomm σ) τ
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal] at hst
  simp only [Matrix.diagonal_mul, Matrix.neg_apply, Matrix.mul_diagonal]
  by_cases hz : staggeredRaisingOpS A N σ τ = 0
  · rw [hz]; ring
  · have hfac : (magEigenvalueS σ - magEigenvalueS τ - 1) * staggeredRaisingOpS A N σ τ = 0 := by
      linear_combination hst
    have heq : magEigenvalueS σ = magEigenvalueS τ + 1 :=
      sub_eq_zero.mp (by linear_combination (mul_eq_zero.mp hfac).resolve_right hz)
    rw [magParitySignS_of_magEig_add_one heq]; ring

/-- `Û Ô_L⁻ = -Ô_L⁻ Û`: the lowering order operator shifts the `Ŝ_tot^{(3)}`-charge by `-1`,
obtained entrywise from the sector commutator `[Ŝ_tot^{(3)}, Ô_L⁻] = -Ô_L⁻`. -/
theorem diagonal_magParitySignS_mul_staggeredLoweringOpS (A : Λ → Bool) :
    Matrix.diagonal (magParitySignS (Λ := Λ) (N := N)) * staggeredLoweringOpS A N
      = -(staggeredLoweringOpS A N * Matrix.diagonal (magParitySignS (Λ := Λ) (N := N))) := by
  have hcomm := totalSpinSOp3_commutator_staggeredLoweringOpS (N := N) A
  rw [totalSpinSOp3_eq_diagonal_magEigenvalueS] at hcomm
  ext σ τ
  have hst := congrFun (congrFun hcomm σ) τ
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.neg_apply] at hst
  simp only [Matrix.diagonal_mul, Matrix.neg_apply, Matrix.mul_diagonal]
  by_cases hz : staggeredLoweringOpS A N σ τ = 0
  · rw [hz]; ring
  · have hfac : (magEigenvalueS σ - magEigenvalueS τ + 1) * staggeredLoweringOpS A N σ τ = 0 := by
      linear_combination hst
    have heq : magEigenvalueS τ = magEigenvalueS σ + 1 :=
      sub_eq_zero.mp (by linear_combination -(mul_eq_zero.mp hfac).resolve_right hz)
    rw [magParitySignS_of_magEig_add_one heq]; ring

/-- The `1`-axis order operator is the half-sum of the raising and lowering order operators:
`Ô_L^{(1)} = ½(Ô_L⁺ + Ô_L⁻)` (Cartesian decomposition, imaginary parts cancel).  Public: consumed
by the §5.3 coherent window mean `becCoherent_mean1` (eq. (5.3.7)), reused verbatim to avoid a
duplicate Cartesian-decomposition lemma. -/
theorem staggeredOrderOp1S_eq_half_smul (A : Λ → Bool) :
    staggeredOrderOp1S A N
      = (2 : ℂ)⁻¹ • (staggeredRaisingOpS A N + staggeredLoweringOpS A N) := by
  have hsum : staggeredRaisingOpS A N + staggeredLoweringOpS A N
      = (2 : ℂ) • staggeredOrderOp1S A N := by
    rw [staggeredRaisingOpS_eq_cartesian, staggeredLoweringOpS_eq_cartesian]
    module
  rw [hsum, smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]

/-- The `2`-axis order operator is the scaled difference of the raising/lowering order operators:
`Ô_L^{(2)} = (2i)⁻¹(Ô_L⁺ − Ô_L⁻)` (Cartesian decomposition, real parts cancel).  Public and
colocated with `staggeredOrderOp1S_eq_half_smul`: consumed both by the `Û`-anticommutation
`diagonal_magParitySignS_mul_staggeredOrderOp2S` (Thm 4.9 fluctuation) and by the §5.3 coherent
window mean `becCoherent_mean2` (eq. (5.3.7)), so it lives here in the common Cartesian file to
avoid a duplicate lemma. -/
theorem staggeredOrderOp2S_eq_smul (A : Λ → Bool) :
    staggeredOrderOp2S A N
      = (2 * Complex.I)⁻¹ • (staggeredRaisingOpS A N - staggeredLoweringOpS A N) := by
  have h : staggeredRaisingOpS A N - staggeredLoweringOpS A N
      = (2 * Complex.I) • staggeredOrderOp2S A N := by
    rw [staggeredRaisingOpS_eq_cartesian, staggeredLoweringOpS_eq_cartesian]; module
  rw [h, smul_smul, inv_mul_cancel₀ (mul_ne_zero two_ne_zero Complex.I_ne_zero), one_smul]

/-- `Û Ô_L^{(1)} = -Ô_L^{(1)} Û`: the parity operator anticommutes with the `1`-axis order operator,
combining the raising and lowering sign flips through `Ô_L^{(1)} = ½(Ô_L⁺ + Ô_L⁻)`. -/
theorem diagonal_magParitySignS_mul_staggeredOrderOp1S (A : Λ → Bool) :
    Matrix.diagonal (magParitySignS (Λ := Λ) (N := N)) * staggeredOrderOp1S A N
      = -(staggeredOrderOp1S A N * Matrix.diagonal (magParitySignS (Λ := Λ) (N := N))) := by
  have key : Matrix.diagonal (magParitySignS (Λ := Λ) (N := N))
        * (staggeredRaisingOpS A N + staggeredLoweringOpS A N)
      = -((staggeredRaisingOpS A N + staggeredLoweringOpS A N)
        * Matrix.diagonal (magParitySignS (Λ := Λ) (N := N))) := by
    rw [Matrix.mul_add, Matrix.add_mul, diagonal_magParitySignS_mul_staggeredRaisingOpS,
      diagonal_magParitySignS_mul_staggeredLoweringOpS, neg_add]
  rw [staggeredOrderOp1S_eq_half_smul, mul_smul_comm, key, smul_neg, smul_mul_assoc]

/-- `Û Ĥ = Ĥ Û`: the parity operator commutes with the Heisenberg Hamiltonian, obtained entrywise
from charge conservation `[Ĥ, Ŝ_tot^{(3)}] = 0`. -/
theorem heisenbergHamiltonianS_mul_diagonal_magParitySignS (J : Λ → Λ → ℂ) :
    heisenbergHamiltonianS J N * Matrix.diagonal (magParitySignS (Λ := Λ) (N := N))
      = Matrix.diagonal (magParitySignS (Λ := Λ) (N := N)) * heisenbergHamiltonianS J N := by
  have hcomm := heisenbergHamiltonianS_commutator_totalSpinSOp3 J N
  rw [totalSpinSOp3_eq_diagonal_magEigenvalueS] at hcomm
  ext σ τ
  have hst := congrFun (congrFun hcomm σ) τ
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.zero_apply] at hst
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hz : heisenbergHamiltonianS J N σ τ = 0
  · rw [hz]; ring
  · have hfac : (magEigenvalueS τ - magEigenvalueS σ) * heisenbergHamiltonianS J N σ τ = 0 := by
      linear_combination hst
    have heq : magEigenvalueS σ = magEigenvalueS τ :=
      ((sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right hz)).symm)
    rw [magParitySignS_congr heq]; ring

/-! ### The parity eigenvalue of a Tanaka tower term and the cross-term vanishing -/

/-- `Û Φ = Φ` for a total-spin-`3`-singlet `Φ`: the parity sign is `1` wherever `Φ` is supported
(`magEigenvalueS σ = 0`), so the diagonal operator acts as the identity. -/
theorem diagonal_magParitySignS_mulVec_singlet {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hsing : (totalSpinSOp3 Λ N).mulVec Φ = 0) :
    (Matrix.diagonal (magParitySignS (Λ := Λ) (N := N))).mulVec Φ = Φ := by
  funext σ
  rw [Matrix.mulVec_diagonal]
  have hσ := congrFun hsing σ
  rw [totalSpinSOp3_mulVec_apply_eq_magEigenvalueS_mul, Pi.zero_apply] at hσ
  by_cases hΦ : Φ σ = 0
  · rw [hΦ, mul_zero]
  · rw [magParitySignS_of_magEig_eq_zero ((mul_eq_zero.mp hσ).resolve_right hΦ), one_mul]

/-- **The Tanaka tower term is a parity eigenvector** (singlet `Φ`):
`Û (Ô_L^{(1)})^k Φ = (-1)^k (Ô_L^{(1)})^k Φ`.  Each `Ô_L^{(1)}` contributes one sign flip
(anticommutation) and `Û Φ = Φ`. -/
theorem diagonal_magParitySignS_mulVec_tanakaTowerTerm (A : Λ → Bool) (k : ℕ)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (hsing : (totalSpinSOp3 Λ N).mulVec Φ = 0) :
    (Matrix.diagonal (magParitySignS (Λ := Λ) (N := N))).mulVec (tanakaTowerTerm A N k Φ)
      = (-1 : ℂ) ^ k • tanakaTowerTerm A N k Φ := by
  induction k with
  | zero =>
    rw [tanakaTowerTerm, pow_zero, Matrix.one_mulVec, pow_zero, one_smul]
    exact diagonal_magParitySignS_mulVec_singlet hsing
  | succ k ih =>
    have hstep : tanakaTowerTerm A N (k + 1) Φ
        = (staggeredOrderOp1S A N).mulVec (tanakaTowerTerm A N k Φ) := by
      rw [tanakaTowerTerm, tanakaTowerTerm, pow_succ', Matrix.mulVec_mulVec]
    rw [hstep, Matrix.mulVec_mulVec, diagonal_magParitySignS_mul_staggeredOrderOp1S,
      Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, pow_succ, mul_comm,
      neg_one_mul, neg_smul]

/-- **Orthogonality of distinct-eigenvalue eigenvectors of a diagonal operator.**  If `D = diag d`,
`D p = λ p` and `D q = μ q` with `λ ≠ μ`, then `p`, `q` have disjoint support, so `⟨p, q⟩ = 0`. -/
theorem dotProduct_eq_zero_of_diagonal_eigen {d p q : (Λ → Fin (N + 1)) → ℂ} {lam mu : ℂ}
    (hp : (Matrix.diagonal d).mulVec p = lam • p) (hq : (Matrix.diagonal d).mulVec q = mu • q)
    (hlm : lam ≠ mu) : star p ⬝ᵥ q = 0 := by
  rw [dotProduct]
  refine Finset.sum_eq_zero (fun σ _ => ?_)
  have hpσ : d σ * p σ = lam * p σ := by
    have := congrFun hp σ
    rwa [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
  have hqσ : d σ * q σ = mu * q σ := by
    have := congrFun hq σ
    rwa [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
  by_cases hp0 : p σ = 0
  · rw [Pi.star_apply, hp0, star_zero, zero_mul]
  · have hq0 : q σ = 0 := by
      by_contra hqne
      exact hlm ((mul_right_cancel₀ hp0 hpσ).symm.trans (mul_right_cancel₀ hqne hqσ))
    rw [hq0, mul_zero]

/-- **Tasaki eq. (4.2.69): the parity cross term vanishes.**  For a total-spin-`3`-singlet `Φ`, the
two adjacent Tanaka tower terms are separated by the Heisenberg Hamiltonian:
`⟨(Ô_L^{(1)})^M Φ, Ĥ (Ô_L^{(1)})^{M+1} Φ⟩ = 0`.  They are `Û`-eigenvectors with eigenvalues
`(-1)^M ≠ (-1)^{M+1}` (using `Û Ĥ = Ĥ Û`), hence orthogonal. -/
theorem tanakaTowerTerm_cross_energy_eq_zero (A : Λ → Bool) (J : Λ → Λ → ℂ) (M : ℕ)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (hsing : (totalSpinSOp3 Λ N).mulVec Φ = 0) :
    star (tanakaTowerTerm A N M Φ)
        ⬝ᵥ (heisenbergHamiltonianS J N).mulVec (tanakaTowerTerm A N (M + 1) Φ) = 0 := by
  refine dotProduct_eq_zero_of_diagonal_eigen (lam := (-1) ^ M) (mu := (-1) ^ (M + 1))
    (diagonal_magParitySignS_mulVec_tanakaTowerTerm A M hsing) ?_ ?_
  · rw [Matrix.mulVec_mulVec, ← heisenbergHamiltonianS_mul_diagonal_magParitySignS,
      ← Matrix.mulVec_mulVec, diagonal_magParitySignS_mulVec_tanakaTowerTerm A (M + 1) hsing,
      Matrix.mulVec_smul]
  · intro h
    have hne : ((-1 : ℂ)) ^ M ≠ 0 := pow_ne_zero M (by norm_num)
    apply hne
    rw [pow_succ] at h
    exact (mul_eq_zero.mp (by linear_combination h : (2 : ℂ) * (-1) ^ M = 0)).resolve_left
      two_ne_zero

end LatticeSystem.Quantum
