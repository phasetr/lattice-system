import LatticeSystem.Quantum.SpinS.SublatticeSpinLadder
import LatticeSystem.Quantum.SpinS.Theorem23PFCasimirPredicted
import LatticeSystem.Math.ComplexVectorKernel

/-!
# Sublattice Casimir dominates `S^3(S^3 ± 1)` (magnitude bound)

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3), option (a),
Route 5 brick 0 (see `.self-local/tex/3717-coupled-total-spin-lower-bound.tex`).

For a simultaneous eigenvector of the sublattice Casimir `(Ŝ_A)²` (eigenvalue `γ`) and
`Ŝ_A^(3)` (eigenvalue `q`), the transverse part is positive semidefinite:
`(Ŝ_A)² − Ŝ_A^(3)(Ŝ_A^(3)±1) = Ŝ_A^∓ Ŝ_A^±` and `⟨v, Ŝ_A^∓ Ŝ_A^± v⟩ = ‖Ŝ_A^± v‖² ≥ 0`
(using `(Ŝ_A^±)^† = Ŝ_A^∓`).  Hence `γ ≥ q(q+1)` and `γ ≥ q(q−1)`.  This excludes
spurious sublattice weights `q = b+1` on the `(Ŝ_A)² = b(b+1)` eigenspace — the
magnitude input the coupled total-spin lower bound (Route 5) needs at the recurrence
boundary.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

private theorem star_dotProduct_self_re_pos {n : Type*} [Fintype n]
    {v : n → ℂ} (hv : v ≠ 0) : 0 < (star v ⬝ᵥ v).re := by
  rw [star_dotProduct_self_eq, Complex.ofReal_re]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
    ⟨i, Finset.mem_univ i, lt_of_le_of_ne (Complex.normSq_nonneg _)
      (Ne.symm (by simpa [Complex.normSq_eq_zero] using hi))⟩

/-- **Sublattice Casimir dominates `S^3(S^3+1)`**: for a simultaneous eigenvector `v ≠ 0`
of `(Ŝ_A)²` (eigenvalue `γ`) and `Ŝ_A^(3)` (eigenvalue `q`), `(q(q+1)).re ≤ γ.re`.  From
`(Ŝ_A)² = Ŝ_A^- Ŝ_A^+ + Ŝ_A^(3)(Ŝ_A^(3)+1)` and `‖Ŝ_A^+ v‖² ≥ 0`. -/
theorem sublatticeSpinSquaredS_re_ge_sublatticeSpinSOp3_mul_succ (A : V → Bool)
    {γ q : ℂ} {v : (V → Fin (N + 1)) → ℂ} (hv_ne : v ≠ 0)
    (hcas : (sublatticeSpinSquaredS N A).mulVec v = γ • v)
    (hz : (sublatticeSpinSOp3 N A).mulVec v = q • v) :
    (q * (q + 1)).re ≤ γ.re := by
  have hid : sublatticeSpinSquaredS N A =
      sublatticeSpinSOpMinus N A * sublatticeSpinSOpPlus N A +
        sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N A + sublatticeSpinSOp3 N A := by
    rw [sublatticeSpinSOpMinus_mul_sublatticeSpinSOpPlus_eq, sublatticeSpinSquaredS_def]
    abel
  have hquad : star v ⬝ᵥ (sublatticeSpinSquaredS N A).mulVec v =
      star v ⬝ᵥ (sublatticeSpinSOpMinus N A * sublatticeSpinSOpPlus N A).mulVec v +
        (q * q + q) * (star v ⬝ᵥ v) := by
    rw [hid]
    simp only [Matrix.add_mulVec, dotProduct_add]
    have h1 : star v ⬝ᵥ (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N A).mulVec v =
        (q * q) * (star v ⬝ᵥ v) := by
      rw [← Matrix.mulVec_mulVec, hz, Matrix.mulVec_smul, hz, smul_smul, dotProduct_smul,
        smul_eq_mul]
    have h2 : star v ⬝ᵥ (sublatticeSpinSOp3 N A).mulVec v = q * (star v ⬝ᵥ v) := by
      rw [hz, dotProduct_smul, smul_eq_mul]
    rw [h1, h2]; ring
  rw [hcas, dotProduct_smul, smul_eq_mul] at hquad
  have hnn : star v ⬝ᵥ (sublatticeSpinSOpMinus N A * sublatticeSpinSOpPlus N A).mulVec v =
      ((∑ i, Complex.normSq ((sublatticeSpinSOpPlus N A).mulVec v i) : ℝ) : ℂ) := by
    rw [← sublatticeSpinSOpPlus_conjTranspose N A]
    exact star_dotProduct_conjTranspose_mul_mulVec_eq _ v
  rw [hnn, star_dotProduct_self_eq] at hquad
  set z : ℝ := ∑ i, Complex.normSq (v i) with hzdef
  set S : ℝ := ∑ i, Complex.normSq ((sublatticeSpinSOpPlus N A).mulVec v i) with hSdef
  have hz_pos : 0 < z := by
    have := star_dotProduct_self_re_pos hv_ne
    rwa [star_dotProduct_self_eq, Complex.ofReal_re] at this
  have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
  have hre := congrArg Complex.re hquad
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] at hre
  have hgoal : (q * (q + 1)).re = q.re * q.re - q.im * q.im + q.re := by
    simp only [Complex.mul_re, Complex.add_re, Complex.one_re, Complex.one_im, Complex.add_im]
    ring
  rw [hgoal]
  nlinarith [hre, hS_nn, hz_pos]

/-- **Sublattice Casimir dominates `S^3(S^3−1)`**: lowering companion, from
`(Ŝ_A)² = Ŝ_A^+ Ŝ_A^- + Ŝ_A^(3)(Ŝ_A^(3)−1)` and `‖Ŝ_A^- v‖² ≥ 0`. -/
theorem sublatticeSpinSquaredS_re_ge_sublatticeSpinSOp3_mul_pred (A : V → Bool)
    {γ q : ℂ} {v : (V → Fin (N + 1)) → ℂ} (hv_ne : v ≠ 0)
    (hcas : (sublatticeSpinSquaredS N A).mulVec v = γ • v)
    (hz : (sublatticeSpinSOp3 N A).mulVec v = q • v) :
    (q * (q - 1)).re ≤ γ.re := by
  have hid : sublatticeSpinSquaredS N A =
      sublatticeSpinSOpPlus N A * sublatticeSpinSOpMinus N A +
        sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N A - sublatticeSpinSOp3 N A := by
    rw [sublatticeSpinSOpPlus_mul_sublatticeSpinSOpMinus_eq, sublatticeSpinSquaredS_def]
    abel
  have hquad : star v ⬝ᵥ (sublatticeSpinSquaredS N A).mulVec v =
      star v ⬝ᵥ (sublatticeSpinSOpPlus N A * sublatticeSpinSOpMinus N A).mulVec v +
        (q * q - q) * (star v ⬝ᵥ v) := by
    rw [hid]
    simp only [Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub, dotProduct_add]
    have h1 : star v ⬝ᵥ (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N A).mulVec v =
        (q * q) * (star v ⬝ᵥ v) := by
      rw [← Matrix.mulVec_mulVec, hz, Matrix.mulVec_smul, hz, smul_smul, dotProduct_smul,
        smul_eq_mul]
    have h2 : star v ⬝ᵥ (sublatticeSpinSOp3 N A).mulVec v = q * (star v ⬝ᵥ v) := by
      rw [hz, dotProduct_smul, smul_eq_mul]
    rw [h1, h2]; ring
  rw [hcas, dotProduct_smul, smul_eq_mul] at hquad
  have hnn : star v ⬝ᵥ (sublatticeSpinSOpPlus N A * sublatticeSpinSOpMinus N A).mulVec v =
      ((∑ i, Complex.normSq ((sublatticeSpinSOpMinus N A).mulVec v i) : ℝ) : ℂ) := by
    rw [← sublatticeSpinSOpMinus_conjTranspose N A]
    exact star_dotProduct_conjTranspose_mul_mulVec_eq _ v
  rw [hnn, star_dotProduct_self_eq] at hquad
  set z : ℝ := ∑ i, Complex.normSq (v i) with hzdef
  set S : ℝ := ∑ i, Complex.normSq ((sublatticeSpinSOpMinus N A).mulVec v i) with hSdef
  have hz_pos : 0 < z := by
    have := star_dotProduct_self_re_pos hv_ne
    rwa [star_dotProduct_self_eq, Complex.ofReal_re] at this
  have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
  have hre := congrArg Complex.re hquad
  simp only [Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at hre
  have hgoal : (q * (q - 1)).re = q.re * q.re - q.im * q.im - q.re := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im, Complex.sub_im]
    ring
  rw [hgoal]
  nlinarith [hre, hS_nn, hz_pos]

end LatticeSystem.Quantum
