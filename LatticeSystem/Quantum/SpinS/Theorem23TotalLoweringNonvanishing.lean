import LatticeSystem.Quantum.SpinS.CasimirRearrangement
import LatticeSystem.Quantum.SpinS.TotalSpin
import LatticeSystem.Quantum.SpinS.Magnetization

/-!
# Non-vanishing of one total-spin lowering/raising step on a weight vector

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3), general-`J`
`hOutside` thread, step 1 (see `.self-local/docs/tasaki-2-5-lieb-mattis-hOutside-design.md`).

From the SU(2) commutator `[Ŝ⁺_tot, Ŝ⁻_tot] = 2 Ŝ³_tot` (equivalently
`Ŝ⁺Ŝ⁻ = Ŝ⁻Ŝ⁺ + 2Ŝ³`) and the adjointness `(Ŝ⁻)† = Ŝ⁺`, a weight-`w` vector `Φ`
(i.e. `Ŝ³_tot Φ = w Φ`) satisfies the magnitude identity

  `‖Ŝ⁻_tot Φ‖² = ‖Ŝ⁺_tot Φ‖² + 2 w ‖Φ‖²`.

Hence `Ŝ⁻_tot Φ ≠ 0` whenever `Φ ≠ 0` and `w.re > 0` (and dually for `Ŝ⁺_tot` when
`w.re < 0`).  This is the non-vanishing input for the inward-ladder discharge of the
non-admissible-sector lower bound `hOutside`: an eigenvector outside the band can be moved
to the band edge by `Ŝ∓_tot` without being annihilated.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42; E. Lieb, D. Mattis,
J. Math. Phys. 3 (1962) 749.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The conjugated quadratic form `⟨v, Mᴴ M v⟩ = ‖M v‖²` is a non-negative real. -/
private theorem star_dotProduct_conjTranspose_mul_mulVec_eq'
    {n : Type*} [Fintype n] (M : Matrix n n ℂ) (v : n → ℂ) :
    star v ⬝ᵥ (M.conjTranspose * M).mulVec v =
      ((∑ i, Complex.normSq ((M.mulVec v) i) : ℝ) : ℂ) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, dotProduct,
    Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]

/-- `star v ⬝ᵥ v = ∑ ‖v i‖²` as a real cast into `ℂ`. -/
private theorem star_dotProduct_self_eq' {n : Type*} [Fintype n] (v : n → ℂ) :
    star v ⬝ᵥ v = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
  rw [dotProduct, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]

/-- **Total-spin lowering magnitude identity** on a weight-`w` vector:
`‖Ŝ⁻_tot Φ‖² = ‖Ŝ⁺_tot Φ‖² + 2 w ‖Φ‖²` (all as the real squared norms cast to `ℂ`). -/
theorem totalSpinSOpMinus_mulVec_normSq_eq (V : Type*) [Fintype V] [DecidableEq V] (N : ℕ)
    {w : ℂ} {Φ : (V → Fin (N + 1)) → ℂ}
    (hz : (totalSpinSOp3 V N).mulVec Φ = w • Φ) :
    ((∑ i, Complex.normSq ((totalSpinSOpMinus V N).mulVec Φ i) : ℝ) : ℂ) =
      ((∑ i, Complex.normSq ((totalSpinSOpPlus V N).mulVec Φ i) : ℝ) : ℂ) +
        (w + w) * ((∑ i, Complex.normSq (Φ i) : ℝ) : ℂ) := by
  -- `Ŝ⁺Ŝ⁻ = Ŝ⁻Ŝ⁺ + (Ŝ³ + Ŝ³)`.
  have hPM : (totalSpinSOpPlus V N : ManyBodyOpS V N) * totalSpinSOpMinus V N =
      totalSpinSOpMinus V N * totalSpinSOpPlus V N +
        (totalSpinSOp3 V N + totalSpinSOp3 V N) := by
    rw [totalSpinSOpPlus_mul_totalSpinSOpMinus_eq_casimir_minus_z_sq_add_z,
      totalSpinSOpMinus_mul_totalSpinSOpPlus_eq_casimir_minus_z_sq_sub_z]
    abel
  -- `‖Ŝ⁻Φ‖²` via `(Ŝ⁻)† = Ŝ⁺`.
  have hM : star Φ ⬝ᵥ (totalSpinSOpPlus V N * totalSpinSOpMinus V N).mulVec Φ =
      ((∑ i, Complex.normSq ((totalSpinSOpMinus V N).mulVec Φ i) : ℝ) : ℂ) := by
    rw [← totalSpinSOpMinus_conjTranspose (Λ := V) (N := N)]
    exact star_dotProduct_conjTranspose_mul_mulVec_eq' _ Φ
  -- `‖Ŝ⁺Φ‖²` via `(Ŝ⁺)† = Ŝ⁻`.
  have hP : star Φ ⬝ᵥ (totalSpinSOpMinus V N * totalSpinSOpPlus V N).mulVec Φ =
      ((∑ i, Complex.normSq ((totalSpinSOpPlus V N).mulVec Φ i) : ℝ) : ℂ) := by
    rw [← totalSpinSOpPlus_conjTranspose (Λ := V) (N := N)]
    exact star_dotProduct_conjTranspose_mul_mulVec_eq' _ Φ
  -- Expand `star Φ ⬝ᵥ (Ŝ⁺Ŝ⁻) Φ` through `hPM`.
  have hexp : star Φ ⬝ᵥ (totalSpinSOpPlus V N * totalSpinSOpMinus V N).mulVec Φ =
      star Φ ⬝ᵥ (totalSpinSOpMinus V N * totalSpinSOpPlus V N).mulVec Φ +
        (w + w) * (star Φ ⬝ᵥ Φ) := by
    rw [hPM]
    simp only [Matrix.add_mulVec, dotProduct_add]
    congr 1
    rw [hz, dotProduct_smul, smul_eq_mul]
    ring
  rw [hM, hP, star_dotProduct_self_eq'] at hexp
  exact hexp

/-- **One lowering step is non-zero on a positive-weight vector.** For `Φ ≠ 0` with
`Ŝ³_tot Φ = w Φ` and `0 < w.re`, `Ŝ⁻_tot Φ ≠ 0`. -/
theorem totalSpinSOpMinus_mulVec_ne_zero_of_pos_weight
    {w : ℂ} {Φ : (V → Fin (N + 1)) → ℂ} (hΦ_ne : Φ ≠ 0)
    (hz : (totalSpinSOp3 V N).mulVec Φ = w • Φ) (hw : 0 < w.re) :
    (totalSpinSOpMinus V N).mulVec Φ ≠ 0 := by
  intro hzero
  have hid := totalSpinSOpMinus_mulVec_normSq_eq V N hz
  have hre := congrArg Complex.re hid
  set Sm : ℝ := ∑ i, Complex.normSq ((totalSpinSOpMinus V N).mulVec Φ i) with hSm
  set Sp : ℝ := ∑ i, Complex.normSq ((totalSpinSOpPlus V N).mulVec Φ i) with hSp
  set z : ℝ := ∑ i, Complex.normSq (Φ i) with hzdef
  have hSm0 : Sm = 0 := by rw [hSm, hzero]; simp
  have hSp_nn : 0 ≤ Sp := Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
  have hz_pos : 0 < z := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hΦ_ne
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ i, lt_of_le_of_ne (Complex.normSq_nonneg _)
        (Ne.symm (by simpa [Complex.normSq_eq_zero] using hi))⟩
  simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.add_im,
    Complex.ofReal_im, mul_zero, sub_zero] at hre
  -- hre : Sm = Sp + (w.re + w.re) * z
  nlinarith [hre, hSm0, hSp_nn, hz_pos, hw]

/-- **One raising step is non-zero on a negative-weight vector.** For `Φ ≠ 0` with
`Ŝ³_tot Φ = w Φ` and `w.re < 0`, `Ŝ⁺_tot Φ ≠ 0`. -/
theorem totalSpinSOpPlus_mulVec_ne_zero_of_neg_weight
    {w : ℂ} {Φ : (V → Fin (N + 1)) → ℂ} (hΦ_ne : Φ ≠ 0)
    (hz : (totalSpinSOp3 V N).mulVec Φ = w • Φ) (hw : w.re < 0) :
    (totalSpinSOpPlus V N).mulVec Φ ≠ 0 := by
  intro hzero
  have hid := totalSpinSOpMinus_mulVec_normSq_eq V N hz
  have hre := congrArg Complex.re hid
  set Sm : ℝ := ∑ i, Complex.normSq ((totalSpinSOpMinus V N).mulVec Φ i) with hSm
  set Sp : ℝ := ∑ i, Complex.normSq ((totalSpinSOpPlus V N).mulVec Φ i) with hSp
  set z : ℝ := ∑ i, Complex.normSq (Φ i) with hzdef
  have hSp0 : Sp = 0 := by rw [hSp, hzero]; simp
  have hSm_nn : 0 ≤ Sm := Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
  have hz_pos : 0 < z := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hΦ_ne
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ i, lt_of_le_of_ne (Complex.normSq_nonneg _)
        (Ne.symm (by simpa [Complex.normSq_eq_zero] using hi))⟩
  simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.add_im,
    Complex.ofReal_im, mul_zero, sub_zero] at hre
  nlinarith [hre, hSp0, hSm_nn, hz_pos, hw]

end LatticeSystem.Quantum
