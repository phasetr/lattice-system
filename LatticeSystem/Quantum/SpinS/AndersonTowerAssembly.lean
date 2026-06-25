/-
Tasaki §4.2.2 Theorem 4.6 (Anderson tower), Tier 4 — assembly.

Combines the renormalized denominator bound (Lemma R1) and the renormalized numerator bound
(Lemma R2, via the variational double-commutator identity) to discharge the energy-bound axiom
`tower_lowLying_energy_bound`.
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerLocality
import LatticeSystem.Quantum.SpinS.HermitianVariationalLowerBound
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueEigenvector

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

/-! ### Variational identity feeders (P9-6) -/

/-- A Hermitian matrix has real eigenvalues: an eigenvalue `E₀` with a nonzero eigenvector
(`H Φ = E₀ Φ`) has `E₀.im = 0`. -/
theorem hermitian_mulVec_eigenvalue_im_zero {n : Type*} [Fintype n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {Φ : n → ℂ} {E₀ : ℂ}
    (hΦ : Φ ≠ 0) (hev : H.mulVec Φ = E₀ • Φ) : E₀.im = 0 := by
  have hnn : (0 : ℂ) ≤ star Φ ⬝ᵥ Φ := dotProduct_star_self_nonneg Φ
  have hpos : (0 : ℂ) < star Φ ⬝ᵥ Φ := Matrix.dotProduct_star_self_pos_iff.mpr hΦ
  have hΦim : (star Φ ⬝ᵥ Φ).im = 0 := ((Complex.le_def.mp hnn).2).symm
  have hΦre : 0 < (star Φ ⬝ᵥ Φ).re := (Complex.lt_def.mp hpos).1
  have him : (star Φ ⬝ᵥ H.mulVec Φ).im = 0 := hermitian_dotProduct_im_zero hH Φ
  rw [hev, dotProduct_smul, smul_eq_mul, Complex.mul_im, hΦim, mul_zero, zero_add] at him
  exact (mul_eq_zero.mp him).resolve_right (ne_of_gt hΦre)

/-- The torus nearest-neighbor coupling is real-valued (`0` or `1`). -/
theorem torusNNCoupling_real (d L : ℕ) [NeZero L] (x y : HypercubicTorus d L) :
    star (torusNNCoupling d L x y) = torusNNCoupling d L x y := by
  unfold torusNNCoupling
  classical
  split <;> simp

/-- The torus AFM Heisenberg Hamiltonian is Hermitian. -/
theorem heisenbergHamiltonianS_torus_isHermitian (d L N : ℕ) [NeZero L] :
    (heisenbergHamiltonianS (torusNNCoupling d L) N).IsHermitian :=
  heisenbergHamiltonianS_isHermitian_of_real (torusNNCoupling_real d L) N

/-- **Variational gap ≤ double commutator (★).**  For a Hermitian `Ĥ` with ground state
`Ĥ Φ = E₀ Φ` (`E₀` the minimum eigenvalue), the raising-tower energy gap is bounded by the symmetric
double commutator: `⟨AΦ,ĤAΦ⟩ − E₀⟨AΦ,AΦ⟩ ≤ ⟨Φ, [A†,[Ĥ,A]] Φ⟩` with `A = (ô⁺)^M`, `A† = (ô⁻)^M`.
Pure-algebra identity `NumGap(A) + NumGap(A†) = ⟨[A†,[Ĥ,A]]⟩` plus `NumGap(A†) ≥ 0`. -/
theorem tower_numerator_double_commutator_le (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ : ℂ) (M : ℕ)
    (hev : (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Φ = E₀ • Φ)
    (hmin : ∀ (E : ℂ) (Ψ : (HypercubicTorus d L → Fin (N + 1)) → ℂ), Ψ ≠ 0 →
       (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re)
    (hΦ : Φ ≠ 0) :
    (star ((staggeredOrderDensityOpS d L N true ^ M).mulVec Φ) ⬝ᵥ
        (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec
          ((staggeredOrderDensityOpS d L N true ^ M).mulVec Φ)).re
      - E₀.re * (star ((staggeredOrderDensityOpS d L N true ^ M).mulVec Φ) ⬝ᵥ
          (staggeredOrderDensityOpS d L N true ^ M).mulVec Φ).re
    ≤ (star Φ ⬝ᵥ
        ((staggeredOrderDensityOpS d L N false ^ M)
            * (heisenbergHamiltonianS (torusNNCoupling d L) N
                * staggeredOrderDensityOpS d L N true ^ M
              - staggeredOrderDensityOpS d L N true ^ M
                * heisenbergHamiltonianS (torusNNCoupling d L) N)
          - (heisenbergHamiltonianS (torusNNCoupling d L) N
                * staggeredOrderDensityOpS d L N true ^ M
              - staggeredOrderDensityOpS d L N true ^ M
                * heisenbergHamiltonianS (torusNNCoupling d L) N)
            * (staggeredOrderDensityOpS d L N false ^ M)).mulVec Φ).re := by
  set H := heisenbergHamiltonianS (torusNNCoupling d L) N with hH
  set A := staggeredOrderDensityOpS d L N true ^ M with hA
  set Adag := staggeredOrderDensityOpS d L N false ^ M with hAd
  have hHerm : H.IsHermitian := heisenbergHamiltonianS_torus_isHermitian d L N
  have hAdag : Adag = Matrix.conjTranspose A := orderDensityFalse_pow_eq_conjTranspose d L N M
  have hE₀im : E₀.im = 0 := hermitian_mulVec_eigenvalue_im_zero hHerm hΦ hev
  -- the four-term complex identity
  have hT1 : star Φ ⬝ᵥ (Adag * (H * A)).mulVec Φ
      = star (A.mulVec Φ) ⬝ᵥ H.mulVec (A.mulVec Φ) := by
    rw [← Matrix.mulVec_mulVec, hAdag, star_dotProduct_mulVec_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.mulVec_mulVec]
  have hT2 : star Φ ⬝ᵥ (Adag * A * H).mulVec Φ
      = E₀ * (star (A.mulVec Φ) ⬝ᵥ A.mulVec Φ) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hev, Matrix.mulVec_smul,
      Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, hAdag,
      star_dotProduct_mulVec_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have hconjE : (star E₀ : ℂ) = E₀ := by
    rw [Complex.star_def]; exact Complex.conj_eq_iff_im.mpr hE₀im
  have hT3 : star Φ ⬝ᵥ (H * A * Adag).mulVec Φ
      = E₀ * (star (Adag.mulVec Φ) ⬝ᵥ Adag.mulVec Φ) := by
    rw [mul_assoc, hermitian_dotProduct_shift hHerm, hev, star_smul, smul_dotProduct, hconjE,
      smul_eq_mul, ← Matrix.mulVec_mulVec, hAdag, star_dotProduct_mulVec_conjTranspose]
  have hT4 : star Φ ⬝ᵥ (A * H * Adag).mulVec Φ
      = star (Adag.mulVec Φ) ⬝ᵥ H.mulVec (Adag.mulVec Φ) := by
    rw [mul_assoc, ← Matrix.mulVec_mulVec, hAdag, star_dotProduct_mulVec_conjTranspose,
      Matrix.mulVec_mulVec]
  have hP : Adag * (H * A - A * H) - (H * A - A * H) * Adag
      = Adag * (H * A) - Adag * A * H - H * A * Adag + A * H * Adag := by noncomm_ring
  have heq : star Φ ⬝ᵥ (Adag * (H * A - A * H) - (H * A - A * H) * Adag).mulVec Φ
      = (star (A.mulVec Φ) ⬝ᵥ H.mulVec (A.mulVec Φ) - E₀ * (star (A.mulVec Φ) ⬝ᵥ A.mulVec Φ))
        + (star (Adag.mulVec Φ) ⬝ᵥ H.mulVec (Adag.mulVec Φ)
            - E₀ * (star (Adag.mulVec Φ) ⬝ᵥ Adag.mulVec Φ)) := by
    rw [hP]
    simp only [Matrix.add_mulVec, Matrix.sub_mulVec, dotProduct_add, dotProduct_sub,
      hT1, hT2, hT3, hT4]
    ring
  -- take real parts; E₀ real and self-products real
  have hself1 : (star (A.mulVec Φ) ⬝ᵥ A.mulVec Φ).im = 0 :=
    ((Complex.le_def.mp (dotProduct_star_self_nonneg (A.mulVec Φ))).2).symm
  have hself2 : (star (Adag.mulVec Φ) ⬝ᵥ Adag.mulVec Φ).im = 0 :=
    ((Complex.le_def.mp (dotProduct_star_self_nonneg (Adag.mulVec Φ))).2).symm
  have hre : (star Φ ⬝ᵥ (Adag * (H * A - A * H) - (H * A - A * H) * Adag).mulVec Φ).re
      = (star (A.mulVec Φ) ⬝ᵥ H.mulVec (A.mulVec Φ)).re
          - E₀.re * (star (A.mulVec Φ) ⬝ᵥ A.mulVec Φ).re
        + ((star (Adag.mulVec Φ) ⬝ᵥ H.mulVec (Adag.mulVec Φ)).re
          - E₀.re * (star (Adag.mulVec Φ) ⬝ᵥ Adag.mulVec Φ).re) := by
    rw [heq]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, hE₀im, hself1, hself2]
    ring
  -- NumGap(A†) ≥ 0 by the variational lower bound
  have hvar := hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec hHerm (Adag.mulVec Φ)
  obtain ⟨v, hv_ne, hv_eig⟩ := exists_nonzero_eigenvector_hermitianMinEigenvalue hHerm
  have hE₀le : E₀.re ≤ hermitianMinEigenvalue hHerm := by
    have := hmin ((hermitianMinEigenvalue hHerm : ℝ) : ℂ) v hv_ne hv_eig
    simpa using this
  have hdenom : 0 ≤ (star (Adag.mulVec Φ) ⬝ᵥ Adag.mulVec Φ).re :=
    (Complex.le_def.mp (dotProduct_star_self_nonneg (Adag.mulVec Φ))).1
  have hnumgap_dag : 0 ≤ (star (Adag.mulVec Φ) ⬝ᵥ H.mulVec (Adag.mulVec Φ)).re
      - E₀.re * (star (Adag.mulVec Φ) ⬝ᵥ Adag.mulVec Φ).re := by
    have h1 : E₀.re * (star (Adag.mulVec Φ) ⬝ᵥ Adag.mulVec Φ).re
        ≤ hermitianMinEigenvalue hHerm * (star (Adag.mulVec Φ) ⬝ᵥ Adag.mulVec Φ).re :=
      mul_le_mul_of_nonneg_right hE₀le hdenom
    have h2 : hermitianMinEigenvalue hHerm * (star (Adag.mulVec Φ) ⬝ᵥ Adag.mulVec Φ).re
        ≤ rayleighOnVec H (Adag.mulVec Φ) := hvar
    have h3 : rayleighOnVec H (Adag.mulVec Φ)
        = (star (Adag.mulVec Φ) ⬝ᵥ H.mulVec (Adag.mulVec Φ)).re := rfl
    linarith
  rw [hre]
  linarith

/-! ### Numerator expansion (P9-7) -/

/-- **Commutator power telescope**: `[H, Aᴹ] = Σ_{j<M} Aʲ [H,A] A^{M-1-j}`. -/
theorem commutator_pow_eq_sum {n : Type*} [Fintype n] [DecidableEq n]
    (H A : Matrix n n ℂ) (M : ℕ) :
    H * A ^ M - A ^ M * H
      = ∑ j ∈ Finset.range M, A ^ j * (H * A - A * H) * A ^ (M - 1 - j) := by
  induction M with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hsplit : H * A ^ (m + 1) - A ^ (m + 1) * H
        = (H * A ^ m - A ^ m * H) * A + A ^ m * (H * A - A * H) := by
      rw [pow_succ]; noncomm_ring
    rw [hsplit, ih, Finset.sum_mul]
    rw [show A ^ (m + 1 - 1 - m) = (1 : Matrix n n ℂ) by simp]
    rw [mul_one]
    congr 1
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    rw [mul_assoc, ← pow_succ]
    congr 2
    omega

/-- The `false`-outer double commutator `[ô⁻,[Ĥ,ô⁺]]` is the conjugate transpose of the `true`-outer
one, hence carries the same `g₀/V` bound: `‖[ô⁻,[Ĥ,ô⁺]]‖ ≤ 96 d N⁴ / V`. -/
theorem orderDensity_double_commutator_false_norm_le (d L N : ℕ) [NeZero L] (hL : 2 ≤ L)
    (hN : 1 ≤ N) :
    manyBodyOperatorNormS
      (staggeredOrderDensityOpS d L N false
          * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true * heisenbergHamiltonianS (torusNNCoupling d L) N)
        - (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true * heisenbergHamiltonianS (torusNNCoupling d L) N)
          * staggeredOrderDensityOpS d L N false)
      ≤ 96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d := by
  have hHerm := (heisenbergHamiltonianS_torus_isHermitian d L N).eq
  have hconj : (staggeredOrderDensityOpS d L N false
          * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true * heisenbergHamiltonianS (torusNNCoupling d L) N)
        - (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true * heisenbergHamiltonianS (torusNNCoupling d L) N)
          * staggeredOrderDensityOpS d L N false)
      = Matrix.conjTranspose
          (staggeredOrderDensityOpS d L N true
              * (heisenbergHamiltonianS (torusNNCoupling d L) N
                  * staggeredOrderDensityOpS d L N false
                - staggeredOrderDensityOpS d L N false
                  * heisenbergHamiltonianS (torusNNCoupling d L) N)
            - (heisenbergHamiltonianS (torusNNCoupling d L) N
                  * staggeredOrderDensityOpS d L N false
                - staggeredOrderDensityOpS d L N false
                  * heisenbergHamiltonianS (torusNNCoupling d L) N)
              * staggeredOrderDensityOpS d L N true) := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hHerm,
      staggeredOrderDensityOpS_conjTranspose, Bool.not_true, Bool.not_false]
    noncomm_ring
  rw [hconj, manyBodyOperatorNormS_conjTranspose]
  exact orderDensity_double_commutator_norm_le d L N hL hN

/-! ### Capstone feeders (P9-8) -/

/-- The nonnegative-`M` tower state is `V^M` times the per-volume order-density power on `Φ`:
`Ψ_M = V^M (ô⁺)^M Φ`. -/
theorem towerState_pos_eq_smul (d L N : ℕ) [NeZero L] (m : ℕ)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) :
    towerState (torusParitySublattice d L) N (m : ℤ) Φ
      = ((L : ℂ) ^ d) ^ m • (staggeredOrderDensityOpS d L N true ^ m).mulVec Φ := by
  rw [towerState, if_pos (by positivity : (0 : ℤ) ≤ (m : ℤ)), Int.natAbs_natCast,
    staggeredRaisingOpS_eq_smul, smul_pow, Matrix.smul_mulVec]

/-- The Rayleigh quotient is invariant under a nonzero scalar rescaling of the vector. -/
theorem rayleigh_smul_invariant {n : Type*} [Fintype n] (H : Matrix n n ℂ)
    (c : ℂ) (hc : c ≠ 0) (v : n → ℂ) :
    (star (c • v) ⬝ᵥ H.mulVec (c • v)).re / (star (c • v) ⬝ᵥ (c • v)).re
      = (star v ⬝ᵥ H.mulVec v).re / (star v ⬝ᵥ v).re := by
  have hns : (0 : ℝ) < Complex.normSq c := Complex.normSq_pos.mpr hc
  have hnum : star (c • v) ⬝ᵥ H.mulVec (c • v)
      = (Complex.normSq c : ℂ) * (star v ⬝ᵥ H.mulVec v) := by
    rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  have hden : star (c • v) ⬝ᵥ (c • v) = (Complex.normSq c : ℂ) * (star v ⬝ᵥ v) := by
    rw [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  rw [hnum, hden, Complex.re_ofReal_mul, Complex.re_ofReal_mul, mul_div_mul_left _ _ (ne_of_gt hns)]

end LatticeSystem.Quantum
