/-
Free-energy `T → 0` limit: the ground-state energy is the zero-temperature limit of the
Helmholtz free energy `−(1/β) log Tr e^{−βĤ}` (Tasaki §4.1 (4.1.40)/(4.1.49), book pp. 85–86,
PR-χ1). This is the real-analysis engine feeding the susceptibility phase: from the finite-`β`
bond-square partition inequality `Z^{BS}_β(h) ≤ Z^{BS}_β(0)` one recovers, in the `β → ∞` limit,
the ground-state energy inequality `E_GS(h) ≥ E_GS(0)`.

Two lemmas are established:
* `(SUM)` `trace_exp_smul_neg_re_eq_sum_exp`: the real part of `Tr e^{−βĤ}` is the eigenvalue sum
  `∑_i e^{−β λ_i}` (spectral theorem, `−β` folded into the diagonal — a `β`-scaled real-part
  specialisation of `LatticeSystem.Math.trace_exp_eq_sum_exp_eigenvalues`, not an α-equivalent
  duplicate: the scalar `−β` lives inside the diagonal and the statement is over `Real.exp`);
* `(χ1-a)` `tendsto_neg_inv_mul_log_trace_exp_re_atTop_hermitianMinEigenvalue`: for a Hermitian
  `H`, `−(1/β) log (Tr e^{−βH}).re → hermitianMinEigenvalue hH` as `β → ∞`, via the `Fintype.card`
  two-sided squeeze `e^{−βE} ≤ Z(β) ≤ (card)·e^{−βE}` (the degeneracy/gap prefactor is
  subleading: `(1/β) log card → 0`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, (4.1.40)/(4.1.49), book pp. 85–86.  See
`.self-local/docs/math-tasaki-4-1-40-free-energy-t0-ground-energy.md` (issue #4777).
-/
import LatticeSystem.Math.MatrixAnalysis.TraceExpMonotone
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueViaRayleigh
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace LatticeSystem.Quantum

open Matrix Filter Topology

/-- **(SUM) — eigenvalue-sum form of the real Gibbs trace.**  For a Hermitian matrix `H`, the real
part of the Gibbs trace `Tr e^{−βH}` is the sum of Boltzmann weights over the (real) eigenvalues,
`Re Tr e^{−βH} = ∑_i e^{−β λ_i}` (Tasaki §4.1, book p.85).  Writing `H = U·diag(λ)·U⋆`
(`Matrix.IsHermitian.spectral_theorem`), the scalar `−β` folds into the diagonal, the exponential
passes through the (continuous) conjugation automorphism (`Matrix.exp_conj`), exponentiates the
diagonal entrywise (`Matrix.exp_diagonal`) and the trace drops the unitary conjugation
(`Matrix.trace_mul_cycle`); each entry `e^{−β λ_i}` is real (`Complex.exp_ofReal_re`).  This is a
`β`-scaled, real-part specialisation of `LatticeSystem.Math.trace_exp_eq_sum_exp_eigenvalues`
(there the sum runs over `Complex.exp` of the eigenvalues of the *unscaled* matrix); the scalar
`−β` living inside the diagonal makes it a distinct statement, not an α-equivalent duplicate. -/
theorem trace_exp_smul_neg_re_eq_sum_exp {m : Type*} [Fintype m] [DecidableEq m]
    {H : Matrix m m ℂ} (hH : H.IsHermitian) (β : ℝ) :
    ((NormedSpace.exp ((-(β : ℂ)) • H)).trace).re
      = ∑ i, Real.exp (-β * hH.eigenvalues i) := by
  have hu : IsUnit (hH.eigenvectorUnitary : Matrix m m ℂ) :=
    IsUnit.of_mul_eq_one _ (Unitary.coe_mul_star_self hH.eigenvectorUnitary)
  have hinv : (star hH.eigenvectorUnitary : Matrix m m ℂ)
      = (hH.eigenvectorUnitary : Matrix m m ℂ)⁻¹ :=
    (Matrix.inv_eq_right_inv (Unitary.coe_mul_star_self _)).symm
  set d : m → ℂ := (RCLike.ofReal ∘ hH.eigenvalues) with hd
  -- move the scalar `−β` through the conjugation onto the diagonal
  have hds : (-(β : ℂ)) • Matrix.diagonal d
      = Matrix.diagonal (fun i => -(β : ℂ) * d i) := by
    ext i j
    rcases eq_or_ne i j with h | h
    · subst h; simp [Matrix.diagonal_apply_eq, Matrix.smul_apply]
    · simp [Matrix.smul_apply, h]
  have hconj : (-(β : ℂ)) • H
      = (hH.eigenvectorUnitary : Matrix m m ℂ)
          * Matrix.diagonal (fun i => -(β : ℂ) * d i)
          * (hH.eigenvectorUnitary : Matrix m m ℂ)⁻¹ := by
    conv_lhs => rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply, hinv]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hds]
  -- complex eigenvalue-sum form of the trace, then take real parts
  have hkey : (NormedSpace.exp ((-(β : ℂ)) • H)).trace
      = ∑ i, Complex.exp (-(β : ℂ) * d i) := by
    rw [hconj, Matrix.exp_conj _ _ hu, Matrix.exp_diagonal, Matrix.trace_mul_cycle,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), one_mul,
      Matrix.trace_diagonal]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.coe_exp]
    exact congrFun Complex.exp_eq_exp_ℂ.symm _
  rw [hkey, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show -(β : ℂ) * d i = (((-β * hH.eigenvalues i : ℝ)) : ℂ) by
        simp only [hd, Function.comp_apply, RCLike.ofReal_eq_complex_ofReal]; push_cast; ring,
    Complex.exp_ofReal_re]

/-- **(χ1-a) — the ground-state energy is the `T → 0` limit of the free energy.**  For a Hermitian
matrix `H` on a non-empty index type, `−(1/β) log (Re Tr e^{−βH}) → hermitianMinEigenvalue hH` as
`β → ∞` (Tasaki §4.1 (4.1.40)/(4.1.49), book pp. 85–86).  With `E = hermitianMinEigenvalue hH` and
`Z(β) = Re Tr e^{−βH} = ∑_i e^{−β λ_i}` `(SUM)`, the bounds `E ≤ λ_i`
(`hermitian_min_eigenvalue_le`) and `β ≥ 0` give the `Fintype.card` squeeze
`e^{−βE} ≤ Z(β) ≤ (card)·e^{−βE}`; taking logs and multiplying by `−(1/β)` yields
`E − (log card)/β ≤ −(1/β) log Z(β) ≤ E`, and both ends tend to `E` (`(log card)/β → 0`), so the
`tendsto_of_tendsto_of_tendsto_of_le_of_le'` squeeze concludes.  The minimum-eigenvalue degeneracy
plays no role: the `(1/β) log card` correction is subleading. -/
theorem tendsto_neg_inv_mul_log_trace_exp_re_atTop_hermitianMinEigenvalue
    {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    {H : Matrix m m ℂ} (hH : H.IsHermitian) :
    Filter.Tendsto
      (fun β : ℝ => -(1 / β) * Real.log ((NormedSpace.exp ((-(β : ℂ)) • H)).trace).re)
      Filter.atTop (nhds (hermitianMinEigenvalue hH)) := by
  set E : ℝ := hermitianMinEigenvalue hH with hE
  set c : ℝ := (Fintype.card m : ℝ) with hc
  have hcpos : 0 < c := by rw [hc]; exact_mod_cast Fintype.card_pos
  obtain ⟨i₀, hi₀⟩ := exists_index_eigenvalue_eq_hermitianMinEigenvalue hH
  have hsum : ∀ β : ℝ, ((NormedSpace.exp ((-(β : ℂ)) • H)).trace).re
      = ∑ i, Real.exp (-β * hH.eigenvalues i) := fun β => trace_exp_smul_neg_re_eq_sum_exp hH β
  have hpos : ∀ β : ℝ, 0 < ((NormedSpace.exp ((-(β : ℂ)) • H)).trace).re := by
    intro β; rw [hsum β]
    exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hlb : ∀ β : ℝ, 0 ≤ β →
      Real.exp (-β * E) ≤ ((NormedSpace.exp ((-(β : ℂ)) • H)).trace).re := by
    intro β _
    rw [hsum β, show Real.exp (-β * E) = Real.exp (-β * hH.eigenvalues i₀) by rw [hi₀]]
    exact Finset.single_le_sum (f := fun i => Real.exp (-β * hH.eigenvalues i))
      (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ i₀)
  have hub : ∀ β : ℝ, 0 ≤ β →
      ((NormedSpace.exp ((-(β : ℂ)) • H)).trace).re ≤ c * Real.exp (-β * E) := by
    intro β hβ
    rw [hsum β]
    calc ∑ i, Real.exp (-β * hH.eigenvalues i)
        ≤ ∑ _i : m, Real.exp (-β * E) := by
          refine Finset.sum_le_sum fun i _ => Real.exp_le_exp.mpr ?_
          nlinarith [mul_le_mul_of_nonneg_left (hermitian_min_eigenvalue_le hH i) hβ]
      _ = c * Real.exp (-β * E) := by
          rw [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul]
  -- the two ends of the squeeze both converge to `E`
  have hinv0 : Filter.Tendsto (fun β : ℝ => Real.log c / β) Filter.atTop (nhds 0) := by
    have := (tendsto_const_nhds (x := Real.log c)).mul tendsto_inv_atTop_zero
    simpa [div_eq_mul_inv] using this
  have hgle : Filter.Tendsto (fun β : ℝ => E - Real.log c / β) Filter.atTop (nhds E) := by
    have := (tendsto_const_nhds (x := E)).sub hinv0
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hgle tendsto_const_nhds
    (Filter.eventually_atTop.2 ⟨1, fun β hβ => ?_⟩)
    (Filter.eventually_atTop.2 ⟨1, fun β hβ => ?_⟩)
  · -- lower bound `E − (log c)/β ≤ −(1/β) log Z(β)`
    have hβpos : 0 < β := by linarith
    have hlogU : Real.log (((NormedSpace.exp ((-(β : ℂ)) • H)).trace).re)
        ≤ Real.log c - β * E := by
      have h1 := (Real.log_le_log_iff (hpos β)
        (mul_pos hcpos (Real.exp_pos _))).mpr (hub β hβpos.le)
      rw [Real.log_mul (ne_of_gt hcpos) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at h1
      linarith
    have hlc : Real.log c / β * β = Real.log c := div_mul_cancel₀ _ (ne_of_gt hβpos)
    rw [show -(1 / β) * Real.log (((NormedSpace.exp ((-(β : ℂ)) • H)).trace).re)
          = (-(Real.log (((NormedSpace.exp ((-(β : ℂ)) • H)).trace).re))) / β by
        rw [neg_mul, one_div_mul_eq_div, ← neg_div], le_div_iff₀ hβpos]
    nlinarith [hlogU, hlc]
  · -- upper bound `−(1/β) log Z(β) ≤ E`
    have hβpos : 0 < β := by linarith
    have hlogL : -β * E ≤ Real.log (((NormedSpace.exp ((-(β : ℂ)) • H)).trace).re) := by
      have h1 := (Real.log_le_log_iff (Real.exp_pos _) (hpos β)).mpr (hlb β hβpos.le)
      rwa [Real.log_exp] at h1
    rw [show -(1 / β) * Real.log (((NormedSpace.exp ((-(β : ℂ)) • H)).trace).re)
          = (-(Real.log (((NormedSpace.exp ((-(β : ℂ)) • H)).trace).re))) / β by
        rw [neg_mul, one_div_mul_eq_div, ← neg_div], div_le_iff₀ hβpos]
    nlinarith [hlogL]

end LatticeSystem.Quantum
