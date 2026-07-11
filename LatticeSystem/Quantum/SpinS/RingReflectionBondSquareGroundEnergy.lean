/-
Ground-state energy uniform-field bound `E_GS(h) ≥ E_GS(0)` (Tasaki §4.1 (4.1.40)/(4.1.49),
book pp. 85–86, PR-χ1). The `T → 0` limit of the finite-`β` bond-square partition inequality
`Z^{BS}_β(h) ≤ Z^{BS}_β(0)` (`ringBondSquareFieldPartitionRe_uniform_bound`, PR-BS10).

Taking logs (both partition functions are strictly positive, `ringBondSquareFieldPartitionRe_pos`,
BS9) and multiplying by `−(1/β) < 0` (which reverses the inequality) gives, for every `β > 0`,
`−(1/β) log Z^{BS}_β(0) ≤ −(1/β) log Z^{BS}_β(h)` (the free energies).  As `β → ∞` both sides
converge to the respective ground-state energies (`(χ1-a)`,
`tendsto_neg_inv_mul_log_trace_exp_re_atTop_hermitianMinEigenvalue`, since
`Z^{BS}_β(g) = Re Tr e^{−βĤ_g}` definitionally), so the limit order-preservation
(`le_of_tendsto_of_tendsto`) yields `E_GS(0) ≤ E_GS(h)`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, (4.1.40)/(4.1.49), book pp. 85–86.  See
`.self-local/docs/math-tasaki-4-1-40-free-energy-t0-ground-energy.md` (issue #4777).
-/
import LatticeSystem.Quantum.SpinS.RingReflectionBondSquareUniformBound
import LatticeSystem.Quantum.SpinS.FreeEnergyGroundEnergyLimit

namespace LatticeSystem.Quantum

open Matrix Filter

variable {N : ℕ}

/-- **Ground-state energy uniform-field bound** `E_GS(h) ≥ E_GS(0)` (Tasaki §4.1 (4.1.40)/(4.1.49),
book pp. 85–86): the ground-state energy of the bond-square field Hamiltonian at field `h` is at
least that at zero field, on the even ring `Fin (2n)` (`n ≥ 1`).  The `T → 0` limit of the
finite-`β` partition bound `ringBondSquareFieldPartitionRe_uniform_bound` (`Z^{BS}_β(h) ≤
Z^{BS}_β(0)`, PR-BS10): both partition functions are strictly positive
(`ringBondSquareFieldPartitionRe_pos`, BS9) so `Real.log` is monotone, and multiplying the log
inequality by `−(1/β) < 0` reverses it into the free-energy inequality
`−(1/β) log Z^{BS}_β(0) ≤ −(1/β) log Z^{BS}_β(h)` for `β > 0`; the free energies converge to the
ground-state energies as `β → ∞` (`(χ1-a)`,
`tendsto_neg_inv_mul_log_trace_exp_re_atTop_hermitianMinEigenvalue`, applied to the field
Hamiltonian whose partition function is `Z^{BS}_β` definitionally), and
`le_of_tendsto_of_tendsto` passes the inequality to the limits. -/
theorem ringBondSquareFieldHamiltonian_hermitianMinEigenvalue_ge_field_zero
    (G : AxisTwoPiRotS N) (n : ℕ) [NeZero n] (hn : 1 ≤ n) (h : Fin (2 * n) → ℝ) :
    hermitianMinEigenvalue (ringBondSquareFieldHamiltonian_isHermitian n N (0 : Fin (2 * n) → ℝ))
      ≤ hermitianMinEigenvalue (ringBondSquareFieldHamiltonian_isHermitian n N h) := by
  -- `(χ1-a)` at both fields (the trace-`re` limit is `Z^{BS}_β` definitionally)
  have th : Filter.Tendsto
      (fun β : ℝ => -(1 / β) * Real.log (ringBondSquareFieldPartitionRe n N β h))
      Filter.atTop
      (nhds (hermitianMinEigenvalue (ringBondSquareFieldHamiltonian_isHermitian n N h))) :=
    tendsto_neg_inv_mul_log_trace_exp_re_atTop_hermitianMinEigenvalue
      (ringBondSquareFieldHamiltonian_isHermitian n N h)
  have t0 : Filter.Tendsto
      (fun β : ℝ => -(1 / β) * Real.log (ringBondSquareFieldPartitionRe n N β 0))
      Filter.atTop
      (nhds (hermitianMinEigenvalue (ringBondSquareFieldHamiltonian_isHermitian n N 0))) :=
    tendsto_neg_inv_mul_log_trace_exp_re_atTop_hermitianMinEigenvalue
      (ringBondSquareFieldHamiltonian_isHermitian n N 0)
  -- the free-energy inequality holds for every `β > 0`
  have hle : (fun β : ℝ => -(1 / β) * Real.log (ringBondSquareFieldPartitionRe n N β 0))
      ≤ᶠ[Filter.atTop]
        fun β : ℝ => -(1 / β) * Real.log (ringBondSquareFieldPartitionRe n N β h) := by
    refine Filter.eventually_atTop.2 ⟨1, fun β hβ => ?_⟩
    have hβpos : 0 < β := by linarith
    have hbound := ringBondSquareFieldPartitionRe_uniform_bound G n hn hβpos.le h
    have hlog : Real.log (ringBondSquareFieldPartitionRe n N β h)
        ≤ Real.log (ringBondSquareFieldPartitionRe n N β 0) :=
      (Real.log_le_log_iff (ringBondSquareFieldPartitionRe_pos n N β h)
        (ringBondSquareFieldPartitionRe_pos n N β 0)).mpr hbound
    have hinv : (0 : ℝ) ≤ 1 / β := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hlog hinv]
  exact le_of_tendsto_of_tendsto t0 th hle

end LatticeSystem.Quantum
