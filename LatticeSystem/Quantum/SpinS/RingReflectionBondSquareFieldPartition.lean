/-
The bond-square field partition function and its scalar-shift reduction to the linear-core
partition function (Tasaki §4.1 Theorem 4.2, reflection-positivity bond-square layer, PR-BS2).

Tasaki's field Hamiltonian (4.1.48), book p.86, couples the staggered field *quadratically* inside
the bond-square.  PR-BS1 (`ringBondSquareFieldHamiltonian_eq`, merged #4987) proved the reduction
`(★)` `Ĥ_h = Ĥ(kOf h) + C(h)·1`.  Here we take the finite-temperature partition function
`Z^{BS}_β(h) = Re Tr e^{−βĤ_h}` (4.1.48) and factor out the central scalar constant: since
`C(h)·1` commutes with `Ĥ(kOf h)`, the matrix exponential splits and the real scalar `e^{−βC(h)}`
pulls out of both the trace and the real part, giving the reduction
`(★★)` `Z^{BS}_β(h) = e^{−βC(h)} · Z^{repo}_β(kOf h)` (Tasaki §4.1 (4.1.49), book p.86, the
finite-`β` form of the uniform field bound).  This equation lets PR-BS3 onward reuse the merged
single-field symmetries of `ringFieldPartitionRe` for the bond-square partition function without
redefining `Z` on a field map.

See `.self-local/docs/math-tasaki-4-1-49-bond-square-partition-reduction.md` (issue #4777).
-/
import LatticeSystem.Quantum.SpinS.RingReflectionBondSquareField

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- **Bond-square field partition function** `Z^{BS}_β(h) = Re Tr exp(−β·Ĥ_h)` (Tasaki §4.1
(4.1.48), book p.86), the canonical partition function of the bond-square field Hamiltonian
`ringBondSquareFieldHamiltonian`.  As with `ringFieldPartitionRe`, the real part is taken
*definitionally*: the bond-square field Hamiltonian is Hermitian
(`ringBondSquareFieldHamiltonian_isHermitian`), so the Gibbs trace is real and `.re` recovers it. -/
noncomputable def ringBondSquareFieldPartitionRe (n N : ℕ) (β : ℝ) (h : Fin (2 * n) → ℝ) : ℝ :=
  (thermalPartitionFnS β (ringBondSquareFieldHamiltonian n N h)).re

/-- **Scalar-shift reduction `(★★)`** (Tasaki §4.1 (4.1.49), book p.86): the bond-square field
partition function equals `e^{−βC(h)}` times the linear-core partition function at the regrouped
field, `Z^{BS}_β(h) = e^{−βC(h)} · Z^{repo}_β(kOf h)`.  Proved from the reduction identity `(★)`
(`ringBondSquareFieldHamiltonian_eq`): the exponent splits as `−β·Ĥ(kOf h) + (−βC(h))·1`, the two
summands commute (the constant is central), so `Matrix.exp_add_of_commute` factors the exponential;
the scalar exponential `exp((−βC)·1) = e^{−βC}·1` is evaluated by `Matrix.exp_diagonal`, and the
real scalar `e^{−βC(h)}` pulls out of the trace (`Matrix.trace_smul`) and the real part
(`Complex.re_ofReal_mul`).  Holds for all `β ∈ ℝ`; `[NeZero n]` is inherited from `(★)`.  This is
the
equation feeding the reflection-positivity chain (PR-BS3 onward) via the merged single-field
symmetries of `ringFieldPartitionRe`. -/
theorem ringBondSquareFieldPartitionRe_eq_scaled (n N : ℕ) [NeZero n] (β : ℝ)
    (h : Fin (2 * n) → ℝ) :
    ringBondSquareFieldPartitionRe n N β h
      = Real.exp (-β * ringBondSquareConst n h)
        * ringFieldPartitionRe n N β (ringBondSquareLinField n h) := by
  simp only [ringBondSquareFieldPartitionRe, ringFieldPartitionRe, thermalPartitionFnS,
    thermalGibbsOpS]
  rw [ringBondSquareFieldHamiltonian_eq]
  set A := ringFieldHamiltonian n N (ringBondSquareLinField n h) with hA
  set c := ringBondSquareConst n h with hc
  have hsplit : -(β : ℂ) • (A + (c : ℂ) • (1 : ManyBodyOpS (Fin (2 * n)) N))
      = -(β : ℂ) • A + (-(β : ℂ) * (c : ℂ)) • 1 := by
    rw [smul_add, smul_smul]
  rw [hsplit]
  have hcomm : Commute (-(β : ℂ) • A)
      ((-(β : ℂ) * (c : ℂ)) • (1 : ManyBodyOpS (Fin (2 * n)) N)) :=
    (Commute.one_right A).smul_left (-(β : ℂ)) |>.smul_right (-(β : ℂ) * (c : ℂ))
  rw [Matrix.exp_add_of_commute _ _ hcomm]
  have hscalar : NormedSpace.exp ((-(β : ℂ) * (c : ℂ)) • (1 : ManyBodyOpS (Fin (2 * n)) N))
      = Complex.exp (-(β : ℂ) * (c : ℂ)) • 1 := by
    have hdiag : ((-(β : ℂ) * (c : ℂ)) • (1 : ManyBodyOpS (Fin (2 * n)) N))
        = Matrix.diagonal (fun _ => -(β : ℂ) * (c : ℂ)) := by
      ext i j; by_cases hij : i = j <;> simp [hij]
    rw [hdiag, Matrix.exp_diagonal]
    ext i j
    by_cases hij : i = j
    · simp only [hij, Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq,
        smul_eq_mul, mul_one, Pi.exp_def]
      rw [← Complex.exp_eq_exp_ℂ]
    · simp [hij, Matrix.smul_apply, Matrix.one_apply_ne hij]
  rw [hscalar, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
  have hcast : Complex.exp (-(β : ℂ) * (c : ℂ)) = ((Real.exp (-β * c) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
  rw [hcast, Complex.re_ofReal_mul]

/-- **Partition-function collapse** `Z^{BS}_β(h^const) = Z^{repo}_β(0)` (Tasaki §4.1 (4.1.49), book
p.86): at a constant field the bond-square field partition function collapses to the field-free
linear-core partition function `ringFieldPartitionRe n N β 0`.  Proved directly from the operator
collapse `ringBondSquareFieldHamiltonian_const` (PR-BS3): both partition functions are the real part
of the Gibbs trace of the same Hamiltonian `ringFieldHamiltonian n N 0`.  Holds for all `β ∈ ℝ` (the
scalar `e^{−βC} = e⁰ = 1` since `C(h^const) = 0`).  This is the finite-`β` form of Tasaki's
`E_GS(h^const) = E_GS(0,…,0)`, consumed by the uniform-field bound (PR-BS10). -/
theorem ringBondSquareFieldPartitionRe_const (n N : ℕ) [NeZero n] (β : ℝ) (c : ℝ) :
    ringBondSquareFieldPartitionRe n N β (fun _ => c) = ringFieldPartitionRe n N β 0 := by
  simp only [ringBondSquareFieldPartitionRe, ringFieldPartitionRe,
    ringBondSquareFieldHamiltonian_const]

end LatticeSystem.Quantum
