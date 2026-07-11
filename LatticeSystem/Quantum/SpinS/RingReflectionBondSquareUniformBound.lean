/-
Uniform-field bound for the bond-square field partition function
`Z^{BS}_β(h) ≤ Z^{BS}_β(0)`
(Tasaki §4.1 Theorem 4.2, reflection-positivity bond-square layer, PR-BS10).

This is the terminal capstone of the bond-square reflection-positivity arc: a purely algebraic glue
on top of the merged chessboard Gaussian-domination bound (PR-BS9,
`ringBondSquareFieldPartition_gaussianDomination`) and the constant-field collapse (PR-BS3,
`ringBondSquareFieldPartitionRe_const`).  The chessboard bound gives
`Z^{BS}_β(h)^{2n} ≤ Π_j Z^{BS}_β(fun _ => h j)`; each constant-field factor collapses **exactly**
(no `e^{−βC} ≤ 1` estimate is needed — the constant field cancels at the operator level via
`ringBondSquareFieldHamiltonian_const`) to `Z^{repo}_β(0) = Z^{BS}_β(0)`, so the product is
`Z^{BS}_β(0)^{2n}` and the `2n`-th root monotonicity `le_of_pow_le_pow_left₀` yields
`Z^{BS}_β(h) ≤ Z^{BS}_β(0)`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, uniform-field bound (4.1.49)/(4.1.52), pp. 85–86 (chessboard estimate Lemma 4.5,
(4.1.55)–(4.1.57), pp. 87–88; DLS 1978; FILS, Comm. Math. Phys. 62 (1978) 1–34).  See
`.self-local/reports/design-thm-4-2-bond-square-BS10-uniform-bound.md` (issue #4777).
-/
import LatticeSystem.Quantum.SpinS.RingReflectionBondSquareGaussianDomination

namespace LatticeSystem.Quantum

variable {N : ℕ}

/-- **Bond-square uniform-field bound.**  For the bond-square field partition function
`Z^{BS}_β(h) = ringBondSquareFieldPartitionRe n N β h` on the even ring `Fin (2n)` (`n ≥ 1`,
`β ≥ 0`), `Z^{BS}_β(h) ≤ Z^{BS}_β(0)` (Tasaki §4.1 uniform-field bound (4.1.49)/(4.1.52),
pp. 85–86).
Purely algebraic glue over the chessboard Gaussian-domination bound
`ringBondSquareFieldPartition_gaussianDomination` (PR-BS9) `Z^{BS}_β(h)^{2n} ≤
Π_j Z^{BS}_β(fun _ => h j)`: each constant-field factor collapses **exactly** (not via an
`e^{−βC} ≤ 1` estimate — the constant field cancels at the operator level) to `Z^{BS}_β(0)` by
`ringBondSquareFieldPartitionRe_const` (PR-BS3), so `Π_j = Z^{BS}_β(0)^{2n}`; the `2n`-th root
monotonicity `le_of_pow_le_pow_left₀` — with positivity from `ringBondSquareFieldPartitionRe_pos` —
then gives the bound. -/
theorem ringBondSquareFieldPartitionRe_uniform_bound (G : AxisTwoPiRotS N) (n : ℕ) (hn : 1 ≤ n)
    {β : ℝ} (hβ : 0 ≤ β) (h : Fin (2 * n) → ℝ) :
    ringBondSquareFieldPartitionRe n N β h ≤ ringBondSquareFieldPartitionRe n N β 0 := by
  haveI : NeZero n := ⟨by omega⟩
  have hcb := ringBondSquareFieldPartition_gaussianDomination G n hn hβ h
  -- Each constant-field factor collapses to the field-free partition function (PR-BS3), so the
  -- chessboard product equals `Z^{repo}_β(0)^{2n}`.
  have hprod : (∏ j : Fin (2 * n), ringBondSquareFieldPartitionRe n N β (fun _ => h j))
      = ringFieldPartitionRe n N β 0 ^ (2 * n) := by
    rw [Finset.prod_congr rfl (fun j _ => ringBondSquareFieldPartitionRe_const n N β (h j)),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- Field-free identity `Z^{BS}_β(0) = Z^{repo}_β(0)` (PR-BS3 at `c = 0`; `0` defeq `fun _ => 0`).
  have h0 : ringBondSquareFieldPartitionRe n N β 0 = ringFieldPartitionRe n N β 0 :=
    ringBondSquareFieldPartitionRe_const n N β 0
  rw [hprod] at hcb
  rw [h0]
  exact le_of_pow_le_pow_left₀ (by omega) (ringFieldPartitionRe_pos n N β 0).le hcb

end LatticeSystem.Quantum
