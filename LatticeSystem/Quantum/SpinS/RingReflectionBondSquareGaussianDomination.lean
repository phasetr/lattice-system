/-
Chessboard Gaussian-domination capstone for the bond-square field partition function
`Z^{BS}_β(h)^{2n} ≤ Π_j Z^{BS}_β(fun _ => h j)`
(Tasaki §4.1 Theorem 4.2, reflection-positivity bond-square layer, PR-BS9).

The one reflection step (PR-BS8b, `ringBondSquareFieldPartitionRe_reflection_step`)
`Z^{BS}_β(g)² ≤ Z^{BS}_β(reflectLeft n g)·Z^{BS}_β(reflectRight n g)` is the finite-β
partition-function form of Tasaki's bond-square reflection bound (4.1.51), stated on the **sign-free
classical mirrors** `reflectLeft`/`reflectRight`.  Here the classical cyclic averaging inequality
`LatticeSystem.Math.reflectionPositivity_averaging` (Tasaki Lemma 4.5, (4.1.55)–(4.1.57), pp. 87–88)
is applied **directly** to the plain functional `F g = −log Z^{BS}_β(g)` — no staggered relabel
bridge, since PR-BS8b already delivers the reflection step on the classical mirrors.  The two
hypotheses come from the bond-square side:

* cyclicity (4.1.55) from `ringBondSquareFieldPartitionRe_reindexCyclic` (PR-BS9), itself the
  scalar-shift reduction of the linear-core translation and spin-flip invariances;
* the reflection bound (4.1.56) from the PR-BS8b one reflection step and the strict positivity
  `ringBondSquareFieldPartitionRe_pos`, converted to `−log` form by `log`-monotonicity.

Exponentiating the resulting `(1/2n) Σ_j (−log Z^{BS}_β(fun _ => h j)) ≤ −log Z^{BS}_β(h)` gives the
`2n`-fold chessboard product bound.  PR-BS10 collapses each constant-field factor
`Z^{BS}_β(fun _ => h j)` to `Z^{repo}_β(0) = Z^{BS}_β(0)`
(`ringBondSquareFieldPartitionRe_const`), yielding Tasaki's uniform-field bound
`Z^{BS}_β(h) ≤ Z^{BS}_β(0)` (4.1.49)/(4.1.52).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, reflection bound (4.1.51) and uniform-field bound (4.1.49)/(4.1.52), pp. 85–86;
chessboard estimate Lemma 4.5, (4.1.55)–(4.1.57), pp. 87–88; DLS 1978; FILS, Comm. Math. Phys. 62
(1978) 1–34.  See
`.self-local/docs/math-tasaki-4-1-51-bond-square-physical-field-reflection-step.md` §5
(issue #4777).
-/
import LatticeSystem.Quantum.SpinS.RingReflectionBondSquarePhysId
import LatticeSystem.Quantum.SpinS.RingReflectionBondSquareFieldPartition
import LatticeSystem.Math.ReflectionPositivityAveraging
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace LatticeSystem.Quantum

open LatticeSystem.Math

variable {n N : ℕ}

/-- **Bond-square chessboard Gaussian-domination capstone.**  For the bond-square field partition
function `Z^{BS}_β(h) = ringBondSquareFieldPartitionRe n N β h` on the even ring `Fin (2n)`
(`n ≥ 1`, `β ≥ 0`), `Z^{BS}_β(h)^{2n} ≤ Π_j Z^{BS}_β(fun _ => h j)`.  This is the finite-β
chessboard bound obtained from Tasaki's bond-square reflection bound (4.1.51) by the cyclic
averaging inequality (Lemma 4.5, (4.1.55)–(4.1.57), pp. 87–88): applying
`reflectionPositivity_averaging` to the plain functional `F g = −log Z^{BS}_β(g)` — with cyclicity
from
`ringBondSquareFieldPartitionRe_reindexCyclic` and the reflection bound from the PR-BS8b one
reflection step `ringBondSquareFieldPartitionRe_reflection_step` and the strict positivity
`ringBondSquareFieldPartitionRe_pos` — gives `(1/2n) Σ_j (−log Z^{BS}_β(fun _ => h j)) ≤
−log Z^{BS}_β(h)`, which exponentiates to the product bound.  PR-BS10 collapses each constant-field
factor to `Z^{BS}_β(0)` to reach the uniform-field bound `Z^{BS}_β(h) ≤ Z^{BS}_β(0)`
(Tasaki (4.1.49)/(4.1.52), pp. 85–86). -/
theorem ringBondSquareFieldPartition_gaussianDomination (G : AxisTwoPiRotS N) (n : ℕ) (hn : 1 ≤ n)
    {β : ℝ} (hβ : 0 ≤ β) (h : Fin (2 * n) → ℝ) :
    ringBondSquareFieldPartitionRe n N β h ^ (2 * n)
      ≤ ∏ j : Fin (2 * n), ringBondSquareFieldPartitionRe n N β (fun _ => h j) := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : NeZero (2 * n) := ⟨by omega⟩
  set F : (Fin (2 * n) → ℝ) → ℝ :=
    fun g => - Real.log (ringBondSquareFieldPartitionRe n N β g) with hFdef
  -- Cyclicity (4.1.55): cyclicity of the bond-square partition function.
  have hcyc : ∀ f, F (reindexCyclic n f) = F f := by
    intro f
    simp only [hFdef]
    exact congrArg (fun t => - Real.log t)
      (ringBondSquareFieldPartitionRe_reindexCyclic G n β f)
  -- Reflection bound (4.1.56): PR-BS8b reflection step + strict positivity.
  have hrefl : ∀ f, (F (reflectLeft n f) + F (reflectRight n f)) / 2 ≤ F f := by
    intro f
    simp only [hFdef]
    have hp := ringBondSquareFieldPartitionRe_pos n N β f
    have hpL := ringBondSquareFieldPartitionRe_pos n N β (reflectLeft n f)
    have hpR := ringBondSquareFieldPartitionRe_pos n N β (reflectRight n f)
    have hstep := ringBondSquareFieldPartitionRe_reflection_step G n hβ f
    have hlog := (Real.log_le_log_iff (pow_pos hp 2) (mul_pos hpL hpR)).mpr hstep
    rw [Real.log_pow, Real.log_mul (ne_of_gt hpL) (ne_of_gt hpR)] at hlog
    push_cast at hlog
    linarith
  -- Apply the classical averaging inequality directly at `f = h`.
  have key := reflectionPositivity_averaging n hn F hcyc hrefl h
  simp only [hFdef] at key
  -- Strict positivity of the base and the constant-field partition functions.
  have ha : 0 < ringBondSquareFieldPartitionRe n N β h :=
    ringBondSquareFieldPartitionRe_pos n N β h
  have hw : ∀ j : Fin (2 * n), 0 < ringBondSquareFieldPartitionRe n N β (fun _ => h j) :=
    fun j => ringBondSquareFieldPartitionRe_pos n N β _
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have h2n : (0 : ℝ) < 2 * (n : ℝ) := by linarith
  -- Turn the averaged `−log` inequality into `2n · log Z^{BS}(h) ≤ Σ_j log Z^{BS}(fun _ => h j)`.
  rw [div_le_iff₀ h2n, Finset.sum_neg_distrib] at key
  have hlogpow : Real.log (ringBondSquareFieldPartitionRe n N β h ^ (2 * n))
      = 2 * (n : ℝ) * Real.log (ringBondSquareFieldPartitionRe n N β h) := by
    rw [Real.log_pow]; push_cast; ring
  have hlogprod : Real.log (∏ j : Fin (2 * n),
        ringBondSquareFieldPartitionRe n N β (fun _ => h j))
      = ∑ j : Fin (2 * n),
          Real.log (ringBondSquareFieldPartitionRe n N β (fun _ => h j)) :=
    Real.log_prod (fun j _ => (hw j).ne')
  have hle : Real.log (ringBondSquareFieldPartitionRe n N β h ^ (2 * n))
      ≤ Real.log (∏ j : Fin (2 * n),
          ringBondSquareFieldPartitionRe n N β (fun _ => h j)) := by
    rw [hlogpow, hlogprod]
    nlinarith [key]
  have hXpos : 0 < ringBondSquareFieldPartitionRe n N β h ^ (2 * n) := pow_pos ha _
  have hYpos : 0 < ∏ j : Fin (2 * n),
      ringBondSquareFieldPartitionRe n N β (fun _ => h j) :=
    Finset.prod_pos (fun j _ => hw j)
  exact (Real.log_le_log_iff hXpos hYpos).mp hle

end LatticeSystem.Quantum
