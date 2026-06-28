import LatticeSystem.Quantum.SpinS.HaldaneConjecture
import LatticeSystem.Quantum.SpinS.AndersonTower
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Tasaki §6.2: the Lieb–Schultz–Mattis theorem (Theorem 6.3)

For the one-dimensional antiferromagnetic Heisenberg chain (eq. (6.1.1)) with a **half-odd-integer**
spin `S`, the Lieb–Schultz–Mattis theorem (extended by Affleck and Lieb to general half-odd-integer
`S`) shows that one can always construct a low-lying excited state with excitation energy `O(1/L)` —
so the model can never have a unique ground state *and* a spectral gap.

The construction uses the **twist operator** (eq. (6.2.2)), a position-dependent `U(1)` rotation
whose angle increases slowly along the chain,
`Û_LSM = exp[−i Σ_x θ_x Ŝ_x^{(3)}]`,  `θ_x = (2π/L) x`  (eq. (6.2.3)),
applied to the (unique, `Ŝ_tot^{(3)} = 0`) ground state to give the **trial state**
`|Φ_LSM⟩ = Û_LSM |Φ_GS⟩` (eq. (6.2.4)).  Two lemmas drive the proof:

* **Lemma 6.1** (eq. (6.2.5)): for any `S` and `L`, the trial state has low energy
  `⟨Φ_LSM| Ĥ |Φ_LSM⟩ − E_GS ≤ 8π²S²/L`;
* **Lemma 6.2** (eq. (6.2.18)): for half-odd-integer `S`, the twist flips the sign under the
  translation eigenvalue, so `⟨Φ_GS|Φ_LSM⟩ = 0` — the trial state is orthogonal to the ground state,
  hence a genuine *excited* state.

Combining them gives **Theorem 6.3** (eq. (6.2.19)): for half-odd-integer `S`,
`0 < E_1st − E_GS ≤ 8π²S²/L`.

These are deep results about the spectrum of the finite-volume chain; following the project policy
we record Lemma 6.1, Lemma 6.2 and Theorem 6.3 as faithful, sound **documented axioms** (the twist
operator and trial state are *defined* here).  Theorem 6.3 is phrased through the spectral-gap
predicate `IsPositiveSpectralGap` of §6.1, so it directly upper-bounds the Haldane-conjecture gap by
`8π²S²/L` in the half-odd-integer case.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §6.2, Lemma 6.1, Lemma 6.2, Theorem 6.3, eqs. (6.2.1)–(6.2.19), pp. 158–162; E. Lieb,
T. Schultz, D. Mattis, Ann. Phys. **16**, 407 (1961); I. Affleck, E. Lieb, Lett. Math. Phys. **12**,
57 (1986).
-/

namespace LatticeSystem.Quantum

open Matrix

/-- The **Lieb–Schultz–Mattis twist operator** `Û_LSM = exp[−i Σ_x θ_x Ŝ_x^{(3)}]` (eq. (6.2.2)) on
the spin-`S` chain `Fin L`, with the slowly varying rotation angle `θ_x = (2π/L) x` (eq. (6.2.3);
the site index `x` runs over `1, …, L`, so `θ_L = 2π ≡ 0`).  It is a `U(1)` rotation whose angle
winds once around the chain. -/
noncomputable def lsmTwistOperator (L N : ℕ) : ManyBodyOpS (Fin L) N :=
  NormedSpace.exp (-Complex.I •
    ∑ x : Fin L, (((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ) : ℝ) : ℂ) • spinSSiteOp3 x N)

/-- The **Lieb–Schultz–Mattis trial state** `|Φ_LSM⟩ = Û_LSM |Φ_GS⟩` (eq. (6.2.4)): the ground state
twisted by `Û_LSM`.  By the constant-rotation invariance of the ground state it is close to `|Φ_GS⟩`
but carries a wavelength-`L` modulation, hence a very low excitation energy. -/
noncomputable def lsmTrialState (L N : ℕ) (Φ : (Fin L → Fin (N + 1)) → ℂ) :
    (Fin L → Fin (N + 1)) → ℂ :=
  (lsmTwistOperator L N).mulVec Φ

-- **Tasaki Lemma 6.1 (the twisted state has low energy)** is now a proved theorem
-- `lsm_energy_bound` in `LatticeSystem.Quantum.SpinS.LiebSchultzMattisProof` (the former axiom
-- here is discharged); `⟨Φ_LSM, Ĥ Φ_LSM⟩ / ⟨Φ_LSM, Φ_LSM⟩ − E_GS ≤ 8π²S²/L` (eq. (6.2.5)).

-- **Tasaki Lemma 6.2 (the twisted state is orthogonal to the ground state)** is now a proved
-- theorem `lsm_ground_twist_orthogonal` in
-- `LatticeSystem.Quantum.SpinS.LiebSchultzMattisOrthogonality` (the former axiom here is
-- discharged); `⟨Φ_GS, Φ_LSM⟩ = 0` for half-odd-integer `S` (eq. (6.2.18)).

-- **Tasaki Theorem 6.3 (Lieb–Schultz–Mattis, Affleck–Lieb theorem)** is now a proved theorem
-- `lieb_schultz_mattis_affleck_lieb` in `LatticeSystem.Quantum.SpinS.LiebSchultzMattisRingGap`
-- (the former axiom here is discharged): for the half-odd-integer antiferromagnetic Heisenberg
-- ring of even length `L` there is a positive spectral gap `≤ 8π²S²/L` (eq. (6.2.19)) — the
-- rigorous half of the Haldane conjecture.  Obtained by combining ground-state uniqueness
-- (connected-graph MLM), Lemma 6.1 (low trial energy), Lemma 6.2 (orthogonality), and the
-- Courant–Fischer second eigenvalue.

end LatticeSystem.Quantum
