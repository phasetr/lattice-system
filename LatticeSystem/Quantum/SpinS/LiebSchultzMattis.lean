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

/-- **Tasaki Lemma 6.2 (the twisted state is orthogonal to the ground state), AXIOM.**  For
**half-odd-integer** spin `S = N/2` (`N` odd) and the *unique* ground state `Φ_GS` of the chain (in
the `Ŝ_tot^{(3)} = 0` sector, by Marshall–Lieb–Mattis), the trial state is orthogonal to the ground
state, `⟨Φ_GS, Φ_LSM⟩ = 0` (eq. (6.2.18)).  This uses translation invariance: the translation
operator acts on the unique ground state by a phase, and for half-odd-integer `S` the twist
multiplies that phase by `−1`, forcing the overlap to vanish.  Recorded as a documented axiom;
`huniq` expresses
that every ground-energy eigenvector is a scalar multiple of `Φ_GS` (uniqueness). -/
axiom lsm_ground_twist_orthogonal (L N : ℕ) (hL : 0 < L) (hNodd : Odd N)
    (Φ_GS : (Fin L → Fin (N + 1)) → ℂ) (E_GS : ℝ) (hne : Φ_GS ≠ 0)
    (heig : (afmHeisenbergChainHamiltonianS L N).mulVec Φ_GS = (E_GS : ℂ) • Φ_GS)
    (hmin : IsGroundEnergy (afmHeisenbergChainHamiltonianS L N) E_GS)
    (huniq : ∀ Ψ : (Fin L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
      (afmHeisenbergChainHamiltonianS L N).mulVec Ψ = (E_GS : ℂ) • Ψ → ∃ c : ℂ, Ψ = c • Φ_GS)
    (hstot : (totalSpinSOp3 (Fin L) N).mulVec Φ_GS = 0) :
    star Φ_GS ⬝ᵥ lsmTrialState L N Φ_GS = 0

/-- **Tasaki Theorem 6.3 (Lieb–Schultz–Mattis, Affleck–Lieb theorem), AXIOM.**  For the
antiferromagnetic Heisenberg chain (eq. (6.1.1)) of **half-odd-integer** spin `S = N/2` (`N` odd) on
an even ring of length `L`, the first excited energy lies just above the ground energy with a gap of
order `1/L` (eq. (6.2.19)):
`0 < E_1st − E_GS ≤ 8π²S²/L`.

Phrased via the spectral-gap predicate `IsPositiveSpectralGap` (§6.1), this says the chain has a
positive spectral gap that is bounded above by `8π²S²/L` — so a half-odd-integer chain can never
have *both* a unique ground state and a nonvanishing (`L`-independent) gap.  This is the rigorous
half of the Haldane conjecture (`IsGapless` for half-odd-integer `S`).  Obtained by combining
Lemma 6.1 (low trial energy) and Lemma 6.2 (orthogonality to the ground state); recorded as a
documented axiom. -/
axiom lieb_schultz_mattis_affleck_lieb (L N : ℕ) (hL : RingLengthEven L) (hNodd : Odd N) :
    ∃ gap : ℝ, IsPositiveSpectralGap (afmHeisenbergChainHamiltonianS L N) gap ∧
      gap ≤ 8 * Real.pi ^ 2 * ((N : ℝ) / 2) ^ 2 / (L : ℝ)

end LatticeSystem.Quantum
