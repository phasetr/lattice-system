import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardFerromagnetismStructure
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Tasaki §11.1.1: impossibility of ferromagnetism at low densities (Theorem 11.4)

For a translation-invariant Hubbard model whose single-particle band satisfies the dimensional
density-of-states bound (11.1.8) in dimension `d > 2`, there is a density threshold `ρ₁ > 0` below
which the model is not ferromagnetic, for *any* `U ≥ 0` (Pieri–Daul–Baeriswyl–Dzierzawa–Fazekas).

The dimension enters only through the exponent `2/d` of the band condition (11.1.8) — no explicit
`d`-dimensional lattice geometry is needed — so the statement is rendered on the project's
`Fin (N+1)`-site Hubbard model with `d > 2` kept as an explicit hypothesis (the conclusion is false
in `d = 1`, so dropping `d > 2` would be unsound).  Recorded as a documented axiom: the proof
(Tasaki's Roth/Gutzwiller variational state and the analytic estimate from (11.1.8)) is deferred.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §11.1.1, Theorem 11.4, eqs. (11.1.8)–(11.1.10), pp. 379–380.
-/

namespace LatticeSystem.Fermion

open Matrix

variable {N : ℕ} (t : Fin (N + 1) → Fin (N + 1) → ℂ)

/-- **The dimensional band condition (Tasaki eq. (11.1.8))** on the ascending single-particle
energies `ε_1 ≤ ε_2 ≤ ⋯` (`ε 0 = ε_1`, `ε n = ε_{n+1}`): there are positive constants `c, ρ₀` and a
cutoff `n₀` such that for the `n`-th level (`n ≥ n₀`, `n/|Λ| ≤ ρ₀`)
`ε_n − ε_1 ≥ c·((n − n₀)/|Λ|)^{2/d}`.  The right-hand side is the `n`-dependence of the levels of a
single particle in `d` dimensions. -/
def hubbardBandCondition (ε : Fin (N + 1) → ℝ) (c ρ₀ : ℝ) (n₀ d : ℕ) : Prop :=
  ∀ n : Fin (N + 1), n₀ ≤ n.val + 1 → ((n.val + 1 : ℝ)) / (N + 1) ≤ ρ₀ →
    c * (((n.val + 1 - n₀ : ℝ)) / (N + 1)) ^ ((2 : ℝ) / (d : ℝ)) ≤ ε n - ε 0

/-- **Tasaki Theorem 11.4 (impossibility of ferromagnetism at low densities), AXIOM.**  Fix `d > 2`
and positive band constants `c, ρ₀, n₀`.  Then there is a density threshold `ρ₁ > 0`, *uniform in
the system size*, such that for any Hermitian, translation-invariant hopping `t` whose ascending
single-particle spectrum `ε` satisfies the band condition (11.1.8), and any electron number `Ne`
with density `Ne/|Λ| ≤ ρ₁` and any `U ≥ 0`, the ground states at filling `Ne` are **not** all
maximal-spin: some ground state has `S_tot < S_max`.

As in Theorem 11.3 the conclusion negates the *pinned* ground-state max-spin property over the real
ground eigenspace `hubbardEigenspaceAt … E₀ Ne` (`E₀` nonempty `hne` and minimal `hmin`), so the
impossibility statement is sound.  Translation invariance is required genuinely (the symmetry `σ`
acts transitively, ruling out the trivial `σ = id`), and the filling is nontrivial (`2 ≤ Ne`, the
zero- and one-electron sectors are trivially maximal-spin).  Tasaki's proof uses the Roth/Gutzwiller
projected trial state and
the analytic estimate furnished by (11.1.8); it is recorded here as a documented axiom (to be
discharged), matching the policy for the other deferred Chapter 11 results. -/
axiom hubbard_theorem_11_4 (c ρ₀ : ℝ) (hc : 0 < c) (hρ₀ : 0 < ρ₀) (n₀ d : ℕ) (hd : 2 < d) :
    ∃ ρ₁ : ℝ, 0 < ρ₁ ∧
      ∀ (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (ht : Matrix.IsHermitian t)
        (σ : Equiv.Perm (Fin (N + 1))) (_htrans : ∀ i j, t (σ i) (σ j) = t i j)
        (_htransitive : ∀ i j : Fin (N + 1), ∃ k : ℕ, (σ ^ k) i = j)
        (ε : Fin (N + 1) → ℝ) (_hmono : Monotone ε)
        (_hspec : Finset.univ.val.map ε = Finset.univ.val.map ht.eigenvalues)
        (_hband : hubbardBandCondition ε c ρ₀ n₀ d)
        (Ne : ℕ) (_hNe2 : 2 ≤ Ne) (_hNe : (Ne : ℝ) / (N + 1) ≤ ρ₁)
        (U : ℝ) (_hU : 0 ≤ U) (E₀ : ℂ)
        (_hne : hubbardEigenspaceAt t (U : ℂ) E₀ Ne ≠ ⊥)
        (_hmin : ∀ E : ℂ, hubbardEigenspaceAt t (U : ℂ) E Ne ≠ ⊥ → E₀.re ≤ E.re),
        ¬ ∀ v ∈ hubbardEigenspaceAt t (U : ℂ) E₀ Ne,
          (fermionTotalSpinSquared N).mulVec v
            = (((Ne : ℂ) / 2) * ((Ne : ℂ) / 2 + 1)) • v

end LatticeSystem.Fermion
