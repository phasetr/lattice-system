import LatticeSystem.Quantum.SpinS.ShastryNoSSB

/-!
# Tasaki §6.1: the antiferromagnetic Heisenberg chain and the Haldane "conjecture"

Chapter 6 (Part II) studies the ground states of the **one-dimensional antiferromagnetic Heisenberg
chain** with spin `S = 1/2, 1, 3/2, …` on `Λ_L = {1, …, L}` (`L` even), with periodic boundary
conditions and the Hamiltonian (eq. (6.1.1))
`Ĥ = Σ_{x} Ŝ_x · Ŝ_{x+1}`  (`Ŝ_{L+1} = Ŝ_1`).
By the Marshall–Lieb–Mattis theorem (Theorem 2.2) the ground state is unique with `S_tot = 0`.

Haldane argued (1983) that the low-energy physics depends *qualitatively* on whether the spin `S`
is a **half-odd integer** or an **integer** — a claim so unexpected it was called the **Haldane
conjecture**:

* **half-odd-integer `S`** (`S = 1/2, 3/2, …`, i.e. `N = 2S` odd): the chain is *gapless*
  (critical / massless) — the energy gap above the ground state scales as `O(1/L)` and vanishes as
  `L↑∞`
  (properties (HOI1)–(HOI3): unique ground state, no gap, power-law correlation decay);
* **integer `S`** (`S = 1, 2, …`, i.e. `N = 2S` even, `N ≥ 2`): the chain is *gapped* — there is a
  nonvanishing, essentially `L`-independent **Haldane gap** `ΔE_H > 0` above the ground state, and
  the correlations decay exponentially (properties (I1)–(I3)).

This is a **conjecture** — believed, with much supporting evidence, but not proved in general.
Following the project policy, conjectures are recorded as `def … : Prop` statements that are **never
asserted true** (no `axiom`/`theorem` derives them).  We formalize here the *spectral-gap* dichotomy
of the Haldane conjecture; the correlation-decay clauses (HOI3)/(I3) are deferred to a later module
(they require the additional design of the two-point correlation function and its asymptotics).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §6.1, eqs. (6.1.1)–(6.1.3), pp. 153–157; F. D. M. Haldane, Phys. Lett. **93A**, 464 (1983)
and Phys. Rev. Lett. **50**, 1153 (1983).
-/

namespace LatticeSystem.Quantum

open Matrix

/-- The **one-dimensional antiferromagnetic Heisenberg chain Hamiltonian** `Ĥ = Σ_x Ŝ_x · Ŝ_{x+1}`
on the ring `Fin L` with periodic boundary conditions (eq. (6.1.1)), for spin `S = N/2`.  Built from
the periodic nearest-neighbor `ringCoupling`. -/
noncomputable def afmHeisenbergChainHamiltonianS (L N : ℕ) : ManyBodyOpS (Fin L) N :=
  heisenbergHamiltonianS (ringCoupling L) N

/-- The **real spectrum** of a chain operator `H`: the set of real numbers `E` that are eigenvalues
of `H` (witnessed by a nonzero eigenvector `Φ` with `H Φ = E Φ`).  For the Hermitian Heisenberg
Hamiltonian all eigenvalues are real, so this captures the full spectrum. -/
def realSpectrum {L N : ℕ} (H : ManyBodyOpS (Fin L) N) : Set ℝ :=
  {E : ℝ | ∃ Φ : (Fin L → Fin (N + 1)) → ℂ, Φ ≠ 0 ∧ H.mulVec Φ = (E : ℂ) • Φ}

/-- `IsGroundEnergy H E₀`: `E₀` is the **ground-state energy** of `H`, i.e. an eigenvalue that is
minimal over the whole real spectrum. -/
def IsGroundEnergy {L N : ℕ} (H : ManyBodyOpS (Fin L) N) (E₀ : ℝ) : Prop :=
  E₀ ∈ realSpectrum H ∧ ∀ E ∈ realSpectrum H, E₀ ≤ E

/-- `IsPositiveSpectralGap H gap`: `H` has a **positive spectral gap** equal to `gap`, i.e. there is
a ground energy `E₀` and a *first excited* eigenvalue `E₁` (the smallest eigenvalue strictly above
`E₀`) with `gap = E₁ − E₀ > 0`. -/
def IsPositiveSpectralGap {L N : ℕ} (H : ManyBodyOpS (Fin L) N) (gap : ℝ) : Prop :=
  ∃ E₀ E₁ : ℝ, IsGroundEnergy H E₀ ∧ E₁ ∈ realSpectrum H ∧ E₀ < E₁ ∧ gap = E₁ - E₀ ∧
    ∀ E ∈ realSpectrum H, E₀ < E → E₁ ≤ E

/-- `RingLengthEven L`: the chain length `L` is **even and positive** (Tasaki takes `L` even). -/
def RingLengthEven (L : ℕ) : Prop := Even L ∧ 0 < L

/-- `GapOfChain L N gap`: `gap` is the spectral gap of the spin-`S` antiferromagnetic Heisenberg
chain of length `L` (`S = N/2`). -/
def GapOfChain (L N : ℕ) (gap : ℝ) : Prop :=
  IsPositiveSpectralGap (afmHeisenbergChainHamiltonianS L N) gap

/-- The chain is **gapless** (`IsGapless N`): the spectral gap of the spin-`S` chain vanishes as
`L↑∞` — for every `ε > 0` all sufficiently large even chains have gap `< ε` (the `O(1/L)` behavior
of the half-odd-integer case). -/
def IsGapless (N : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → RingLengthEven L →
    ∃ gap : ℝ, GapOfChain L N gap ∧ gap < ε

/-- The chain is **gapped** (`IsGapped N`): there is a uniform `Δ > 0` (the Haldane gap) below which
the spectral gap of the spin-`S` chain never falls for large even chains. -/
def IsGapped (N : ℕ) : Prop :=
  ∃ Δ : ℝ, 0 < Δ ∧ ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → RingLengthEven L →
    ∃ gap : ℝ, GapOfChain L N gap ∧ Δ ≤ gap

/-- **The Haldane "conjecture"** (Tasaki §6.1), as a `Prop` statement (the spectral-gap dichotomy).
For the spin-`S` antiferromagnetic Heisenberg chain (`S = N/2`): if `S` is a **half-odd integer**
(`N` odd) the chain is *gapless*, while if `S` is a positive **integer** (`N` even, `N ≥ 2`) the
chain is *gapped* (has a nonvanishing Haldane gap).

This is a genuine conjecture: it is recorded as a `def … : Prop` and is **never asserted true** (no
`axiom`/`theorem` derives it).  Tasaki presents it as a conjecture supported by exact solutions
(`S = 1/2`), field theory, and numerics; a general proof is not known. -/
def haldaneConjecture (N : ℕ) : Prop :=
  (Odd N → IsGapless N) ∧ (2 ≤ N → Even N → IsGapped N)

end LatticeSystem.Quantum
