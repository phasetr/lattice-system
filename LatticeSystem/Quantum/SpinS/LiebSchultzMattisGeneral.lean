import LatticeSystem.Quantum.SpinS.LiebSchultzMattis
import LatticeSystem.Quantum.SpinS.OrderOperatorAlgebra

/-!
# Tasaki §6.2: the generalized Lieb–Schultz–Mattis variational bound (Lemma 6.4)

Lemma 6.1 (the low energy of the twisted state) generalizes far beyond the standard
antiferromagnetic Heisenberg chain: it holds for **any** short-ranged, `U(1)`-invariant chain
Hamiltonian
`Ĥ = Σ_{x=1}^{L} ĥ_x`  (eq. (6.2.23)),
where each local term `ĥ_x` acts only on sites within a fixed range `r` of `x` (with periodic
boundary conditions), is bounded `‖ĥ_x‖ ≤ h₀`, and is `U(1)`-invariant,
`(Û_θ^{(3)})† ĥ_x Û_θ^{(3)} = ĥ_x` — equivalently `[ĥ_x, Ŝ_tot^{(3)}] = 0`.

**Lemma 6.4** (eq. (6.2.24)): there is a constant `C > 0`, depending only on `S`, `r` and `h₀`, such
that for *any* ground state `Φ_GS` (uniqueness is **not** assumed) the twisted trial state has
energy `⟨Φ_LSM, Ĥ Φ_LSM⟩ / ⟨Φ_LSM, Φ_LSM⟩ − E_GS ≤ C/L`, for any `L`.

Tasaki further remarks that if `S` is a half-odd integer and the ground state is translation
invariant (`T̂ Φ_GS = e^{iα} Φ_GS`), then *the same orthogonality argument* (a generalization of
Lemma 6.2)
gives `0 ≤ E_1st − E_GS ≤ C/L`, as in Theorem 6.3 — now for a whole class of `U(1)`-invariant
short-ranged chains.  We do **not** formalize that gap consequence here: the formal Lemma 6.2
(`lsm_ground_twist_orthogonal`) is specialized to the antiferromagnetic Heisenberg chain, so
deriving it for a general `IsShortRangeU1Chain` would require a separate generalized orthogonality
lemma.

We record the locality of each `ĥ_x` through the (uninterpreted) marker predicate `IsLocalRangeR`,
the norm bound through the `L²` operator norm `manyBodyOperatorNormS`, and `U(1)`-invariance through
`Commute (ĥ_x) Ŝ_tot^{(3)}`, all bundled into `IsShortRangeU1Chain`.  Lemma 6.4 itself (the `C/L`
variational bound, eq. (6.2.24)) is the documented axiom recorded here.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §6.2, Lemma 6.4, eqs. (6.2.23)–(6.2.24), pp. 162–163.
-/

namespace LatticeSystem.Quantum

open Matrix

/-- **Locality marker** `IsLocalRangeR L N r x op`: the operator `op` acts only on the sites within
distance `r` of `x` on the ring `Fin L` (with periodic boundary conditions).  A full
local-observable framework is heavier than Lemma 6.4 needs, so the locality is recorded here as an
uninterpreted
predicate (a hypothesis constraining the chain, never asserted of arbitrary operators). -/
axiom IsLocalRangeR (L N r : ℕ) (x : Fin L) (op : ManyBodyOpS (Fin L) N) : Prop

/-- **A short-ranged `U(1)`-invariant chain** of local terms `ĥ_x` (Tasaki eq. (6.2.23) and the
assumptions below it): each `ĥ_x` is self-adjoint (`hermitian`, so `Ĥ = Σ_x ĥ_x` is a genuine
Hamiltonian), `r`-local (`range`), bounded by `h₀` in the `L²` operator norm (`norm_le`), and
`U(1)`-invariant, i.e. commutes with the total spin `Ŝ_tot^{(3)}` (`u1_comm`). -/
structure IsShortRangeU1Chain (L N r : ℕ) (h₀ : ℝ)
    (h : Fin L → ManyBodyOpS (Fin L) N) : Prop where
  /-- Each local term `ĥ_x` is self-adjoint (Hermitian), so `Σ_x ĥ_x` is a Hermitian Hamiltonian. -/
  hermitian : ∀ x, (h x).IsHermitian
  /-- Each local term `ĥ_x` acts only on sites within range `r` of `x`. -/
  range : ∀ x, IsLocalRangeR L N r x (h x)
  /-- Each local term is bounded in the `L²` operator norm by `h₀`. -/
  norm_le : ∀ x, manyBodyOperatorNormS (h x) ≤ h₀
  /-- Each local term is `U(1)`-invariant: it commutes with the total spin `Ŝ_tot^{(3)}`. -/
  u1_comm : ∀ x, Commute (h x) (totalSpinSOp3 (Fin L) N)

/-- **Tasaki Lemma 6.4 (generalized LSM variational bound), AXIOM.**  For the class of short-ranged
`U(1)`-invariant chain Hamiltonians `Ĥ = Σ_x ĥ_x` (`IsShortRangeU1Chain`, range `r`, bound `h₀`,
spin `S = N/2`), there is a constant `C > 0` — depending only on `N`, `r` and `h₀` — such that for
**any** ground state `Φ_GS` (a nonzero eigenvector at the minimal energy `E_GS`; uniqueness is *not*
assumed) the Lieb–Schultz–Mattis trial state has energy bounded by `C/L` above the ground state
(eq. (6.2.24)):
`⟨Φ_LSM, Ĥ Φ_LSM⟩ / ⟨Φ_LSM, Φ_LSM⟩ − E_GS ≤ C/L`, for any `L`.

The constant `C` is uniform over the volume `L`, the local terms `ĥ`, and the ground state — it
depends only on `S`, `r`, `h₀`.  Tasaki remarks that for half-odd-integer `S` with a
translation-invariant ground state a generalized orthogonality argument then yields
`0 ≤ E_1st − E_GS ≤ C/L` (as in Theorem 6.3); that gap consequence is *not* formalized here (the
formal Lemma 6.2 is Heisenberg-chain-specific).  Recorded as a documented axiom. -/
axiom tasaki_lemma_6_4_general_trial_energy_bound (N r : ℕ) (h₀ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {L : ℕ} (h : Fin L → ManyBodyOpS (Fin L) N)
      (Φ_GS : (Fin L → Fin (N + 1)) → ℂ) (E_GS : ℝ), 0 < L →
      IsShortRangeU1Chain L N r h₀ h →
      (∑ x : Fin L, h x).mulVec Φ_GS = (E_GS : ℂ) • Φ_GS → Φ_GS ≠ 0 →
      IsGroundEnergy (∑ x : Fin L, h x) E_GS →
      expectationRatioRe (∑ x : Fin L, h x) (lsmTrialState L N Φ_GS) - E_GS ≤ C / (L : ℝ)

end LatticeSystem.Quantum
