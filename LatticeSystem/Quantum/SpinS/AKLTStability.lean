import LatticeSystem.Quantum.SpinS.AKLT
import LatticeSystem.Quantum.SpinS.LiebSchultzMattisGeneral

/-!
# Tasaki §7.1.3: stability of the AKLT gap under local perturbations (Theorem 7.3, Yarotsky)

The unique gapped ground state of the AKLT model (Theorem 7.1) is *stable* against small local
perturbations.  Let
`Ĥ_ε = Ĥ_AKLT + ε Σ_x v̂_x`  (eq. (7.1.4)),
where `v̂_o` is an arbitrary self-adjoint operator acting only on a finite number of spins (range
`r`)
and `v̂_x = T̂^x v̂_o (T̂†)^x` is its translate.  Yarotsky [91] proved, by a sophisticated cluster
expansion:

**Theorem 7.3**: for `|ε|` sufficiently small there is a positive constant `ΔE_ε > 0`, independent
of `L`, such that for any `L` the ground state of `Ĥ_ε` is **unique**, the energy gap above it is at
least `ΔE_ε`, and the ground-state **connected** correlation functions **decay exponentially**.  (We
state the connected/truncated correlation, since a symmetry-breaking perturbation can give nonzero
one-point functions; and we take `L ≥ 3` to exclude the degenerate small rings.)

We model the perturbation through `IsAKLTPerturbation` (a self-adjoint, range-`r`, uniformly bounded
family whose translation covariance — `v̂_x = T̂^x v̂_o (T̂†)^x` — is recorded by the uninterpreted
marker `IsTranslationCovariant`; dropping it would over-strengthen the statement, since arbitrary
bounded range-`r` families need not be translates of one local operator).  The thresholds `ε₀`,
`ΔE`,
`C`, `ξ` are quantified outside `∀ L`, so they are genuinely `L`-independent.  This deep stability
result is recorded as a documented axiom.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.1.3, Theorem 7.3, eq. (7.1.4), p. 180; D. A. Yarotsky, Commun. Math. Phys. **261**, 799
(2006).
-/

namespace LatticeSystem.Quantum

open Matrix

/-- **Translation-covariance marker** `IsTranslationCovariant L v`: the local-perturbation family
`v_x` consists of the translates `v̂_x = T̂^x v̂_o (T̂†)^x` of a single local operator `v̂_o` (eq.
(7.1.4)).  A faithful definition needs the chain translation operator; it is kept as an
uninterpreted
predicate so Theorem 7.3 applies only to genuine translation-covariant perturbations. -/
axiom IsTranslationCovariant (L : ℕ) (v : Fin L → ManyBodyOpS (Fin L) 2) : Prop

/-- **An AKLT local perturbation** (Tasaki eq. (7.1.4) and the assumptions below it): a family of
local terms `v_x` that are each self-adjoint (`hermitian`), `r`-local (`local_range`), uniformly
bounded by `v₀` in the `L²` operator norm (`bounded`), and translation covariant
(`translation_covariant`, i.e. translates of one `v̂_o`). -/
structure IsAKLTPerturbation (L r : ℕ) (v₀ : ℝ) (v : Fin L → ManyBodyOpS (Fin L) 2) : Prop where
  /-- Each local term `v_x` is self-adjoint. -/
  hermitian : ∀ x, (v x).IsHermitian
  /-- Each local term `v_x` acts only on sites within range `r` of `x` (genuine spatial locality via
  the commutant-form `IsLocalRangeR`: `v_x` commutes with every single-site operator farther than
  `r` from `x`; the strong form keeps this Theorem 7.3 hypothesis faithful). -/
  local_range : ∀ x, IsLocalRangeR L 2 r x (v x)
  /-- Each local term is bounded in the `L²` operator norm by `v₀`. -/
  bounded : ∀ x, manyBodyOperatorNormS (v x) ≤ v₀
  /-- The family is translation covariant: `v_x = T̂^x v̂_o (T̂†)^x` for a single local `v̂_o`. -/
  translation_covariant : IsTranslationCovariant L v

/-- The **perturbed AKLT Hamiltonian** `Ĥ_ε = Ĥ_AKLT + ε Σ_x v̂_x` (eq. (7.1.4)) on the ring `Fin
L`. -/
noncomputable def perturbedAKLTHamiltonianS (L : ℕ) (ε : ℝ)
    (v : Fin L → ManyBodyOpS (Fin L) 2) : ManyBodyOpS (Fin L) 2 :=
  akltHamiltonianS L + (ε : ℂ) • ∑ x : Fin L, v x

/-- The **connected (truncated) two-point correlation** `⟨Φ, Ŝ_x · Ŝ_y Φ⟩ − Σ_α ⟨Φ, Ŝ_x^{(α)} Φ⟩
⟨Φ, Ŝ_y^{(α)} Φ⟩` (each expectation a Rayleigh ratio).  For a symmetry-breaking perturbed ground
state the one-point functions `⟨Ŝ_x^{(α)}⟩` need not vanish, so it is the *connected* correlation —
not the raw `⟨Ŝ_x · Ŝ_y⟩` — that decays exponentially in Yarotsky's stability theorem. -/
noncomputable def connectedChainCorrelation (L : ℕ) (Φ : (Fin L → Fin 3) → ℂ) (x y : Fin L) : ℝ :=
  expectationRatioRe (spinSDot x y 2) Φ -
    (expectationRatioRe (spinSSiteOp1 x 2) Φ * expectationRatioRe (spinSSiteOp1 y 2) Φ +
      expectationRatioRe (spinSSiteOp2 x 2) Φ * expectationRatioRe (spinSSiteOp2 y 2) Φ +
      expectationRatioRe (spinSSiteOp3 x 2) Φ * expectationRatioRe (spinSSiteOp3 y 2) Φ)

/-- `IsUniqueChainGroundState H E Φ`: `Φ` is the **unique ground state** of the chain Hamiltonian
`H`
at energy `E` — a nonzero eigenvector at the ground energy `E`, with every ground-energy eigenvector
a scalar multiple of `Φ`. -/
def IsUniqueChainGroundState {L : ℕ} (H : ManyBodyOpS (Fin L) 2) (E : ℝ)
    (Φ : (Fin L → Fin 3) → ℂ) : Prop :=
  Φ ≠ 0 ∧ H.mulVec Φ = (E : ℂ) • Φ ∧ IsGroundEnergy H E ∧
    ∀ Ψ : (Fin L → Fin 3) → ℂ, Ψ ≠ 0 → H.mulVec Ψ = (E : ℂ) • Ψ → ∃ c : ℂ, Ψ = c • Φ

/-- **Tasaki Theorem 7.3 (stability of the AKLT gap, Yarotsky), AXIOM.**  For perturbations of range
`r` bounded by `v₀`, there is a positive coupling threshold `ε₀` such that for every `|ε| < ε₀`
there
are positive constants `ΔE`, `C`, `ξ` — all **independent of the chain length `L`** — such that for
any `L ≥ 3` and any AKLT perturbation family `v` (`IsAKLTPerturbation`), the perturbed AKLT
Hamiltonian `Ĥ_ε = Ĥ_AKLT + ε Σ_x v̂_x` has a **unique ground state** `Φ`
(`IsUniqueChainGroundState`), a **gap** above it of at least `ΔE` (`∃ gap ≥ ΔE`,
`IsPositiveSpectralGap`), and **exponentially decaying connected correlations**
`|connectedChainCorrelation| ≤ C e^{−d(x,y)/ξ}` (`d` the ring distance).  The correlation is the
*connected* (truncated) one — for a symmetry-breaking perturbation the one-point functions need not
vanish, so the raw `⟨Ŝ_x · Ŝ_y⟩` need not decay; `L ≥ 3` excludes the degenerate one- and two-site
rings (where the AKLT term is a single-bond Casimir polynomial and the ground state is not unique).

The gap stays open and the disorder persists for the whole family of small local perturbations — the
gapful AKLT phase is stable.  Proved by Yarotsky [91] via cluster expansion; recorded as a
documented
axiom. -/
axiom aklt_theorem_7_3 (r : ℕ) (v₀ : ℝ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, |ε| < ε₀ →
      ∃ ΔE C ξ : ℝ, 0 < ΔE ∧ 0 < C ∧ 0 < ξ ∧
        ∀ (L : ℕ), 3 ≤ L → ∀ (v : Fin L → ManyBodyOpS (Fin L) 2), IsAKLTPerturbation L r v₀ v →
          ∃ (E : ℝ) (Φ : (Fin L → Fin 3) → ℂ),
            IsUniqueChainGroundState (perturbedAKLTHamiltonianS L ε v) E Φ ∧
            (∃ gap : ℝ, ΔE ≤ gap ∧ IsPositiveSpectralGap (perturbedAKLTHamiltonianS L ε v) gap) ∧
            ∀ x y : Fin L, |connectedChainCorrelation L Φ x y| ≤
              C * Real.exp (-(ringDist L x y : ℝ) / ξ)

end LatticeSystem.Quantum
