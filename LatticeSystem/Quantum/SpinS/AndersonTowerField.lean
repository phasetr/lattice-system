import LatticeSystem.Quantum.SpinS.AndersonTower

/-!
# Tasaki §4.2: spontaneous symmetry breaking under an infinitesimal staggered field (Theorem 4.13)

Adding an infinitesimal staggered magnetic field `−h Ô_L^{(1)}` to the antiferromagnetic Heisenberg
Hamiltonian triggers spontaneous symmetry breaking.  With the field Hamiltonian (eq. (4.2.27))
`Ĥ_h = Ĥ − h Ô_L^{(1)}` and its ground state `Φ_GS,h`, Theorem 4.13 (eq. (4.2.28)) states
`lim_{h↓0} liminf_{L↑∞} ⟨Φ_GS,h| Ô_L^{(1)}/L^d |Φ_GS,h⟩ ≥ m∗`,
so the staggered moment per site survives the `L↑∞` then `h↓0` limits — symmetry breaking.  Combined
with Theorem 4.11 (`m∗ ≥ √(3 q₀)`) this gives a strictly positive order parameter.

We record it as a documented axiom over the torus family, following the established design (codex):
the double limit is stated in explicit `ε`–`δ` form with the *inner* threshold `L₀` depending on the
field `h` (outer `h↓0`, inner `liminf_L`); the field ground states `Φ_GS,h` are a *given* family
(eigenvector + minimizer of `Ĥ_h`, nonzero — not chosen by definition, since they need not be
unique); `m∗` is the genuine order parameter, pinned by a realizing unperturbed ground state
(`IsTanakaFullSSBConstants` + exact LRO/SSB limits, as in Theorem 4.11), which is unsatisfiable in
`d = 1` (no LRO, Corollary 4.3), so the statement is vacuous there.  The matching `m∗ ≥ √(3 q₀)` is
left to Theorem 4.11 (`tanakaSSB_orderParameter_lowerBound`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.1, Theorem 4.13, eqs. (4.2.27)–(4.2.28), pp. 102–103 (footnote 26: rigorously `liminf`).
-/

namespace LatticeSystem.Quantum

open Matrix Filter

variable {N : ℕ}

/-- The **staggered-field Hamiltonian** `Ĥ_h = Ĥ − h Ô_L^{(1)}` (eq. (4.2.27)) on the
`d`-dimensional
hypercubic torus: the antiferromagnetic nearest-neighbor Heisenberg Hamiltonian minus an external
staggered field `h ≥ 0` coupled to the `1`-axis staggered order operator. -/
noncomputable def staggeredFieldHamiltonianS (d L N : ℕ) [NeZero L] (h : ℝ) :
    ManyBodyOpS (HypercubicTorus d L) N :=
  heisenbergHamiltonianS (torusNNCoupling d L) N -
    (h : ℂ) • staggeredOrderOp1S (torusParitySublattice d L) N

/-- **Tasaki Theorem 4.13 (SSB under an infinitesimal staggered field), AXIOM.**  For the
staggered-field Hamiltonian `Ĥ_h = Ĥ − h Ô_L^{(1)}`, the per-site staggered moment of the
field ground state survives the iterated limit `lim_{h↓0} liminf_{L↑∞}` and is bounded below by the
SSB order parameter `m∗` (eq. (4.2.28)): for every `ε > 0` there is a field threshold `δ > 0` such
that for each `0 < h < δ` there is a size threshold `L₀` (depending on `h`) beyond which every
even-side field ground state `Φ_GS,h,L` has `m∗ − ε ≤ ⟨Φ_GS,h,L, Ô_L^{(1)} Φ_GS,h,L⟩.re / L^d`.

`m∗` is the genuine order parameter, pinned (as in Theorem 4.11) by a realizing *unperturbed* ground
state family `Φ₀` and slow tower `M` (`hFamily : IsRealizingTanakaGroundStateFamily …`: exact LRO
and
staggered-moment limits plus `IsTanakaFullSSBConstants`) — these are unsatisfiable in `d = 1` (no
LRO
ground state, Corollary 4.3), so the statement is vacuous there.
The field ground states `Φ_GS,h` are a *given* family of eigenvector/minimizer/nonzero states of
`Ĥ_h` (`hField`).  Combined with Theorem 4.11, this yields `≥ m∗ ≥ √(3 q₀) > 0`. -/
axiom tanakaSSB_field_lowerBound (d N : ℕ) (hd : 1 ≤ d) (q₀ mStar C₁ : ℝ)
    (hq₀ : 0 < q₀) (hC₁ : 0 < C₁)
    (Φ₀ : (L : ℕ) → (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ : ℕ → ℂ) (M : ℕ → ℕ)
    (hFamily : IsRealizingTanakaGroundStateFamily d N q₀ mStar C₁ Φ₀ E₀ M)
    (PhiGS : ℝ → (L : ℕ) → (HypercubicTorus d L → Fin (N + 1)) → ℂ) (EField : ℝ → ℕ → ℂ)
    (hField : ∀ h : ℝ, 0 < h → ∃ L₁ : ℕ, ∀ (L : ℕ) [NeZero L], L₁ ≤ L → 2 ≤ L → Even L →
      (staggeredFieldHamiltonianS d L N h).mulVec (PhiGS h L) = EField h L • PhiGS h L ∧
      (∀ E : ℂ, ∀ Ψ : (HypercubicTorus d L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
        (staggeredFieldHamiltonianS d L N h).mulVec Ψ = E • Ψ → (EField h L).re ≤ E.re) ∧
      PhiGS h L ≠ 0) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
        mStar - ε ≤
          expectationRatioRe (staggeredOrderOp1S (torusParitySublattice d L) N) (PhiGS h L) /
            (L : ℝ) ^ d

/-- **Tasaki Theorem 4.8/§4.2.2 trial energy bound, `hFamily`-pinned, AXIOM (energy/`ô` parity
companion of `orderSqMoment_ratio_le_mStarSq_family`).**  For a realizing Tanaka ground-state family
`(Φ L, M L, E₀ L)`, the trial state `Ξ_{M L} = tanakaSSBState … (M L) (Φ L)` built from the family's
slow tower `M L` is *low-lying*: its Rayleigh energy exceeds the ground energy by at most
`C₂ (M L+1)²/V` (eq. (4.2.11)), with a single tower-dispersion constant `C₂` existentially fixed by
the family and the bound holding eventually in (even) `L`.  This is the energy/`ô` mirror of
`IsTanakaSSBConstants`'s conclusion (Theorem 4.8, `AndersonTower.lean:280-285`), rekeyed from the
per-`L` inputs to the whole realizing family.

**Parity with the Theorem 4.11 `ô²` companion.**  Statement, quantifier shape and hypothesis surface
(`hd`, `hq₀`, `hC₁`, `hFamily`; even `L`, `L ≥ 2`, `d ≥ 1`; vacuous in `d = 1`) are identical to the
already-accepted concentration companion `orderSqMoment_ratio_le_mStarSq_family`
(`AndersonTowerOrderSqConcentration.lean`).  Both share the *same* truth-maker: Koma–Tasaki [66]'s
omitted finite-size **moment↔energy coupling** ("repeat the argument", eqs. (4.2.59)–(4.2.61)), one
recording the `ô²`-moment concentration and this one the trial-energy dispersion of the same tower.

**Why an axiom-free discharge (Option ①) is impossible.**  The realizing family carries only an
*abstract* growth constant `C₁` (`0 < C₁`, growth conjunct `(M L)+1 ≤ C₁·L^{d/2}`,
`AndersonTower.lean:398`); no conjunct forces `C₁ ≤ C₁_E`, the *fixed* small constant under which
Theorem 4.8's gate `(M L)+1 ≤ C₁_E·L^{d/2}` (`AndersonTower.lean:276`) fires.  A `min`-reduction
fails — shrinking `C₁` *strengthens* the growth bound, which is not preserved.  The bridge that
would close ① ("`tanakaOrderMean1(M L) → m∗`, the *maximal* density, forces the slow regime
`M L = o(√V)`, hence eventually `(M L)+1 ≤ C₁_E·√V`") is precisely [66]'s omitted moment↔energy
profile, absent from the Lean conjuncts (which record only the *limit* `→ m∗`, not the finite-size
profile).  So ① would
silently smuggle [66] in; making the input explicit here is the honest, precedent-matching choice.

**Why a gate-free predicate (Option ②) is UNSAFE, and how the `∀`-trap is avoided.**  Taken purely
syntactically the family predicate *admits* a hypothetical large-`C₁` family with `M L ~ c·√V` and
`moment → m∗`; for such an `M` Theorem 4.8's clean `C₂ (M+1)²/V` bound is **likely false** — its
½-denominator estimate `orderSum_pow_two_denom_lower` needs `3N M² ≤ 2q₀ V`
(`AndersonTowerTanakaDenominator.lean:103`) and the numerator needs budget `≤ ½`
(`AndersonTowerTanakaNumeratorAssembly.lean:256`), both requiring `C₁ ≲ √(q₀/N)`.  A gate-free
statement asserting the bound for *any* growth would therefore violate the "`∀` must hold for all"
discipline (`False` derivable).  We avoid the trap exactly as the Theorem 4.11 companion does: pin
the *whole* family via `hFamily`.  [66]'s coupling rules such fast families out (maximal-density
convergence forces the low-energy regime), so for every family actually satisfying `hFamily` the
bound is TRUE; the physical realized families (Theorem 4.9, `M(L) = ⌊L^{d/4}⌋ ≪ √V`, whose `C₁` is
Theorem 4.8's small constant) satisfy the gate outright, so the axiom over-states nothing.

**Why this pinned statement is TRUE.**  Under `hFamily`, `tanakaOrderMean1(M L) → m∗` (the maximal
staggered density) forces the slow tower `M L = o(√V)`, so Theorem 4.8's double-commutator estimate
(eqs. (4.2.69)–(4.2.71)) applies to the family's own `M L`, yielding the low-lying trial-energy
bound `R_Ĥ(Ξ_{M L}) ≤ E_GS + C₂ (M L+1)²/V` for a single family-fixed dispersion `C₂`.  The family
is unsatisfiable in `d = 1` (no LRO ground state, Corollary 4.3), so the axiom is vacuous there.

Reference: Koma, Tasaki, *Symmetry breaking and finite-size effects in quantum many-body systems*,
J. Stat. Phys. **76** (1994) 745–803 [66] (eqs. (4.2.59)–(4.2.61), proof omitted); Hal Tasaki,
*Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer, 2020), §4.2.2,
Theorem 4.8, eq. (4.2.11), p. 99. -/
axiom tanakaSSB_realizingFamily_energyBound (d N : ℕ) (hd : 1 ≤ d) (q₀ mStar C₁ : ℝ)
    (hq₀ : 0 < q₀) (hC₁ : 0 < C₁)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ : ℕ → ℂ) (M : ℕ → ℕ)
    (hFamily : IsRealizingTanakaGroundStateFamily d N q₀ mStar C₁ Φ E₀ M) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
      (star (tanakaSSBState (torusParitySublattice d L) N (M L) (Φ L)) ⬝ᵥ
          (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec
            (tanakaSSBState (torusParitySublattice d L) N (M L) (Φ L))).re /
        (star (tanakaSSBState (torusParitySublattice d L) N (M L) (Φ L)) ⬝ᵥ
          tanakaSSBState (torusParitySublattice d L) N (M L) (Φ L)).re ≤
      (E₀ L).re + C₂ * ((M L : ℝ) + 1) ^ 2 / (L : ℝ) ^ d

end LatticeSystem.Quantum
