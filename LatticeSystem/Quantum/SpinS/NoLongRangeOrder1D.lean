import LatticeSystem.Quantum.SpinS.NoLongRangeOrderConditional

/-!
# Tasaki §4.1: absence of long-range order in one dimension (Corollary 4.3), conditional

The conditional reduction `no_long_range_order_1d_of_susceptibility`
(`NoLongRangeOrderConditional.lean`) proves the exact `ε`–`δ` statement of Tasaki's Corollary 4.3
*modulo a single quantitative input*: the staggered static susceptibility of every ground state of
the zero-field one-dimensional antiferromagnetic Heisenberg ring is `o(L³)`, i.e. for every margin
`δ > 0` there is a size threshold beyond which every ground state admits a potential `y` for `ÔΦ`
with `Re⟨y, ÔΦ⟩ ≤ δ·L³`.  Tasaki proves no such bound, and neither source examined here states one
at the antiferromagnetic wavevector `k* = π`: his "hard analysis" remark (p. 83) concerns the
infrared bound (4.1.24), which is stated for `k ≠ k*` only and diverges as `k → k*`, and Shastry's
own upper bound (his eq. (22)) diverges at `q = Q` the same way.  That quantitative input is
therefore recorded as a documented axiom
`shastry_staggered_susceptibility_subcubic` — an assumption of this project, with the attribution
analysis and the boundary cases carried at its declaration site — and fed into the conditional
reduction to obtain `no_long_range_order_1d`.

**That is a conditional reduction, not a discharge of Corollary 4.3.**  The axiom is strictly
stronger than the corollary it is fed into (see "Strength relative to Corollary 4.3 itself"
below), so `no_long_range_order_1d` is a `theorem` in the bookkeeping sense only:
`#print axioms` on it names `shastry_staggered_susceptibility_subcubic`.  Only the degenerate
spin-`0` case `N = 0` is unconditional.

Only the *zero-field* Corollary 4.3 is reduced here; the field version Theorem 4.2
(`shastry_no_symmetry_breaking_1d`, the iterated `lim_{h↓0} lim_{L↑∞}` double limit) is a strictly
stronger statement not reachable by this static-susceptibility route.  It is a conditional theorem
in `ShastryNoSSBReduction.lean`, resting on the documented axiom `shastryEnergyGain`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, Corollary 4.3, eq. (4.1.11), p. 77 (with footnotes 3, p. 76 and 9, p. 83).
-/

namespace LatticeSystem.Quantum

open Matrix

/-- **Shastry staggered susceptibility, sub-cubic form (`χ(k*) = o(L³)`), DOCUMENTED AXIOM.**  For
the zero-field one-dimensional spin-`S` antiferromagnetic Heisenberg ring on an **even** number
`L ≥ 2` of sites: for every margin `δ > 0` there is a size threshold `L₀` beyond which every
*normalized* ground state `Φ` (energy `hermitianMinEigenvalue`) admits a potential `y` for `ÔΦ` —
`(Ĥ − E₀) y = ÔΦ` — whose static staggered susceptibility obeys `Re⟨y, ÔΦ⟩ ≤ δ·L³`.  Physically
`Re⟨y, ÔΦ⟩ = χ(k*) = L · f_L^{(-1)}(k*)`, the zero-frequency staggered susceptibility at the
antiferromagnetic wavevector `k* = π`.

**Neither source examined here states a bound on `f_L^{(-1)}(k*)`.**  The two examined are Tasaki
(pp. 81, 83) and Shastry (his eq. (22), p. L252); Tanaka–Takeda–Idogaki [63] was *not* examined —
this repository has no copy of it — so nothing is claimed here about what [63] does or does not
state.  Tasaki's "This is nontrivial, and requires a hard analysis" (§4.1, p. 83) is about bounding
`f_L^{(-1)}(k)` *inside the derivation of the infrared bound* (4.1.24), which §4.1.2 uses to prove
Theorem 4.1 (long-range order for `d ≥ 3` and any `S`, or `d = 2` and `S ≥ 1`; p. 75) — not to
prove the one-dimensional Corollary 4.3.  That infrared bound is stated on p. 81 explicitly "for
any `k ∈ 𝒦_L \ {k*}`", and Tasaki notes on the same page that its right-hand side is roughly
`(const.)/|k − k*|` when `|k − k*| ≪ 1`: it *diverges* as `k → k*`.  Shastry's own upper bound
(`g_q^x ≤ G(q)`, his eq. (22), p. L252) diverges at `q = Q` in the same way.  So the earlier
reading of that footnote as a citation for a bound *at* `k*` was a misattribution, and what is
recorded below is an assumption of this project rather than a transcription of a published estimate.

**The earlier `≤ C·L` form was false, not merely unsourced.**  At `N = 1` — the spin-1/2 chain,
which is the case the asymptotic Shastry quotes is about — the large-separation behaviour gives
`⟨Ô²⟩ ≍ L (log L)^{3/2}`, and running this repository's own
`staggeredOrder_sq_le_susceptibility` (`2⟨Ô²⟩² ≤ 12 N³ L χ`) backwards forces `χ ≳ L (log L)³`.
Then `χ/L → ∞`, so no size-uniform `C` with `χ ≤ C·L` exists.  That single `N` already refutes the
`∀ N ≥ 1` form the axiom is stated at; whether the same holds at every odd `N` is an extrapolation
the quoted source does not make.  The one non-rigorous input to the refutation is the correlation
asymptotic `g(r) ~ (−1)^r (log r)^{1/2}/r`, which Shastry introduces as what "a considerable body
of numerical and approximate analytical work at `T = 0` K … suggests" (p. L252).  It is recorded at
exactly that strength — literature asymptotics, **no Lean witness** — the same status this project
already gives the `≍ L·η^{4/3}` response of the gapless chains.

**Why the threshold `∃ L₀` is part of the statement.**  The un-thresholded form
`∀ δ > 0, ∀ L, χ ≤ δ·L³` is false at `N = 1`, `L = 2`: the two-site ring is the dimer
`Ĥ = 2 Ŝ₀·Ŝ₁`, for which `χ = 1/2` against `δ·2³ = 8δ`, so every `δ < 1/16` refutes it.  That is a
hand computation with **no Lean witness**; mechanising it needs a two-site spectral result (the
explicit singlet/triplet splitting of the dimer and the resulting resolvent) that this repository
does not have.  The threshold therefore sits inside `∀ δ`, as `∀ δ > 0, ∃ L₀, ∀ L ≥ L₀`.

**Why `o(L³)` and nothing stronger.**  The only route from `χ` to Corollary 4.3 available here is
`staggeredOrder_sq_le_susceptibility`, i.e. `s² ≤ 6 N³ L χ` with `s = ⟨Φ, Ô²Φ⟩.re`.  A fixed
`χ ≤ C·L³` yields only `s ≤ √(6 N³ C)·L²`, leaving `s/L²` bounded rather than vanishing; the
vanishing that Corollary 4.3 asserts needs the margin to be arbitrary, which is exactly `o(L³)`.
Conversely `o(L³)` follows both from a gapped chain and from the `χ ≍ L²` growth that exact
diagonalisation of small rings indicates (numerics, no Lean witness), so the axiom stays neutral on
the open Haldane-gap question.

**Strength relative to Corollary 4.3 itself.**  The crude bounds already reach exactly `O(L³)`:
`⟨Ô²⟩ ≤ ‖Ô‖² ≤ S²L²` for normalized `Φ`, and `χ ≤ ⟨Ô²⟩/Δ` for the gap `Δ` above the ground space,
so any `Δ ≳ 1/L` gives `χ = O(S²L³)`.  Hence `o(L³)` is the first statement past the trivial
ceiling, and by `staggeredOrder_sq_le_susceptibility` it holds *only if* `⟨Ô²⟩ = o(L²)` — which is
Corollary 4.3's own conclusion.  The axiom is therefore strictly stronger than the corollary it
is fed into (the converse would additionally need `Δ ≳ 1/L`, which this repository does not have:
its only gap result, `lieb_schultz_mattis_affleck_lieb`, bounds `Δ` from *above*), but of the same
order of difficulty — what separates it from Corollary 4.3 is strength, not only sourcing.

**This is a real assumption, not a formality.**  No rigorous upper bound on `χ` for this model
exists in this repository or, at `k*`, in the literature examined here, and the one spectral input
the repository does have points the other way: `lieb_schultz_mattis_affleck_lieb` (Theorem 6.3)
bounds the gap from *above* by `8π²S²/L` for odd `N`, which makes `χ` large rather than small.

Restricted to **even** rings `L ≥ 2` (`Even L`): only bipartite (even) rings carry a balanced
staggered sublattice `Σ_x ε_x = 0`, so the ground state is an SU(2)-invariant singlet with
`⟨Φ, ÔΦ⟩ = 0`, hence `ÔΦ ⊥ ker(Ĥ − E₀)` and the resolvent potential `y` with `(Ĥ − E₀) y = ÔΦ`
genuinely exists.  Odd rings are non-bipartite: the staggered sublattice is unbalanced
(`Σ_x ε_x ≠ 0`, e.g. `L = 3`), `ÔΦ` need not be orthogonal to the ground state, no such `y` exists,
and they lie outside Tasaki's §4.1 setting (whose lattice `(Λ_L, B_L)` is defined for even `L`
only; §3.1, §4.1.1).  The statement is the `hsusc` hypothesis of
`no_long_range_order_1d_of_susceptibility`, so feeding it into that conditional reduction yields
the even-ring Corollary 4.3 **conditionally on this axiom**.  It does not discharge the
corollary: by the paragraph above the axiom is strictly stronger than it.

* B. S. Shastry, *Bounds for correlation functions of the Heisenberg antiferromagnet*,
  J. Phys. A: Math. Gen. **25**, L249 (1992) — Tasaki's [58]; the `g(r)` asymptotic is on p. L252.
* K. Tanaka, K. Takeda, T. Idogaki, *Absence of spontaneous symmetry breaking in the ground state
  of one-dimensional spin-orbital model*, J. Magn. Magn. Mater. **272–276**, 908–909 (2004) —
  Tasaki's [63]; not examined here (this repository has no copy). -/
axiom shastry_staggered_susceptibility_subcubic (N : ℕ) (hN : 1 ≤ N) :
    ∀ δ : ℝ, 0 < δ → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → 2 ≤ L → Even L →
      ∀ Φ : (Fin L → Fin (N + 1)) → ℂ, star Φ ⬝ᵥ Φ = 1 →
      (heisenbergHamiltonianS (ringCoupling L) N).mulVec Φ
          = (hermitianMinEigenvalue
              (heisenbergHamiltonianS_isHermitian_of_real (ringCoupling_self_star L) N) : ℂ) • Φ →
      ∃ y : (Fin L → Fin (N + 1)) → ℂ,
        (heisenbergHamiltonianS (ringCoupling L) N
            - (hermitianMinEigenvalue
                (heisenbergHamiltonianS_isHermitian_of_real (ringCoupling_self_star L) N) : ℂ)
              • (1 : ManyBodyOpS (Fin L) N)).mulVec y
          = (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ
        ∧ (star y ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ).re
            ≤ δ * (L : ℝ) ^ 3

/-- The staggered order operator is the zero operator at spin `S = 0` (`N = 0`): the single-site
spin-`3` matrix `spinSOp3 0` is the `1 × 1` diagonal with entry `(0/2 - 0) = 0`, so each summand
`ε_x • Ŝ_x^{(3)}` vanishes.  This makes the (squared) staggered order parameter trivially zero for
the degenerate spin-`0` chain, discharging the `N = 0` case of Corollary 4.3 unconditionally. -/
private theorem staggeredOrderOpS_spin_zero {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (A : Λ → Bool) :
    staggeredOrderOpS A 0 = 0 := by
  have h3 : spinSOp3 0 = 0 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [spinSOp3]
  rw [staggeredOrderOpS]
  refine Finset.sum_eq_zero (fun x _ => ?_)
  rw [spinSSiteOp3_def, h3, onSiteS_zero, smul_zero]

/-- **Tasaki Corollary 4.3 (absence of long-range order in one dimension), CONDITIONAL
THEOREM.**  For the
zero-field one-dimensional spin-`S` antiferromagnetic Heisenberg ring
(`heisenbergHamiltonianS (ringCoupling L) N`, i.e. `staggeredFieldChainHamiltonianS L 0 N`), the
squared staggered order parameter per site vanishes in the thermodynamic limit (eq. (4.1.11)):
for every `ε > 0` there is a size threshold `L₀` beyond which every normalized ground state `Φ` of
the zero-field **even** ring `L` has `|⟨Φ, (Ô_L^{(3)})² Φ⟩.re / L²| < ε`.

Restricted to even rings (`Even L`), faithful to Tasaki: §3.1 defines the lattice `(Λ_L, B_L)`
for even `L`, and §4.1.1 states the model "with even L".  Only bipartite (even) rings carry the
balanced staggered sublattice underlying the staggered order parameter and the unique-singlet
ground state (MLM, Thm 2.2); odd rings are non-bipartite and lie outside §4.1's setting.

**Conditional, not a discharge of Corollary 4.3.**  For `N ≥ 1` this is the conditional reduction
`no_long_range_order_1d_of_susceptibility` fed with the documented Shastry susceptibility axiom
`shastry_staggered_susceptibility_subcubic`, which is **strictly stronger** than the corollary —
the crude bounds `⟨Ô²⟩ ≤ S²L²` and `χ ≤ ⟨Ô²⟩/Δ` already reach exactly `O(L³)`, and via
`staggeredOrder_sq_le_susceptibility` the axiom holds only if `⟨Ô²⟩ = o(L²)`, which is this
statement's own conclusion.  So `#print axioms` here names
`shastry_staggered_susceptibility_subcubic`, and the corollary itself remains open.  Only the
degenerate spin-`0` case `N = 0` is unconditional, the staggered order operator vanishing there
(`staggeredOrderOpS_spin_zero`). -/
theorem no_long_range_order_1d (N : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → Even L →
      ∀ Φ : (Fin L → Fin (N + 1)) → ℂ,
        star Φ ⬝ᵥ Φ = 1 →
        (∃ E₀ : ℂ, (staggeredFieldChainHamiltonianS L 0 N).mulVec Φ = E₀ • Φ ∧
          (∀ E : ℂ, ∀ Ψ : (Fin L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
            (staggeredFieldChainHamiltonianS L 0 N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) ∧
          Φ ≠ 0) →
        |(star Φ ⬝ᵥ ((staggeredOrderOpS (ringStaggeredSublattice L) N *
            staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ)).re / ((L : ℝ) ^ 2)| < ε
    := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- spin-`0`: the staggered order operator vanishes, so the parameter is identically zero.
    intro ε hε
    refine ⟨0, fun L _ _ Φ _ _ => ?_⟩
    rw [staggeredOrderOpS_spin_zero]
    simpa using hε
  · -- `N ≥ 1`: feed the Shastry sub-cubic susceptibility axiom into the conditional reduction.
    exact no_long_range_order_1d_of_susceptibility N hN
      (shastry_staggered_susceptibility_subcubic N hN)

end LatticeSystem.Quantum
