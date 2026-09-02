import LatticeSystem.Quantum.SpinS.ShastryNoSSBReduction

/-!
# Fixtures for the Theorem 4.2 variational/concavity reduction

Exercises the reduction of `shastry_no_symmetry_breaking_1d` (Tasaki §4.1, Theorem 4.2,
eqs. (4.1.9)–(4.1.10), pp. 76–77) to a single scalar energy-gain condition:

1. `staggeredFieldChainHamiltonianS_isHermitian`
2. `staggeredFieldChainHamiltonianS_conj_manyBodyReversalS` and `chainGroundEnergy_neg`
3. `chainGroundEnergy_concave` and `chainGroundEnergy_le_zero_field`
4. `chainGroundState_order_mean_sandwich`
5. the conditional capstone `shastry_no_symmetry_breaking_1d_of_energy_gain` and the documented
   axiom `shastryEnergyGain` that carries the energy-gain hypothesis it consumes.

Items 2b–4 are typed at the abstract `ManyBodyOpS Λ N` level of Tasaki's symmetry-breaking field
family `Ĥ_h = Ĥ − h Ô_L` (eq. (3.4.19), p. 69): an arbitrary Hermitian `H`, Hermitian `O`, and a
reversal `Θ` with `Θ Θ = 1`, `Θ H Θ = H`, `Θ O Θ = −O`.  The ring specialisation appears in items 1
and 2a, and in the capstone.

**The energy-gain hypothesis carries an `∃ L₀` that an earlier draft of these fixtures omitted.**
Without it the statement is false for every `N ≥ 1` (at `N = 0` it is true, every gain being `0`),
so a `∀ L` form would make `False` derivable at each such `N`; the two hand-computed
counterexamples (`L = 1` for any `N ≥ 1`, and the frustrated `L = 3`, `N = 1` triangle) are recorded
in the doc comment of `shastryEnergyGain`, are not witnessed in Lean, and are the reason the
fixtures below instantiate the hypothesis at `L`s taken beyond its own threshold rather than at
literal small `L`.  The two small-`L` fixtures here therefore test what *does* hold at `L = 0` and
`L = 1` — that the Hermiticity statement of item 1 elaborates and applies there at all.
-/

namespace LatticeSystem.Tests.ShastryEnergyGainReduction

open LatticeSystem
open LatticeSystem.Quantum
open Matrix

variable {N : ℕ}

/-! ## Signature pin 1 — `staggeredFieldChainHamiltonianS_isHermitian` -/

/-- **Signature pin.** `Ĥ_h` is Hermitian for every ring size `L`, field `h` and spin `N`. -/
example (L : ℕ) (h : ℝ) (N : ℕ) :
    (staggeredFieldChainHamiltonianS L h N).IsHermitian :=
  staggeredFieldChainHamiltonianS_isHermitian L h N

/-- **Boundary fixture (`L = 0`).** The `0`-site ring has a `1`-dimensional Hilbert space (the
unique empty configuration), so the statement — and, downstream, `hermitianMinEigenvalue`'s
`Nonempty` instance on `Fin 0 → Fin (N + 1)` — must still resolve.  Catches a hidden `1 ≤ L`
assumption in item 1. -/
example (h : ℝ) (N : ℕ) :
    hermitianMinEigenvalue (staggeredFieldChainHamiltonianS_isHermitian 0 h N) =
      hermitianMinEigenvalue (staggeredFieldChainHamiltonianS_isHermitian 0 h N) :=
  rfl

/-- **Boundary fixture (`L = 1`).** `ringCoupling 1` has `J 0 0 = 1`, a self-loop (the unique site
is its own cyclic successor), so `Ĥ_0` is a multiple of the identity; Hermiticity must still hold.
This is exactly the ring at which the *energy-gain* bound fails once `N ≥ 1` —
`E_1(0) − E_1(2η) = η·N` there, which no `ε·η·1` with `ε < N` can dominate — so the fixture pins the
item-1 statement rather than the hypothesis. -/
example (h : ℝ) (N : ℕ) :
    (staggeredFieldChainHamiltonianS 1 h N).IsHermitian :=
  staggeredFieldChainHamiltonianS_isHermitian 1 h N

/-! ## Signature pin 2a — `staggeredFieldChainHamiltonianS_conj_manyBodyReversalS` -/

/-- **Signature pin.** `Θ Ĥ_h Θ = Ĥ_{−h}`: conjugating the concrete staggered-field chain
Hamiltonian by the many-body reversal negates the field. -/
example (L : ℕ) (h : ℝ) (N : ℕ) :
    manyBodyReversalS (Fin L) N * staggeredFieldChainHamiltonianS L h N *
        manyBodyReversalS (Fin L) N =
      staggeredFieldChainHamiltonianS L (-h) N :=
  staggeredFieldChainHamiltonianS_conj_manyBodyReversalS L h N

/-- **Boundary fixture (odd ring, `L = 3`).** The staggered sublattice sign is not a genuine
bipartition on an odd cycle (site `2` and site `0` are both "even" and adjacent), yet the reversal
identity is asserted for every `L`; this pins that item 2a is not silently restricted to even
rings. -/
example (h : ℝ) (N : ℕ) :
    manyBodyReversalS (Fin 3) N * staggeredFieldChainHamiltonianS 3 h N *
        manyBodyReversalS (Fin 3) N =
      staggeredFieldChainHamiltonianS 3 (-h) N :=
  staggeredFieldChainHamiltonianS_conj_manyBodyReversalS 3 h N

/-! ## Signature pin 2b — `chainGroundEnergy` and `chainGroundEnergy_neg` -/

/-- **Signature pin (definition).** `chainGroundEnergy` is the ground energy of the abstract field
family `H − h·O`, taking only Hermiticity of `H` and `O` as hypotheses (no ring, no `Θ`). -/
noncomputable example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty (Λ → Fin (N + 1))]
    {H O : ManyBodyOpS Λ N} (hH : H.IsHermitian) (hO : O.IsHermitian) (h : ℝ) : ℝ :=
  chainGroundEnergy hH hO h

/-- **Signature pin.** `E(h) = E(−h)`: the abstract reversal symmetry `Θ H Θ = H`, `Θ O Θ = −O`
forces the ground energy of `H − h·O` to be an even function of `h`. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty (Λ → Fin (N + 1))]
    {H O Θ : ManyBodyOpS Λ N} (hH : H.IsHermitian) (hO : O.IsHermitian)
    (hΘ2 : Θ * Θ = 1) (hΘH : Θ * H * Θ = H) (hΘO : Θ * O * Θ = -O) (h : ℝ) :
    chainGroundEnergy hH hO h = chainGroundEnergy hH hO (-h) :=
  chainGroundEnergy_neg hH hO hΘ2 hΘH hΘO h

/-! ## Signature pin 3 — `chainGroundEnergy_concave` and `chainGroundEnergy_le_zero_field` -/

/-- **Signature pin.** `chainGroundEnergy` is concave in the field `h` (minimum of an affine family
of eigenvalues), needing only Hermiticity of `H`, `O` — no `Θ` hypothesis at all. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty (Λ → Fin (N + 1))]
    {H O : ManyBodyOpS Λ N} (hH : H.IsHermitian) (hO : O.IsHermitian)
    (h₁ h₂ t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * chainGroundEnergy hH hO h₁ + (1 - t) * chainGroundEnergy hH hO h₂ ≤
      chainGroundEnergy hH hO (t * h₁ + (1 - t) * h₂) :=
  chainGroundEnergy_concave hH hO h₁ h₂ t ht0 ht1

/-- **Signature pin.** `E(h) ≤ E(0)`: concavity plus the `E(h) = E(−h)` symmetry force `h = 0` to be
a maximiser. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty (Λ → Fin (N + 1))]
    {H O Θ : ManyBodyOpS Λ N} (hH : H.IsHermitian) (hO : O.IsHermitian)
    (hΘ2 : Θ * Θ = 1) (hΘH : Θ * H * Θ = H) (hΘO : Θ * O * Θ = -O) (h : ℝ) :
    chainGroundEnergy hH hO h ≤ chainGroundEnergy hH hO 0 :=
  chainGroundEnergy_le_zero_field hH hO hΘ2 hΘH hΘO h

/-! ## Signature pin 4 — `chainGroundState_order_mean_sandwich` -/

/-- **Signature pin.** The order-parameter sandwich `0 ≤ E(0) − E(h) ≤ h⟨Ô⟩_h ≤ E(0) − E(2h)` for
any normalized ground state `Φ` of `H − h·O`, `h ≥ 0`. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty (Λ → Fin (N + 1))]
    {H O Θ : ManyBodyOpS Λ N} (hH : H.IsHermitian) (hO : O.IsHermitian)
    (hΘ2 : Θ * Θ = 1) (hΘH : Θ * H * Θ = H) (hΘO : Θ * O * Θ = -O)
    (h : ℝ) (hh : 0 ≤ h) {Φ : (Λ → Fin (N + 1)) → ℂ} (hΦnorm : star Φ ⬝ᵥ Φ = 1)
    (hΦE : (H - (h : ℂ) • O).mulVec Φ = ((chainGroundEnergy hH hO h : ℝ) : ℂ) • Φ) :
    0 ≤ chainGroundEnergy hH hO 0 - chainGroundEnergy hH hO h ∧
      chainGroundEnergy hH hO 0 - chainGroundEnergy hH hO h ≤
        h * (star Φ ⬝ᵥ O.mulVec Φ).re ∧
      h * (star Φ ⬝ᵥ O.mulVec Φ).re ≤
        chainGroundEnergy hH hO 0 - chainGroundEnergy hH hO (2 * h) :=
  chainGroundState_order_mean_sandwich hH hO hΘ2 hΘH hΘO h hh hΦnorm hΦE

/-! ## Signature pin 5a — the documented axiom `shastryEnergyGain` -/

/-- **Signature pin.** The energy-gain hypothesis, quantified in `ε`, `η`, `L` and stated in the
`≤ ε · η · L` form (linear in `η`, which is the weakest shape the reduction needs — see the exponent
fixture below for why `η²` would be a genuinely different, strictly stronger statement).  The
`∃ L₀ : ℕ, ∀ L, L₀ ≤ L →` nest is part of the statement and not an artefact: see the module
header. -/
example (N : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ η : ℝ, 0 < η → η < η₀ → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
        hermitianMinEigenvalue (staggeredFieldChainHamiltonianS_isHermitian L 0 N) -
            hermitianMinEigenvalue (staggeredFieldChainHamiltonianS_isHermitian L (2 * η) N) ≤
          ε * η * (L : ℝ) :=
  shastryEnergyGain N

/-! ## Boundary fixture — `N = 0` (`Ô = 0`, the bound is trivially satisfied) -/

/-- **Boundary fixture (`N = 0`).** At `N = 0` every site carries a single spin state, so
`staggeredOrderOpS` and the staggered field term of `Ĥ_h` both vanish identically and `Ĥ_h = Ĥ_0`
for every `h`; the energy-gain bound must still be asserted there (and holds trivially, both ground
energies coinciding).  Catches an over-quantified `∀ N` that quietly assumes `N ≥ 1`. -/
example : ∀ ε : ℝ, 0 < ε → ∃ η₀ : ℝ, 0 < η₀ ∧
    ∀ η : ℝ, 0 < η → η < η₀ → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      hermitianMinEigenvalue (staggeredFieldChainHamiltonianS_isHermitian L 0 0) -
          hermitianMinEigenvalue (staggeredFieldChainHamiltonianS_isHermitian L (2 * η) 0) ≤
        ε * η * (L : ℝ) :=
  shastryEnergyGain 0

/-! ## Boundary fixture — the bound is asserted at odd rings too -/

/-- **Boundary fixture (odd rings are not excluded).** Instantiates the hypothesis at
`L := 2 * L₀ + 1`, which is odd and `≥ L₀` for every threshold `L₀` the axiom hands back.  On an odd
cycle the staggered sublattice sign is not a bipartition (site `L − 1` and site `0` are both "even"
and adjacent), and the axiom nevertheless asserts the bound there; this pins that the `∀ L` beyond
the threshold has not been quietly narrowed to even `L`.  It is the *unbounded* odd rings that are
covered: the fixed odd ring `L = 3` at `N = 1` violates the inequality (a hand computation recorded
in `shastryEnergyGain`'s doc comment, which also records that odd `L` is asserted on the same
footing as even `L`, with no separate argument for either), which is what the threshold exists
for. -/
example (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ → ∃ L₀ : ℕ,
      hermitianMinEigenvalue (staggeredFieldChainHamiltonianS_isHermitian (2 * L₀ + 1) 0 N) -
          hermitianMinEigenvalue
            (staggeredFieldChainHamiltonianS_isHermitian (2 * L₀ + 1) (2 * η) N) ≤
        ε * η * ((2 * L₀ + 1 : ℕ) : ℝ) := by
  obtain ⟨η₀, hη₀, hall⟩ := shastryEnergyGain N ε hε
  refine ⟨η₀, hη₀, fun η hη hη' => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hall η hη hη'
  exact ⟨L₀, hL₀ (2 * L₀ + 1) (by omega)⟩

/-! ## Exponent fixture — linear `η`, not `η²` -/

/-- **Exponent fixture (discriminator).** Instantiates `shastryEnergyGain` at `ε := 1` and, safely
inside the existentially-given window, at `η := η₀ / 2`, then at the threshold `L := L₀` it hands
back.  The right-hand side the axiom returns is *syntactically* `1 * (η₀ / 2) * (L₀ : ℝ)`; the
`have hshape` states the equal-but-differently-written form and `rw`s it into `h`.  If the exponent
on `η` were `2` instead of `1` (the strictly stronger form, which the reduction does not need and
which the expected `η^(4/3)` response of the gapless half-integer chains would falsify), the
right-hand side would be `1 * (η₀ / 2) ^ 2 * L₀`, which does **not** syntactically contain the
pattern rewritten here, so `rw [hshape] at h` would fail: the fixture discriminates the exponent
rather than merely asserting an inequality a stronger bound would also satisfy. -/
example (N : ℕ) : True := by
  obtain ⟨η₀, hη₀, hall⟩ := shastryEnergyGain N 1 (by norm_num)
  have hη_pos : 0 < η₀ / 2 := by linarith
  have hη_lt : η₀ / 2 < η₀ := by linarith
  obtain ⟨L₀, hL₀⟩ := hall (η₀ / 2) hη_pos hη_lt
  have h := hL₀ L₀ le_rfl
  have hshape : (1 : ℝ) * (η₀ / 2) * ((L₀ : ℕ) : ℝ) = (L₀ : ℝ) * (η₀ / 2) := by ring
  rw [hshape] at h
  trivial

/-! ## Signature pin 5b — the capstone `shastry_no_symmetry_breaking_1d_of_energy_gain` -/

/-- **Signature pin (capstone, target-shape check).** The capstone's conclusion is copied literally
from `shastry_no_symmetry_breaking_1d`'s own statement (same `∀ ε … ∃ h₀ … ∀ h … ∃ L₀ … ∀ L … ∀ Φ …`
shape, same normalization and ground-state hypotheses, same `|… .re / L| < ε` conclusion), so the
reduction cannot silently prove something weaker. -/
example (N : ℕ)
    (hgain : ∀ ε : ℝ, 0 < ε → ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ η : ℝ, 0 < η → η < η₀ → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
        hermitianMinEigenvalue (staggeredFieldChainHamiltonianS_isHermitian L 0 N) -
            hermitianMinEigenvalue (staggeredFieldChainHamiltonianS_isHermitian L (2 * η) N) ≤
          ε * η * (L : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ h : ℝ, 0 < h → h < h₀ → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
        ∀ Φ : (Fin L → Fin (N + 1)) → ℂ,
          star Φ ⬝ᵥ Φ = 1 →
          (∃ E₀ : ℂ, (staggeredFieldChainHamiltonianS L h N).mulVec Φ = E₀ • Φ ∧
            (∀ E : ℂ, ∀ Ψ : (Fin L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
              (staggeredFieldChainHamiltonianS L h N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) ∧
            Φ ≠ 0) →
          |(star Φ ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ).re / (L : ℝ)|
            < ε :=
  shastry_no_symmetry_breaking_1d_of_energy_gain N hgain

/-- **Target-preservation fixture.** The demoted `shastry_no_symmetry_breaking_1d` still has
*exactly* its former statement: this `example` states it independently and discharges it by the
identifier alone, so any weakening of the target — an added hypothesis, an `Even L` guard, a changed
quantifier nest — would break here rather than pass unnoticed. -/
example (N : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ h : ℝ, 0 < h → h < h₀ → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
        ∀ Φ : (Fin L → Fin (N + 1)) → ℂ,
          star Φ ⬝ᵥ Φ = 1 →
          (∃ E₀ : ℂ, (staggeredFieldChainHamiltonianS L h N).mulVec Φ = E₀ • Φ ∧
            (∀ E : ℂ, ∀ Ψ : (Fin L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
              (staggeredFieldChainHamiltonianS L h N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) ∧
            Φ ≠ 0) →
          |(star Φ ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ).re / (L : ℝ)|
            < ε :=
  shastry_no_symmetry_breaking_1d N

/-! ## Signature pin 5c — `hermitianMinEigenvalue_le_re_of_eigenpair` -/

/-- **Signature pin.** Any eigenpair of a Hermitian matrix has real part at least
`hermitianMinEigenvalue`; the converse direction to
`groundState_mulVec_eq_hermitianMinEigenvalue`. -/
example {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) {E : ℂ} {Ψ : n → ℂ} (hΨ : Ψ ≠ 0) (heig : H.mulVec Ψ = E • Ψ) :
    hermitianMinEigenvalue hH ≤ E.re :=
  hermitianMinEigenvalue_le_re_of_eigenpair hH hΨ heig

/-! ## Signature pin 5d — the converse capstone `shastryEnergyGain_of_no_symmetry_breaking_1d` -/

/-- **Signature pin (converse capstone).** The hypothesis is Theorem 4.2's conclusion, copied
literally from `shastry_no_symmetry_breaking_1d`'s statement; the conclusion is
`shastryEnergyGain`'s statement, copied literally. Together with item 5b this pins that the two
directions are stated over the identical pair of shapes, not merely similar ones. -/
example (N : ℕ)
    (hssb : ∀ ε : ℝ, 0 < ε → ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ h : ℝ, 0 < h → h < h₀ → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
        ∀ Φ : (Fin L → Fin (N + 1)) → ℂ,
          star Φ ⬝ᵥ Φ = 1 →
          (∃ E₀ : ℂ, (staggeredFieldChainHamiltonianS L h N).mulVec Φ = E₀ • Φ ∧
            (∀ E : ℂ, ∀ Ψ : (Fin L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
              (staggeredFieldChainHamiltonianS L h N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) ∧
            Φ ≠ 0) →
          |(star Φ ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ).re / (L : ℝ)|
            < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ η : ℝ, 0 < η → η < η₀ → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
        hermitianMinEigenvalue (staggeredFieldChainHamiltonianS_isHermitian L 0 N) -
            hermitianMinEigenvalue (staggeredFieldChainHamiltonianS_isHermitian L (2 * η) N) ≤
          ε * η * (L : ℝ) :=
  shastryEnergyGain_of_no_symmetry_breaking_1d N hssb

/-! ## Round-trip fixture — the acceptance artifact -/

/-- **Round-trip fixture (acceptance artifact).** Composes the forward capstone
(`shastry_no_symmetry_breaking_1d_of_energy_gain`, gain → Theorem 4.2) with the converse
(`shastryEnergyGain_of_no_symmetry_breaking_1d`, Theorem 4.2 → gain) and checks the composite has
the *same* gain-shaped hypothesis and conclusion. It deliberately takes `hgain` as a bound variable
of `shastryEnergyGain`'s shape rather than invoking the axiom `shastryEnergyGain` itself: had the
converse trivialised — e.g. by ignoring `hssb` and reconstructing the gain bound from `N` alone, or
by using `shastryEnergyGain N` internally and discarding `hssb` — this composite would still
typecheck against the axiom but would prove nothing about `hssb` being an actual converse input;
by threading an arbitrary `hgain` through both directions with no axiom in sight, the fixture forces
`shastryEnergyGain_of_no_symmetry_breaking_1d` to genuinely consume the `hssb` it is given. -/
example (N : ℕ)
    (hgain : ∀ ε : ℝ, 0 < ε → ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ η : ℝ, 0 < η → η < η₀ → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
        hermitianMinEigenvalue (staggeredFieldChainHamiltonianS_isHermitian L 0 N) -
            hermitianMinEigenvalue (staggeredFieldChainHamiltonianS_isHermitian L (2 * η) N) ≤
          ε * η * (L : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ η : ℝ, 0 < η → η < η₀ → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
        hermitianMinEigenvalue (staggeredFieldChainHamiltonianS_isHermitian L 0 N) -
            hermitianMinEigenvalue (staggeredFieldChainHamiltonianS_isHermitian L (2 * η) N) ≤
          ε * η * (L : ℝ) :=
  shastryEnergyGain_of_no_symmetry_breaking_1d N
    (shastry_no_symmetry_breaking_1d_of_energy_gain N hgain)

/-! ## Non-vacuity witness — the abstract hypothesis bundle is satisfiable, non-degenerately -/

/-- **Non-vacuity witness.** Instantiates the abstract hypothesis set consumed by items 3–4
(`H.IsHermitian`, `O.IsHermitian`, `Θ Θ = 1`, `Θ H Θ = H`, `Θ O Θ = −O`) at `Λ := Fin 1`, `N := 1`
(one spin-`½` site), `H := 0`, `O := staggeredOrderOpS (ringStaggeredSublattice 1) 1`,
`Θ := manyBodyReversalS (Fin 1) 1`, discharged entirely from lemmas that do not belong to this
reduction (`Matrix.isHermitian_zero`, `staggeredOrderOpS_isHermitian`, `manyBodyReversalS_mul_self`,
`manyBodyReversalS_conj_totalSpinSOp3`).

**This witness is degenerate in `H`**: `H := 0` carries no interaction, so it says nothing about a
real antiferromagnetic ring.  **It is not degenerate in `O`/`Θ`**: `O` is the nonzero single-site
`Ŝ³` and `Θ O Θ = −O` is a genuine sign flip, not the vacuous `O = 0` or `Θ = 1` case.  It
establishes only that the abstract hypothesis bundle is non-vacuous; the interacting instance is
supplied by `staggeredFieldChainHamiltonianS_conj_manyBodyReversalS` (item 2a). -/
example :
    (0 : ManyBodyOpS (Fin 1) 1).IsHermitian ∧
      (staggeredOrderOpS (ringStaggeredSublattice 1) 1).IsHermitian ∧
      manyBodyReversalS (Fin 1) 1 * manyBodyReversalS (Fin 1) 1 = 1 ∧
      manyBodyReversalS (Fin 1) 1 * (0 : ManyBodyOpS (Fin 1) 1) * manyBodyReversalS (Fin 1) 1 =
        (0 : ManyBodyOpS (Fin 1) 1) ∧
      manyBodyReversalS (Fin 1) 1 * staggeredOrderOpS (ringStaggeredSublattice 1) 1 *
          manyBodyReversalS (Fin 1) 1 =
        -staggeredOrderOpS (ringStaggeredSublattice 1) 1 := by
  refine ⟨Matrix.isHermitian_zero, staggeredOrderOpS_isHermitian _ 1,
    manyBodyReversalS_mul_self (Fin 1) 1, by simp, ?_⟩
  have hOeq : staggeredOrderOpS (ringStaggeredSublattice 1) 1 = totalSpinSOp3 (Fin 1) 1 := by
    simp [staggeredOrderOpS, totalSpinSOp3, ringStaggeredSublattice, spinSSiteOp3_def, one_smul]
  rw [hOeq]
  exact manyBodyReversalS_conj_totalSpinSOp3 (Fin 1) 1

end LatticeSystem.Tests.ShastryEnergyGainReduction
