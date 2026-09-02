import LatticeSystem.Quantum.SpinS.ShastryNoSSB
import LatticeSystem.Quantum.SpinS.ReversalSymmetricGroundEnergy
import LatticeSystem.Quantum.SpinS.AndersonTowerTanakaMoments
import LatticeSystem.Quantum.SpinS.AnisotropicReflectionSymmetry
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergReduction

/-!
# Tasaki §4.1 Theorem 4.2: variational reduction to a scalar energy-gain condition

The one-dimensional staggered-field ring Hamiltonian `Ĥ_h = Σ_x Ŝ_x · Ŝ_{x+1} − h Ô_L^{(3)}`
(eq. (4.1.9), p. 76) is the concrete instance of Tasaki's abstract symmetry-breaking field family
`Ĥ_h = Ĥ − h Ô_L` (eq. (3.4.19), p. 69).  The many-body spin reversal `Θ` commutes with the
Heisenberg part and reverses the staggered order operator, so it maps `Ĥ_h` to `Ĥ_{−h}`; that is
the concrete input the abstract ground-energy layer of `ReversalSymmetricGroundEnergy.lean` needs.

Feeding it the order-parameter sandwich `0 ≤ E_L(0) − E_L(h) ≤ h⟨Ô_L^{(3)}⟩_h ≤ E_L(0) − E_L(2h)`
turns Theorem 4.2 (eq. (4.1.10), p. 77) into a statement about the *scalar* ground-energy function
`E_L(η)` alone: if the zero-temperature energy gain of the staggered field is `o(η)` per site,
uniformly in large `L`, then the per-site staggered moment of every ground state vanishes in the
iterated limit.  That scalar condition is `shastryEnergyGain`, and the conditional capstone is
`shastry_no_symmetry_breaking_1d_of_energy_gain`.

**This is a reduction, not a discharge.**  Tasaki does not prove Theorem 4.2 (footnote 3, p. 76:
"We do not prove Theorem 4.2 in the present book"), and the analytic input he does not supply is
still missing here — it has only been isolated, in scalar form, into `shastryEnergyGain`.  The
declaration `shastry_no_symmetry_breaking_1d` is now a `theorem` rather than an `axiom`, with its
statement unchanged, but its `#print axioms` names `shastryEnergyGain`: the mathematical content of
Theorem 4.2 is exactly as unproved as before.  What the reduction buys is structural — the
eigenvector quantifiers, the ground-state degeneracy and the inner limit are gone, leaving one
inequality between real numbers.

That "nothing was gained mathematically" is itself checked, not merely stated:
`shastryEnergyGain_of_no_symmetry_breaking_1d` derives the scalar condition back from Theorem 4.2's
own conclusion, so the two statements are inter-derivable in Lean and the axiom is exactly as strong
as the theorem it stands in for.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, Theorem 4.2, eqs. (4.1.9)–(4.1.10), pp. 76–77, footnote 3, p. 76 (Shastry [58];
cf. Tanaka–Takeda–Idogaki [63]); §3.4, eqs. (3.4.19)–(3.4.20), pp. 69–70.
-/

namespace LatticeSystem.Quantum

open Matrix

/-- **The staggered-field chain Hamiltonian is Hermitian** (eq. (4.1.9), p. 76): the ring instance
of the generic `fieldOpS_isHermitian`, applied to the Hermitian ring Heisenberg Hamiltonian
(`heisenbergHamiltonianS_isHermitian_of_real` at the real `0`/`1` coupling `ringCoupling_self_star`)
and the Hermitian staggered order operator (`staggeredOrderOpS_isHermitian`).  It lives here rather
than beside the model in `ShastryNoSSB.lean` so that the fact is proved once, in its general form,
and not a second time at the ring.  No parity or positivity restriction on `L` is used: it holds
verbatim at `L = 0` (one-dimensional Hilbert space, both summands empty) and at `L = 1` (where
`ringCoupling 1` degenerates to the self-loop `J 0 0 = 1`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, eq. (4.1.9), p. 76. -/
theorem staggeredFieldChainHamiltonianS_isHermitian (L : ℕ) (h : ℝ) (N : ℕ) :
    (staggeredFieldChainHamiltonianS L h N).IsHermitian :=
  fieldOpS_isHermitian (heisenbergHamiltonianS_isHermitian_of_real (ringCoupling_self_star L) N)
    (staggeredOrderOpS_isHermitian (ringStaggeredSublattice L) N) h

/-- **The many-body spin reversal fixes the Heisenberg Hamiltonian**: `Θ Ĥ_J Θ = Ĥ_J` for every
coupling `J` (Tasaki's `Ĥ` of eq. (3.4.19), p. 69, at the ring coupling of eq. (4.1.9), p. 76).
Immediate from the anisotropic case at `λ = 1`, `D = 0`.  Private because it is a one-line
specialisation of `manyBodyReversalS_conj_anisotropicHeisenbergS` with no independent content; it is
used inside this module only, by `staggeredFieldChainHamiltonianS_conj_manyBodyReversalS` and by the
two capstones, which need the reversal symmetry of the Heisenberg part on its own rather than in the
combined `Θ Ĥ_h Θ = Ĥ_{−h}` form.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, eq. (3.4.19), p. 69; §4.1, eq. (4.1.9), p. 76. -/
private theorem manyBodyReversalS_conj_heisenbergHamiltonianS {Λ : Type*} [Fintype Λ]
    [DecidableEq Λ] (J : Λ → Λ → ℂ) (N : ℕ) :
    manyBodyReversalS Λ N * heisenbergHamiltonianS J N * manyBodyReversalS Λ N =
      heisenbergHamiltonianS J N := by
  rw [← anisotropicHeisenbergS_one_zero J N, manyBodyReversalS_conj_anisotropicHeisenbergS]

/-- **The many-body spin reversal negates the staggered field**: `Θ Ĥ_h Θ = Ĥ_{−h}` (eq. (4.1.9),
p. 76).  The Heisenberg part is fixed by `Θ` while `manyBodyReversalS_conj_staggeredOrderOpS`
reverses `Ô_L^{(3)}`; the two signs combine to flip `h`.  Holds for every ring size `L` — no parity
assumption — because the reversal acts site-by-site and never sees the sublattice pattern.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, eq. (4.1.9), p. 76. -/
theorem staggeredFieldChainHamiltonianS_conj_manyBodyReversalS (L : ℕ) (h : ℝ) (N : ℕ) :
    manyBodyReversalS (Fin L) N * staggeredFieldChainHamiltonianS L h N *
        manyBodyReversalS (Fin L) N =
      staggeredFieldChainHamiltonianS L (-h) N := by
  unfold staggeredFieldChainHamiltonianS
  simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    manyBodyReversalS_conj_heisenbergHamiltonianS, manyBodyReversalS_conj_staggeredOrderOpS]
  simp [smul_neg, neg_smul]

/-- **The staggered-field energy gain is `o(η)` per site, uniformly in large `L`: DOCUMENTED
AXIOM.**  For every `ε > 0` there is a field scale `η₀ > 0` such that for each `0 < η < η₀` there is
a size threshold `L₀` beyond which the ring ground energies obey
`E_L(0) − E_L(2η) ≤ ε · η · L`, where `E_L(c) = hermitianMinEigenvalue (Ĥ_c)` is the minimum
eigenvalue of `staggeredFieldChainHamiltonianS L c N` (eq. (4.1.9), p. 76).

**This is the analytic input Tasaki does not prove.**  Footnote 3, p. 76 reads verbatim "We do not
prove Theorem 4.2 in the present book.  Although the statement is not presented as a mathematical
theorem in [58], it can be made rigorous with some effort.  See [63] for a more mathematical
formulation of Shastry's argument."  Nothing here recovers that missing argument: this axiom is
**equivalent in strength to an `L`-uniform form of Theorem 4.2**, since the capstone
`shastry_no_symmetry_breaking_1d_of_energy_gain` derives Theorem 4.2 from it while, conversely, the
sandwich `E_L(0) − E_L(η) ≤ η⟨Ô⟩_η` of `chainGroundState_order_mean_sandwich` turns a per-site
staggered-moment bound back into an energy-gain bound of the same order.  **Both halves of that
equivalence are in Lean**: the forward one as the capstone, the converse as
`shastryEnergyGain_of_no_symmetry_breaking_1d` below, which derives this axiom's statement from
Theorem 4.2's own conclusion.  So the equivalence is not a hand argument but a checked fact, and
the present development is a **conditional reduction of Theorem 4.2, not a discharge of its
mathematical content**; what it removes is the eigenvector quantifiers, the ground-state degeneracy
and the inner thermodynamic limit, leaving a single inequality between real numbers.

**Why the exponent on `η` is `1` and not `2`.**  The linear form is the *weaker* of the two, and it
is the whole of what the reduction consumes: a bound `E_L(0) − E_L(2η) ≤ C · η² · L` with `C > 0`
implies this axiom outright (take `η₀ = ε / C`, `L₀ = 0`), so replacing `ε · η · L` by an `η²` shape
would assume strictly more without buying anything.  It would in addition assume a *quadratic*
zero-temperature response to the staggered field.  That is the behaviour expected of the gapped
integer-spin chains only; the half-integer chains — `N` is a parameter of this axiom, so odd `N` is
among the instances asserted — are gapless and are expected to respond as `L · η^{4/3}` up to
logarithmic corrections, which, `4/3` being below `2`, would falsify the `η²` shape there.  That
expected scaling is a statement of the physics literature: it is **not** formalised anywhere in this
development, is not derived from anything cited here, and is recorded only as the reason for not
strengthening the exponent.  Nothing below depends on it.

**Why the `∃ L₀` is present, and required.**  With `∀ L` in place of `∃ L₀, ∀ L ≥ L₀` the statement
is *false for every `N ≥ 1`*, so writing it that way would make `False` derivable at each such `N`.
It is not false at `N = 0`: there `Ŝ^{(3)} = 0`, every gain is `0`, and the `∀ L` form holds.  Two
explicit failures at `N ≥ 1`, both inside the range such a `∀ L` would quantify over:
* `L = 1`.  Here `ringCoupling 1` is the self-loop `J 0 0 = 1`, so `Ĥ_0 = Ŝ_0 · Ŝ_0 = S(S+1)·1` is a
  multiple of the identity and `Ô_1^{(3)} = Ŝ_0^{(3)}` has largest eigenvalue `S = N/2`.  Hence
  `E_1(0) − E_1(2η) = 2η·S = η·N` exactly, which exceeds `ε · η · 1` exactly when `ε < N`; since `ε`
  ranges over all positive reals, such an `ε` exists precisely when `N ≥ 1`.
* `L = 3`, `N = 1` (the frustrated spin-`½` triangle).  `Ĥ_0 = Ŝ_0·Ŝ_1 + Ŝ_1·Ŝ_2 + Ŝ_2·Ŝ_0` has a
  four-fold degenerate `S_tot = ½` ground space, on which the staggered operator
  `Ô_3^{(3)} = Ŝ_0^{(3)} − Ŝ_1^{(3)} + Ŝ_2^{(3)}` attains the value `5/6`; the corresponding
  ground-space vector is a variational trial state for `Ĥ_{2η}`, giving
  `E_3(0) − E_3(2η) ≥ 2η·(5/6) = (5/3)·η` for every `η > 0`, which exceeds `ε · η · 3` for every
  `ε < 5/9`.
Both are hand computations from the definitions above; **neither is witnessed in Lean**, and the
`∃ L₀` is stated so that neither has to be.  Both are `O(1)` boundary/frustration effects that the
factor `L` on the right-hand side absorbs once `L` is large, which is exactly what the `∃ L₀`
records — and it is all the capstone needs, since Theorem 4.2's own conclusion is likewise only
asserted beyond a size threshold.  The `∃ L₀` sits *inside* `∀ η` because the correction is `O(1/L)`
relative to the `ε·η` budget, so the threshold must be allowed to grow as `η ↓ 0`; the resulting
quantifier nest `ε → η₀ → η → L₀ → L` is the same one Theorem 4.2 itself uses.

**Odd `L` is asserted on the same footing as even `L`, with no separate argument for either.**  On
an odd ring the staggered pattern `ε_x = (−1)^x` has a sign defect: sites `L − 1` and `0` are both
`+1` and adjacent, so no perfect alternation exists.  The comparison available for it — with the
open chain on the same `L` sites, where `(−1)^x` alternates without defect — is
*parity-independent*: `ringCoupling` is nonzero exactly at `y = (x + 1) % L`, so at every `L ≥ 2`,
even and odd alike, ring and open chain differ by the single wrap bond `Ŝ_{L−1} · Ŝ_0`, whose
operator norm is `S(S+1) ≤ 3S²`, independently of `L` and of `η`; a minimum eigenvalue is
`1`-Lipschitz in the operator norm, so the two energy gains differ by at most `6S²`.  That transfers
an energy-gain bound between ring and open chain in either direction and distinguishes no parity;
it does not establish the open-chain case, which is established nowhere in this development either.
So the defect neither exempts odd `L` nor is disposed of here: the axiom asserts odd `L` on exactly
the terms on which it asserts even `L`.  Like the two failures above, this comparison is a hand
estimate and is not witnessed in Lean.

Two boundary cases are *not* excluded and hold outright.  At `N = 0` every site carries a single
spin state, `Ŝ^{(3)} = 0`, so `Ô_L^{(3)} = 0` and `Ĥ_c = Ĥ_0` for all `c`: the gain is `0`.  At
`L = 0` the Hilbert space is one-dimensional and both `Ĥ_0` and `Ĥ_{2η}` are the zero matrix, so
the gain is `0 ≤ ε · η · 0`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, Theorem 4.2, eqs. (4.1.9)–(4.1.10), pp. 76–77, footnote 3, p. 76; B. S. Shastry,
J. Phys. A **25**, L249 (1992) [58]; K. Tanaka, K. Takeda, T. Idogaki, J. Magn. Magn. Mater.
**272–276**, 908 (2004) [63]. -/
axiom shastryEnergyGain (N : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ η : ℝ, 0 < η → η < η₀ → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
        hermitianMinEigenvalue (staggeredFieldChainHamiltonianS_isHermitian L 0 N) -
            hermitianMinEigenvalue (staggeredFieldChainHamiltonianS_isHermitian L (2 * η) N) ≤
          ε * η * (L : ℝ)

/-- **Tasaki Theorem 4.2 (Shastry no-SSB in 1D), conditional on the energy-gain hypothesis.**
Assuming only the scalar hypothesis `hgain` — the `L`-uniform `o(η)` staggered-field energy gain,
in the shape of `shastryEnergyGain` — the per-site staggered order parameter of every normalized
ground state vanishes in the iterated limit `lim_{h↓0} lim_{L↑∞}` (eq. (4.1.10), p. 77).

Proof.  Fix `ε > 0` and run `hgain` at `ε/2`, taking `h₀ := η₀`.  For `0 < h < h₀` take the `L₀` it
supplies (enlarged to at least `1`, so that division by `L` is legitimate).  For a normalized ground
state `Φ` of `Ĥ_h`, `groundState_mulVec_eq_hermitianMinEigenvalue` identifies its eigenvalue with
`E_L(h)`, and `chainGroundState_order_mean_sandwich` — fed the two halves of the reversal symmetry
separately, `Θ Ĥ Θ = Ĥ` from `manyBodyReversalS_conj_heisenbergHamiltonianS` and `Θ Ô Θ = −Ô` from
`manyBodyReversalS_conj_staggeredOrderOpS` — gives
`0 ≤ E_L(0) − E_L(h) ≤ h⟨Ô_L^{(3)}⟩ ≤ E_L(0) − E_L(2h)`.  The left half forces `⟨Ô_L^{(3)}⟩ ≥ 0`;
the right half together with `hgain` gives `h⟨Ô_L^{(3)}⟩ ≤ (ε/2)·h·L`, so
`0 ≤ ⟨Ô_L^{(3)}⟩/L ≤ ε/2 < ε`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, Theorem 4.2, eqs. (4.1.9)–(4.1.10), pp. 76–77; §3.4, eq. (3.4.20), p. 70. -/
theorem shastry_no_symmetry_breaking_1d_of_energy_gain (N : ℕ)
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
            < ε := by
  intro ε hε
  obtain ⟨η₀, hη₀, hall⟩ := hgain (ε / 2) (by linarith)
  refine ⟨η₀, hη₀, fun h hh0 hhη => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hall h hh0 hhη
  refine ⟨max L₀ 1, fun L hL Φ hΦnorm hgs => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
  obtain ⟨E₀, heig, hmin, _hΦne⟩ := hgs
  have hHring : (heisenbergHamiltonianS (ringCoupling L) N).IsHermitian :=
    heisenbergHamiltonianS_isHermitian_of_real (ringCoupling_self_star L) N
  have hOring : (staggeredOrderOpS (ringStaggeredSublattice L) N).IsHermitian :=
    staggeredOrderOpS_isHermitian (ringStaggeredSublattice L) N
  have hbridge : ∀ c : ℝ, chainGroundEnergy hHring hOring c =
      hermitianMinEigenvalue (staggeredFieldChainHamiltonianS_isHermitian L c N) := fun _ => rfl
  have hΦE : (heisenbergHamiltonianS (ringCoupling L) N -
      (h : ℂ) • staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ =
      ((chainGroundEnergy hHring hOring h : ℝ) : ℂ) • Φ := by
    rw [hbridge h]
    exact groundState_mulVec_eq_hermitianMinEigenvalue
      (staggeredFieldChainHamiltonianS_isHermitian L h N) hΦnorm heig hmin
  have hΘH := manyBodyReversalS_conj_heisenbergHamiltonianS (ringCoupling L) N
  have hΘO := manyBodyReversalS_conj_staggeredOrderOpS (Λ := Fin L) (N := N)
    (ringStaggeredSublattice L)
  obtain ⟨hs1, _hs2, hs3⟩ := chainGroundState_order_mean_sandwich hHring hOring
    (manyBodyReversalS_mul_self (Fin L) N) hΘH hΘO h hh0.le hΦnorm hΦE
  have hgainL := hL₀ L (le_trans (le_max_left _ _) hL)
  rw [← hbridge 0, ← hbridge (2 * h)] at hgainL
  set eO := (star Φ ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ).re with heOdef
  have hshape : ε / 2 * h * (L : ℝ) = h * (ε / 2 * (L : ℝ)) := by ring
  have hmul : h * eO ≤ h * (ε / 2 * (L : ℝ)) := by linarith [hs3, hgainL, hshape]
  have hnonneg : h * 0 ≤ h * eO := by linarith [hs1, hs3]
  have heO_nonneg : (0 : ℝ) ≤ eO := le_of_mul_le_mul_left hnonneg hh0
  have heO_ub : eO ≤ ε / 2 * (L : ℝ) := le_of_mul_le_mul_left hmul hh0
  rw [abs_of_nonneg (div_nonneg heO_nonneg hLpos.le), div_lt_iff₀ hLpos]
  linarith [heO_ub, mul_pos (half_pos hε) hLpos]

/-- **The converse of the reduction: Theorem 4.2 implies the energy-gain condition.**  From `hssb`
— the conclusion of `shastry_no_symmetry_breaking_1d` verbatim, that the per-site staggered order
parameter of every normalized ground state vanishes in the iterated limit (eq. (4.1.10), p. 77) —
the scalar bound `E_L(0) − E_L(2η) ≤ ε · η · L` of `shastryEnergyGain` follows verbatim, with the
same `ε → η₀ → η → L₀ → L` quantifier nest.

**What this buys.**  Together with `shastry_no_symmetry_breaking_1d_of_energy_gain` it makes both
implications between Theorem 4.2 and `shastryEnergyGain` machine-checked, so the two statements are
inter-derivable in Lean rather than merely asserted to be so.  That assertion — that the axiom is
*equivalent in strength* to an `L`-uniform form of Theorem 4.2, and hence that the reduction
relocates the missing analytic input without weakening it — is carried as prose in six places in
this development: the doc comment of `shastryEnergyGain` above, the Chapter 4 documented-axiom
ledger, the public proof guide, two records of the legacy catalogue, and the machine-readable
Chapter 4 status record.  It is now also a theorem, so "this is a relocation, not progress" is
checked rather than said, and a future reader cannot mistake the reduction for a partial discharge
on the strength of an unverified equivalence claim.

**Why the field handed to `hssb` is `2η`, not `η`.**  The sandwich
`0 ≤ E(0) − E(h) ≤ h⟨Ô⟩_h ≤ E(0) − E(2h)` of `chainGroundState_order_mean_sandwich` bounds
`E(0) − E(h)` — not `E(0) − E(2h)` — by the order parameter *at the same field* `h`.  The prose
statements of the equivalence all quote that middle inequality in the form
`E_L(0) − E_L(η) ≤ η⟨Ô⟩_η`, whereas `shastryEnergyGain`'s left-hand side is `E_L(0) − E_L(2η)`.
The two are matched by running the middle inequality at `h := 2η`: the state whose order parameter
`hssb` bounds is then a ground state of `Ĥ_{2η}`, which is the field the axiom's left-hand side
refers to.  This is what fixes `η₀ := h₀/2` — so that `0 < η < η₀` places `2η` inside `hssb`'s own
field window `(0, h₀)` — and it is the one step of the derivation the prose does not spell out.

**Why the threshold is `max L₀ 1`.**  Theorem 4.2's conclusion bounds `|⟨Ô⟩.re / L|`, and in Lean
`x / 0 = 0`, so at `L = 0` that conclusion reads `0 < ε` and says nothing whatever about `⟨Ô⟩`.
This route converts the per-site bound back into `⟨Ô⟩.re < (ε/2)·L` through `div_lt_iff₀`, which
needs `0 < (L : ℝ)`; enlarging to `max L₀ 1` is what supplies it, and with `hssb`'s own `L₀` left
unchanged the step has no such hypothesis at `L = 0` and the proof fails to elaborate.
It is load-bearing for **this proof route**, not for soundness: the goal is
`∃ L₀, ∀ L ≥ L₀, …`, so raising the threshold only weakens what has to be shown and cannot rule
out an unsound step.  Nothing is being excluded either — at `L = 0` the goal reads
`E_0(0) − E_0(2η) ≤ 0`, which holds because the empty ring's Hamiltonian is the zero matrix at
every field (a hand computation, no Lean witness here).

Proof.  Instantiate `hssb` at `ε/2` to obtain `h₀ > 0` and set `η₀ := h₀/2`.  For `0 < η < η₀` put
`h := 2η`, which lies in `(0, h₀)`, and take the threshold `hssb` supplies there, enlarged to
`max L₀ 1`.  At `L` beyond it, `exists_unit_eigenvector_hermitianMinEigenvalue` produces a
normalized minimum eigenvector `Φ` of `Ĥ_{2η}`, and `hermitianMinEigenvalue_le_re_of_eigenpair`
certifies its eigenvalue as minimal over all eigenpairs, which is what `hssb`'s ground-state
hypothesis demands; `hssb` then yields `⟨Ô_L^{(3)}⟩.re < (ε/2)·L`.  The middle inequality of
`chainGroundState_order_mean_sandwich` at field `2η` closes the argument:
`E_L(0) − E_L(2η) ≤ 2η·⟨Ô_L^{(3)}⟩.re < 2η·(ε/2)·L = ε·η·L`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, Theorem 4.2, eqs. (4.1.9)–(4.1.10), pp. 76–77, footnote 3, p. 76; §3.4,
eqs. (3.4.19)–(3.4.20), pp. 69–70. -/
theorem shastryEnergyGain_of_no_symmetry_breaking_1d (N : ℕ)
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
          ε * η * (L : ℝ) := by
  intro ε hε
  obtain ⟨h₀, hh₀, hall⟩ := hssb (ε / 2) (by linarith)
  refine ⟨h₀ / 2, by linarith, fun η hη hηlt => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hall (2 * η) (by linarith) (by linarith)
  refine ⟨max L₀ 1, fun L hL => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
  have hHring : (heisenbergHamiltonianS (ringCoupling L) N).IsHermitian :=
    heisenbergHamiltonianS_isHermitian_of_real (ringCoupling_self_star L) N
  have hOring : (staggeredOrderOpS (ringStaggeredSublattice L) N).IsHermitian :=
    staggeredOrderOpS_isHermitian (ringStaggeredSublattice L) N
  have hbridge : ∀ c : ℝ, chainGroundEnergy hHring hOring c =
      hermitianMinEigenvalue (staggeredFieldChainHamiltonianS_isHermitian L c N) := fun _ => rfl
  obtain ⟨Φ, hΦnorm, hΦeig⟩ := exists_unit_eigenvector_hermitianMinEigenvalue
    (staggeredFieldChainHamiltonianS_isHermitian L (2 * η) N)
  have hΦne : Φ ≠ 0 := by
    intro h0
    rw [h0] at hΦnorm
    simp at hΦnorm
  have hmin : ∀ E : ℂ, ∀ Ψ : (Fin L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
      (staggeredFieldChainHamiltonianS L (2 * η) N).mulVec Ψ = E • Ψ →
      (((hermitianMinEigenvalue
        (staggeredFieldChainHamiltonianS_isHermitian L (2 * η) N) : ℝ) : ℂ)).re ≤ E.re := by
    intro E Ψ hΨ hΨeig
    rw [Complex.ofReal_re]
    exact hermitianMinEigenvalue_le_re_of_eigenpair _ hΨ hΨeig
  have habs := hL₀ L (le_trans (le_max_left _ _) hL) Φ hΦnorm ⟨_, hΦeig, hmin, hΦne⟩
  have hΦE : (heisenbergHamiltonianS (ringCoupling L) N -
      ((2 * η : ℝ) : ℂ) • staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ =
      ((chainGroundEnergy hHring hOring (2 * η) : ℝ) : ℂ) • Φ := by
    rw [hbridge (2 * η)]
    exact hΦeig
  have hΘH := manyBodyReversalS_conj_heisenbergHamiltonianS (ringCoupling L) N
  have hΘO := manyBodyReversalS_conj_staggeredOrderOpS (Λ := Fin L) (N := N)
    (ringStaggeredSublattice L)
  obtain ⟨_hs1, hs2, _hs3⟩ := chainGroundState_order_mean_sandwich hHring hOring
    (manyBodyReversalS_mul_self (Fin L) N) hΘH hΘO (2 * η) (by linarith) hΦnorm hΦE
  set eO := (star Φ ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ).re
  have heO_ub : eO < ε / 2 * (L : ℝ) := (div_lt_iff₀ hLpos).mp (lt_of_abs_lt habs)
  have hmul : 2 * η * eO ≤ 2 * η * (ε / 2 * (L : ℝ)) :=
    mul_le_mul_of_nonneg_left heO_ub.le (by linarith)
  have hshape : 2 * η * (ε / 2 * (L : ℝ)) = ε * η * (L : ℝ) := by ring
  rw [← hbridge 0, ← hbridge (2 * η)]
  linarith [hs2, hmul, hshape]

/-- **Tasaki Theorem 4.2 (Shastry's theorem: no symmetry breaking in one dimension).**
For the one-dimensional spin-`S` antiferromagnetic Heisenberg ring under a staggered magnetic field
`Ĥ_h = Σ_x Ŝ_x · Ŝ_{x+1} − h Ô_L^{(3)}` (eq. (4.1.9), p. 76), the per-site staggered order
parameter of every *normalized* ground state vanishes in the iterated limit `lim_{h↓0} lim_{L↑∞}`
(eq. (4.1.10), p. 77): for every `ε > 0` there is a field threshold `h₀ > 0` such that for each
field `0 < h < h₀` there is a size threshold `L₀` beyond which every normalized ground state `Φ` of
`staggeredFieldChainHamiltonianS L h N` satisfies `|⟨Φ, Ô_L^{(3)} Φ⟩.re / L| < ε`.  Here a ground
state is a normalized energy-minimizing eigenvector (`Φ ≠ 0`, `star Φ ⬝ᵥ Φ = 1`, `Ĥ_h Φ = E₀ • Φ`
with `E₀.re` minimal over eigenpairs); the normalization makes the per-site bound scale-invariant.

**Status: conditional, not discharged.**  This is a `theorem` rather than an `axiom` only in the
bookkeeping sense: it is `shastry_no_symmetry_breaking_1d_of_energy_gain` applied to the documented
axiom `shastryEnergyGain`, so `#print axioms shastry_no_symmetry_breaking_1d` names
`shastryEnergyGain` alongside the standard three.  Tasaki does not prove Theorem 4.2 (footnote 3,
p. 76), and the argument he cites — Shastry [58], made mathematical in Tanaka–Takeda–Idogaki [63] —
is not reconstructed here.  What the reduction achieves is that the whole gap is now carried by one
scalar inequality between ground energies, with the eigenvector quantifiers, the ground-state
degeneracy and the inner thermodynamic limit discharged.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, Theorem 4.2, eqs. (4.1.9)–(4.1.10), pp. 76–77, footnote 3, p. 76 (Shastry [58];
cf. Tanaka–Takeda–Idogaki [63]). -/
theorem shastry_no_symmetry_breaking_1d (N : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ h : ℝ, 0 < h → h < h₀ → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
        ∀ Φ : (Fin L → Fin (N + 1)) → ℂ,
          star Φ ⬝ᵥ Φ = 1 →
          (∃ E₀ : ℂ, (staggeredFieldChainHamiltonianS L h N).mulVec Φ = E₀ • Φ ∧
            (∀ E : ℂ, ∀ Ψ : (Fin L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
              (staggeredFieldChainHamiltonianS L h N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) ∧
            Φ ≠ 0) →
          |(star Φ ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ).re / (L : ℝ)| < ε
    := shastry_no_symmetry_breaking_1d_of_energy_gain N (shastryEnergyGain N)

end LatticeSystem.Quantum
