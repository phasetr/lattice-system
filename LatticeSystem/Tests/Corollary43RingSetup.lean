import LatticeSystem.Quantum.SpinS.AndersonTowerTanakaMoments
import LatticeSystem.Quantum.SpinS.LiebSchultzMattisRingGroundData
import LatticeSystem.Math.MatrixAnalysis.UniqueEigenspaceInvolution
import LatticeSystem.Quantum.HorschVonderLindenLowLyingState
import LatticeSystem.Quantum.SpinS.HorschVonderLindenAfmRing

/-!
# Fixtures for issue #5416 PR-1 (§3.4's setting at the antiferromagnetic ring)

Each fixture pins a signature or an application shape of the declarations this PR adds, so that a
later change to a statement's conjunct order, hypothesis list or printed constants breaks
compilation here rather than passing silently.

## No new reversal involution

`LatticeSystem/Quantum/SpinS/ManyBodyReversalS.lean` defines
`manyBodyReversalS (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ)`, a general spin-`S` (arbitrary
`N`) involution on `ManyBodyOpS Λ N` rather than a spin-1/2-only construction, and
`AndersonTowerTanakaMoments.lean` proves
`manyBodyReversalS_conj_staggeredOrderOpS : Θ Ô_L^{(3)} Θ = -Ô_L^{(3)}` for `Ô = staggeredOrderOpS`
at general `Λ`, `N`. No new reversal involution is therefore introduced: the only new conjugation
is the cube `Θ Ô³ Θ = -Ô³`, needed for the third odd moment, `Ô` itself being covered by the
existing first-power lemma.

## What is pinned

1. `manyBodyReversalS_conj_staggeredOrderOpS_cube` — the new cube-conjugation lemma
   `Θ Ô³ Θ = -Ô³`, the one genuinely new piece of reversal-involution infrastructure.
2. That lemma consumed by `dotProduct_mulVec_eq_zero_of_conj_anti` exactly as the third odd
   moment's proof will consume it (the same shape as that lemma's existing first-power application
   inside `tanakaOrderMean2_eq_zero`, with `O` specialized to `Ô³`).
3. `afm_ring_staggeredOrderOpS_odd_moments_vanish` — eq. (3.4.4) at the ring: both odd moments
   vanish for the (unique) ground state, consuming `afm_ring_ground_state_data`'s `Φ_GS ≠ 0`,
   eigenvector equation and `finrank ≤ 1` conjuncts (normalisation is deliberately absent from the
   hypothesis list: `exists_involution_eigenvalue_of_unique_eigenspace` and
   `dotProduct_mulVec_eq_zero_of_conj_anti` need `Φ ≠ 0`, not `star Φ ⬝ᵥ Φ = 1`).
4. That declaration applied in the exact form its consumer (the ring instantiation of
   eq. (3.4.16), item 2 of the issue) will apply it — directly on `afm_ring_ground_state_data`'s
   output.
5. `tasaki_eq_3_4_16_afmRing_ssb_fromGroundState` — the ring instantiation of eq. (3.4.16): the
   generic capstone `tasaki_eq_3_4_16_lowLyingState_ssb` specialized to `Λ := Fin L`, to the ring's
   staggered per-site term
   `o := fun x => (if ringStaggeredSublattice L x then (1 : ℂ) else -1) • spinSSiteOp3 x N` (whose
   sum `∑ x, o x` is `staggeredOrderOpS (ringStaggeredSublattice L) N` by `rfl`, since that is
   exactly `staggeredOrderOpS`'s own definition), and to the ring's own bond decomposition and norm
   bounds, so that the caller supplies only `L`, `N`, the guards, the ground state and its data
   (`afm_ring_ground_state_data`'s witnesses plus normalisation), and the long-range-order
   hypothesis. The ring bound values `h₀ = 3N²`, `o₀ = N/2` are spelled directly into the
   energy-bound conjunct rather than hidden inside a proof.
6. That that declaration's *statement* is `tasaki_eq_3_4_16_lowLyingState_ssb`'s statement at the
   ring data (`B := Finset.univ`, `hb x := spinSDot x (finRotate L x) N`,
   `W x := {x, finRotate L x}`, `d := 1`, `h₀ := 3N²`, `o₀ := N/2`): an equation between the two
   applications, closed by `rfl`. It pins the statement — conjunct order, hypothesis list, printed
   constants — and not how either theorem is proved; the next section states exactly what a green
   and a red compile of it do and do not establish.

## What the `rfl` pin guarantees

Both sides of fixture 6's equation are proofs of propositions, so proof irrelevance reduces the
equation to a definitional-equality check on the two *statements*. That check backs the fixture in
one direction only, and the tempting biconditional ("`rfl` succeeds exactly when the statements are
definitionally equal") is false, so the two directions are worth separating:

* A green compile establishes that the check accepted the two statements as definitionally equal.
  That, and nothing about either proof, is what the fixture pins.
* A red one establishes only that the check did *not* accept. It is not a certificate that the
  statements differ: the check runs on a heartbeat budget and can stop without reaching a verdict,
  and even when it reaches one the message may not survive printing. Restating the energy conjuncts
  of `tasaki_eq_3_4_16_afmRing_ssb_fromGroundState` over `afmHeisenbergChainHamiltonianS` is
  rejected as a type mismatch whose explanation is replaced, at the default heartbeat budget, by a
  deterministic `whnf` timeout; raising `maxHeartbeats` prints the mismatch in full.
* Both outcomes fail the build, so the pin is fail-closed and drift cannot pass silently. The price
  is that a red fixture has to be diagnosed from the message rather than read as proof of drift.

## Boundary cases

`Even L` / `2 ≤ L` are carried explicitly as guard hypotheses on both new ring declarations,
reproducing exactly the guards `afm_ring_ground_state_data` and `ringSym_ground_uniqueness`
already require (uniqueness is proved only for the even, connected-bipartite ring: an odd ring is
non-bipartite and outside the MLM route). No fixture attempts an odd-`L` or `L < 2` instance:
misusing a declaration there fails at hypothesis instantiation (an unprovable `Even L` or `2 ≤ L`
obligation), not at any interesting boundary inside the *proof* — the exclusion is structural (the
hypothesis itself), not a computed edge case. This is recorded here rather than pinned with a
fixture that would look like coverage but isn't.

`N = 0` is excluded from this whole route the same way, by the `1 ≤ N` guard the declarations carry
(mirroring `afm_ring_ground_state_data`'s own `hN : 1 ≤ N`). The existing witness for why `N = 0`
is degenerate, `staggeredOrderOpS_spin_zero`, is `private` to
`LatticeSystem/Quantum/SpinS/NoLongRangeOrder1D.lean` and is therefore syntactically unreachable
from this file, so it is not referenced here. `no_long_range_order_1d`'s own doc comment already
records that the `N = 0` case is discharged unconditionally by a different, non-uniqueness route;
this PR does not touch that route.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4 "Setting and assumptions" p. 65, eqs. (3.4.4), (3.4.16).
-/

namespace LatticeSystem.Tests.Corollary43RingSetup

open LatticeSystem.Quantum LatticeSystem.Math Matrix Module

/-! ### Fixture 1: the new cube-conjugation lemma, signature pin -/

/-- Pins `manyBodyReversalS_conj_staggeredOrderOpS_cube`, `Θ Ô³ Θ = -Ô³`, in the same shape as the
existing first-power lemma
`manyBodyReversalS_conj_staggeredOrderOpS`. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ} (A : Λ → Bool) :
    manyBodyReversalS Λ N * (staggeredOrderOpS A N) ^ 3 * manyBodyReversalS Λ N
      = -(staggeredOrderOpS A N) ^ 3 :=
  manyBodyReversalS_conj_staggeredOrderOpS_cube A

/-! ### Fixture 2: the cube lemma consumed exactly as the third odd moment will consume it -/

/-- Pins the exact application shape the third-moment vanishing proof uses — the same call as the
existing first-moment application (`dotProduct_mulVec_eq_zero_of_conj_anti` at `O := Ô`) but with
`O` specialized to `Ô³` and fed by the cube lemma. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ} (A : Λ → Bool)
    {Φ : (Λ → Fin (N + 1)) → ℂ} {δ : ℂ}
    (hΘΦ : (manyBodyReversalS Λ N).mulVec Φ = δ • Φ) (hδ : δ * star δ = 1) :
    star Φ ⬝ᵥ ((staggeredOrderOpS A N) ^ 3).mulVec Φ = 0 :=
  dotProduct_mulVec_eq_zero_of_conj_anti _ _ _
    (manyBodyReversalS_conjTranspose Λ N) hΘΦ hδ
    (manyBodyReversalS_conj_staggeredOrderOpS_cube A)

/-! ### Fixture 3: eq. (3.4.4) at the ring, signature pin -/

/-- Pins `afm_ring_staggeredOrderOpS_odd_moments_vanish`, and in particular that normalisation is
absent from its hypothesis list: only `Φ ≠ 0` and the `finrank ≤ 1` uniqueness datum are needed. -/
example (L N : ℕ) (hLeven : Even L) (hL2 : 2 ≤ L) (hN : 1 ≤ N)
    {Φ : (Fin L → Fin (N + 1)) → ℂ} {E₀ : ℝ} (hΦ_ne : Φ ≠ 0)
    (hΦE : (afmHeisenbergChainHamiltonianS L N).mulVec Φ = (E₀ : ℂ) • Φ)
    (huniq : finrank ℂ ↥(End.eigenspace
        (Matrix.toLin' (afmHeisenbergChainHamiltonianS L N)) (E₀ : ℂ)) ≤ 1) :
    star Φ ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ = 0
      ∧ star Φ ⬝ᵥ ((staggeredOrderOpS (ringStaggeredSublattice L) N) ^ 3).mulVec Φ = 0 :=
  afm_ring_staggeredOrderOpS_odd_moments_vanish L N hLeven hL2 hN hΦ_ne hΦE huniq

/-! ### Fixture 4: fixture 3's declaration applied exactly as its consumer will apply it -/

/-- Pins that eq. (3.4.4)'s ring capstone is fed directly from
`afm_ring_ground_state_data`'s output (`Φ_GS ≠ 0`, the eigenvector equation and the
`finrank ≤ 1` conjunct) — the form in which the eq. (3.4.16) ring instantiation discharges its
`hodd1`/`hodd3` hypotheses. -/
example (L N : ℕ) (hLeven : Even L) (hL2 : 2 ≤ L) (hN : 1 ≤ N) :
    ∃ (E₀ : ℝ) (Φ_GS : (Fin L → Fin (N + 1)) → ℂ),
      IsGroundEnergy (afmHeisenbergChainHamiltonianS L N) E₀ ∧
      Φ_GS ≠ 0 ∧
      (afmHeisenbergChainHamiltonianS L N).mulVec Φ_GS = (E₀ : ℂ) • Φ_GS ∧
      star Φ_GS ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ_GS = 0 ∧
      star Φ_GS ⬝ᵥ ((staggeredOrderOpS (ringStaggeredSublattice L) N) ^ 3).mulVec Φ_GS = 0 := by
  obtain ⟨E₀, Φ_GS, hE, hΦne, hΦE, hfin, _⟩ := afm_ring_ground_state_data L N hLeven hL2 hN
  exact ⟨E₀, Φ_GS, hE, hΦne, hΦE,
    afm_ring_staggeredOrderOpS_odd_moments_vanish L N hLeven hL2 hN hΦne hΦE hfin⟩

/-! ### Fixture 5: eq. (3.4.16) at the ring, signature pin -/

/-- Pins `tasaki_eq_3_4_16_afmRing_ssb_fromGroundState`: no bond decomposition (`B`, `hb`, `W`,
`d`) and no norm bounds (`h₀`, `o₀`, `hnh`, `hno`) are taken as hypotheses. The caller supplies
only the ring size `L`, the spin label `N`, the guards, the ground state and its data (exactly
`afm_ring_ground_state_data`'s witnesses `hE`/`hΦne`/`hΦE`/`hfin` plus its normalisation `hΦ`), and
the long-range-order hypothesis `hLRO`; the generic capstone's own volume guard `1 ≤ L` is derived
from `2 ≤ L` rather than asked for. The instantiation data `d := 1` and the bound values
`h₀ := 3N²`, `o₀ := N/2` are spelled directly into the energy-bound conjunct rather than hidden
inside a proof, so a later change to either ring norm bound breaks this fixture's compilation. -/
example (L N : ℕ) (hLeven : Even L) (hL2 : 2 ≤ L) (hN : 1 ≤ N)
    {E₀ : ℝ} {Φ_GS : (Fin L → Fin (N + 1)) → ℂ}
    (hE : IsGroundEnergy (afmHeisenbergChainHamiltonianS L N) E₀) (hΦne : Φ_GS ≠ 0)
    (hΦE : (afmHeisenbergChainHamiltonianS L N).mulVec Φ_GS = (E₀ : ℂ) • Φ_GS)
    (hfin : finrank ℂ ↥(End.eigenspace
        (Matrix.toLin' (afmHeisenbergChainHamiltonianS L N)) (E₀ : ℂ)) ≤ 1)
    (hΦ : star Φ_GS ⬝ᵥ Φ_GS = 1) (q₀ : ℝ) (hq₀ : 0 < q₀)
    (hLRO : q₀ ≤ rayleighOnVec ((staggeredOrderOpS (ringStaggeredSublattice L) N) ^ 2) Φ_GS
      / ((L : ℝ) ^ (1 : ℕ)) ^ 2) :
    star (hvlPlusState (staggeredOrderOpS (ringStaggeredSublattice L) N) Φ_GS)
        ⬝ᵥ hvlPlusState (staggeredOrderOpS (ringStaggeredSublattice L) N) Φ_GS = 1
    ∧ 0 ≤ rayleighOnVec (∑ x : Fin L, spinSDot x (finRotate L x) N)
        (hvlPlusState (staggeredOrderOpS (ringStaggeredSublattice L) N) Φ_GS) - E₀
    ∧ rayleighOnVec (∑ x : Fin L, spinSDot x (finRotate L x) N)
        (hvlPlusState (staggeredOrderOpS (ringStaggeredSublattice L) N) Φ_GS) - E₀
        ≤ 4 * ((1 : ℕ) : ℝ) * (3 * (N : ℝ) ^ 2) * ((N : ℝ) / 2) ^ 2 / q₀ / (L : ℝ) ^ (1 : ℕ)
    ∧ Real.sqrt q₀ ≤ rayleighOnVec (staggeredOrderOpS (ringStaggeredSublattice L) N)
        (hvlPlusState (staggeredOrderOpS (ringStaggeredSublattice L) N) Φ_GS) / (L : ℝ) ^ (1 : ℕ) :=
  tasaki_eq_3_4_16_afmRing_ssb_fromGroundState L N hLeven hL2 hN hE hΦne hΦE hfin hΦ q₀ hq₀ hLRO

/-! ### Fixture 6: fixture 5's declaration is the generic capstone applied, not a restatement -/

/-- Pins that `tasaki_eq_3_4_16_afmRing_ssb_fromGroundState`'s statement is *definitionally* the
generic capstone `tasaki_eq_3_4_16_lowLyingState_ssb`'s statement at the ring's own bond
decomposition (`B := Finset.univ`, `hb x := spinSDot x (finRotate L x) N`,
`W x := {x, finRotate L x}`, `d := 1`) and ring norm bounds (`h₀ := 3N²`, `o₀ := N/2`), closed by
`rfl`: both sides are proofs of propositions, so proof irrelevance reduces the equation to a
definitional-equality check on the two statements. A green compile means that check accepted them;
a red one means only that it did not, the check being budgeted (module doc, "What the `rfl` pin
guarantees"). The extra hypotheses below
(`hH`/`hO`/`hW`/`hoo`/`hnh`/`hno`/`hbond`/`hB`/`hΦE'`/`hmin`/`hodd1`/`hodd3`) are *fixture-only*
stand-ins for what the real declaration
derives from the ground-state data via `heisenbergHamiltonianS_ringCoupling_eq_bondSum_general`,
`onSiteS_commute_of_ne`, `spinSDot_commutator_onSiteS_spinSOp3_eq_zero_of_ne`,
`spinSDot_manyBodyOperatorNormS_le`, `onSiteS_spinSOp3_manyBodyOperatorNormS_le` and
`hermitianMinEigenvalue_le_rayleighOnVec_of_unit`: this fixture pins the *shape* of the reduction,
so drift in either statement's conjunct order, hypothesis list or printed constants breaks
compilation here. -/
example (L N : ℕ) (hLeven : Even L) (hL2 : 2 ≤ L) (hN : 1 ≤ N)
    {E₀ : ℝ} {Φ_GS : (Fin L → Fin (N + 1)) → ℂ}
    (hE : IsGroundEnergy (afmHeisenbergChainHamiltonianS L N) E₀) (hΦne : Φ_GS ≠ 0)
    (hΦE : (afmHeisenbergChainHamiltonianS L N).mulVec Φ_GS = (E₀ : ℂ) • Φ_GS)
    (hfin : finrank ℂ ↥(End.eigenspace
        (Matrix.toLin' (afmHeisenbergChainHamiltonianS L N)) (E₀ : ℂ)) ≤ 1)
    (hΦ : star Φ_GS ⬝ᵥ Φ_GS = 1) (q₀ : ℝ) (hq₀ : 0 < q₀) (hL : 1 ≤ L)
    (hLRO : q₀ ≤ rayleighOnVec ((staggeredOrderOpS (ringStaggeredSublattice L) N) ^ 2) Φ_GS
      / ((L : ℝ) ^ (1 : ℕ)) ^ 2)
    (hH : (∑ x : Fin L, spinSDot x (finRotate L x) N).IsHermitian)
    (hO : (∑ x : Fin L,
        (if ringStaggeredSublattice L x then (1 : ℂ) else -1) • spinSSiteOp3 x N).IsHermitian)
    (hW : ∀ b ∈ (Finset.univ : Finset (Fin L)), ∀ z ∉ ({b, finRotate L b} : Finset (Fin L)),
      Commute (spinSDot b (finRotate L b) N)
        ((if ringStaggeredSublattice L z then (1 : ℂ) else -1) • spinSSiteOp3 z N))
    (hoo : ∀ x z : Fin L, x ≠ z → Commute
      ((if ringStaggeredSublattice L x then (1 : ℂ) else -1) • spinSSiteOp3 x N)
      ((if ringStaggeredSublattice L z then (1 : ℂ) else -1) • spinSSiteOp3 z N))
    (hnh : ∀ b ∈ (Finset.univ : Finset (Fin L)),
      manyBodyOperatorNormS (spinSDot b (finRotate L b) N) ≤ 3 * (N : ℝ) ^ 2)
    (hno : ∀ x : Fin L, manyBodyOperatorNormS
      ((if ringStaggeredSublattice L x then (1 : ℂ) else -1) • spinSSiteOp3 x N) ≤ (N : ℝ) / 2)
    (hbond : ∀ b ∈ (Finset.univ : Finset (Fin L)),
      ({b, finRotate L b} : Finset (Fin L)).card ≤ 2)
    (hB : ((Finset.univ : Finset (Fin L)).card : ℝ) ≤ ((1 : ℕ) : ℝ) * (L : ℝ) ^ (1 : ℕ))
    (hΦE' : (∑ x : Fin L, spinSDot x (finRotate L x) N).mulVec Φ_GS = (E₀ : ℂ) • Φ_GS)
    (hmin : ∀ v : (Fin L → Fin (N + 1)) → ℂ, star v ⬝ᵥ v = 1 →
      E₀ ≤ rayleighOnVec (∑ x : Fin L, spinSDot x (finRotate L x) N) v)
    (hodd1 : star Φ_GS ⬝ᵥ Matrix.mulVec
      (∑ x : Fin L, (if ringStaggeredSublattice L x then (1 : ℂ) else -1) • spinSSiteOp3 x N)
      Φ_GS = 0)
    (hodd3 : star Φ_GS ⬝ᵥ Matrix.mulVec
      ((∑ x : Fin L, (if ringStaggeredSublattice L x then (1 : ℂ) else -1) • spinSSiteOp3 x N) ^ 3)
      Φ_GS = 0) :
    tasaki_eq_3_4_16_afmRing_ssb_fromGroundState L N hLeven hL2 hN hE hΦne hΦE hfin hΦ q₀ hq₀ hLRO
    = tasaki_eq_3_4_16_lowLyingState_ssb (Finset.univ : Finset (Fin L))
        (fun x => spinSDot x (finRotate L x) N)
        (fun x => (if ringStaggeredSublattice L x then (1 : ℂ) else -1) • spinSSiteOp3 x N)
        (fun x => ({x, finRotate L x} : Finset (Fin L))) 1 L q₀ (3 * (N : ℝ) ^ 2) ((N : ℝ) / 2)
        hH hO hW hoo hnh hno (by positivity) (by positivity) hbond hB hΦ hΦE' hmin hodd1 hodd3
        hq₀ hL hLRO :=
  rfl

end LatticeSystem.Tests.Corollary43RingSetup
