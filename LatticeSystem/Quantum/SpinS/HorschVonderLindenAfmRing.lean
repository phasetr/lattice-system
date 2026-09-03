/-
Tasaki §3.4's general setting for low-lying states and SSB, read at the one-dimensional
antiferromagnetic Heisenberg ring of §6.1, eq. (6.1.1), p. 153.

Two pieces are recorded here.  First, the no-SSB condition (3.4.4), p. 65, holds at the ring: the
many-body spin reversal `Θ` fixes the ring Heisenberg Hamiltonian and reverses the staggered order
operator `Ô_L^{(3)}`, so on a ground state spanning a one-dimensional eigenspace — the
Marshall–Lieb–Mattis situation Tasaki invokes in the proof of Corollary 4.3, p. 77 — both odd
moments `⟨Φ_GS|Ô_L|Φ_GS⟩` and `⟨Φ_GS|(Ô_L)³|Φ_GS⟩` vanish.  This is footnote 21 of p. 65 with
`Û := Θ`.  Second, eq. (3.4.16), p. 68, is read at the ring by instantiating the generic capstone
`tasaki_eq_3_4_16_lowLyingState_ssb` at `Λ := Fin L`, at the ring's staggered per-site term
`ô_x = (-1)^x Ŝ_x^{(3)}` — whose sum over the ring is definitionally
`staggeredOrderOpS (ringStaggeredSublattice L)` — and at the ring's own bond decomposition and norm
bounds, so that the caller supplies only the ring's ground-state data, the normalisation of that
state and the long-range-order assumption (3.4.3).

Nothing here discharges a documented axiom or strengthens an existing statement; it supplies the
two order-operator inputs that a §4.1 Corollary 4.3 assembly needs.

This file is the only non-`Tests` importer of `Quantum/SpinS/ShastryNoSSBReduction.lean`, which it
uses for `staggeredFieldChainHamiltonianS_conj_manyBodyReversalS`.  The library root lists only the
tips of the non-`Tests` import DAG, so that file has no line of its own there, and root coverage of
it — hence of `shastry_no_symmetry_breaking_1d` and of its documented axiom `shastryEnergyGain` —
runs through the import below.  Removing that import means giving that file a root line of its own.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, eqs. (3.4.1)-(3.4.4) and footnote 21, p. 65, eqs. (3.4.14)-(3.4.16), p. 68; §4.1,
eq. (4.1.9), p. 76, Corollary 4.3, p. 77; §6.1, eq. (6.1.1), p. 153.
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerTanakaMoments
import LatticeSystem.Quantum.SpinS.HaldaneConjecture
import LatticeSystem.Quantum.SpinS.RingBondSumGeneral
import LatticeSystem.Quantum.SpinS.SingleBondSpinSOp3Commutator
import LatticeSystem.Quantum.SpinS.ShastryNoSSBReduction
import LatticeSystem.Math.MatrixAnalysis.UniqueEigenspaceInvolution
import LatticeSystem.Quantum.HorschVonderLindenLowLyingState

namespace LatticeSystem.Quantum

open Matrix Module

/-! ### The zero-field bridge between the §4.1 and §6.1 spellings of the ring Hamiltonian -/

/-- **The staggered-field ring Hamiltonian at zero field is the antiferromagnetic Heisenberg ring
Hamiltonian**: `Ĥ_0 = Σ_x Ŝ_x · Ŝ_{x+1}`.  Putting `h = 0` in eq. (4.1.9), p. 76, kills the
staggered Zeeman term `-(-1)^x h Ŝ_x^{(3)}` and leaves eq. (6.1.1), p. 153.

The two spellings are not syntactically equal — recovering the Heisenberg part needs `zero_smul`
and `sub_zero` — so every argument that reads a §4.1 statement (quantified over
`staggeredFieldChainHamiltonianS L 0 N`) against §6.2's ring ground-state data (stated for
`afmHeisenbergChainHamiltonianS L N`) has to pass through this identification.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, eq. (4.1.9), p. 76; §6.1, eq. (6.1.1), p. 153. -/
theorem staggeredFieldChainHamiltonianS_zero_eq_afmHeisenberg (L N : ℕ) :
    staggeredFieldChainHamiltonianS L 0 N = afmHeisenbergChainHamiltonianS L N := by
  rw [staggeredFieldChainHamiltonianS, afmHeisenbergChainHamiltonianS, Complex.ofReal_zero,
    zero_smul, sub_zero]

/-! ### The no-SSB condition (3.4.4) at the antiferromagnetic ring -/

/-- **Tasaki's no-SSB condition (3.4.4), p. 65, at the antiferromagnetic Heisenberg ring**: a
non-zero ground state `Φ` of `Ĥ = Σ_x Ŝ_x · Ŝ_{x+1}` (eq. (6.1.1), p. 153) whose energy eigenspace
is at most one-dimensional has vanishing odd staggered moments,
`⟨Φ|Ô_L^{(3)}|Φ⟩ = ⟨Φ|(Ô_L^{(3)})³|Φ⟩ = 0`.

This is footnote 21 of p. 65 at `Û := Θ`, the many-body spin reversal: `Θ` commutes with the
Hamiltonian (eq. (4.1.9), p. 76, at `h = 0`, through
`staggeredFieldChainHamiltonianS_zero_eq_afmHeisenberg`) and reverses the order operator and its
cube, while uniqueness of the eigenspace forces `Θ Φ = δ Φ` with `δ = ±1`, so each odd moment
equals its own negative.  It is the input Tasaki's proof of Corollary 4.3, p. 77, gets from the
Marshall–Lieb–Mattis theorem.

Normalisation of `Φ` is deliberately not assumed: the sign extraction and the sandwich argument
need only `Φ ≠ 0`.  The guards `Even L`, `2 ≤ L`, `1 ≤ N` are carried unused (hence underscored) to
record the regime in which `afm_ring_ground_state_data` actually supplies the three hypotheses —
uniqueness of the ground state is proved only for the even, connected-bipartite ring.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, eq. (3.4.4) and footnote 21, p. 65; §4.1, Corollary 4.3, p. 77; §6.1, eq. (6.1.1),
p. 153. -/
theorem afm_ring_staggeredOrderOpS_odd_moments_vanish (L N : ℕ)
    (_hLeven : Even L) (_hL2 : 2 ≤ L) (_hN : 1 ≤ N)
    {Φ : (Fin L → Fin (N + 1)) → ℂ} {E₀ : ℝ} (hΦ_ne : Φ ≠ 0)
    (hΦE : (afmHeisenbergChainHamiltonianS L N).mulVec Φ = (E₀ : ℂ) • Φ)
    (huniq : finrank ℂ ↥(End.eigenspace
        (Matrix.toLin' (afmHeisenbergChainHamiltonianS L N)) (E₀ : ℂ)) ≤ 1) :
    star Φ ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ = 0
      ∧ star Φ ⬝ᵥ ((staggeredOrderOpS (ringStaggeredSublattice L) N) ^ 3).mulVec Φ = 0 := by
  have hconj : manyBodyReversalS (Fin L) N * afmHeisenbergChainHamiltonianS L N
      * manyBodyReversalS (Fin L) N = afmHeisenbergChainHamiltonianS L N := by
    have h := staggeredFieldChainHamiltonianS_conj_manyBodyReversalS L 0 N
    rwa [neg_zero, staggeredFieldChainHamiltonianS_zero_eq_afmHeisenberg] at h
  have hcomm : afmHeisenbergChainHamiltonianS L N * manyBodyReversalS (Fin L) N
      = manyBodyReversalS (Fin L) N * afmHeisenbergChainHamiltonianS L N := by
    have h3 : manyBodyReversalS (Fin L) N * afmHeisenbergChainHamiltonianS L N
        * manyBodyReversalS (Fin L) N * manyBodyReversalS (Fin L) N
        = afmHeisenbergChainHamiltonianS L N * manyBodyReversalS (Fin L) N :=
      congrArg (· * manyBodyReversalS (Fin L) N) hconj
    rw [mul_assoc (manyBodyReversalS (Fin L) N * afmHeisenbergChainHamiltonianS L N),
      manyBodyReversalS_mul_self, mul_one] at h3
    exact h3.symm
  obtain ⟨δ, hΘΦ, hδ2⟩ := LatticeSystem.Math.exists_involution_eigenvalue_of_unique_eigenspace
    (afmHeisenbergChainHamiltonianS L N) (manyBodyReversalS (Fin L) N) (E₀ : ℂ) huniq hΦ_ne hΦE
    hcomm (manyBodyReversalS_mul_self (Fin L) N)
  -- `δ * δ̄ = 1` from `δ² = 1` (`δ = ±1`, both of unit modulus).
  have hδ : δ * star δ = 1 := by
    have hself : δ * δ = 1 := by rw [← pow_two]; exact hδ2
    rcases mul_self_eq_one_iff.mp hself with h1 | h1
    · rw [h1, star_one, mul_one]
    · rw [h1, star_neg, star_one, neg_mul_neg, mul_one]
  exact ⟨dotProduct_mulVec_eq_zero_of_conj_anti _ _ _
      (manyBodyReversalS_conjTranspose (Fin L) N) hΘΦ hδ
      (manyBodyReversalS_conj_staggeredOrderOpS (ringStaggeredSublattice L)),
    dotProduct_mulVec_eq_zero_of_conj_anti _ _ _
      (manyBodyReversalS_conjTranspose (Fin L) N) hΘΦ hδ
      (manyBodyReversalS_conj_staggeredOrderOpS_cube (ringStaggeredSublattice L))⟩

/-! ### Eq. (3.4.16) at the antiferromagnetic ring -/

/-- **Tasaki eq. (3.4.16), p. 68, at the antiferromagnetic Heisenberg ring, with the Hamiltonian
side instantiated.**  For a normalised ground state `Φ_GS` of `Ĥ = Σ_x Ŝ_x · Ŝ_{x+1}`
(eq. (6.1.1), p. 153) whose energy eigenspace is at most one-dimensional and which carries staggered
long-range order (eq. (3.4.3), p. 65), the state `Ξ₊` of eq. (3.4.14), p. 68, is normalised, lies
between `E_GS` and `E_GS + (C/2) L^{-1}` in energy, and satisfies
`⟨Ξ₊|Ô_L/L|Ξ₊⟩ ≥ √q₀`, which is eq. (3.4.16).

The bond decomposition and the norm bounds of eqs. (3.4.1)-(3.4.2), p. 65, are fixed at the ring:
the bond set is all of `Fin L` with `ĥ_x = Ŝ_x · Ŝ_{x+1}` supported on `{x, x+1}`, the dimension is
`d = 1`, and the two norms of p. 65 are carried at the *bound* values `h₀ = 3N²` and `o₀ = N/2`.
Tasaki defines `h₀` and `o₀` by equality on p. 65; what is available here are upper bounds — the
ones `spinSDot_manyBodyOperatorNormS_le` and `onSiteS_spinSOp3_manyBodyOperatorNormS_le` prove at
spin `S = N/2` — and `3N²` in particular is not tight, since that bound loosens `S ≤ N` inside a
three-term sum.  Only the bound direction is used, and both values are spelled into the energy
conjunct rather than hidden in the proof.

The caller supplies exactly the ground-state data `afm_ring_ground_state_data` produces (`hE`,
`hΦne`, `hΦE`, `hfin`), the normalisation `hΦ`, and the long-range-order assumption (3.4.3)
(`hq₀`, `hLRO`), under the guards `Even L`, `2 ≤ L`, `1 ≤ N` that supplier itself requires.
Everything the generic capstone additionally asks for is derived here: its volume guard `1 ≤ L`
(from `2 ≤ L`); the bond decomposition
(`heisenbergHamiltonianS_ringCoupling_eq_bondSum_general`) and with it Hermiticity of `Ĥ` and the
eigenvector equation in bond-sum form; Hermiticity of `Ô_L`; the locality of the bonds against the
order terms (`spinSDot_commutator_onSiteS_spinSOp3_eq_zero_of_ne`) and of the order terms against
each other (`onSiteS_commute_of_ne`); both norm bounds; the bond and volume counts; the variational
minimality of `E_GS` (via `exists_nonzero_eigenvector_hermitianMinEigenvalue` and
`hermitianMinEigenvalue_le_rayleighOnVec_of_unit`); and the two odd moments (3.4.4)
(`afm_ring_staggeredOrderOpS_odd_moments_vanish`).

Normalisation is genuinely an assumption, not an omission: `afm_ring_ground_state_data` delivers
only `Φ_GS ≠ 0`, and `⟨Ξ₊|Ξ₊⟩ = 1` fails for an unnormalised `Φ_GS`, so it cannot be derived for the
given vector.  Tasaki assumes it too, on p. 65 ("`|Φ_GS⟩` is a normalized ground state").

The two energy conjuncts are spelled with the bond sum `Σ_x Ŝ_x · Ŝ_{x+1}` while the hypotheses are
spelled with `afmHeisenbergChainHamiltonianS L N`.  The two agree only through
`heisenbergHamiltonianS_ringCoupling_eq_bondSum_general`, not definitionally, and the bond-sum
spelling is what makes this statement *be* the generic capstone's own statement at the ring data —
the property `Tests/Corollary43RingSetup.lean` pins by `rfl`.  Restating the energy conjuncts over
`afmHeisenbergChainHamiltonianS` makes the two sides different propositions and that fixture stops
compiling; at the default heartbeat budget Lean reports the type mismatch with its explanation
replaced by a deterministic `whnf` timeout, so the message has to be read as "the check did not
accept", not as a printed diff.  A caller wanting that spelling rewrites with the same lemma.

This instantiation is deliberately outside the book's own example range.  Tasaki lists the
antiferromagnetic Heisenberg model as an example of the §3.4 setting on p. 65 only on the
`d`-dimensional hypercubic lattice with `d ≥ 2`; here the setting is read at `d = 1`, where
assumption (3.4.3) is expected to be false — that failure is exactly Corollary 4.3, p. 77
(eq. (4.1.11), the staggered order parameter per site vanishing on the ring in the thermodynamic
limit), which `no_long_range_order_1d` carries conditionally on a documented axiom.  The
contradiction is the point of reading §3.4's machinery here: assuming (3.4.3) at the ring buys
low-lying states within `O(1/L)` of the ground energy.  Nothing is thereby asserted unconditionally
at `d = 1` — every conclusion below is conditional on `hLRO`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, eqs. (3.4.1)-(3.4.4), p. 65 (the `d ≥ 2` example range on that page) and
eqs. (3.4.14)-(3.4.16), p. 68; §4.1, Corollary 4.3 and eq. (4.1.11), p. 77; §6.1, eq. (6.1.1),
p. 153. -/
theorem tasaki_eq_3_4_16_afmRing_ssb_fromGroundState (L N : ℕ)
    (hLeven : Even L) (hL2 : 2 ≤ L) (hN : 1 ≤ N)
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
        (hvlPlusState (staggeredOrderOpS (ringStaggeredSublattice L) N) Φ_GS)
        / (L : ℝ) ^ (1 : ℕ) := by
  haveI : NeZero L := ⟨by omega⟩
  have hbond : afmHeisenbergChainHamiltonianS L N
      = ∑ x : Fin L, spinSDot x (finRotate L x) N := by
    rw [afmHeisenbergChainHamiltonianS]
    exact heisenbergHamiltonianS_ringCoupling_eq_bondSum_general L N
  have hH : (∑ x : Fin L, spinSDot x (finRotate L x) N).IsHermitian := by
    rw [← hbond]; exact afmHeisenbergChainHamiltonianS_isHermitian L N
  have hHloc : ∀ b ∈ (Finset.univ : Finset (Fin L)),
      ∀ z ∉ ({b, finRotate L b} : Finset (Fin L)),
      Commute (spinSDot b (finRotate L b) N)
        ((if ringStaggeredSublattice L z then (1 : ℂ) else -1) • spinSSiteOp3 z N) := by
    intro b _ z hz
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    refine Commute.smul_right ?_ _
    rw [spinSSiteOp3_def]
    exact sub_eq_zero.mp
      (spinSDot_commutator_onSiteS_spinSOp3_eq_zero_of_ne hz.1 hz.2 N)
  have hoo : ∀ x z : Fin L, x ≠ z →
      Commute ((if ringStaggeredSublattice L x then (1 : ℂ) else -1) • spinSSiteOp3 x N)
        ((if ringStaggeredSublattice L z then (1 : ℂ) else -1) • spinSSiteOp3 z N) := by
    intro x z hxz
    rw [spinSSiteOp3_def, spinSSiteOp3_def]
    exact ((onSiteS_commute_of_ne hxz (spinSOp3 N) (spinSOp3 N)).smul_left _).smul_right _
  have hno : ∀ x : Fin L, manyBodyOperatorNormS
      ((if ringStaggeredSublattice L x then (1 : ℂ) else -1) • spinSSiteOp3 x N)
      ≤ (N : ℝ) / 2 := by
    intro x
    rw [manyBodyOperatorNormS_smul, spinSSiteOp3_def,
      show ‖(if ringStaggeredSublattice L x then (1 : ℂ) else -1)‖ = 1 from by
        split_ifs <;> simp, one_mul]
    exact onSiteS_spinSOp3_manyBodyOperatorNormS_le x
  have hmin : ∀ v : (Fin L → Fin (N + 1)) → ℂ, star v ⬝ᵥ v = 1 →
      E₀ ≤ rayleighOnVec (∑ x : Fin L, spinSDot x (finRotate L x) N) v := by
    intro v hv
    rw [← hbond]
    obtain ⟨w, hw0, hweig⟩ := exists_nonzero_eigenvector_hermitianMinEigenvalue
      (afmHeisenbergChainHamiltonianS_isHermitian L N)
    exact le_trans (hE.2 _ ⟨w, hw0, hweig⟩)
      (hermitianMinEigenvalue_le_rayleighOnVec_of_unit
        (afmHeisenbergChainHamiltonianS_isHermitian L N) hv)
  obtain ⟨hodd1, hodd3⟩ :=
    afm_ring_staggeredOrderOpS_odd_moments_vanish L N hLeven hL2 hN hΦne hΦE hfin
  exact tasaki_eq_3_4_16_lowLyingState_ssb (Finset.univ : Finset (Fin L))
    (fun x => spinSDot x (finRotate L x) N)
    (fun x => (if ringStaggeredSublattice L x then (1 : ℂ) else -1) • spinSSiteOp3 x N)
    (fun x => ({x, finRotate L x} : Finset (Fin L))) 1 L q₀ (3 * (N : ℝ) ^ 2) ((N : ℝ) / 2)
    hH (staggeredOrderOpS_isHermitian (ringStaggeredSublattice L) N) hHloc hoo
    (fun b _ => spinSDot_manyBodyOperatorNormS_le b (finRotate L b) hN) hno
    (by positivity) (by positivity)
    (fun b _ => by simpa using Finset.card_insert_le b ({finRotate L b} : Finset (Fin L)))
    (by simp) hΦ (by rw [← hbond]; exact hΦE) hmin hodd1 hodd3 hq₀ (by omega) hLRO

end LatticeSystem.Quantum
