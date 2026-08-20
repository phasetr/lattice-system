import LatticeSystem.Quantum.SpinS.MultiSiteCore

/-!
# Tasaki §8.3.2–§8.3.3: protecting symmetries and "topological" indices for SPT phases

Different SPT phases cannot be told apart by any local order parameter (there is no symmetry
breaking).  The Haldane phase is protected by any one of three symmetries:

* **(S1) Z₂ × Z₂** — the π-rotations about the spin axes (`IsZ2Z2Invariant`);
* **(S2) time-reversal** `Θ̂` (`IsTimeReversalInvariant`);
* **(S3) bond-centered inversion** `Û_inv` (`IsBondInversionInvariant`).

A clean characterization uses **"topological" indices** of the ground-state entanglement, invariant
under continuous symmetric deformation.  The simplest is the **inversion parity**: for the spin-`S`
VBS state on an `L`-site ring, `Û_inv |Φ_VBS^S⟩ = (−1)^{L·S} |Φ_VBS^S⟩`.  When `L·S` is odd the VBS
state has *odd* parity and cannot be continuously connected to the *even*-parity trivial state, so
it is a nontrivial SPT.  At `S = 1` the inversion operator, the parity identity and the
odd-`L` contrast with the trivial product state are proved in `VBSInversionParity.lean`; general
`S` is not covered there, since the library has no general-`S` VBS state to apply `Û_inv` to
(see the "General-`S` bond-inversion parity" entry of
`docs/limitations/documented-axioms/chapter-08-part-02.md`).
More generally the book
states as a *belief* — not as a
theorem — that the spin-`S` VBS is a nontrivial SPT phase (protected by (S1), (S2), or (S3))
exactly when `S` is odd, the even-`S` side being trivial; that belief is not formalized here
(same ledger).

The general "topological" indices arise from the **Schmidt decomposition** of the infinite-chain
ground state `|Φ_GS⟩ = Σ_j √p_j |Φ_j⟩_L ⊗ |Ψ_j⟩_R` (eq. (8.3.7)), the reduced density matrix
`ρ̂_R = Σ_j p_j |Ψ_j⟩_R ⟨Ψ_j|` (eq. (8.3.8)), and the **entanglement entropy**
`S_LR = −Σ_j p_j log p_j` (`entanglementEntropyS`).  This section is heuristic; the precise
definitions for matrix product states are in §8.3.4 and Ogata's rigorous infinite-chain indices in
§8.3.6.

The protecting symmetries and the entanglement entropy are uninterpreted markers (the antiunitary
time reversal and the half-infinite-chain Schmidt decomposition belong to the operator-algebra
framework).  The (S2) marker `IsTimeReversalInvariant` below has the same type and meaning as the
`N = 2` instance of the general-`N` `IsTimeReversalSymmetricS` (`LiebSchultzMattisDiscrete.lean`);
this module does not import that file, so the cross-reference is prose inside a doc comment, not a
Lean consumer relation.

The (S3) geometry is *not* missing any more: the bond-centered inversion is the site map
`x ↦ L − 1 − x`, i.e. `Fin.rev`, which is total and involutive on every `Fin L` and fixes the bond
`{L − 1, 0}` setwise, so it is bond-centered for odd and even `L` alike (for odd `L` it fixes in
addition the single site `(L − 1) / 2`, as every reflection of an odd cycle does).  Its
configuration action and permutation operator `Û_inv` are `bondInversionConfigS` /
`bondInversionUnitaryS` (`VBSInversionParity.lean`); on `Fin (2 * n)` the same map is the even-ring
`ringReflect` (`RingBondReflection.lean`) with its action `ringConfigReflect`
(`RingReflectionTheta.lean`).  All of these differ from the on-site spin reversal
`Θ = manyBodyReversalS` (`ManyBodyReversalS.lean`), which reverses each site's spin index
(`σ ↦ Fin.rev ∘ σ`) and leaves the sites in place.  None of those modules is imported here, since
the (S3) predicate below is a marker with no consumer.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.3.2–§8.3.3, eqs. (8.3.6)–(8.3.10), pp. 256–263; F. Pollmann, A. M. Turner, E. Berg, M.
Oshikawa, Phys. Rev. B **81**, 064439 (2010); Phys. Rev. B **85**, 075125 (2012).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {L : ℕ}

/-- **(S2) Time-reversal symmetry marker** `IsTimeReversalInvariant H`: the Hamiltonian `H` is
invariant under the antiunitary time-reversal `Θ̂`.  A faithful definition needs the antiunitary
operator; kept as an uninterpreted predicate.  Its type and meaning coincide with the `N = 2`
instance of the general-`N` `IsTimeReversalSymmetricS` (`LiebSchultzMattisDiscrete.lean`), so the
pair is a genuine duplicate and not a deliberate scope split; consolidating it would delete a
declaration, which is a separately approved decision that has not been taken, so the two are
recorded here as knowingly parallel markers. -/
axiom IsTimeReversalInvariant (H : ManyBodyOpS (Fin L) 2) : Prop

/-- **(S3) Bond-centered inversion symmetry marker** `IsBondInversionInvariant H`: the Hamiltonian
`H` is invariant under the bond-centered spatial inversion `Û_inv`, i.e. `Û_inv H Û_inv = H` for
the operator `bondInversionUnitaryS` of `VBSInversionParity.lean`.  It is kept as an uninterpreted
predicate because no result consumes it yet: concretizing it needs a site-permutation conjugation
lemma for `onSiteS` / `spinSDot` and invariance of `ringCoupling` under `Fin.rev`, which is a unit
of work of its own. -/
axiom IsBondInversionInvariant (H : ManyBodyOpS (Fin L) 2) : Prop

/-- The **bipartite entanglement entropy** `S_LR = −Σ_j p_j log p_j` of a chain state, from the
Schmidt weights `p_j` of the left/right bipartition (eqs. (8.3.7)–(8.3.8)).  The half-infinite-chain
Schmidt decomposition / partial trace / von Neumann entropy is recorded as an uninterpreted
real-valued marker. -/
axiom entanglementEntropyS {L N : ℕ} : ((Fin L → Fin (N + 1)) → ℂ) → ℝ

end LatticeSystem.Quantum
