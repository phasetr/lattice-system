import LatticeSystem.Quantum.SpinS.SPTMatrixProductIndex

/-!
# Tasaki §8.3.5: a Lieb–Schultz–Mattis-type theorem without continuous symmetry (Theorem 8.6)

The matrix-product no-go of §8.3.4 (Corollary 8.5) suggests a general **Lieb–Schultz–Mattis-type
theorem**.  Unlike the original LSM theorem (§6.2), which relies essentially on the continuous
`U(1)`
symmetry, the following statement needs only a *discrete* symmetry:

**Theorem 8.6** (Ogata–Tasaki): a quantum spin chain with **half-odd-integer** spin (`S = N/2` with
`N` odd) and a **short-ranged, translation-invariant** Hamiltonian that has **either Z₂ × Z₂
symmetry or time-reversal symmetry** can never have a ground state that is *both* unique *and*
accompanied by a nonzero energy gap.

Heuristically: a unique gapped ground state inherits the symmetry of the Hamiltonian and (having
short-range correlations) is approximable by a symmetric injective matrix product state, which
Corollary 8.5 forbids for half-odd-integer spin.  Making this rigorous needs strong control over
matrix-product approximation; Ogata and Tasaki instead gave a fully rigorous proof via the Cuntz
algebra of a pure state with the split property (building on Matsui), with no MPS approximation.

All predicates here (translation invariance, short range, the two symmetries, and the unique-gapped
ground state) are honest uninterpreted markers (their faithful forms live in the infinite-chain
operator-algebra framework); Theorem 8.6 is a documented axiom.  The conclusion is the negation of
the bundled "unique gapped ground state" marker — the no-go statement.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.3.5, Theorem 8.6, pp. 276–280; Y. Ogata, H. Tasaki, Commun. Math. Phys. **372**, 951
(2019); T. Matsui, Rev. Math. Phys. **13**, 1349 (2001).
-/

namespace LatticeSystem.Quantum

open Matrix

/-- **Translation-invariance marker** `IsTranslationInvariantS H`: the Hamiltonian `H` is invariant
under the chain translation.  An uninterpreted predicate. -/
axiom IsTranslationInvariantS {L N : ℕ} : ManyBodyOpS (Fin L) N → Prop

/-- **Short-range marker** `HasShortRangeHamiltonianS H`: the Hamiltonian `H` is a sum of local
terms
of bounded range.  An uninterpreted predicate (general-spin analogue of
`HasShortRangeInteraction`). -/
axiom HasShortRangeHamiltonianS {L N : ℕ} : ManyBodyOpS (Fin L) N → Prop

/-- **Z₂ × Z₂ symmetry marker** `IsZ2Z2SymmetricS H` for a general spin chain: `H` is invariant
under
the π-rotations about two spin axes.  An uninterpreted predicate. -/
axiom IsZ2Z2SymmetricS {L N : ℕ} : ManyBodyOpS (Fin L) N → Prop

/-- **Time-reversal symmetry marker** `IsTimeReversalSymmetricS H` for a general spin chain: `H` is
invariant under the antiunitary time-reversal `Θ̂`.  An uninterpreted predicate. -/
axiom IsTimeReversalSymmetricS {L N : ℕ} : ManyBodyOpS (Fin L) N → Prop

/-- **Unique-gapped-ground-state marker** `HasUniqueGappedGroundStateS H`: the Hamiltonian `H` has a
ground state that is both unique and accompanied by a nonvanishing energy gap.  An uninterpreted
predicate; its negation is the conclusion of the no-go Theorem 8.6. -/
axiom HasUniqueGappedGroundStateS {L N : ℕ} : ManyBodyOpS (Fin L) N → Prop

/-- **Tasaki Theorem 8.6 (discrete-symmetry Lieb–Schultz–Mattis no-go, Ogata–Tasaki), AXIOM.**  For
a
chain of **half-odd-integer** spin (`S = N/2` with `N` odd) with a short-ranged,
translation-invariant
Hamiltonian `H` that has **either Z₂ × Z₂ or time-reversal symmetry**, the ground state can
**never**
be both unique and gapped: `¬ HasUniqueGappedGroundStateS H`.  Unlike the original LSM theorem
(§6.2,
which uses the continuous `U(1)` symmetry), this needs only a discrete symmetry.  Proved rigorously
by
Ogata and Tasaki via the Cuntz algebra / split-property analysis; recorded as a documented axiom. -/
axiom tasaki_theorem_8_6 {L N : ℕ} (hN : Odd N) (H : ManyBodyOpS (Fin L) N)
    (hSR : HasShortRangeHamiltonianS H) (hTI : IsTranslationInvariantS H)
    (hSym : IsZ2Z2SymmetricS H ∨ IsTimeReversalSymmetricS H) :
    ¬ HasUniqueGappedGroundStateS H

end LatticeSystem.Quantum
