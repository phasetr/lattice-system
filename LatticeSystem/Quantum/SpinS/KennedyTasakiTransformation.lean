import LatticeSystem.Quantum.SpinS.AnisotropicLargeD

/-!
# Tasaki §8.2.2–§8.2.3: the Kennedy–Tasaki transformation and Proposition 8.4

The picture of **hidden Z₂ × Z₂ symmetry breaking** in the Haldane phase is made precise by the
**Kennedy–Tasaki transformation**, the non-local unitary (eq. (8.2.5))
`Û_KT = ∏_{u < v} exp(iπ Ŝ_u^{(3)} Ŝ_v^{(1)})`,
written in this concise form by Oshikawa.  The commuting factors each square to the identity, so
`Û_KT² = 1` and `Û_KT = Û_KT†` (a self-adjoint involution).  Conjugating by `Û_KT` turns the
*hidden*
antiferromagnetic order of the Haldane phase into *manifest* Z₂ × Z₂ symmetry breaking.

The relevant symmetry is **Z₂ × Z₂**: the three π-rotations `Û_π^{(α)} = ∏_x exp(iπ Ŝ_x^{(α)})`
about the spin axes (any two generate the group).  A Hamiltonian is Z₂ × Z₂ invariant when
`(Û_π^{(α)})† Ĥ Û_π^{(α)} = Ĥ` for `α = 1, 2, 3`.

**Proposition 8.4** (Pollmann–Turner–Berg–Oshikawa): for an `S = 1` open chain `Ĥ` with short-range
interactions, the transformed Hamiltonian `Û_KT Ĥ Û_KT` again has only short-range interactions
**iff**
`Ĥ` is Z₂ × Z₂ invariant.  So the hidden-symmetry-breaking picture is effective exactly when the
original Hamiltonian has Z₂ × Z₂ symmetry.

The π-rotations and the Z₂ × Z₂ invariance condition are *defined concretely* (via the on-site
matrix
exponentials).  The non-local Kennedy–Tasaki unitary is recorded as an operator with its defining
involutive/self-adjoint properties as documented axioms (its explicit nonlocal exponential product
is
not built), and Proposition 8.4 — together with the short-range-interaction predicate — is a
documented axiom.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.2.2–§8.2.3, Proposition 8.4, eqs. (8.2.5)–(8.2.7), pp. 241–251; T. Kennedy, H. Tasaki,
Commun. Math. Phys. **147**, 431 (1992); F. Pollmann, A. M. Turner, E. Berg, M. Oshikawa, Phys. Rev.
B **81**, 064439 (2010).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {L : ℕ}

/-- The **Kennedy–Tasaki unitary** `Û_KT = ∏_{u < v} exp(iπ Ŝ_u^{(3)} Ŝ_v^{(1)})` (eq. (8.2.5)), the
non-local transformation turning hidden Z₂ × Z₂ symmetry breaking into manifest symmetry breaking.
Its explicit nonlocal exponential product is not built; it is recorded as an operator with the
defining properties `ktUnitaryS_sq` and `ktUnitaryS_selfAdjoint` below. -/
axiom ktUnitaryS (L : ℕ) : ManyBodyOpS (Fin L) 2

/-- **`Û_KT² = 1`** (eq. (8.2.5) ff.): the commuting two-site factors each square to the identity,
so
the Kennedy–Tasaki unitary is an involution. -/
axiom ktUnitaryS_sq (L : ℕ) : ktUnitaryS L * ktUnitaryS L = 1

/-- **`Û_KT = Û_KT†`**: the Kennedy–Tasaki unitary is self-adjoint (hence `Û_KT` and `Û_KT†` may be
used interchangeably). -/
axiom ktUnitaryS_selfAdjoint (L : ℕ) : (ktUnitaryS L).conjTranspose = ktUnitaryS L

/-- The **π-rotation** `Û_π^{(α)} = ∏_x exp(iπ Ŝ_x^{(α)})` about the spin axis `α : Fin 3`: the
product of the on-site π-rotations.  Together the three generate the Z₂ × Z₂ group. -/
noncomputable def piRotationS (L : ℕ) (α : Fin 3) : ManyBodyOpS (Fin L) 2 :=
  (List.ofFn fun x : Fin L =>
    NormedSpace.exp ((Complex.I * (Real.pi : ℂ)) • spinSSiteComponentS α x)).prod

/-- **Z₂ × Z₂ invariance** of a Hamiltonian `H`: `(Û_π^{(α)})† H Û_π^{(α)} = H` for every spin axis
`α = 1, 2, 3`, i.e. `H` commutes with each of the three π-rotations. -/
def IsZ2Z2Invariant (H : ManyBodyOpS (Fin L) 2) : Prop :=
  ∀ α : Fin 3, (piRotationS L α).conjTranspose * H * piRotationS L α = H

/-- **Short-range-interaction marker** `HasShortRangeInteraction H r`: the open-chain Hamiltonian
`H`
is a sum of local terms each acting within range `r`.  A faithful definition needs the local-term
decomposition; it is kept as an uninterpreted predicate (cf. the commutant-form `IsLocalRangeR`). -/
axiom HasShortRangeInteraction (H : ManyBodyOpS (Fin L) 2) (r : ℕ) : Prop

/-- `H` **has some short-range interaction**: it is range-`r` local for some `r`. -/
def HasSomeShortRangeInteraction (H : ManyBodyOpS (Fin L) 2) : Prop :=
  ∃ r : ℕ, HasShortRangeInteraction H r

/-- **Tasaki Proposition 8.4 (Pollmann–Turner–Berg–Oshikawa), AXIOM.**  For an `S = 1` open-chain
Hamiltonian `Ĥ` with short-range interactions, the Kennedy–Tasaki-transformed Hamiltonian
`Û_KT Ĥ Û_KT` again has only short-range interactions **iff** `Ĥ` is Z₂ × Z₂ invariant.  Thus the
hidden Z₂ × Z₂ symmetry-breaking picture is effective exactly when the original Hamiltonian has
Z₂ × Z₂ symmetry.  Recorded as a documented axiom. -/
axiom tasaki_prop_8_4 (H : ManyBodyOpS (Fin L) 2) (hH : HasSomeShortRangeInteraction H) :
    HasSomeShortRangeInteraction (ktUnitaryS L * H * ktUnitaryS L) ↔ IsZ2Z2Invariant H

end LatticeSystem.Quantum
