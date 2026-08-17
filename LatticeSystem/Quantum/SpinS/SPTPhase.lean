import LatticeSystem.Quantum.SpinS.AnisotropicLargeD

/-!
# Tasaki §8.3.1–§8.3.2: symmetry protected topological (SPT) phases

The Haldane phase cannot be fully characterized by hidden antiferromagnetic order: Gu and Wen
studied the `S = 1` chain with a magnetic field (eq. (8.3.4))
`Ĥ_{D,B} = Σ_x [Ŝ_x·Ŝ_{x+1} + D (Ŝ_x^{(3)})² + B Ŝ_x^{(1)}]`,
whose `B Ŝ_x^{(1)}` term breaks the Z₂ × Z₂ symmetry down to a single Z₂ (the π-rotation about the
1-axis), so the Kennedy–Tasaki picture fails for `B ≠ 0`; yet a distinct, disordered, gapped Haldane
phase (including the Heisenberg point) persists.  Moreover Oshikawa found that the hidden order of
the
spin-`S` VBS state depends on the parity of `S` (eq. (8.3.3)): the string order parameter is
positive
for **odd** `S` and vanishes for **even** `S`, and the AKLT open chain has `(S+1)²`-fold edge
degeneracy (not the four-fold predicted by Z₂ × Z₂).

These observations led to the notion of a **symmetry protected topological (SPT) phase** (§8.3.2).
Two short-range Hamiltonians with a unique gapped ground state are **continuously connected** if
there
is a continuous path of such Hamiltonians joining them.  Without any imposed symmetry, all such 1D
Hamiltonians are connected (Ogata).  But if one fixes a symmetry `G` and requires every Hamiltonian
on the path to be `G`-symmetric, distinct phases can appear: the **trivial phase** contains the
product states, and any other phase under the fixed symmetry is a **(nontrivial) SPT phase**.  The
Haldane phase is the prototypical SPT phase, protected by Z₂ × Z₂ (or inversion / time-reversal).

The Gu–Wen Hamiltonian is *defined concretely*.  The SPT-phase notions (`ContinuouslyConnected`,
`IsTrivialPhase`, `IsSPTPhase`) are honest **`def`s** (never axioms — the SPT phase is a definition,
not a theorem), built on a genuine continuous path of Hamiltonians together with uninterpreted
markers
for the deep predicates (short-range, gapped-unique, product-state, symmetry) whose faithful forms
belong to the infinite-chain / operator-algebra framework.  The Oshikawa parity and the edge
degeneracy are documented axioms.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.3.1–§8.3.2, eqs. (8.3.1)–(8.3.4), pp. 251–256; Z.-C. Gu, X.-G. Wen, Phys. Rev. B **80**,
155131 (2009); F. Pollmann, A. M. Turner, E. Berg, M. Oshikawa, Phys. Rev. B **81**, 064439 (2010).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {L : ℕ}

/-- The **Gu–Wen Hamiltonian** (eq. (8.3.4)) `Ĥ_{D,B} = Σ_x [Ŝ_x·Ŝ_{x+1} + D (Ŝ_x^{(3)})² +
B Ŝ_x^{(1)}]`: the anisotropic `S = 1` chain plus a uniform magnetic field `B` in the 1-direction.
The field term breaks the Z₂ × Z₂ symmetry down to the single Z₂ of the π-rotation about the 1-axis;
at `B = 0` it is the anisotropic model (8.1.1). -/
noncomputable def guWenHamiltonianS (L : ℕ) (D B : ℝ) : ManyBodyOpS (Fin L) 2 :=
  anisotropicChainHamiltonianS L D + (B : ℂ) • ∑ x : Fin L, spinSSiteOp1 x 2

/-- The **string order parameter of the spin-`S` VBS state** `O_string^{(α)}(Φ_VBS^S)` (Oshikawa),
as a function of the spin `S` and the direction `α`.  An uninterpreted real-valued marker (the
thermodynamic double limit is not formalized). -/
axiom vbsStringOrderParameterS : ℕ → Fin 3 → ℝ

/-- **Tasaki/Oshikawa eq. (8.3.3) (parity dependence of hidden order), AXIOM.**  The hidden
antiferromagnetic order of the spin-`S` VBS state — measured by the string order parameter — is
**positive for odd `S`** and **vanishes for even `S`**: `O_string^{(α)}(Φ_VBS^S) > 0` if `S` is odd,
`= 0` if `S` is even.  So the hidden Z₂ × Z₂ symmetry is fully broken for odd-`S` VBS states but
unbroken for even-`S` ones — a qualitative even/odd-`S` distinction beyond Haldane's integer vs
half-odd-integer one. -/
axiom tasaki_oshikawa_8_3_3 (S : ℕ) (α : Fin 3) :
    (Odd S → 0 < vbsStringOrderParameterS S α) ∧ (Even S → vbsStringOrderParameterS S α = 0)

/-- The **ground-state degeneracy of the spin-`S` AKLT model on an open chain**, from the effective
`S/2` edge spins.  An uninterpreted marker. -/
axiom vbsOpenChainGroundDegeneracyS : ℕ → ℕ

/-- **Tasaki §8.3.1 (edge-state degeneracy), AXIOM.**  The spin-`S` AKLT model on an open chain has
`(S+1)²`-fold degenerate ground states (the generalized VBS states), from the two effective `S/2`
edge spins.  For even `S` this is not a multiple of four, so it does not fit the Z₂ × Z₂ picture. -/
axiom tasaki_vbs_edge_degeneracy (S : ℕ) : vbsOpenChainGroundDegeneracyS S = (S + 1) ^ 2

/-- **Gapped-unique marker** `IsShortRangeGappedUniqueGS H`: the Hamiltonian `H` is short-ranged and
has a unique ground state with a nonvanishing energy gap.  Kept as an uninterpreted predicate (its
faithful form is the infinite-chain gapped-uniqueness used to classify phases).  Bundling both
conditions at `N = 2` is deliberate: it is the single hypothesis the phase classification below
travels along paths with, and it is not to be merged with the separate general-`N` markers
`HasShortRangeHamiltonianS` / `HasUniqueGappedGroundStateS` (`LiebSchultzMattisDiscrete.lean`). -/
axiom IsShortRangeGappedUniqueGS (H : ManyBodyOpS (Fin L) 2) : Prop

/-- **Product-state marker** `IsProductStateHamiltonian H`: `H` has a trivial tensor-product ground
state (the representative of the trivial phase). -/
axiom IsProductStateHamiltonian (H : ManyBodyOpS (Fin L) 2) : Prop

/-- A **continuous path of Hamiltonians** `Ĥ_s`, `s ∈ [0,1]`, each short-ranged with a unique gapped
ground state: the object along which two gapped phases are compared.  `toFun` is continuous in `s`
and `gapped_unique` holds on the unit interval. -/
structure HamiltonianPath (L : ℕ) where
  /-- The Hamiltonian `Ĥ_s` at parameter `s`. -/
  toFun : ℝ → ManyBodyOpS (Fin L) 2
  /-- The path depends continuously on `s`. -/
  continuous_toFun : Continuous toFun
  /-- Every `Ĥ_s` on the unit interval is short-ranged with a unique gapped ground state. -/
  gapped_unique : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → IsShortRangeGappedUniqueGS (toFun s)

/-- **Continuously connected** (without symmetry): there is a continuous gapped path joining `H₀`
and `H₁`.  By Ogata's theorem all short-range gapped-unique 1D Hamiltonians are connected in this
sense. -/
def ContinuouslyConnected (H₀ H₁ : ManyBodyOpS (Fin L) 2) : Prop :=
  ∃ P : HamiltonianPath L, P.toFun 0 = H₀ ∧ P.toFun 1 = H₁

/-- **Symmetry-respecting continuous connection**: a continuous gapped path joining `H₀` and `H₁`
*every Hamiltonian of which* has the imposed symmetry `sym` (a predicate on Hamiltonians, e.g.
`IsZ2Z2Invariant`).  This is the relation that classifies symmetry-protected phases. -/
def SymmetryConnected (sym : ManyBodyOpS (Fin L) 2 → Prop)
    (H₀ H₁ : ManyBodyOpS (Fin L) 2) : Prop :=
  ∃ P : HamiltonianPath L, P.toFun 0 = H₀ ∧ P.toFun 1 = H₁ ∧
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → sym (P.toFun s)

/-- **Trivial phase** (relative to the symmetry `sym`): `H` is symmetry-connected to a
product-state Hamiltonian.  No matter the symmetry, the trivial product states always form one
phase. -/
def IsTrivialPhase (sym : ManyBodyOpS (Fin L) 2 → Prop) (H : ManyBodyOpS (Fin L) 2) : Prop :=
  ∃ Hprod : ManyBodyOpS (Fin L) 2, IsProductStateHamiltonian Hprod ∧ SymmetryConnected sym H Hprod

/-- **Symmetry protected topological (SPT) phase** (relative to `sym`): `H` is short-range
gapped-unique, has the symmetry `sym`, but is **not** in the trivial phase — it cannot be
symmetry-connected to any product state.  The Haldane phase is the prototypical SPT phase, protected
by Z₂ × Z₂ (`IsZ2Z2Invariant`).  This is a definition, not a theorem. -/
def IsSPTPhase (sym : ManyBodyOpS (Fin L) 2 → Prop) (H : ManyBodyOpS (Fin L) 2) : Prop :=
  IsShortRangeGappedUniqueGS H ∧ sym H ∧ ¬ IsTrivialPhase sym H

end LatticeSystem.Quantum
