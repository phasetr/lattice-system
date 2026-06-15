import LatticeSystem.Quantum.SpinS.AKLTMatrixProduct

/-!
# Tasaki §8.3.4: the matrix-product "topological" index (Theorem 8.7, Corollary 8.5)

For matrix product states the heuristic entanglement indices of §8.3.3 become a precise invariant: a
**projective representation** of the protecting symmetry group `G` on the auxiliary (bond) space.
A symmetry `g ∈ G` acts on a spin chain by `V̂(g) = ∏_x û_x(g)` (with an extra complex conjugation
`K̂` for antiunitary `g`, eq. (8.3.44)), and on the bond matrices of an injective MPS by a virtual
operator `v̂(g)` obeying `v̂(g) v̂(h) = e^{iφ̃(g,h)} v̂(gh)` (eq. (8.3.42)) for a **phase function**
`φ̃ : G × G → ℝ` (a 2-cocycle).  The projective representation is **trivial** iff its phase function
is a coboundary, `φ̃(g,h) = ψ̃(g) + s(g)ψ̃(h) − ψ̃(gh)` (mod `2π`, eq. (8.3.43)); the cohomology
class
of `φ̃` is the matrix-product SPT index.

**Theorem 8.7** (Tachikawa): if an injective matrix product state `|Φ⟩` is invariant up to a phase
under the symmetry, `V̂(g)|Φ⟩ = e^{iη_L(g)}|Φ⟩` for all `g` and all `L`, then the on-site projective
representation `v̂(·)` is **trivial**.

**Corollary 8.5**: for half-odd-integer spin (`S = N/2` with `N` odd) the Z₂ × Z₂ projective
representation `{1̂, û₁, û₂, û₃}` is *nontrivial* (eq. (2.1.31)), and the time-reversal
representation
has `Θ̂² = −1`; hence there is **no** Z₂ × Z₂ -invariant (resp. time-reversal-invariant) injective
matrix product state — the Lieb–Schultz–Mattis-type no-go obstruction.

The projective representation, its triviality, and the existence of a symmetric injective MPS are
honest **uninterpreted markers** (the cocycle/coboundary cohomology and the half-infinite-chain MPS
construction belong to the operator-algebra framework).  Theorem 8.7 and the half-odd-integer
nontriviality are documented axioms; **Corollary 8.5 is then *proved*** as the contrapositive of
Theorem 8.7.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.3.4, Theorem 8.7, Corollary 8.5, eqs. (8.3.42)–(8.3.47), pp. 269–279; F. Pollmann, A. M.
Turner, E. Berg, M. Oshikawa, Phys. Rev. B **85**, 075125 (2012); X. Chen, Z.-C. Gu, X.-G. Wen,
Phys.
Rev. B **83**, 035107 (2011).
-/

namespace LatticeSystem.Quantum

open Matrix

/-- **Projective-representation marker** `IsProjectiveRep G φ`: the symmetry group `G` acts on the
auxiliary space by a projective representation `v̂(·)` whose phase function (2-cocycle) is
`φ : G → G → ℝ`, i.e. `v̂(g) v̂(h) = e^{iφ(g,h)} v̂(gh)` (eq. (8.3.42)).  An uninterpreted
predicate. -/
axiom IsProjectiveRep (G : Type) (φ : G → G → ℝ) : Prop

/-- **Triviality marker** `IsTrivialProjectiveRep G φ`: the projective representation with phase
function `φ` is *trivial*, i.e. `φ` is a coboundary `φ(g,h) = ψ(g) + s(g)ψ(h) − ψ(gh)` (mod `2π`,
eq. (8.3.43)) for some `ψ : G → ℝ`.  The cohomology class of `φ` is the matrix-product SPT index;
this
is an uninterpreted predicate (its faithful form is the 2-cohomology coboundary condition). -/
axiom IsTrivialProjectiveRep (G : Type) (φ : G → G → ℝ) : Prop

/-- **Symmetric-MPS marker** `SymmetricInjectiveMPSExists G φ`: there is an injective matrix product
state invariant up to a phase under the symmetry `G` whose on-site projective representation has
phase function `φ`, i.e. `V̂(g)|Φ⟩ = e^{iη_L(g)}|Φ⟩` for all `g` and all chain lengths `L`
(eq. (8.3.45)).  An uninterpreted predicate. -/
axiom SymmetricInjectiveMPSExists (G : Type) (φ : G → G → ℝ) : Prop

/-- **Tasaki Theorem 8.7 (matrix-product SPT index, Tachikawa), AXIOM.**  If there is an injective
matrix product state invariant up to a phase under the symmetry `G` (`SymmetricInjectiveMPSExists`),
then the on-site projective representation `v̂(·)` is **trivial** (`IsTrivialProjectiveRep`).
Contrapositive: a nontrivial projective representation forbids any symmetric injective MPS, the
defining obstruction of a nontrivial SPT phase.  Recorded as a documented axiom. -/
axiom tasaki_theorem_8_7 (G : Type) (φ : G → G → ℝ) (hrep : IsProjectiveRep G φ) :
    SymmetricInjectiveMPSExists G φ → IsTrivialProjectiveRep G φ

/-- The **Z₂ × Z₂ symmetry group** as the four-element carrier `Fin 4` (the elements
`e, û₁, û₂, û₃`). -/
abbrev Z2xZ2Spin : Type := Fin 4

/-- The **phase function (2-cocycle) of the Z₂ × Z₂ on-site projective representation** for spin
`S = N/2` (the standard `{1̂, û₁, û₂, û₃}` representation of eq. (2.1.29)).  An uninterpreted
marker. -/
axiom z2z2SpinCocycle (N : ℕ) : Z2xZ2Spin → Z2xZ2Spin → ℝ

/-- **The Z₂ × Z₂ projective representation, AXIOM.**  For each spin `N`, the standard Z₂ × Z₂
representation with cocycle `z2z2SpinCocycle N` is indeed a projective representation. -/
axiom z2z2Spin_isProjectiveRep (N : ℕ) : IsProjectiveRep Z2xZ2Spin (z2z2SpinCocycle N)

/-- **Half-odd-integer nontriviality (eq. (2.1.31)), AXIOM.**  For half-odd-integer spin (`S = N/2`
with `N` *odd*), the Z₂ × Z₂ projective representation `{1̂, û₁, û₂, û₃}` is **nontrivial**: its
phase
function is not a coboundary (`û_α` anticommute, so `(û₁ û₃)² = −1`).  This is the rigorous input to
Corollary 8.5. -/
axiom z2z2Spin_nontrivial_of_odd (N : ℕ) (hN : Odd N) :
    ¬ IsTrivialProjectiveRep Z2xZ2Spin (z2z2SpinCocycle N)

/-- **Tasaki Corollary 8.5 (no symmetric injective MPS for half-odd-integer spin), PROVED.**  For
half-odd-integer spin (`S = N/2` with `N` odd) there is **no** Z₂ × Z₂ -invariant injective matrix
product state.  This is the contrapositive of Theorem 8.7: a symmetric injective MPS would force the
Z₂ × Z₂ projective representation to be trivial, contradicting its nontriviality for odd `N`
(eq. (2.1.31)).  It is the matrix-product form of the Lieb–Schultz–Mattis-type no-go theorem. -/
theorem tasaki_corollary_8_5 (N : ℕ) (hN : Odd N) :
    ¬ SymmetricInjectiveMPSExists Z2xZ2Spin (z2z2SpinCocycle N) := fun hMPS =>
  z2z2Spin_nontrivial_of_odd N hN
    (tasaki_theorem_8_7 Z2xZ2Spin (z2z2SpinCocycle N) (z2z2Spin_isProjectiveRep N) hMPS)

end LatticeSystem.Quantum
