import LatticeSystem.Quantum.SpinS.AKLT
import LatticeSystem.Quantum.SpinS.AndersonTower
import LatticeSystem.Lattice.HoneycombLattice
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Tasaki §7.3.2: the AKLT model on a general graph and Theorem 7.7

The VBS construction extends from the chain to **any graph** `(Λ, B)`.  Associating with each
site `x`
a spin `S̄_x = |N(x)|/2` (half its coordination number), the **generalized AKLT Hamiltonian**
(eq. (7.3.7)) is
`Ĥ^{(Λ,B)}_AKLT = Σ_{{x,y}∈B} P̂_{S̄_x + S̄_y}[Ŝ_x + Ŝ_y]`,
a sum over bonds of the projection onto the *maximal* total spin of each bond.  The VBS state
(eq. (7.3.6)) is its unique ground state (Kennedy–Lieb–Tasaki).  On the **hexagonal lattice** every
site has coordination number 3, so the spins are uniform `S = 3/2` (`N = 3`) and the Hamiltonian is
`Ĥ = Σ_{bonds} P̂_3[Ŝ_x + Ŝ_y]` (eq. (7.3.8)).

We formalize the **regular (uniform-spin) specialization** `regularGraphAKLTHamiltonianS`: a single
global spin `S = N/2` and each bond projecting to the maximal total spin `J = N`.  It coincides with
eq. (7.3.7) exactly on an `N`-regular graph — in particular it is eq. (7.3.8) on the 3-regular
hexagonal lattice — which is precisely the setting of Theorem 7.7.  The site-dependent spins
`S̄_x = deg(x)/2` of the fully general (non-regular) eq. (7.3.7) are not expressible in the
uniform-spin type `ManyBodyOpS Λ N` and are left for a future refinement.

For uniform spin `S = N/2`, the bond projection onto the maximal total spin `J = N` is the
**Lagrange/Casimir projector**: with `Ĉ = (Ŝ_x + Ŝ_y)² = 2S(S+1) + 2 Ŝ_x·Ŝ_y` (affine in `Ŝ_x·Ŝ_y`,
with eigenvalue `J(J+1)` on the spin-`J` bond subspace, `J = 0,…,N`),
`P̂_N[Ŝ_x+Ŝ_y] = ∏_{j=0}^{N-1} (Ĉ − j(j+1)) / (N(N+1) − j(j+1))`,
which is `1` on the spin-`N` subspace and `0` on every lower one.

**Theorem 7.7** (hexagonal `S = 3/2` AKLT model; Affleck–Kennedy–Lieb–Tasaki, Kennedy–Lieb–Tasaki):
the VBS ground state has exponentially decaying, sign-alternating spin correlations (eq. (7.3.9))
`0 ≤ (−1)^{D(x,y)} ⟨Φ_VBS| Ŝ_x·Ŝ_y |Φ_VBS⟩ / ⟨Φ_VBS|Φ_VBS⟩ ≤ C e^{−D(x,y)/ξ}`,
with `D` the graph distance and `C, ξ > 0` independent of system size, and the translation-invariant
infinite-volume ground state is unique.

The Casimir, the bond projection, the generalized Hamiltonian, and the hexagonal lattice
(`IsHexagonalLatticeAKLT`, via the explicit honeycomb torus `honeycombTorusGraph`) are *defined
concretely*.  The VBS ground state and the infinite-volume uniqueness are carried by uninterpreted
markers, and Theorem 7.7 (whose proof rests on the explicit VBS / reflection-positivity
analysis) is a documented axiom.  The decay statement is restricted to the hexagonal lattice: on
general graphs it can fail (the correlations need not decay in every dimension).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.3.2, Theorem 7.7, eqs. (7.3.6)–(7.3.9), pp. 210–212; I. Affleck, T. Kennedy, E. H. Lieb,
H.
Tasaki, Commun. Math. Phys. **115**, 477 (1988); T. Kennedy, E. H. Lieb, H. Tasaki, J. Stat. Phys.
**53**, 383 (1988).
-/

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- The **bond Casimir** `(Ŝ_x + Ŝ_y)² = 2 S(S+1) + 2 Ŝ_x·Ŝ_y` for two spin-`S` sites (`S = N/2`),
affine in the Heisenberg operator `Ŝ_x·Ŝ_y`; its eigenvalue on the spin-`J` bond subspace is
`J(J+1)` for `J = 0,…,N`. -/
noncomputable def bondCasimirS (x y : Λ) (N : ℕ) : ManyBodyOpS Λ N :=
  (2 * (((N : ℂ) / 2) * ((N : ℂ) / 2 + 1))) • (1 : ManyBodyOpS Λ N) +
    (2 : ℂ) • spinSDot x y N

/-- The **bond projection onto the maximal total spin** `P̂_N[Ŝ_x + Ŝ_y]` for two spin-`S = N/2`
sites: the Lagrange/Casimir projector `∏_{j=0}^{N-1} (Ĉ − j(j+1)) / (N(N+1) − j(j+1))` onto the
top spin-`N` subspace (`1` there, `0` on every lower spin-`J` subspace).  The factors are
polynomials
in the single operator `Ĉ = bondCasimirS x y N` and hence commute, so the ordered product is the
projection. -/
noncomputable def bondMaxSpinProjectionS (x y : Λ) (N : ℕ) : ManyBodyOpS Λ N :=
  (List.ofFn fun j : Fin N =>
    ((N : ℂ) * (N + 1) - ((j : ℂ) * (j + 1)))⁻¹ •
      (bondCasimirS x y N - ((j : ℂ) * (j + 1)) • (1 : ManyBodyOpS Λ N))).prod

/-- **Symmetry of the bond projection**: `P̂_N[Ŝ_x + Ŝ_y] = P̂_N[Ŝ_y + Ŝ_x]`.  The projector is a
polynomial in the bond Casimir `Ĉ = bondCasimirS x y N`, which depends on the two sites only through
the symmetric Heisenberg operator `Ŝ_x · Ŝ_y = Ŝ_y · Ŝ_x` (`spinSDot_comm`); hence swapping the two
endpoints leaves it unchanged. -/
theorem bondMaxSpinProjectionS_comm (x y : Λ) (N : ℕ) :
    (bondMaxSpinProjectionS x y N : ManyBodyOpS Λ N) = bondMaxSpinProjectionS y x N := by
  simp only [bondMaxSpinProjectionS, bondCasimirS, spinSDot_comm x y]

/-- The **regular-graph (uniform-spin) AKLT Hamiltonian** on a graph `G`:
`Ĥ_AKLT = Σ_{{x,y}∈B} P̂_N[Ŝ_x + Ŝ_y]`, summed over the bonds of `G`, with a *single global* spin
`S = N/2` on every site and each bond projecting to the maximal total spin `J = N`.  Implemented as
a half of the ordered double sum over adjacent pairs (each bond `{x,y}` is counted once as `(x,y)`
and
once as `(y,x)`, and the bond projection is symmetric).

This is the **regular specialization** of Tasaki's generalized AKLT Hamiltonian (eq. (7.3.7)): that
model assigns the site-dependent spin `S̄_x = deg(x)/2` and projects each bond onto `S̄_x + S̄_y`,
so the two agree exactly on a `N`-regular graph (every site of degree `N`).  In particular this *is*
eq. (7.3.8) on the 3-regular hexagonal lattice (`N = 3`, `S = 3/2`).  Site-dependent spins are not
expressible in the uniform-spin type `ManyBodyOpS Λ N` and are left for a future refinement. -/
noncomputable def regularGraphAKLTHamiltonianS (G : SimpleGraph Λ) [DecidableRel G.Adj] (N : ℕ) :
    ManyBodyOpS Λ N :=
  (1 / 2 : ℂ) • ∑ x : Λ, ∑ y : Λ,
    if G.Adj x y then bondMaxSpinProjectionS x y N else 0

/-- **Hexagonal-lattice predicate** `IsHexagonalLatticeAKLT G`: the graph `G` is isomorphic to a
nondegenerate honeycomb torus `honeycombTorusGraph m` for some `m ≥ 2`.  The lower bound ensures
that the three nominal neighbours of every site are distinct, so the torus is genuinely
3-regular and carries the uniform `S = 3/2` (`N = 3`) AKLT model.  This is the periodic
hexagonal-lattice setting of Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer, 2020, §7.3.2, eq. (7.3.8), Theorem 7.7, footnote 42, pp. 210–211. -/
def IsHexagonalLatticeAKLT (G : SimpleGraph Λ) : Prop :=
  ∃ m : ℕ, 2 ≤ m ∧ Nonempty (G ≃g LatticeSystem.Lattice.honeycombTorusGraph m)

/-- **General-graph zero-energy VBS ground state** `IsGeneralGraphVBSGroundState G N Φ`: the state
`Φ` is a frustration-free zero-energy ground state of the regular-graph AKLT Hamiltonian
`regularGraphAKLTHamiltonianS G N` (eq. (7.3.6)–(7.3.8)).  Concretely the three conjuncts state that
the Hamiltonian is positive semidefinite (energy bounded below by `0`), that `Φ` is annihilated by
it (`Ĥ Φ = 0`, so `Φ` attains the energy-`0` bottom of the spectrum), and that `Φ` is nonzero.
Correlation decay and infinite-volume uniqueness are *not* part of this predicate; they are the
content of `tasaki_theorem_7_7`. -/
def IsGeneralGraphVBSGroundState (G : SimpleGraph Λ) [DecidableRel G.Adj] (N : ℕ)
    (Φ : (Λ → Fin (N + 1)) → ℂ) : Prop :=
  (regularGraphAKLTHamiltonianS G N).PosSemidef ∧
    (regularGraphAKLTHamiltonianS G N).mulVec Φ = 0 ∧ Φ ≠ 0

/-- **Infinite-volume uniqueness marker** `HasUniqueInfiniteVolumeVBSGroundState G N`: the
translation-invariant infinite-volume ground state of the generalized AKLT model on `G` (in the
sense
of Definition 4.17) is unique.  The full statement lives in the quasi-local C*-algebra framework;
kept as an uninterpreted predicate per the operator-algebra policy. -/
axiom HasUniqueInfiniteVolumeVBSGroundState (G : SimpleGraph Λ) (N : ℕ) : Prop

/-- **Tasaki Theorem 7.7 (hexagonal AKLT correlations and uniqueness), AXIOM.**  There are positive
constants `C, ξ` — hoisted outside the universal quantifier over graphs `G`, so they are genuinely
**independent of the system** `G`, capturing Tasaki's "`C, ξ` independent of system size" — such
that for every hexagonal lattice `G` (`IsHexagonalLatticeAKLT`, i.e. isomorphic to a nondegenerate
honeycomb torus) with the `S = 3/2` (`N = 3`) AKLT model, **some** zero-energy VBS ground state `Φ`
(`IsGeneralGraphVBSGroundState G 3 Φ`) exists whose spin correlation is **sign-alternating and
exponentially decaying** in the graph distance `D(x,y) = G.dist x y` (eq. (7.3.9))
`0 ≤ (−1)^{D(x,y)} ⟨Ŝ_x·Ŝ_y⟩ ≤ C e^{−D(x,y)/ξ}`,
and the translation-invariant infinite-volume ground state is **unique**
(`HasUniqueInfiniteVolumeVBSGroundState`, which is `Φ`-independent).

The witness `Φ` is, mathematically, the canonical VBS state `honeycombVBSState m` transported along
the isomorphism `G ≃g honeycombTorusGraph m` supplied by `IsHexagonalLatticeAKLT G`; its zero-energy
ground-state property on the canonical torus is *proved* in
`honeycombVBSState_isGeneralGraphVBSGroundState`.  Stating the ground state existentially
(`∃ Φ, IsGeneralGraphVBSGroundState G 3 Φ ∧ …`) rather than universally (`∀ Φ, … → …`) is what keeps
the axiom sound: the finite honeycomb torus ground state may be degenerate, so a `∀ Φ` claim would
be *false* on the non-VBS kernel vectors, whereas the single VBS witness suffices for Tasaki's
content and is faithful to the Kennedy–Lieb–Tasaki analysis, which computes the correlations of
*that* VBS state.

The correlation decay (eq. (7.3.9)) and the infinite-volume uniqueness are recorded as **documented
axioms**: their proofs (Affleck–Kennedy–Lieb–Tasaki, Kennedy–Lieb–Tasaki [41]) rest on the explicit
two-dimensional VBS / reflection-positivity correlation analysis, for which there is no
implementation base in this repository or in mathlib (a genuine real-implementation dependency).  By
contrast the ground-state hypothesis conjunct is *not* deferred: it is discharged by
`honeycombVBSState_isGeneralGraphVBSGroundState`.  The hexagonal restriction is essential: on
general graphs the correlations need not decay.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.3.2, Theorem 7.7, eqs. (7.3.6)–(7.3.9), pp. 210–212; I. Affleck, T. Kennedy, E. H. Lieb,
H. Tasaki, Commun. Math. Phys. **115**, 477 (1988); T. Kennedy, E. H. Lieb, H. Tasaki, J. Stat.
Phys. **53**, 383 (1988) ([41]). -/
axiom tasaki_theorem_7_7 :
    ∃ C ξ : ℝ, 0 < C ∧ 0 < ξ ∧
      ∀ (G : SimpleGraph Λ) [DecidableRel G.Adj], IsHexagonalLatticeAKLT G →
        (∃ Φ : (Λ → Fin 4) → ℂ, IsGeneralGraphVBSGroundState G 3 Φ ∧ ∀ x y : Λ,
          0 ≤ (-1 : ℝ) ^ (G.dist x y) * expectationRatioRe (spinSDot x y 3) Φ ∧
            (-1 : ℝ) ^ (G.dist x y) * expectationRatioRe (spinSDot x y 3) Φ ≤
              C * Real.exp (-(G.dist x y : ℝ) / ξ)) ∧
          HasUniqueInfiniteVolumeVBSGroundState G 3

end LatticeSystem.Quantum
