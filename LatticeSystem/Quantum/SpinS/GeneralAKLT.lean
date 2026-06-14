import LatticeSystem.Quantum.SpinS.AKLT
import LatticeSystem.Quantum.SpinS.AndersonTower

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

The Casimir, the bond projection, and the generalized Hamiltonian are *defined concretely*.  The
hexagonal lattice, the VBS ground state, and the infinite-volume uniqueness are carried by
uninterpreted markers, and Theorem 7.7 (whose proof rests on the explicit VBS /
reflection-positivity
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

/-- The **generalized AKLT Hamiltonian** on a graph `G` (eq. (7.3.7)) for uniform spin `S = N/2`:
`Ĥ^{(Λ,B)}_AKLT = Σ_{{x,y}∈B} P̂_{max}[Ŝ_x + Ŝ_y]`, summed over the bonds of `G`.  Implemented as a
half of the ordered double sum over adjacent pairs (each bond `{x,y}` is counted once as `(x,y)` and
once as `(y,x)`, and the bond projection is symmetric). -/
noncomputable def generalAKLTHamiltonianS (G : SimpleGraph Λ) [DecidableRel G.Adj] (N : ℕ) :
    ManyBodyOpS Λ N :=
  (1 / 2 : ℂ) • ∑ x : Λ, ∑ y : Λ,
    if G.Adj x y then bondMaxSpinProjectionS x y N else 0

/-- **Hexagonal-lattice marker** `IsHexagonalLatticeAKLT G`: the graph `G` is the (periodic)
hexagonal lattice, on which every site has coordination number 3, giving the uniform `S = 3/2`
(`N = 3`) AKLT model of eq. (7.3.8).  A faithful definition needs the explicit hexagonal embedding;
it is kept as an uninterpreted predicate so Theorem 7.7's decay statement applies only to the
hexagonal lattice (where it holds), not to an arbitrary graph (where it can fail). -/
axiom IsHexagonalLatticeAKLT (G : SimpleGraph Λ) : Prop

/-- **General-graph VBS ground-state marker** `IsGeneralGraphVBSGroundState G N Φ`: the state `Φ` is
the valence-bond-solid ground state (eq. (7.3.6)) of the generalized AKLT Hamiltonian on `G`.  Kept
as an uninterpreted predicate (the explicit graph VBS construction is not formalized). -/
axiom IsGeneralGraphVBSGroundState (G : SimpleGraph Λ) (N : ℕ) (Φ : (Λ → Fin (N + 1)) → ℂ) : Prop

/-- **Infinite-volume uniqueness marker** `HasUniqueInfiniteVolumeVBSGroundState G N`: the
translation-invariant infinite-volume ground state of the generalized AKLT model on `G` (in the
sense
of Definition 4.17) is unique.  The full statement lives in the quasi-local C*-algebra framework;
kept as an uninterpreted predicate per the operator-algebra policy. -/
axiom HasUniqueInfiniteVolumeVBSGroundState (G : SimpleGraph Λ) (N : ℕ) : Prop

/-- **Tasaki Theorem 7.7 (hexagonal AKLT correlations and uniqueness), AXIOM.**  For the `S = 3/2`
(`N = 3`) AKLT model on the hexagonal lattice `G` (`IsHexagonalLatticeAKLT`), with VBS ground state
`Φ` (`IsGeneralGraphVBSGroundState`): there are positive constants `C, ξ` — independent of system
size — such that the spin correlation is **sign-alternating and exponentially decaying** in the
graph
distance `D(x,y) = G.dist x y` (eq. (7.3.9))
`0 ≤ (−1)^{D(x,y)} ⟨Ŝ_x·Ŝ_y⟩ ≤ C e^{−D(x,y)/ξ}`,
and the translation-invariant infinite-volume ground state is **unique**
(`HasUniqueInfiniteVolumeVBSGroundState`).  The hexagonal restriction is essential: on general
graphs
the correlations need not decay.  Proved by Affleck–Kennedy–Lieb–Tasaki and Kennedy–Lieb–Tasaki via
the explicit VBS analysis; recorded as a documented axiom. -/
axiom tasaki_theorem_7_7 (G : SimpleGraph Λ) (Φ : (Λ → Fin 4) → ℂ)
    (hG : IsHexagonalLatticeAKLT G) (hΦ : IsGeneralGraphVBSGroundState G 3 Φ) :
    (∃ C ξ : ℝ, 0 < C ∧ 0 < ξ ∧ ∀ x y : Λ,
      0 ≤ (-1 : ℝ) ^ (G.dist x y) * expectationRatioRe (spinSDot x y 3) Φ ∧
        (-1 : ℝ) ^ (G.dist x y) * expectationRatioRe (spinSDot x y 3) Φ ≤
          C * Real.exp (-(G.dist x y : ℝ) / ξ)) ∧
    HasUniqueInfiniteVolumeVBSGroundState G 3

end LatticeSystem.Quantum
