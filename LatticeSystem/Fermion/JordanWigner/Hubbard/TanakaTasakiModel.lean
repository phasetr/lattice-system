import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinfulVectorOperator
import LatticeSystem.Fermion.JordanWigner.Hubbard.GroundSubspaceAtFilling

/-!
# Tasaki §11.5.4: the Tanaka–Tasaki model and Theorem 11.27

The **Tanaka–Tasaki model** (Tasaki §11.5.4, eqs. (11.5.19)–(11.5.24)) is the only rigorous
example of metallic ferromagnetism in a Hubbard model in arbitrary dimension `d`.  It lives on
a heavily decorated lattice `Λ = E × {1, 2, 3} ∪ I × {1, 2}`: external sites are *triplicated*
and internal sites *duplicated*.  We formalise the `d = 1` realisation (`K + 1` cells,
periodic): the `5(K + 1)` sites are packed into `Fin (5K + 5)` by `cell ↦ {0,1,2 ↦ external
copies, 3,4 ↦ internal copies}`.

**Special single-particle states** (`Ĉ_σ(φ) = Σ_x φ(x) ĉ_{x,σ}` via
`spinfulCreationFromVector`):
* `â_p` (eq. (11.5.19)):
  `1/√(3+4ν²) · [Σ_{ζ} ĉ_{(p,ζ)} + ν Σ_{ζ=1,2}(ĉ_{(p+b,ζ)} + (−1)^ζ ĉ_{(p−b,ζ)})]`;
* `b̂_p` (eq. (11.5.20)): `1/√2 (ĉ_{(p,1)} − ĉ_{(p,2)})`;
* `d̂_p` (eq. (11.5.21)): `ĉ_{(p,1)} + ĉ_{(p,2)} − 2 ĉ_{(p,3)}`;
* `d̂_{(u,ζ)}` (eq. (11.5.22)): `ĉ_{(u,ζ)} − ν (ĉ_{(u−b,3)} + (−1)^ζ ĉ_{(u+b,3)})`.

The `â` and `b̂` operators satisfy the standard anticommutation relations (eq. (11.5.23)); the
duplication/triplication is what guarantees this.  The Hamiltonian is `Ĥ = Ĥ_hop + Ĥ_int` with
`Ĥ_int = U Σ_x n̂_{x↑} n̂_{x↓}` (eq. (11.5.13)) and (eq. (11.5.24))
`Ĥ_hop = Σ_{⟨p,q⟩∈E,σ}(−s â†_p â_q − t b̂†_p b̂_q) + u₁ Σ_{p,σ} b̂†_p b̂_p
         + u₂ (Σ_{p,σ} d̂†_p d̂_p + Σ_{(u,ζ),σ} d̂†_{(u,ζ)} d̂_{(u,ζ)})`;
the `d̂`-bands are pushed to infinity in the `u₂ ↑ ∞` limit.

**Theorem 11.27** (Tanaka–Tasaki): for any `d` and `L^d ≤ N ≤ 2L^d` with
`u₁ > 2d(|s| + 2|t|)`, in the limit `u₂, U ↑ ∞` the ground states have the maximum possible
total spin `S_tot = N/2` (metallic when `N/L^d` is strictly between 1 and 2).  Tasaki cites the
original paper [63] for the (technical) proof; recorded as a documented axiom.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.4, eqs. (11.5.19)–(11.5.24) and Theorem 11.27 (pp. 449–452).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- The external copy `(p, ζ)` (`ζ : Fin 3`) packed into `Fin (5K + 5)` at index `5p + ζ`. -/
def ttExtSite (K : ℕ) (p : Fin (K + 1)) (ζ : Fin 3) : Fin (5 * K + 5) :=
  ⟨5 * p.val + ζ.val, by have := p.isLt; have := ζ.isLt; omega⟩

/-- The internal copy `(c, ζ)` (`ζ : Fin 2`) of bond `c`, packed at index `5c + 3 + ζ`. -/
def ttIntSite (K : ℕ) (c : Fin (K + 1)) (ζ : Fin 2) : Fin (5 * K + 5) :=
  ⟨5 * c.val + 3 + ζ.val, by have := c.isLt; have := ζ.isLt; omega⟩

/-- The single-particle state `α_p = â_p` (eq. (11.5.19), `d = 1`): the prefactor
`1/√(3+4ν²)` times `1` on the three external copies of `p`, `ν` on the `ζ`-copies of the bond
just after `p` (`p+b`), and `(−1)^ζ ν` on the copies of the bond just before `p` (`p−b`). -/
noncomputable def ttAlpha (K : ℕ) (ν : ℝ) (p : Fin (K + 1)) : Fin (5 * K + 5) → ℝ :=
  fun x =>
    let pref := 1 / Real.sqrt (3 + 4 * ν ^ 2)
    if x = ttExtSite K p 0 ∨ x = ttExtSite K p 1 ∨ x = ttExtSite K p 2 then pref
    else if x = ttIntSite K p 0 then pref * ν
    else if x = ttIntSite K (p - 1) 0 then pref * (-ν)
    else if x = ttIntSite K p 1 then pref * ν
    else if x = ttIntSite K (p - 1) 1 then pref * ν
    else 0

/-- The single-particle state `b̂_p` (eq. (11.5.20)): `1/√2 (ĉ_{(p,1)} − ĉ_{(p,2)})`. -/
noncomputable def ttBeta (K : ℕ) (p : Fin (K + 1)) : Fin (5 * K + 5) → ℝ :=
  fun x =>
    if x = ttExtSite K p 0 then 1 / Real.sqrt 2
    else if x = ttExtSite K p 1 then -(1 / Real.sqrt 2)
    else 0

/-- The single-particle state `d̂_p` (eq. (11.5.21)): `ĉ_{(p,1)} + ĉ_{(p,2)} − 2 ĉ_{(p,3)}`. -/
def ttDeltaP (K : ℕ) (p : Fin (K + 1)) : Fin (5 * K + 5) → ℝ :=
  fun x =>
    if x = ttExtSite K p 0 ∨ x = ttExtSite K p 1 then 1
    else if x = ttExtSite K p 2 then -2
    else 0

/-- The single-particle state `d̂_{(c,ζ)}` (eq. (11.5.22)): `ĉ_{(c,ζ)} − ν (ĉ_{(ext c,3)} +
(−1)^ζ ĉ_{(ext c+1,3)})`, where `ext c`/`ext c+1` are the external neighbours of bond `c`. -/
noncomputable def ttDeltaI (K : ℕ) (ν : ℝ) (c : Fin (K + 1)) (ζ : Fin 2) :
    Fin (5 * K + 5) → ℝ :=
  fun x =>
    if x = ttIntSite K c ζ then 1
    else if x = ttExtSite K c 2 then -ν
    else if x = ttExtSite K (c + 1) 2 then (if ζ = 0 then ν else -ν)
    else 0

/-- `â†_{p,σ}` (eq. (11.5.19)). -/
noncomputable def ttACreation (K : ℕ) (ν : ℝ) (p : Fin (K + 1)) (σ : Fin 2) :
    ManyBodyOp (Fin (2 * (5 * K + 4) + 2)) :=
  spinfulCreationFromVector (5 * K + 4) (fun x => (ttAlpha K ν p x : ℂ)) σ

/-- `â_{p,σ}`. -/
noncomputable def ttAAnnihilation (K : ℕ) (ν : ℝ) (p : Fin (K + 1)) (σ : Fin 2) :
    ManyBodyOp (Fin (2 * (5 * K + 4) + 2)) :=
  spinfulAnnihilationFromVector (5 * K + 4) (fun x => (ttAlpha K ν p x : ℂ)) σ

/-- `b̂†_{p,σ}` (eq. (11.5.20)). -/
noncomputable def ttBCreation (K : ℕ) (p : Fin (K + 1)) (σ : Fin 2) :
    ManyBodyOp (Fin (2 * (5 * K + 4) + 2)) :=
  spinfulCreationFromVector (5 * K + 4) (fun x => (ttBeta K p x : ℂ)) σ

/-- `b̂_{p,σ}`. -/
noncomputable def ttBAnnihilation (K : ℕ) (p : Fin (K + 1)) (σ : Fin 2) :
    ManyBodyOp (Fin (2 * (5 * K + 4) + 2)) :=
  spinfulAnnihilationFromVector (5 * K + 4) (fun x => (ttBeta K p x : ℂ)) σ

/-- `d̂†_{p,σ}` (eq. (11.5.21)). -/
noncomputable def ttDeltaPCreation (K : ℕ) (p : Fin (K + 1)) (σ : Fin 2) :
    ManyBodyOp (Fin (2 * (5 * K + 4) + 2)) :=
  spinfulCreationFromVector (5 * K + 4) (fun x => (ttDeltaP K p x : ℂ)) σ

/-- `d̂_{p,σ}`. -/
noncomputable def ttDeltaPAnnihilation (K : ℕ) (p : Fin (K + 1)) (σ : Fin 2) :
    ManyBodyOp (Fin (2 * (5 * K + 4) + 2)) :=
  spinfulAnnihilationFromVector (5 * K + 4) (fun x => (ttDeltaP K p x : ℂ)) σ

/-- `d̂†_{(c,ζ),σ}` (eq. (11.5.22)). -/
noncomputable def ttDeltaICreation (K : ℕ) (ν : ℝ) (c : Fin (K + 1)) (ζ σ : Fin 2) :
    ManyBodyOp (Fin (2 * (5 * K + 4) + 2)) :=
  spinfulCreationFromVector (5 * K + 4) (fun x => (ttDeltaI K ν c ζ x : ℂ)) σ

/-- `d̂_{(c,ζ),σ}`. -/
noncomputable def ttDeltaIAnnihilation (K : ℕ) (ν : ℝ) (c : Fin (K + 1)) (ζ σ : Fin 2) :
    ManyBodyOp (Fin (2 * (5 * K + 4) + 2)) :=
  spinfulAnnihilationFromVector (5 * K + 4) (fun x => (ttDeltaI K ν c ζ x : ℂ)) σ

/-- **The Tanaka–Tasaki hopping Hamiltonian** `Ĥ_hop` (eq. (11.5.24)): nearest-neighbour
`â`/`b̂` hopping `−s â†â − t b̂†b̂` over the periodic external chain, the `b̂`-band shift
`u₁ Σ b̂†b̂`, and the `u₂` penalty `Σ d̂†d̂` on both `d̂_p` and `d̂_{(c,ζ)}` (pushed to `∞`). -/
noncomputable def ttHopping (K : ℕ) (ν s t u1 u2 : ℝ) :
    ManyBodyOp (Fin (2 * (5 * K + 4) + 2)) :=
  (∑ p : Fin (K + 1), ∑ σ : Fin 2,
      (-(s : ℂ) • (ttACreation K ν p σ * ttAAnnihilation K ν (p + 1) σ +
          ttACreation K ν p σ * ttAAnnihilation K ν (p - 1) σ)
        - (t : ℂ) • (ttBCreation K p σ * ttBAnnihilation K (p + 1) σ +
          ttBCreation K p σ * ttBAnnihilation K (p - 1) σ)))
    + (u1 : ℂ) • ∑ p : Fin (K + 1), ∑ σ : Fin 2, ttBCreation K p σ * ttBAnnihilation K p σ
    + (u2 : ℂ) •
        (∑ p : Fin (K + 1), ∑ σ : Fin 2, ttDeltaPCreation K p σ * ttDeltaPAnnihilation K p σ
          + ∑ c : Fin (K + 1), ∑ ζ : Fin 2, ∑ σ : Fin 2,
            ttDeltaICreation K ν c ζ σ * ttDeltaIAnnihilation K ν c ζ σ)

/-- **The Tanaka–Tasaki interaction Hamiltonian** `Ĥ_int = U Σ_x n̂_{x↑} n̂_{x↓}`
(eq. (11.5.13)) over all `5(K+1)` physical sites. -/
noncomputable def ttInteraction (K : ℕ) (U : ℝ) :
    ManyBodyOp (Fin (2 * (5 * K + 4) + 2)) :=
  ∑ x : Fin (5 * K + 5), (U : ℂ) • hubbardDoubleOccupancy (5 * K + 4) x

/-- **The Tanaka–Tasaki Hubbard model** `Ĥ = Ĥ_hop + Ĥ_int` (Tasaki §11.5.4,
eqs. (11.5.13), (11.5.24)). -/
noncomputable def ttHamiltonian (K : ℕ) (ν s t u1 u2 U : ℝ) :
    ManyBodyOp (Fin (2 * (5 * K + 4) + 2)) :=
  ttHopping K ν s t u1 u2 + ttInteraction K U

/-- **Tasaki Theorem 11.27 (Tanaka–Tasaki metallic ferromagnetism), AXIOM.**  For the
`d = 1` Tanaka–Tasaki model, if `u₁ > 2(|s| + 2|t|)` (Tasaki's `u₁ > 2d(|s|+2|t|)`) and the
electron number satisfies `L = K + 1 ≤ Ne ≤ 2L = 2(K + 1)` (Tasaki's `L^d ≤ N ≤ 2L^d`), then
in the limit `u₂, U ↑ ∞` (for large enough `u₂, U`) the ground states have the **maximum
possible total spin** `S_tot = Ne/2`: every ground state in the `Ne`-electron hard-core ground
subspace is an `(Ŝ_tot)²` eigenvector at `(Ne/2)(Ne/2 + 1)`.  (Tasaki states only the maximal
spin, not the precise degeneracy, so this is weaker than `IsMaximalSpinMultipletSubmodule`.)
The ground states are metallic when `1 < Ne/L < 2`.  Tasaki cites the original paper [63] for
the technical proof; recorded as a documented axiom. -/
axiom theorem_11_27 (K : ℕ) (ν s t u1 : ℝ) (hν : 0 < ν)
    (hu1 : 2 * (|s| + 2 * |t|) < u1) (Ne : ℕ) (hNe1 : K + 1 ≤ Ne) (hNe2 : Ne ≤ 2 * (K + 1)) :
    ∃ W V : ℝ, 0 < W ∧ 0 < V ∧
      ∀ u2 U : ℝ, W ≤ u2 → V ≤ U →
        ∀ v ∈ groundSubmoduleAtFilling (ttHamiltonian K ν s t u1 u2 U) Ne,
          (fermionTotalSpinSquared (5 * K + 4)).mulVec v
            = (((Ne : ℂ) / 2) * ((Ne : ℂ) / 2 + 1)) • v

end LatticeSystem.Fermion
