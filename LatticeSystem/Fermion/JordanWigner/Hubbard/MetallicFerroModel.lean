import LatticeSystem.Fermion.JordanWigner.Hubbard.TJModel
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJMaximalSpinUnified

/-!
# Tasaki §11.5.3: the d = 1 decorated Hubbard model (towards Theorem 11.26)

This file sets up the one-dimensional Hubbard model on the *duplicated-internal-site*
decorated lattice `Λ = E ∪ (I × {1, 2})` of Tasaki §11.5.3, whose `t, U ↑ ∞` limit is the
ferromagnetic t-J model (Lemma 11.25) and which exhibits metallic ferromagnetism in one
dimension (Theorem 11.26).  Compared with the §11.3.1 flat-band chain, each internal site
`u ∈ I` is *duplicated* into two copies `(u, 1)`, `(u, 2)`; this duplication is what makes the
`â`-operators satisfy the *standard* (normalised) anticommutation relation
`{â_{p,σ}, â†_{q,τ}} = (1 + 4dν²) δ_{p,q} δ_{σ,τ}` (eq. (11.5.11)), which simplifies the
analysis.

**Lattice realisation (`d = 1`, `K + 1` cells, periodic).**  The `3(K + 1)` physical sites
are packed into `Fin (3K + 3)` by `cell ↦ {0 ↦ external, 1 ↦ internal copy 1, 2 ↦ internal
copy 2}`: external `p ↦ 3p`, internal `(c, 1) ↦ 3c + 1`, `(c, 2) ↦ 3c + 2`, where the
internal "bond" `c` sits between the external sites `c` and `c + 1` (cyclically).  The
spinful Jordan–Wigner backbone is `ManyBodyOp (Fin (2(3K+2)+2))`.

**Localised single-particle states** (eqs. (11.5.7)–(11.5.9), `d = 1`, unit shift `b`; the
bond just after external `p` is `p`, the bond just before is `p − 1`):
* `α_p` : `1` at `p`; `ν` at `(p, 1)`; `−ν` at `(p, 2)`, `(p−1, 1)`, `(p−1, 2)`.
* `β_{(c,1)}` : `1` at `(c, 1)`; `ν` at external `c + 1`; `−ν` at external `c`.
* `β_{(c,2)}` : `1` at `(c, 2)`; `ν` at external `c + 1` and external `c`.

**Hamiltonian** `Ĥ = Ĥ_hop + Ĥ_int` with `Ĥ_int = U Σ_x n̂_{x↑} n̂_{x↓}` (eq. (11.5.13)) and
`Ĥ_hop = t Σ_{(c,ζ),σ} b̂†_{(c,ζ),σ} b̂_{(c,ζ),σ} − s Σ_{⟨p,q⟩∈E,σ} â†_{p,σ} â_{q,σ}`
(eq. (11.5.14), `s ∈ ℝ\{0}`, `t > 0`); the off-diagonal `â†_p â_q` over adjacent external
pairs makes the lowest (`α`) band dispersive, distinguishing this from the §11.4.3 model.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.3, eqs. (11.5.7)–(11.5.14) (pp. 445–447).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- The external site `p ∈ E` packed into `Fin (3K + 3)` at index `3p`. -/
def decExternalSite (K : ℕ) (p : Fin (K + 1)) : Fin (3 * K + 3) :=
  ⟨3 * p.val, by have := p.isLt; omega⟩

/-- The first copy `(c, 1)` of the internal site of bond `c`, packed at index `3c + 1`. -/
def decInternalSite1 (K : ℕ) (c : Fin (K + 1)) : Fin (3 * K + 3) :=
  ⟨3 * c.val + 1, by have := c.isLt; omega⟩

/-- The second copy `(c, 2)` of the internal site of bond `c`, packed at index `3c + 2`. -/
def decInternalSite2 (K : ℕ) (c : Fin (K + 1)) : Fin (3 * K + 3) :=
  ⟨3 * c.val + 2, by have := c.isLt; omega⟩

/-- The single-particle state `α_p` (eq. (11.5.7), `d = 1`) as a coefficient vector over the
`3(K+1)` physical sites: `1` at external `p`; `ν` at internal `(p, 1)`; `−ν` at `(p, 2)` and
at both copies `(p−1, 1)`, `(p−1, 2)` of the preceding bond. -/
def decAlpha (K : ℕ) (ν : ℝ) (p : Fin (K + 1)) : Fin (3 * K + 3) → ℝ :=
  fun x =>
    if x = decExternalSite K p then 1
    else if x = decInternalSite1 K p then ν
    else if x = decInternalSite2 K p ∨ x = decInternalSite1 K (p - 1) ∨
        x = decInternalSite2 K (p - 1) then -ν
    else 0

/-- The single-particle state `β_{(c,1)}` (eq. (11.5.8), `d = 1`): `1` at internal `(c, 1)`;
`ν` at external `c + 1`; `−ν` at external `c`. -/
def decBeta1 (K : ℕ) (ν : ℝ) (c : Fin (K + 1)) : Fin (3 * K + 3) → ℝ :=
  fun x =>
    if x = decInternalSite1 K c then 1
    else if x = decExternalSite K (c + 1) then ν
    else if x = decExternalSite K c then -ν
    else 0

/-- The single-particle state `β_{(c,2)}` (eq. (11.5.9), `d = 1`): `1` at internal `(c, 2)`;
`ν` at both external neighbours `c` and `c + 1`. -/
def decBeta2 (K : ℕ) (ν : ℝ) (c : Fin (K + 1)) : Fin (3 * K + 3) → ℝ :=
  fun x =>
    if x = decInternalSite2 K c then 1
    else if x = decExternalSite K (c + 1) ∨ x = decExternalSite K c then ν
    else 0

/-- `â_{p,σ}` (eq. (11.5.10)): the annihilation operator of the single-particle state `α_p`,
`â_{p,σ} = Σ_x α_p(x) ĉ_{x,σ}` on the spinful backbone. -/
noncomputable def decACreationAux (K : ℕ) (ν : ℝ) (p : Fin (K + 1)) (σ : Fin 2)
    (creation : Bool) : ManyBodyOp (Fin (2 * (3 * K + 2) + 2)) :=
  ∑ x : Fin (3 * K + 3), (decAlpha K ν p x : ℂ) •
    (if creation then fermionMultiCreation (2 * (3 * K + 2) + 1) (spinfulIndex (3 * K + 2) x σ)
      else fermionMultiAnnihilation (2 * (3 * K + 2) + 1) (spinfulIndex (3 * K + 2) x σ))

/-- `â_{p,σ}` — annihilation operator of `α_p`. -/
noncomputable def decAAnnihilation (K : ℕ) (ν : ℝ) (p : Fin (K + 1)) (σ : Fin 2) :
    ManyBodyOp (Fin (2 * (3 * K + 2) + 2)) :=
  decACreationAux K ν p σ false

/-- `â†_{p,σ}` — creation operator of `α_p` (`α_p` is real, so coefficients are unchanged). -/
noncomputable def decACreation (K : ℕ) (ν : ℝ) (p : Fin (K + 1)) (σ : Fin 2) :
    ManyBodyOp (Fin (2 * (3 * K + 2) + 2)) :=
  decACreationAux K ν p σ true

/-- `b̂_{(c,ζ),σ}` (eq. (11.5.10)): the annihilation operator of `β_{(c,ζ)}`
(`ζ : Fin 2`, `0 ↦ copy 1`, `1 ↦ copy 2`). -/
noncomputable def decBAnnihilation (K : ℕ) (ν : ℝ) (c : Fin (K + 1)) (ζ σ : Fin 2) :
    ManyBodyOp (Fin (2 * (3 * K + 2) + 2)) :=
  ∑ x : Fin (3 * K + 3),
    (((if ζ = 0 then decBeta1 K ν c x else decBeta2 K ν c x) : ℝ) : ℂ) •
      fermionMultiAnnihilation (2 * (3 * K + 2) + 1) (spinfulIndex (3 * K + 2) x σ)

/-- `b̂†_{(c,ζ),σ}` — creation operator of `β_{(c,ζ)}`. -/
noncomputable def decBCreation (K : ℕ) (ν : ℝ) (c : Fin (K + 1)) (ζ σ : Fin 2) :
    ManyBodyOp (Fin (2 * (3 * K + 2) + 2)) :=
  ∑ x : Fin (3 * K + 3),
    (((if ζ = 0 then decBeta1 K ν c x else decBeta2 K ν c x) : ℝ) : ℂ) •
      fermionMultiCreation (2 * (3 * K + 2) + 1) (spinfulIndex (3 * K + 2) x σ)

/-- **The hopping Hamiltonian** `Ĥ_hop` (eq. (11.5.14)):
`t Σ_{(c,ζ),σ} b̂†_{(c,ζ),σ} b̂_{(c,ζ),σ} − s Σ_{⟨p,q⟩∈E,σ} â†_{p,σ} â_{q,σ}`, where the
external hopping runs over ordered adjacent pairs `q = p ± 1` of the periodic chain `E`. -/
noncomputable def decHopping (K : ℕ) (ν s t : ℝ) :
    ManyBodyOp (Fin (2 * (3 * K + 2) + 2)) :=
  (t : ℂ) • ∑ c : Fin (K + 1), ∑ ζ : Fin 2, ∑ σ : Fin 2,
      decBCreation K ν c ζ σ * decBAnnihilation K ν c ζ σ
    - (s : ℂ) • ∑ p : Fin (K + 1), ∑ σ : Fin 2,
      (decACreation K ν p σ * decAAnnihilation K ν (p + 1) σ +
        decACreation K ν p σ * decAAnnihilation K ν (p - 1) σ)

/-- **The interaction Hamiltonian** `Ĥ_int = U Σ_x n̂_{x↑} n̂_{x↓}` (eq. (11.5.13)), the
on-site Hubbard repulsion over all `3(K+1)` physical sites. -/
noncomputable def decInteraction (K : ℕ) (U : ℝ) :
    ManyBodyOp (Fin (2 * (3 * K + 2) + 2)) :=
  ∑ x : Fin (3 * K + 3),
    (U : ℂ) • hubbardDoubleOccupancy (3 * K + 2) x

/-- **The d = 1 decorated Hubbard model** `Ĥ = Ĥ_hop + Ĥ_int` of Tasaki §11.5.3
(eqs. (11.5.13)–(11.5.14)), whose `t, U ↑ ∞` limit gives metallic ferromagnetism
(Theorem 11.26). -/
noncomputable def decHubbardHamiltonian (K : ℕ) (ν s t U : ℝ) :
    ManyBodyOp (Fin (2 * (3 * K + 2) + 2)) :=
  decHopping K ν s t + decInteraction K U

/-- **Tasaki Lemma 11.25 (Hubbard–t-J equivalence in the strong-coupling limit), AXIOM.**
The `t, U ↑ ∞` limit of the decorated Hubbard model `decHubbardHamiltonian K ν s t U` at
electron number `Ne` (`≤` the `|E| = K + 1` lowest-band states) is equivalent to the
`J ↑ ∞` limit of the ferromagnetic t-J model (eq. (11.5.4)) on the external chain
`E = cycleGraph (K + 1)` with the same electron number `Ne` and hopping amplitude
`τ = (1 + 4dν²)s` (here `d = 1`, so `τ = (1 + 4ν²)s`).  Tasaki's proof identifies both
finite-energy subspaces with hard-core electrons on `E` carrying the *same effective
Hamiltonian* (Theorem A.12 / Lemma A.11), so the ground spaces — and in particular their
total-spin structure — coincide.  We render this **spin-structure transfer** faithfully: for
large enough `t, U, J` the Hubbard ground subspace at filling `Ne` is the maximal-spin
`(Ne + 1)`-fold multiplet **iff** the t-J ground subspace is.  (Combined with Proposition 11.24,
which supplies the t-J side, this yields Theorem 11.26.)  Recorded as a documented axiom. -/
axiom lemma_11_25 (K : ℕ) (ν s : ℝ) (hν : 0 < ν) (hs : 0 < s) (Ne : ℕ) (hNe : Ne ≤ K + 1) :
    ∃ T V W : ℝ, 0 < T ∧ 0 < V ∧ 0 < W ∧
      ∀ t U J : ℝ, T ≤ t → V ≤ U → W ≤ J →
        (IsMaximalSpinMultipletSubmodule (3 * K + 2)
            (groundSubmoduleAtFilling (decHubbardHamiltonian K ν s t U) Ne) Ne ↔
          IsMaximalSpinMultipletSubmodule K
            (groundSubmoduleAtFilling
              (tJHamiltonian K (SimpleGraph.cycleGraph (K + 1)) ((1 + 4 * ν ^ 2) * s) J) Ne) Ne)

/-- **Tasaki Theorem 11.26 (metallic ferromagnetism in the d = 1 Hubbard model), AXIOM.**
For the one-dimensional decorated Hubbard model `decHubbardHamiltonian K ν s t U`, if the
electron number `Ne` is **odd** and `≤ K + 1 = |E|` (Tasaki's `N ≤ L`), then in the limit
`t, U ↑ ∞` (for large enough `t, U`) the ground states have total spin `S_tot = Ne/2` and are
non-degenerate apart from the trivial `2 S_tot + 1 = Ne + 1`-fold `SU(2)` multiplet — captured
at once by `IsMaximalSpinMultipletSubmodule`.  The ground states are *metallic* when `Ne < K+1`
(the lowest band is partially filled, density `Ne/L < 1`) and reduce to the insulating
Heisenberg ferromagnet at `Ne = K + 1`.  Tasaki derives this from Proposition 11.24 (the t-J
side) and Lemma 11.25 (the equivalence) via a Perron–Frobenius argument; recorded as a
PROVED from Lemma 11.25 (the documented strong-coupling equivalence axiom) and the t-J side
(`tJ_isMaximalSpinMultiplet_of_le`). -/
theorem theorem_11_26 (K : ℕ) (ν s : ℝ) (hν : 0 < ν) (hs : 0 < s) (Ne : ℕ)
    (hNe : Ne ≤ K + 1) (hodd : Odd Ne) :
    ∃ T V : ℝ, 0 < T ∧ 0 < V ∧
      ∀ t U : ℝ, T ≤ t → V ≤ U →
        IsMaximalSpinMultipletSubmodule (3 * K + 2)
          (groundSubmoduleAtFilling (decHubbardHamiltonian K ν s t U) Ne) Ne := by
  obtain ⟨T, V, W, hT, hV, hW, hiff⟩ := lemma_11_25 K ν s hν hs Ne hNe
  refine ⟨T, V, hT, hV, fun t U htT hUV => ?_⟩
  rw [hiff t U W htT hUV (le_refl W)]
  exact tJ_isMaximalSpinMultiplet_of_le K ((1 + 4 * ν ^ 2) * s) W
    (mul_pos (by positivity) hs) hW Ne hNe hodd

end LatticeSystem.Fermion
