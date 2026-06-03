import LatticeSystem.Fermion.JordanWigner.Hubbard
import LatticeSystem.Fermion.JordanWigner.Hubbard.HardcoreProjection

/-!
# Tasaki's flat-band model: the d = 1 decorated (Delta) chain (Tasaki §11.3.1)

This file sets up the geometry of the simplest version of Tasaki's flat-band
Hubbard model — the one-dimensional decorated chain (the "Delta chain") of
Tasaki §11.3.1.  The lattice is `Λ = E ∪ I`, where `E` are the `K + 1` external
sites (the original periodic chain) and `I` are the `K + 1` internal sites (one
per bond, at the bond midpoints).

The decorated chain has `2(K + 1)` physical sites, so it is realized inside the
existing spinful Hubbard framework on `N + 1 = 2K + 2` sites (i.e. Hubbard
`N = 2K + 1`), with the external/internal sites **interleaved** into the physical
chain `Fin (2K + 2)`:

* external site `i : Fin (K + 1)` ↦ physical site `2 i`  ([`deltaExternalSite`]);
* internal site `i : Fin (K + 1)` ↦ physical site `2 i + 1`  ([`deltaInternalSite`]).

Spinful modes then reuse the existing [`spinfulIndex`] `(2K+1)`.  Adjacency: in
`d = 1` the external site `p` (midpoint position `p`) is incident to the two
internal sites at distance `1/2`, namely the bonds `p - 1` and `p` (periodic);
equivalently internal site `u` is incident to external sites `u` and `u + 1`.

This is the first file of the §11.3.1 development (Issue #4158); it provides the
site embeddings and their injectivity/disjointness, on which the single-particle
states `α_p`, `β_u` and the fermion operators `â`, `b̂` are built.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1, eqs. (11.3.1)–(11.3.6).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- The external site `i` of the `d = 1` decorated chain, as a physical site
`2 i` of the underlying `Fin (2K + 2)` spinful chain. -/
def deltaExternalSite (K : ℕ) (i : Fin (K + 1)) : Fin (2 * K + 2) :=
  ⟨2 * i.val, by have := i.isLt; omega⟩

/-- The internal site `i` of the `d = 1` decorated chain, as a physical site
`2 i + 1` of the underlying `Fin (2K + 2)` spinful chain. -/
def deltaInternalSite (K : ℕ) (i : Fin (K + 1)) : Fin (2 * K + 2) :=
  ⟨2 * i.val + 1, by have := i.isLt; omega⟩

/-- External and internal sites never coincide (external sites are even, internal
sites are odd). -/
theorem deltaExternalSite_ne_internal (K : ℕ) (i j : Fin (K + 1)) :
    deltaExternalSite K i ≠ deltaInternalSite K j := by
  intro h
  have : 2 * i.val = 2 * j.val + 1 := congrArg Fin.val h
  omega

/-- The external-site embedding is injective. -/
theorem deltaExternalSite_injective (K : ℕ) :
    Function.Injective (deltaExternalSite K) := by
  intro i j h
  have : 2 * i.val = 2 * j.val := congrArg Fin.val h
  exact Fin.ext (by omega)

/-- The internal-site embedding is injective. -/
theorem deltaInternalSite_injective (K : ℕ) :
    Function.Injective (deltaInternalSite K) := by
  intro i j h
  have : 2 * i.val + 1 = 2 * j.val + 1 := congrArg Fin.val h
  exact Fin.ext (by omega)

/-- Every physical site of the decorated chain is either an external site or an
internal site (the embeddings cover `Fin (2K + 2)`). -/
theorem deltaSite_cover (K : ℕ) (x : Fin (2 * K + 2)) :
    (∃ i, x = deltaExternalSite K i) ∨ (∃ i, x = deltaInternalSite K i) := by
  rcases Nat.even_or_odd x.val with ⟨m, hm⟩ | ⟨m, hm⟩
  · refine Or.inl ⟨⟨m, by have := x.isLt; omega⟩, ?_⟩
    exact Fin.ext (by simp [deltaExternalSite, hm, two_mul])
  · refine Or.inr ⟨⟨m, by have := x.isLt; omega⟩, ?_⟩
    exact Fin.ext (by simp [deltaInternalSite, hm])

/-! ## Single-particle states `α_p` and `β_u` (eqs. (11.3.1), (11.3.2)) -/

/-- The single-particle state `α_p` (eq. (11.3.1)) as a coefficient vector over
the physical sites: `1` at the external site `p`, `−ν` at the two incident
internal sites (bonds `p` and `p − 1`, periodic), `0` elsewhere. -/
def flatBandAlpha (K : ℕ) (ν : ℝ) (p : Fin (K + 1)) : Fin (2 * K + 2) → ℝ :=
  fun x =>
    if x = deltaExternalSite K p then 1
    else if x = deltaInternalSite K p ∨ x = deltaInternalSite K (p - 1) then -ν
    else 0

/-- The single-particle state `β_u` (eq. (11.3.2)) as a coefficient vector over
the physical sites: `1` at the internal site `u`, `+ν` at the two incident
external sites (`u` and `u + 1`, periodic), `0` elsewhere. -/
def flatBandBeta (K : ℕ) (ν : ℝ) (u : Fin (K + 1)) : Fin (2 * K + 2) → ℝ :=
  fun x =>
    if x = deltaInternalSite K u then 1
    else if x = deltaExternalSite K u ∨ x = deltaExternalSite K (u + 1) then ν
    else 0

/-! ## Fermion operators `â_{p,σ}` and `b̂_{u,σ}` (eqs. (11.3.3), (11.3.4))

`â_{p,σ} = Ĉ_σ(α_p) = Σ_x α_p(x) ĉ_{x,σ}` and `b̂_{u,σ} = Ĉ_σ(β_u)`, expressed in
the underlying spinful Hubbard chain (`fermionMultiAnnihilation (2K+1)` at the
spinful mode `spinfulIndex (2K+1) x σ`). -/

/-- `â_{p,σ}` (eq. (11.3.3)): the annihilation operator of the single-particle
state `α_p`. -/
noncomputable def flatBandAAnnihilation (K : ℕ) (ν : ℝ) (p : Fin (K + 1))
    (σ : Fin 2) : ManyBodyOp (Fin (2 * (2 * K + 1) + 2)) :=
  ∑ x : Fin (2 * K + 2), (flatBandAlpha K ν p x : ℂ) •
    fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ)

/-- `â†_{p,σ}`: the creation operator of `α_p` (adjoint of `flatBandAAnnihilation`;
`α_p` is real, so the coefficients are unchanged). -/
noncomputable def flatBandACreation (K : ℕ) (ν : ℝ) (p : Fin (K + 1))
    (σ : Fin 2) : ManyBodyOp (Fin (2 * (2 * K + 1) + 2)) :=
  ∑ x : Fin (2 * K + 2), (flatBandAlpha K ν p x : ℂ) •
    fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ)

/-- `b̂_{u,σ}` (eq. (11.3.4)): the annihilation operator of the single-particle
state `β_u`. -/
noncomputable def flatBandBAnnihilation (K : ℕ) (ν : ℝ) (u : Fin (K + 1))
    (σ : Fin 2) : ManyBodyOp (Fin (2 * (2 * K + 1) + 2)) :=
  ∑ x : Fin (2 * K + 2), (flatBandBeta K ν u x : ℂ) •
    fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ)

/-- `b̂†_{u,σ}`: the creation operator of `β_u`. -/
noncomputable def flatBandBCreation (K : ℕ) (ν : ℝ) (u : Fin (K + 1))
    (σ : Fin 2) : ManyBodyOp (Fin (2 * (2 * K + 1) + 2)) :=
  ∑ x : Fin (2 * K + 2), (flatBandBeta K ν u x : ℂ) •
    fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ)

/-- `flatBandACreation` is the adjoint of `flatBandAAnnihilation`. -/
theorem flatBandACreation_eq_conjTranspose (K : ℕ) (ν : ℝ) (p : Fin (K + 1))
    (σ : Fin 2) :
    (flatBandAAnnihilation K ν p σ)ᴴ = flatBandACreation K ν p σ := by
  unfold flatBandAAnnihilation flatBandACreation
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Matrix.conjTranspose_smul, fermionMultiAnnihilation_conjTranspose]
  congr 1
  simp [Complex.conj_ofReal]

/-- `flatBandBCreation` is the adjoint of `flatBandBAnnihilation`. -/
theorem flatBandBCreation_eq_conjTranspose (K : ℕ) (ν : ℝ) (u : Fin (K + 1))
    (σ : Fin 2) :
    (flatBandBAnnihilation K ν u σ)ᴴ = flatBandBCreation K ν u σ := by
  unfold flatBandBAnnihilation flatBandBCreation
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Matrix.conjTranspose_smul, fermionMultiAnnihilation_conjTranspose]
  congr 1
  simp [Complex.conj_ofReal]

/-! ## The Tasaki flat-band Hamiltonian (eqs. (11.3.5), (11.3.6)) -/

/-- **The Tasaki flat-band Hamiltonian** `Ĥ = Ĥ_hop + Ĥ_int` (eqs. (11.3.5),
(11.3.6)): `Ĥ_hop = t Σ_{u,σ} b̂†_{u,σ} b̂_{u,σ}` (the flat-band kinetic term) plus
the standard on-site Hubbard interaction `Ĥ_int = U Σ_x n̂_{x,↑} n̂_{x,↓}`. -/
noncomputable def flatBandHamiltonian (K : ℕ) (ν t U : ℝ) :
    ManyBodyOp (Fin (2 * (2 * K + 1) + 2)) :=
  (t : ℂ) • (∑ u : Fin (K + 1), ∑ σ : Fin 2,
      flatBandBCreation K ν u σ * flatBandBAnnihilation K ν u σ)
    + (U : ℂ) • (∑ x : Fin (2 * K + 2), hubbardDoubleOccupancy (2 * K + 1) x)

/-- Each flat-band kinetic term `b̂†_{u,σ} b̂_{u,σ}` is Hermitian. -/
theorem flatBandBCreation_mul_BAnnihilation_isHermitian (K : ℕ) (ν : ℝ)
    (u : Fin (K + 1)) (σ : Fin 2) :
    (flatBandBCreation K ν u σ * flatBandBAnnihilation K ν u σ).IsHermitian := by
  have hb : (flatBandBCreation K ν u σ)ᴴ = flatBandBAnnihilation K ν u σ := by
    rw [← flatBandBCreation_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  change (flatBandBCreation K ν u σ * flatBandBAnnihilation K ν u σ)ᴴ = _
  rw [Matrix.conjTranspose_mul, flatBandBCreation_eq_conjTranspose, hb]

/-- The Tasaki flat-band Hamiltonian is Hermitian. -/
theorem flatBandHamiltonian_isHermitian (K : ℕ) (ν t U : ℝ) :
    (flatBandHamiltonian K ν t U).IsHermitian := by
  have hsa : ∀ r : ℝ, IsSelfAdjoint (r : ℂ) := fun r =>
    isSelfAdjoint_iff.mpr (by rw [Complex.star_def, Complex.conj_ofReal])
  have hsum : ∀ {ι : Type} (s : Finset ι) (M : ι → ManyBodyOp (Fin (2 * (2 * K + 1) + 2))),
      (∀ i ∈ s, (M i).IsHermitian) → (∑ i ∈ s, M i).IsHermitian := by
    intro ι s M hM
    exact Finset.sum_induction _ _ (fun _ _ hA hB => hA.add hB) Matrix.isHermitian_zero hM
  unfold flatBandHamiltonian
  refine Matrix.IsHermitian.add ?_ ?_
  · exact (hsum Finset.univ _ (fun u _ =>
      hsum Finset.univ _ (fun σ _ =>
        flatBandBCreation_mul_BAnnihilation_isHermitian K ν u σ))).smul (hsa t)
  · exact (hsum Finset.univ _ (fun x _ =>
      hubbardDoubleOccupancy_isHermitian (2 * K + 1) x)).smul (hsa U)

end LatticeSystem.Fermion

