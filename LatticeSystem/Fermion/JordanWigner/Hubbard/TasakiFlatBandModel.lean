import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandModelCore

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

