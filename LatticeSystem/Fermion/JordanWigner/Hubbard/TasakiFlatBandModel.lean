import LatticeSystem.Fermion.JordanWigner.Hubbard

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

end LatticeSystem.Fermion
