import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandProjectionBridge
import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandDisconnected

/-!
# Tasaki Theorem 11.15: the projection-irreducibility bridge

This file discharges `tasaki_theorem_11_15`
(`generalFlatBandFerromagnetic T U ↔ generalFlatBandProjectionIrreducible T`) by composing the
already-proved Theorem 11.17 (`generalFlatBand_theorem_11_17`,
`ferromagnetic ↔ basis connected`) with the purely combinatorial/linear-algebraic **bridge**

`generalFlatBandProjectionIrreducible T ↔ generalFlatBandBasisConnected I μ`.

The bridge factors through an intermediate `generalFlatBandProjectionBlockReducible` predicate — the
existence of a coordinate cut `W` separating two active sites with no `P₀` entries across it:

* `blockReducible ↔ ¬ basisConnected` — direction `¬basisConnected ⟹ blockReducible` builds the
  cut from the basis disconnection (`exists_disconnection_cut_of_not_connected` +
  `generalFlatBand_proj_offdiag_eq_zero_across_cut`); the converse uses
  `generalFlatBand_mu_confined_of_block` (a basis vector cannot straddle a `P₀`-block cut).
* `projectionIrreducible ↔ ¬ blockReducible` — the support matrix on the active sites is irreducible
  (strongly connected) iff there is no such block cut.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §11.3.4, Theorem 11.15, pp. 408–412.
-/

namespace LatticeSystem.Fermion

open Matrix
open scoped ComplexOrder

variable {M : ℕ} (T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ)

/-- **`P₀` is block-reducible**: there is a coordinate set `W` containing an active site, whose
complement also contains an active site, with no `P₀` entries linking `W` to its complement
(`(P₀)_{yx} = 0` for `x ∈ W`, `y ∉ W`).  This is the matrix form of "the flat-band projection
decomposes into two non-interacting blocks", the negation of irreducibility. -/
def generalFlatBandProjectionBlockReducible : Prop :=
  ∃ W : Finset (Fin (M + 1)),
    (∃ x ∈ W, generalFlatBandProjectionMatrix T x x ≠ 0) ∧
    (∃ y ∉ W, generalFlatBandProjectionMatrix T y y ≠ 0) ∧
    (∀ x ∈ W, ∀ y ∉ W, generalFlatBandProjectionMatrix T y x = 0)

/-- **A disconnected basis gives a block-reducible projection**: if the special basis is not
connected then `P₀` is block-reducible.  Take the basis-disconnection cut `(A, Aᶜ)`
(`exists_disconnection_cut_of_not_connected`, with opposite-side `μ`'s of disjoint support) and let
`W` be the `μ`-support of the `A`-side.  Each index in `A` is an active site in `W` and each index
in `Aᶜ` an active site outside `W` (a shared site would be a forbidden cross-overlap), while
`(P₀)_{yx} = 0` across `W` by `generalFlatBand_proj_offdiag_eq_zero_across_cut` and `P₀`
Hermitian. -/
theorem generalFlatBand_blockReducible_of_not_basisConnected
    {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    (hbasis : IsGeneralFlatBandSpecialBasis T I μ) (hD0 : 0 < generalFlatBandDim T)
    (hnc : ¬ generalFlatBandBasisConnected I μ) :
    generalFlatBandProjectionBlockReducible T := by
  classical
  have hne : I.Nonempty := Finset.card_pos.mp (hbasis.1.symm ▸ hD0)
  obtain ⟨A, hAne, hAcne, hcut⟩ := exists_disconnection_cut_of_not_connected hnc hne
  -- per-site disjunction form of the cut
  have hdisj : ∀ z ∈ (↑A : Set ↥I), ∀ z' ∈ (↑A : Set ↥I)ᶜ, ∀ x, μ z.1 x = 0 ∨ μ z'.1 x = 0 := by
    intro z hz z' hz' x
    rw [Set.mem_compl_iff, Finset.mem_coe] at hz'
    rw [Finset.mem_coe] at hz
    exact mul_eq_zero.mp (hcut z hz z' (Finset.mem_compl.mpr hz') x)
  refine ⟨Finset.univ.filter (fun x => ∃ z ∈ A, μ z.1 x ≠ 0), ?_, ?_, ?_⟩
  · -- A-index site is active and in W
    obtain ⟨z₀, hz₀⟩ := hAne
    exact ⟨z₀.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, z₀, hz₀, hbasis.2.2.2.1 z₀.1 z₀.2⟩,
      generalFlatBand_special_index_active T hbasis z₀.2⟩
  · -- Aᶜ-index site is active and outside W
    obtain ⟨w₀, hw₀⟩ := hAcne
    have hw₀A : w₀ ∉ A := Finset.mem_compl.mp hw₀
    refine ⟨w₀.1, ?_, generalFlatBand_special_index_active T hbasis w₀.2⟩
    rw [Finset.mem_filter]
    rintro ⟨_, z, hzA, hzw⟩
    exact mul_ne_zero hzw (hbasis.2.2.2.1 w₀.1 w₀.2) (hcut z hzA w₀ hw₀ w₀.1)
  · -- no P₀ entries across W
    intro x hxW y hyW
    rw [Finset.mem_filter] at hxW
    obtain ⟨_, zx, hzxA, hzxx⟩ := hxW
    have hxS : ∀ z ∈ (↑A : Set ↥I)ᶜ, μ z.1 x = 0 := by
      intro z hz
      rw [Set.mem_compl_iff, Finset.mem_coe] at hz
      exact (mul_eq_zero.mp (hcut zx hzxA z (Finset.mem_compl.mpr hz) x)).resolve_left hzxx
    have hyS : ∀ z ∈ (↑A : Set ↥I), μ z.1 y = 0 := by
      intro z hz
      rw [Finset.mem_coe] at hz
      by_contra hzy
      exact hyW (Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, hz, hzy⟩)
    have hxy : generalFlatBandProjectionMatrix T x y = 0 :=
      generalFlatBand_proj_offdiag_eq_zero_across_cut T hbasis (↑A : Set ↥I) hdisj hxS hyS
    have hH := generalFlatBandProjectionMatrix_isHermitian T
    have h2 := hH.apply x y
    rw [hxy] at h2
    exact star_eq_zero.mp h2

end LatticeSystem.Fermion
