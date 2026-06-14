import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandProjectionBlock
import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandDisconnected

/-!
# Tasaki Theorem 11.15: the projection-irreducibility bridge (DISCHARGED)

This file discharges `tasaki_theorem_11_15`
(`generalFlatBandFerromagnetic T U ↔ generalFlatBandProjectionIrreducible T`) by composing the
proved Theorem 11.17 (`generalFlatBand_theorem_11_17`, `ferromagnetic ↔ basis connected`) with the
purely combinatorial/linear-algebraic **bridge**

`generalFlatBandProjectionIrreducible T ↔ generalFlatBandBasisConnected I μ`.

The bridge factors through an intermediate `generalFlatBandProjectionBlockReducible` predicate — the
existence of a coordinate cut `W` separating two active sites with no `P₀` entries across it:

* `blockReducible ↔ ¬ basisConnected` (`generalFlatBand_blockReducible_of_not_basisConnected` and
  `generalFlatBand_not_basisConnected_of_blockReducible`): a basis disconnection gives a `μ`-support
  cut (`exists_disconnection_cut_of_not_connected` plus
  `generalFlatBand_proj_offdiag_eq_zero_across_cut`)
  and conversely each `μ_z` is confined to one side of a block cut
  (`generalFlatBand_mu_confined_of_block`).
* `projectionIrreducible ↔ ¬ blockReducible`
  (`generalFlatBand_not_projectionIrreducible_of_blockReducible` and
  `generalFlatBand_blockReducible_of_not_projectionIrreducible`): the support matrix on the active
  sites is irreducible iff there is no such block cut (support powers stay in a block;
  conversely the reachable set from an unreachable pair is a block cut).

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

/-- **A block-reducible projection forces a disconnected basis**: if `P₀` is block-reducible then
the special basis is not connected.  For a block cut `W`, each `μ_z` is confined to its index's side
(`generalFlatBand_mu_confined_of_block`): `z.1 ∈ W ⟹ μ_z` supported in `W`, `z.1 ∉ W ⟹ μ_z`
supported in `Wᶜ`.  Hence the index set splits into `J = {z | z.1 ∈ W}` and its complement (both
nonempty, witnessed by the active sites on each side), with no basis edge crossing — a crossing edge
`z ~ z'` would need a shared site `x` with `μ_z(x), μ_{z'}(x) ≠ 0`, impossible since `μ_z` lives in
`W` and `μ_{z'}` in `Wᶜ`.  A vertex in `J` therefore cannot reach one outside `J`. -/
theorem generalFlatBand_not_basisConnected_of_blockReducible
    {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hred : generalFlatBandProjectionBlockReducible T) :
    ¬ generalFlatBandBasisConnected I μ := by
  classical
  obtain ⟨W, ⟨xa, hxaW, hxaA⟩, ⟨yb, hybW, hybA⟩, hblock⟩ := hred
  -- symmetric block hypothesis for the complementary side
  have hblock' : ∀ a ∈ Wᶜ, ∀ b ∉ Wᶜ, generalFlatBandProjectionMatrix T b a = 0 := by
    intro a ha b hb
    rw [Finset.mem_compl] at ha
    simp only [Finset.mem_compl, not_not] at hb
    have h := hblock b hb a ha
    have h2 := (generalFlatBandProjectionMatrix_isHermitian T).apply a b
    rw [h] at h2
    exact star_eq_zero.mp h2
  -- each basis vector is confined to its index's side
  have hconfW : ∀ z ∈ I, z ∈ W → ∀ x ∉ W, μ z x = 0 :=
    fun z hzI hzW x hxW => generalFlatBand_mu_confined_of_block T hbasis W hblock hzI hzW hxW
  have hconfWc : ∀ z ∈ I, z ∉ W → ∀ x ∈ W, μ z x = 0 := by
    intro z hzI hzW x hxW
    exact generalFlatBand_mu_confined_of_block T hbasis Wᶜ hblock' hzI
      (Finset.mem_compl.mpr hzW) (by simp only [Finset.mem_compl, not_not]; exact hxW)
  -- the index side `{z | z.1 ∈ W}` is closed under basis-graph adjacency
  have hadj : ∀ u v : ↥I, (generalFlatBandBasisGraph I μ).Adj u v → u.1 ∈ W → v.1 ∈ W := by
    intro u v hAdj huW
    obtain ⟨_, x, hux, hvx⟩ := hAdj
    have hxW : x ∈ W := by
      by_contra hxW; exact hux (hconfW u.1 u.2 huW x hxW)
    by_contra hvW; exact hvx (hconfWc v.1 v.2 hvW x hxW)
  have hclosed : ∀ {u v : ↥I}, (generalFlatBandBasisGraph I μ).Reachable u v →
      u.1 ∈ W → v.1 ∈ W := by
    intro u v hr
    obtain ⟨p⟩ := hr
    induction p with
    | nil => exact id
    | cons h _ ih => exact fun hu => ih (hadj _ _ h hu)
  -- the two active sites give vertices on opposite sides
  obtain ⟨za, hzaI, hza_ne⟩ := (generalFlatBand_active_iff_exists_mu_ne T hbasis xa).mp hxaA
  obtain ⟨zb, hzbI, hzb_ne⟩ := (generalFlatBand_active_iff_exists_mu_ne T hbasis yb).mp hybA
  have ha : za ∈ W := by by_contra h; exact hza_ne (hconfWc za hzaI h xa hxaW)
  have hb : zb ∉ W := by intro h; exact hzb_ne (hconfW zb hzbI h yb hybW)
  intro hconn
  exact hb (hclosed (hconn.preconnected ⟨za, hzaI⟩ ⟨zb, hzbI⟩) ha)

/-- **Support powers stay inside a block**: if `(P₀)_{yx} = 0` across a coordinate cut `W`, then for
active sites `i` with `i.1 ∈ W` and `j` with `j.1 ∉ W`, every power `(support^k)_{ij} = 0`.  The
base case is the support entry itself (`|(P₀)_{ij}|² = 0`, since `P₀` is Hermitian and vanishes
across `W`); the induction splits the intermediate vertex `l` by side. -/
theorem generalFlatBand_support_pow_eq_zero_across_block
    (W : Finset (Fin (M + 1)))
    (hblock : ∀ x ∈ W, ∀ y ∉ W, generalFlatBandProjectionMatrix T y x = 0)
    (k : ℕ) (i j : generalFlatBandActiveSites T) (hi : i.1 ∈ W) (hj : j.1 ∉ W) :
    (generalFlatBandProjectionSupportMatrix T ^ k) i j = 0 := by
  have hbase : ∀ (a b : generalFlatBandActiveSites T), a.1 ∈ W → b.1 ∉ W →
      generalFlatBandProjectionSupportMatrix T a b = 0 := by
    intro a b ha hb
    change Complex.normSq (generalFlatBandProjectionMatrix T a.1 b.1) = 0
    rw [Complex.normSq_eq_zero]
    have h := hblock a.1 ha b.1 hb
    have h2 := (generalFlatBandProjectionMatrix_isHermitian T).apply b.1 a.1
    rw [h] at h2
    exact star_eq_zero.mp h2
  induction k generalizing j with
  | zero =>
    rw [pow_zero, Matrix.one_apply, if_neg]
    intro hij; rw [hij] at hi; exact hj hi
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun l _ => ?_)
    by_cases hl : l.1 ∈ W
    · rw [hbase l j hl hj, mul_zero]
    · rw [ih l hl, zero_mul]

/-- **A block-reducible projection is not irreducible**: if `P₀` is block-reducible then the support
matrix on the active sites is not irreducible.  The two active sites of the cut never connect:
every power of the support matrix vanishes between them
(`generalFlatBand_support_pow_eq_zero_across_block`), contradicting
`isIrreducible_iff_exists_pow_pos`. -/
theorem generalFlatBand_not_projectionIrreducible_of_blockReducible
    (hred : generalFlatBandProjectionBlockReducible T) :
    ¬ generalFlatBandProjectionIrreducible T := by
  obtain ⟨W, ⟨xa, hxaW, hxaA⟩, ⟨yb, hybW, hybA⟩, hblock⟩ := hred
  intro hirr
  have hnonneg : ∀ i j, 0 ≤ generalFlatBandProjectionSupportMatrix T i j :=
    fun i j => Complex.normSq_nonneg _
  obtain ⟨k, _, hpos⟩ :=
    ((isIrreducible_iff_exists_pow_pos hnonneg).mp hirr) ⟨xa, hxaA⟩ ⟨yb, hybA⟩
  rw [generalFlatBand_support_pow_eq_zero_across_block T W hblock k
    ⟨xa, hxaA⟩ ⟨yb, hybA⟩ hxaW hybW] at hpos
  exact lt_irrefl 0 hpos

/-- **A non-irreducible projection is block-reducible**: if the support matrix is not irreducible
then `P₀` is block-reducible.  By `isIrreducible_iff_exists_pow_pos` there are active sites `i₀, j₀`
with `(support^k)_{i₀ j₀} = 0` for all `k > 0` (no positive path).  Let `W` be the sites reachable
from `i₀` (every active site `i` with `(support^k)_{i₀ i} > 0` for some `k > 0`).  Then `i₀` is in
`W` (its diagonal `|(P₀)_{i₀ i₀}|² > 0` gives a self-loop) and `j₀` is not (it is unreachable);
both are active.  No `P₀` entry crosses out of `W`: an entry `(P₀)_{yx} ≠ 0` with `x ∈ W` active
would give a support edge `x → y` (Hermitian), extending a path from `i₀`, so `y` would be reachable
— contradiction; an inactive `y` has a zero projection row. -/
theorem generalFlatBand_blockReducible_of_not_projectionIrreducible
    (hred : ¬ generalFlatBandProjectionIrreducible T) :
    generalFlatBandProjectionBlockReducible T := by
  classical
  have hnonneg : ∀ i j, 0 ≤ generalFlatBandProjectionSupportMatrix T i j :=
    fun i j => Complex.normSq_nonneg _
  have hpownn : ∀ k i j, 0 ≤ (generalFlatBandProjectionSupportMatrix T ^ k) i j :=
    fun k => Matrix.pow_apply_nonneg hnonneg k
  have hloop : ∀ i : generalFlatBandActiveSites T,
      0 < generalFlatBandProjectionSupportMatrix T i i :=
    fun i => Complex.normSq_pos.mpr i.2
  have hni : ¬ ∀ i j, ∃ k > 0, 0 < (generalFlatBandProjectionSupportMatrix T ^ k) i j :=
    mt (isIrreducible_iff_exists_pow_pos hnonneg).mpr hred
  push Not at hni
  obtain ⟨i₀, j₀, hcut⟩ := hni
  have hnoreach : ∀ k, 0 < k → (generalFlatBandProjectionSupportMatrix T ^ k) i₀ j₀ = 0 :=
    fun k hk => le_antisymm (hcut k hk) (hpownn k i₀ j₀)
  refine ⟨Finset.univ.filter (fun x => ∃ i : generalFlatBandActiveSites T,
      (i : Fin (M + 1)) = x ∧ ∃ k, 0 < k ∧
        0 < (generalFlatBandProjectionSupportMatrix T ^ k) i₀ i), ?_, ?_, ?_⟩
  · refine ⟨i₀.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i₀, rfl, 1, one_pos, ?_⟩, i₀.2⟩
    rw [pow_one]; exact hloop i₀
  · refine ⟨j₀.1, ?_, j₀.2⟩
    rw [Finset.mem_filter]
    rintro ⟨_, i, hi, k, hk, hpos⟩
    rw [Subtype.ext hi, hnoreach k hk] at hpos
    exact lt_irrefl 0 hpos
  · intro x hxW y hyW
    rw [Finset.mem_filter] at hxW
    obtain ⟨_, ix, hix, kx, hkx, hposx⟩ := hxW
    by_cases hyact : generalFlatBandProjectionMatrix T y y = 0
    · exact generalFlatBand_proj_row_eq_zero_of_diag_zero T y x hyact
    · set jy : generalFlatBandActiveSites T := ⟨y, hyact⟩ with hjy
      by_contra hPyx
      have hPxy : generalFlatBandProjectionMatrix T ix.1 jy.1 ≠ 0 := by
        rw [hix]
        intro h0
        have h2 := (generalFlatBandProjectionMatrix_isHermitian T).apply jy.1 x
        rw [h0, star_zero] at h2
        exact hPyx h2.symm
      have hAedge : 0 < generalFlatBandProjectionSupportMatrix T ix jy :=
        Complex.normSq_pos.mpr hPxy
      have hreach : 0 < (generalFlatBandProjectionSupportMatrix T ^ (kx + 1)) i₀ jy := by
        rw [pow_succ, Matrix.mul_apply]
        exact Finset.sum_pos' (fun l _ => mul_nonneg (hpownn kx i₀ l) (hnonneg l jy))
          ⟨ix, Finset.mem_univ _, mul_pos hposx hAedge⟩
      exact hyW (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, jy, rfl, kx + 1, Nat.succ_pos _, hreach⟩)

/-- **The projection-irreducibility bridge**: for a special basis, the support matrix on the active
sites is irreducible iff the basis is connected.  Both directions are contrapositives through
`generalFlatBandProjectionBlockReducible`: `¬basisConnected ⟹ blockReducible ⟹ ¬projIrred` and
`¬projIrred ⟹ blockReducible ⟹ ¬basisConnected`. -/
theorem generalFlatBand_projectionIrreducible_iff_basisConnected
    {I : Finset (Fin (M + 1))} {μ : Fin (M + 1) → Fin (M + 1) → ℂ}
    (hbasis : IsGeneralFlatBandSpecialBasis T I μ) (hD0 : 0 < generalFlatBandDim T) :
    generalFlatBandProjectionIrreducible T ↔ generalFlatBandBasisConnected I μ := by
  constructor
  · intro hirr
    by_contra hnc
    exact generalFlatBand_not_projectionIrreducible_of_blockReducible T
      (generalFlatBand_blockReducible_of_not_basisConnected T hbasis hD0 hnc) hirr
  · intro hconn
    by_contra hni
    exact generalFlatBand_not_basisConnected_of_blockReducible T hbasis
      (generalFlatBand_blockReducible_of_not_projectionIrreducible T hni) hconn

/-- **Tasaki Theorem 11.15 (general flat-band ferromagnetism).**  For a Hermitian
positive-semidefinite hopping matrix `T` with nonempty flat band (`D₀ > 0`) and `U > 0`, the
`D₀`-electron Hubbard model is saturated-ferromagnetic **iff** the `Λ₀ × Λ₀` projection submatrix is
irreducible.  Proved by choosing a special basis (Lemma 11.16, `generalFlatBand_lemma_11_16`),
applying the proved Theorem 11.17 (`ferromagnetic ↔ basis connected`), and composing with the
projection-irreducibility bridge (`generalFlatBand_projectionIrreducible_iff_basisConnected`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §11.3.4, Theorem 11.15, pp. 408–412. -/
theorem tasaki_theorem_11_15 (U : ℝ) (hT : T.PosSemidef)
    (hD0 : 0 < generalFlatBandDim T) (hU : 0 < U) :
    generalFlatBandFerromagnetic T U ↔ generalFlatBandProjectionIrreducible T := by
  obtain ⟨I, μ, hbasis⟩ := generalFlatBand_lemma_11_16 T hT
  rw [generalFlatBand_theorem_11_17 T U hT hD0 hU hbasis]
  exact (generalFlatBand_projectionIrreducible_iff_basisConnected T hbasis hD0).symm

end LatticeSystem.Fermion
