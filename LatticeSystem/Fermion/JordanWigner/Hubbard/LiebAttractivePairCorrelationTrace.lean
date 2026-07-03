import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractivePairTransferMatrix
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveNormFoundation
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveKineticEntry
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBalancedPosDefCompress

/-!
# The pair-correlation expectation as a coefficient trace (Tasaki §10.2.4)

Second implementation layer toward discharging
`theorem_10_3_tian_pair_correlation_positive` (Tian's pair-correlation positivity, Tasaki
Theorem 10.3).

Combining the polarized coordinate isometry `blockWCoeff_dotProduct_cross_eq`
(`⟨ψ', ψ⟩ = Tr((blockWCoeff ψ')ᴴ · blockWCoeff ψ)`, Tasaki eq. (10.2.34)) with the
pair-transfer coefficient action `blockWCoeff_pairCorrelation_mulVec` (`blockWCoeff (P·ψ) = S·W·Sᵀ`)
gives the trace formula (Tasaki eq. (10.2.51))

  `⟨φ| P_{x,y} |φ⟩ = Tr(Wᴴ · S · W · Sᵀ)`,

with `W := blockWCoeff φ` and `S := hubbardBlockKineticUpFixedMatrix N (single x y 1)` the fixed
single-hop up-kinetic matrix.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.4, p. 372 (eq. (10.2.51)); E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **The pair-correlation expectation equals a coefficient trace** (Tasaki eq. (10.2.51)).
For any Euclidean state `φ`, writing `W := blockWCoeff N φ` and
`S := hubbardBlockKineticUpFixedMatrix N (single x y 1)`,
`⟨φ| ĉ†_{x,↑} ĉ†_{x,↓} ĉ_{y,↓} ĉ_{y,↑} |φ⟩ = Tr(Wᴴ · S · W · Sᵀ)`.  Immediate from the polarized
coordinate isometry `blockWCoeff_dotProduct_cross_eq` and the coefficient action
`blockWCoeff_pairCorrelation_mulVec`.  This is step L4 of Tasaki §10.2.4 (Theorem 10.3). -/
theorem euclideanExpectation_pairCorrelation_eq_trace (N : ℕ) (x y : Fin (N + 1))
    (φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) :
    euclideanExpectation (hubbardPairCorrelationOp N x y) φ
      = Matrix.trace ((blockWCoeff N φ.ofLp)ᴴ
          * (hubbardBlockKineticUpFixedMatrix N (Matrix.single x y 1) * blockWCoeff N φ.ofLp
              * (hubbardBlockKineticUpFixedMatrix N (Matrix.single x y 1))ᵀ)) := by
  rw [euclideanExpectation, blockWCoeff_dotProduct_cross_eq, blockWCoeff_pairCorrelation_mulVec]

/-- A count-`k` up-configuration whose occupied set is a prescribed `k`-element finset. -/
private theorem countSector_of_finset {k : ℕ} (S : Finset (Fin (N + 1))) (hS : S.card = k) :
    ∃ s : hubbardSpinCountSector N k, ∀ z, s.val z = if z ∈ S then 1 else 0 := by
  have hcount : (∑ z : Fin (N + 1), ((if z ∈ S then (1 : Fin 2) else 0) : Fin 2).val) = k := by
    have h1 : ∀ z : Fin (N + 1),
        ((if z ∈ S then (1 : Fin 2) else 0) : Fin 2).val = if z ∈ S then 1 else 0 := by
      intro z; split <;> rfl
    simp_rw [h1]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one, hS]
  exact ⟨⟨fun z => if z ∈ S then 1 else 0, hcount⟩, fun _ => rfl⟩

/-- The diagonal entry of the single-site up transfer matrix `S = hubbardBlockKineticUpFixedMatrix
(single x x 1)` at a configuration occupied at `x` is nonzero (it is the `x`-up occupation number,
here `1`).  Computed from the number-operator action `ĉ†_{x,↑} ĉ_{x,↑} |c⟩ = jwSign² |c⟩`. -/
private theorem hubbardBlockKineticUpFixedMatrix_single_diag_ne (x : Fin (N + 1))
    (u : hubbardSpinConfig N) (hux : u x = 1) :
    hubbardBlockKineticUpFixedMatrix N (Matrix.single x x 1) u u ≠ 0 := by
  set D := particleHoleConfig N (fun _ : Fin (N + 1) => (0 : Fin 2)) with hD
  set c := hubbardBlockMergeConfig N u D with hc
  have hcx : c (hubbardBlockIndex N x 0) = 1 := by
    rw [hc, hubbardBlockMergeConfig_blockIndex_zero]; exact hux
  have hentry : hubbardBlockKineticUpFixedMatrix N (Matrix.single x x 1) u u
      = ((hubbardBlockKineticUp N (Matrix.single x x 1)).mulVec (basisVec c)) c := by
    rw [hubbardBlockKineticUpFixedMatrix, hubbardBlockKineticUpCoeffMatrix,
      Matrix.mulVec, dotProduct, sum_mul_basisVec c
        (fun w => (hubbardBlockKineticUp N (Matrix.single x x 1))
          (hubbardBlockMergeConfig N u (particleHoleConfig N (fun _ => 0))) w)]
  have hjw : ∀ (M : ℕ) (j : Fin (M + 1)) (d : Fin (M + 1) → Fin 2), jwSign M j d ≠ 0 := by
    intro M j d
    rw [jwSign]
    exact Finset.prod_ne_zero_iff.mpr (fun _ _ => by split <;> norm_num)
  rw [hentry, hubbardBlockKineticUp_single,
    fermionMultiCreation_mul_Annihilation_mulVec_basisVec,
    if_pos ⟨hcx, by rw [Function.update_self]⟩]
  rw [Pi.smul_apply, smul_eq_mul,
    show Function.update (Function.update c (hubbardBlockIndex N x 0) 0)
        (hubbardBlockIndex N x 0) 1 = c from by
      rw [Function.update_idem, Function.update_eq_self_iff.mpr hcx.symm],
    basisVec_self, mul_one, jwSign_update_eq]
  exact mul_ne_zero (hjw _ _ _) (hjw _ _ _)

/-- **The count-sector compression of the single-site up transfer matrix is nonzero** (Tasaki
§10.2.4, the combinatorial witness of Theorem 10.3, step L5).  For `1 ≤ k ≤ N` and any sites
`x, y`, the sector compression `S_c = Jᴴ · S · J` of `S = hubbardBlockKineticUpFixedMatrix
(single x y 1)` is nonzero.  A count-`k` up-configuration with `y` occupied and `x` empty (for
`x ≠ y`, giving a nonzero hop entry `S_apply_hop_ne`), resp. a count-`k` configuration with `x`
occupied (for `x = y`, giving a nonzero diagonal number entry), witnesses a nonzero sector entry
via the entry readoff `hubbardCountSectorEmbedding_conjTranspose_mul_mul_apply`. -/
theorem hubbardCountSectorEmbedding_pairFixed_compress_ne_zero (k : ℕ)
    (hk1 : 1 ≤ k) (hkN : k ≤ N) (x y : Fin (N + 1)) :
    (hubbardCountSectorEmbedding N k)ᴴ
        * hubbardBlockKineticUpFixedMatrix N (Matrix.single x y 1)
        * hubbardCountSectorEmbedding N k ≠ 0 := by
  set S := hubbardBlockKineticUpFixedMatrix N (Matrix.single x y 1) with hSdef
  suffices h : ∃ s s' : hubbardSpinCountSector N k,
      ((hubbardCountSectorEmbedding N k)ᴴ * S * hubbardCountSectorEmbedding N k) s s' ≠ 0 by
    obtain ⟨s, s', hss⟩ := h
    exact fun hzero => hss (by rw [hzero]; rfl)
  by_cases hxy : x = y
  · subst hxy
    obtain ⟨T₀, hT₀sub, hT₀card⟩ := Finset.exists_subset_card_eq
      (show k - 1 ≤ ((Finset.univ : Finset (Fin (N + 1))) \ {x}).card from by
        rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ,
          Finset.card_singleton]; omega)
    have hxT₀ : x ∉ T₀ := fun h => by simpa using hT₀sub h
    obtain ⟨s, hs⟩ := countSector_of_finset (k := k) (insert x T₀)
      (by rw [Finset.card_insert_of_notMem hxT₀, hT₀card]; omega)
    have hsx : s.val x = 1 := by rw [hs]; simp
    exact ⟨s, s, by
      rw [hubbardCountSectorEmbedding_conjTranspose_mul_mul_apply]
      exact hubbardBlockKineticUpFixedMatrix_single_diag_ne x s.val hsx⟩
  · obtain ⟨T₀, hT₀sub, hT₀card⟩ := Finset.exists_subset_card_eq
      (show k - 1 ≤ ((Finset.univ : Finset (Fin (N + 1))) \ {x, y}).card from by
        rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ,
          show ({x, y} : Finset (Fin (N + 1))).card = 2 from Finset.card_pair hxy]; omega)
    have hxT₀ : x ∉ T₀ := fun h => by
      have := hT₀sub h; simp only [Finset.mem_sdiff, Finset.mem_insert,
        Finset.mem_singleton] at this; tauto
    have hyT₀ : y ∉ T₀ := fun h => by
      have := hT₀sub h; simp only [Finset.mem_sdiff, Finset.mem_insert,
        Finset.mem_singleton] at this; tauto
    obtain ⟨s, hs⟩ := countSector_of_finset (k := k) (insert y T₀)
      (by rw [Finset.card_insert_of_notMem hyT₀, hT₀card]; omega)
    have hsy : s.val y = 1 := by rw [hs]; simp
    have hsx : s.val x = 0 := by
      rw [hs, if_neg]; rw [Finset.mem_insert]; rintro (h | h)
      · exact hxy h
      · exact hxT₀ h
    have hhopeq : hubbardSpinHopConfig N s.val y x = basisSwap s.val y x := by
      unfold basisSwap hubbardSpinHopConfig; rw [hsy, hsx]
    have hcounthop : (∑ z : Fin (N + 1), (hubbardSpinHopConfig N s.val y x z).val) = k := by
      rw [hhopeq, sumVal_basisSwap]; exact s.property
    refine ⟨⟨hubbardSpinHopConfig N s.val y x, hcounthop⟩, s, ?_⟩
    rw [hubbardCountSectorEmbedding_conjTranspose_mul_mul_apply]
    exact hubbardBlockKineticUpFixedMatrix_apply_hop_ne s.val x y hsy hsx hxy
      (by rw [Matrix.single_apply_same]; exact one_ne_zero)

end LatticeSystem.Fermion
