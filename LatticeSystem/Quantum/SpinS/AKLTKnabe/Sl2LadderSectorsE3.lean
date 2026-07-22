import LatticeSystem.Quantum.SpinS.AKLTKnabe.Sl2SubmoduleProbeE2
import LatticeSystem.Quantum.SpinS.MultiSiteCartanPlusMinus
import LatticeSystem.Quantum.SpinS.OrderOperatorAlgebra

/-!
# Gate E3: the `sl₂` ladder algebra and the magnetisation-sector structure

This module (Issue #5094; Tasaki §7.1.4, Knabe's argument, pp. 188–190) carries out the residual
work listed in §(f) of the Gate E2 probe report (`aklt-theorem-7-1-e2-submodule-probe.md`), i.e.
steps (B), (D) of the design note `aklt-theorem-7-1-e1a-general-window-bound-design.md` §2.1:

1. the third Cartan relation for the **total** spin operators, `[Ŝ⁺_tot, Ŝ⁻_tot] = 2 Ŝ³_tot`,
   is the production lemma `totalSpinSOpPlus_commutator_totalSpinSOpMinus`
   (`MultiSiteCartanPlusMinus.lean`), reused here directly;
2. the **sector transport**: `Ŝ⁺_tot` maps the magnetisation sector `V_{k+1}` into `V_k` and
   annihilates `V_0`, `Ŝ⁻_tot` maps `V_k` into `V_{k+1}`, and `Ŝ³_tot` acts on `V_k` by the scalar
   `|Λ|N/2 − k`;
3. the **ladder norm identity** `‖Ŝ⁻v‖² = ‖Ŝ⁺v‖² + (|Λ|N − 2k)‖v‖²` on `V_k`, whence `Ŝ⁻_tot` is
   injective on `V_k` as soon as `2k < |Λ|N`;
4. the **dimension count** `dim V_k = #{σ | magSumS σ = k}` and, through the surjectivity of
   `Ŝ⁺_tot : V_{k+1} ↠ V_k` and the E2 rank–nullity statement,
   `dim V_k + dim hw_{k+1} = dim V_{k+1}`.

For the AKLT window (`Λ = Fin 4`, `N = 2`, i.e. four spin-`1` sites) this yields the highest-weight
dimensions `dim hw_k = 1, 3, 6, 6, 3` for `k = 0, 1, 2, 3, 4`, which are the multiplicities
`k_S` of the total-spin `S = 4, 3, 2, 1, 0` sectors of `(ℂ³)^{⊗4}` (design note §1).

The indexing convention is the natural-number magnetisation index `magSumS σ = Σ_x (σ x).val`,
which *decreases* when the physical magnetic quantum number increases; the physical value is
`m = |Λ|N/2 − magSumS σ`, so `V_0` is the highest-weight (all spins up) sector.

No `81 × 81` entry table occurs anywhere: the Cartan relation is obtained as a sum of the
single-site relation over the sites, and the sector transport is a support statement about
individual matrix entries.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.1 eq. (2.1.1) p. 15, §7.1.4 pp. 188–190; S. Knabe, *J. Stat. Phys.* **52**, 627–638
(1988).
-/

namespace LatticeSystem.Quantum.AKLTSl2LadderSectorsE3

open LatticeSystem.Quantum
open LatticeSystem.Quantum.AKLTSl2SubmoduleProbeE2

variable (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ)

/-! ## 1. Sector transport -/

/-- Membership in the magnetisation sector `V_k`, unfolded to the support condition. -/
theorem mem_magSectorE3_iff (k : ℕ) (v : ManyBodyVecE2 Λ N) :
    v ∈ magSectorE2 Λ N k ↔
      ∀ σ : Λ → Fin (N + 1), magSumS σ ≠ k → WithLp.ofLp v σ = 0 :=
  Iff.rfl

omit [Fintype Λ] [DecidableEq Λ] in
/-- Two vectors of the many-body Hilbert space agreeing componentwise are equal. -/
private theorem eq_of_ofLp_eqE3 {v w : ManyBodyVecE2 Λ N}
    (h : WithLp.ofLp v = WithLp.ofLp w) : v = w :=
  congrArg (WithLp.toLp 2) h

/-- Component description of `totalMinusLinE2`, the lowering counterpart of
`ofLp_totalPlusLinE2`. -/
private theorem ofLp_totalMinusLinE3 (v : ManyBodyVecE2 Λ N) :
    WithLp.ofLp (totalMinusLinE2 Λ N v) = (totalSpinSOpMinus Λ N).mulVec (WithLp.ofLp v) := rfl

omit [DecidableEq Λ] in
/-- If two configurations agree away from the site `x`, their magnetisation sums differ exactly by
the difference of their values at `x`. -/
private theorem magSumS_add_of_agree_offE3 {σ' σ : Λ → Fin (N + 1)} (x : Λ)
    (h : ∀ k, k ≠ x → σ' k = σ k) :
    magSumS σ' + (σ x).val = magSumS σ + (σ' x).val := by
  classical
  unfold magSumS
  have e1 : ∑ y : Λ, (σ' y).val
      = (σ' x).val + ∑ y ∈ Finset.univ.erase x, (σ' y).val :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ x)).symm
  have e2 : ∑ y : Λ, (σ y).val
      = (σ x).val + ∑ y ∈ Finset.univ.erase x, (σ y).val :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ x)).symm
  have e3 : ∑ y ∈ Finset.univ.erase x, (σ' y).val
      = ∑ y ∈ Finset.univ.erase x, (σ y).val :=
    Finset.sum_congr rfl fun y hy => by rw [h y (Finset.ne_of_mem_erase hy)]
  rw [e1, e2, e3]
  omega

/-- A matrix entry of `Ŝ⁺_tot` vanishes unless the column configuration has magnetisation index
exactly one more than the row configuration: `Ŝ⁺_tot` lowers `magSumS` by one. -/
private theorem totalSpinSOpPlus_apply_eq_zero_of_magSumS_neE3 (σ' σ : Λ → Fin (N + 1))
    (h : magSumS σ ≠ magSumS σ' + 1) : totalSpinSOpPlus Λ N σ' σ = 0 := by
  rw [totalSpinSOpPlus_def, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [onSiteS_apply]
  by_cases hagree : ∀ k, k ≠ x → σ' k = σ k
  · rw [if_pos hagree]
    refine spinSOpPlus_apply_other N ?_
    intro hval
    have hsum := magSumS_add_of_agree_offE3 Λ N x hagree
    exact h (by omega)
  · rw [if_neg hagree]

/-- A matrix entry of `Ŝ⁻_tot` vanishes unless the row configuration has magnetisation index
exactly one more than the column configuration: `Ŝ⁻_tot` raises `magSumS` by one. -/
private theorem totalSpinSOpMinus_apply_eq_zero_of_magSumS_neE3 (σ' σ : Λ → Fin (N + 1))
    (h : magSumS σ + 1 ≠ magSumS σ') : totalSpinSOpMinus Λ N σ' σ = 0 := by
  rw [totalSpinSOpMinus_def, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [onSiteS_apply]
  by_cases hagree : ∀ k, k ≠ x → σ' k = σ k
  · rw [if_pos hagree]
    refine spinSOpMinus_apply_other N ?_
    intro hval
    have hsum := magSumS_add_of_agree_offE3 Λ N x hagree
    exact h (by omega)
  · rw [if_neg hagree]

/-- **Sector transport for `Ŝ⁺_tot`**: the total raising operator maps `V_{k+1}` into `V_k`. -/
theorem totalPlusLinE3_mem_magSector (k : ℕ) (v : ManyBodyVecE2 Λ N)
    (hv : v ∈ magSectorE2 Λ N (k + 1)) :
    totalPlusLinE2 Λ N v ∈ magSectorE2 Λ N k := by
  have hv' := (mem_magSectorE3_iff Λ N (k + 1) v).mp hv
  refine (mem_magSectorE3_iff Λ N k _).mpr fun σ' hσ' => ?_
  rw [ofLp_totalPlusLinE2]
  change ∑ σ, totalSpinSOpPlus Λ N σ' σ * WithLp.ofLp v σ = 0
  refine Finset.sum_eq_zero fun σ _ => ?_
  by_cases hσ : magSumS σ = k + 1
  · rw [totalSpinSOpPlus_apply_eq_zero_of_magSumS_neE3 Λ N σ' σ (by omega), zero_mul]
  · rw [hv' σ hσ, mul_zero]

/-- **Sector transport for `Ŝ⁻_tot`**: the total lowering operator maps `V_k` into `V_{k+1}`. -/
theorem totalMinusLinE3_mem_magSector (k : ℕ) (v : ManyBodyVecE2 Λ N)
    (hv : v ∈ magSectorE2 Λ N k) :
    totalMinusLinE2 Λ N v ∈ magSectorE2 Λ N (k + 1) := by
  have hv' := (mem_magSectorE3_iff Λ N k v).mp hv
  refine (mem_magSectorE3_iff Λ N (k + 1) _).mpr fun σ' hσ' => ?_
  rw [ofLp_totalMinusLinE3]
  change ∑ σ, totalSpinSOpMinus Λ N σ' σ * WithLp.ofLp v σ = 0
  refine Finset.sum_eq_zero fun σ _ => ?_
  by_cases hσ : magSumS σ = k
  · rw [totalSpinSOpMinus_apply_eq_zero_of_magSumS_neE3 Λ N σ' σ (by omega), zero_mul]
  · rw [hv' σ hσ, mul_zero]

/-- The top sector `V_0` (all spins maximally up) is annihilated by `Ŝ⁺_tot`: there is no sector
above it. -/
theorem totalPlusLinE3_eq_zero_of_mem_magSector_zero (v : ManyBodyVecE2 Λ N)
    (hv : v ∈ magSectorE2 Λ N 0) : totalPlusLinE2 Λ N v = 0 := by
  have hv' := (mem_magSectorE3_iff Λ N 0 v).mp hv
  rw [← WithLp.ofLp_eq_zero]
  funext σ'
  rw [Pi.zero_apply, ofLp_totalPlusLinE2]
  change ∑ σ, totalSpinSOpPlus Λ N σ' σ * WithLp.ofLp v σ = 0
  refine Finset.sum_eq_zero fun σ _ => ?_
  by_cases hσ : magSumS σ = 0
  · rw [totalSpinSOpPlus_apply_eq_zero_of_magSumS_neE3 Λ N σ' σ (by omega), zero_mul]
  · rw [hv' σ hσ, mul_zero]

/-- **`Ŝ³_tot` is scalar on a magnetisation sector**: on vectors supported on the configurations
with `magSumS σ = k` the total `3`-axis operator acts by `|Λ|N/2 − k`. -/
private theorem totalSpinSOp3_mulVec_of_magSectorE3 (k : ℕ) (w : (Λ → Fin (N + 1)) → ℂ)
    (hw : ∀ σ, magSumS σ ≠ k → w σ = 0) :
    (totalSpinSOp3 Λ N).mulVec w
      = (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (k : ℂ)) • w := by
  funext σ'
  change ∑ σ, totalSpinSOp3 Λ N σ' σ * w σ
      = (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (k : ℂ)) * w σ'
  rw [Fintype.sum_eq_single σ' (fun σ hσ => by
    rw [totalSpinSOp3_apply_off_diag (Ne.symm hσ), zero_mul])]
  rw [totalSpinSOp3_apply_diag]
  by_cases hσ' : magSumS σ' = k
  · rw [magEigenvalueS_def, hσ']
  · rw [hw σ' hσ', mul_zero, mul_zero]

/-! ## 2. The ladder norm identity and injectivity of `Ŝ⁻_tot` -/

/-- **Design §2.1 (B), assembled**: on the magnetisation sector `V_k` the ladder commutator acts by
the scalar `|Λ|N − 2k`, i.e. `Ŝ⁺Ŝ⁻v − Ŝ⁻Ŝ⁺v = (|Λ|N − 2k) v`. -/
theorem ladderCommutatorApplyE3 (k : ℕ) (v : ManyBodyVecE2 Λ N)
    (hv : v ∈ magSectorE2 Λ N k) :
    totalPlusLinE2 Λ N (totalMinusLinE2 Λ N v)
        - totalMinusLinE2 Λ N (totalPlusLinE2 Λ N v)
      = (((Fintype.card Λ : ℂ) * (N : ℂ)) - 2 * (k : ℂ)) • v := by
  have hv' := (mem_magSectorE3_iff Λ N k v).mp hv
  refine eq_of_ofLp_eqE3 Λ N ?_
  have e1 : WithLp.ofLp (totalPlusLinE2 Λ N (totalMinusLinE2 Λ N v)
        - totalMinusLinE2 Λ N (totalPlusLinE2 Λ N v))
      = (totalSpinSOpPlus Λ N * totalSpinSOpMinus Λ N
          - totalSpinSOpMinus Λ N * totalSpinSOpPlus Λ N).mulVec (WithLp.ofLp v) := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rfl
  rw [e1, totalSpinSOpPlus_commutator_totalSpinSOpMinus, Matrix.smul_mulVec,
    totalSpinSOp3_mulVec_of_magSectorE3 Λ N k _ hv', smul_smul]
  change ((2 : ℂ) * (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (k : ℂ))) • WithLp.ofLp v
      = (((Fintype.card Λ : ℂ) * (N : ℂ)) - 2 * (k : ℂ)) • WithLp.ofLp v
  congr 1
  ring

/-- **Design §2.1 (B)**: the ladder norm identity on the magnetisation sector `V_k`,
`‖Ŝ⁻v‖² = ‖Ŝ⁺v‖² + (|Λ|N − 2k)‖v‖²`.  Combines the E2 operator half `ladderInnerNormSqE2`
with the Cartan relation and the scalar action of `Ŝ³_tot` on `V_k`. -/
theorem ladderNormSqE3 (k : ℕ) (v : ManyBodyVecE2 Λ N) (hv : v ∈ magSectorE2 Λ N k) :
    ‖totalMinusLinE2 Λ N v‖ ^ 2
      = ‖totalPlusLinE2 Λ N v‖ ^ 2
        + ((Fintype.card Λ : ℝ) * (N : ℝ) - 2 * (k : ℝ)) * ‖v‖ ^ 2 := by
  have hin : inner ℂ v (totalPlusLinE2 Λ N (totalMinusLinE2 Λ N v))
      - inner ℂ v (totalMinusLinE2 Λ N (totalPlusLinE2 Λ N v))
      = (((Fintype.card Λ : ℂ) * (N : ℂ)) - 2 * (k : ℂ)) * (‖v‖ : ℂ) ^ 2 := by
    rw [← inner_sub_right, ladderCommutatorApplyE3 Λ N k v hv, inner_smul_right,
      inner_self_eq_norm_sq_to_K]
    rfl
  have h2 := ladderInnerNormSqE2 Λ N v
  rw [hin] at h2
  have h3 : ((‖totalMinusLinE2 Λ N v‖ ^ 2 : ℝ) : ℂ)
      = ((‖totalPlusLinE2 Λ N v‖ ^ 2
          + ((Fintype.card Λ : ℝ) * (N : ℝ) - 2 * (k : ℝ)) * ‖v‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    linear_combination -h2
  exact_mod_cast h3

/-- **Design §2.1 (B), consequence**: `Ŝ⁻_tot` is injective on the magnetisation sector `V_k` as
soon as `2k < |Λ|N`, i.e. as soon as the physical magnetisation of `V_k` is positive. -/
theorem eq_zero_of_totalMinusLinE3_eq_zero (k : ℕ) (hk : 2 * k < Fintype.card Λ * N)
    (v : ManyBodyVecE2 Λ N) (hv : v ∈ magSectorE2 Λ N k)
    (h0 : totalMinusLinE2 Λ N v = 0) : v = 0 := by
  have h := ladderNormSqE3 Λ N k v hv
  rw [h0, norm_zero] at h
  have hcast : ((2 * k : ℕ) : ℝ) < ((Fintype.card Λ * N : ℕ) : ℝ) := by exact_mod_cast hk
  push_cast at hcast
  have hc : (0 : ℝ) < (Fintype.card Λ : ℝ) * (N : ℝ) - 2 * (k : ℝ) := by linarith
  have hzero : ‖v‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hne)
    nlinarith [sq_nonneg ‖totalPlusLinE2 Λ N v‖, mul_pos hc (mul_pos hpos hpos)]
  exact norm_eq_zero.mp hzero

/-! ## 3. Surjectivity of `Ŝ⁺_tot` and the highest-weight dimensions -/

/-- **Design §2.1 (D)**: for `2k < |Λ|N` the total raising operator restricted to `V_{k+1}` has
image exactly `V_k`.  The inclusion is the sector transport; surjectivity follows from the
orthogonal decomposition of `V_k` along the image together with the injectivity of `Ŝ⁻_tot` on
`V_k` (a vector of `V_k` orthogonal to the image is killed by the adjoint `Ŝ⁻_tot`). -/
theorem range_domRestrict_totalPlusLinE3 (k : ℕ) (hk : 2 * k < Fintype.card Λ * N) :
    LinearMap.range ((totalPlusLinE2 Λ N).domRestrict (magSectorE2 Λ N (k + 1)))
      = magSectorE2 Λ N k := by
  have hle : LinearMap.range ((totalPlusLinE2 Λ N).domRestrict (magSectorE2 Λ N (k + 1)))
      ≤ magSectorE2 Λ N k := by
    rintro w ⟨u, rfl⟩
    exact totalPlusLinE3_mem_magSector Λ N k u.1 u.2
  refine le_antisymm hle fun w hw => ?_
  obtain ⟨y, hy, z, hz, rfl⟩ :=
    (LinearMap.range ((totalPlusLinE2 Λ N).domRestrict
      (magSectorE2 Λ N (k + 1)))).exists_add_mem_mem_orthogonal w
  have hyk : y ∈ magSectorE2 Λ N k := hle hy
  have hzk : z ∈ magSectorE2 Λ N k := by
    have hsub := Submodule.sub_mem (magSectorE2 Λ N k) hw hyk
    rwa [add_sub_cancel_left] at hsub
  have hmem : totalMinusLinE2 Λ N z ∈ magSectorE2 Λ N (k + 1) :=
    totalMinusLinE3_mem_magSector Λ N k z hzk
  have h1 : inner ℂ (totalPlusLinE2 Λ N (totalMinusLinE2 Λ N z)) z = 0 :=
    (Submodule.mem_orthogonal _ z).mp hz _
      (LinearMap.mem_range.mpr ⟨⟨totalMinusLinE2 Λ N z, hmem⟩, rfl⟩)
  rw [← adjoint_totalMinusLinE2 Λ N, LinearMap.adjoint_inner_left] at h1
  have hz0 : z = 0 :=
    eq_zero_of_totalMinusLinE3_eq_zero Λ N k hk z hzk (inner_self_eq_zero.mp h1)
  rw [hz0, add_zero]
  exact hy

/-- **Design §2.1 (D)**: for `2k < |Λ|N`, `dim V_k + dim hw_{k+1} = dim V_{k+1}`, where
`hw_m = V_m ∩ ker Ŝ⁺_tot`.  Rank–nullity (E2) plus the surjectivity above. -/
theorem finrank_magSector_add_finrank_highestWeightE3 (k : ℕ)
    (hk : 2 * k < Fintype.card Λ * N) :
    Module.finrank ℂ (magSectorE2 Λ N k) + Module.finrank ℂ (highestWeightE2 Λ N (k + 1))
      = Module.finrank ℂ (magSectorE2 Λ N (k + 1)) := by
  rw [← range_domRestrict_totalPlusLinE3 Λ N k hk]
  exact finrank_range_add_finrank_highestWeightE2 Λ N (k + 1)

/-- The top highest-weight space coincides with the top magnetisation sector, `hw_0 = V_0`. -/
theorem highestWeightE3_zero : highestWeightE2 Λ N 0 = magSectorE2 Λ N 0 := by
  unfold highestWeightE2
  refine le_antisymm inf_le_left fun v hv => ?_
  rw [Submodule.mem_inf]
  exact ⟨hv, LinearMap.mem_ker.mpr (totalPlusLinE3_eq_zero_of_mem_magSector_zero Λ N v hv)⟩

/-! ## 4. The dimension of a magnetisation sector -/

/-- The magnetisation sector `V_k` is linearly isomorphic to the coordinate space on the set of
configurations with `magSumS σ = k`: a vector of `V_k` is exactly a family of coefficients indexed
by that set, extended by zero. -/
noncomputable def magSectorEquivE3 (k : ℕ) :
    magSectorE2 Λ N k ≃ₗ[ℂ] ({σ : Λ → Fin (N + 1) // magSumS σ = k} → ℂ) where
  toFun v := fun σ => WithLp.ofLp (v : ManyBodyVecE2 Λ N) σ.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f :=
    ⟨WithLp.toLp 2 (fun σ => if h : magSumS σ = k then f ⟨σ, h⟩ else 0), by
      refine (mem_magSectorE3_iff Λ N k _).mpr fun σ hσ => ?_
      change (if h : magSumS σ = k then f ⟨σ, h⟩ else 0) = 0
      rw [dif_neg hσ]⟩
  left_inv v := by
    have hv' := (mem_magSectorE3_iff Λ N k (v : ManyBodyVecE2 Λ N)).mp v.2
    refine Subtype.ext (eq_of_ofLp_eqE3 Λ N (funext fun σ => ?_))
    change (if h : magSumS σ = k then WithLp.ofLp (v : ManyBodyVecE2 Λ N) σ else 0)
        = WithLp.ofLp (v : ManyBodyVecE2 Λ N) σ
    by_cases hσ : magSumS σ = k
    · rw [dif_pos hσ]
    · rw [dif_neg hσ, hv' σ hσ]
  right_inv f := by
    funext σ
    change (if h : magSumS σ.1 = k then f ⟨σ.1, h⟩ else 0) = f σ
    rw [dif_pos σ.2]

/-- **Design §2.1 (D), dimension input**: the magnetisation sector `V_k` has dimension the number
of configurations with `magSumS σ = k`. -/
theorem finrank_magSectorE3 (k : ℕ) :
    Module.finrank ℂ (magSectorE2 Λ N k)
      = Fintype.card {σ : Λ → Fin (N + 1) // magSumS σ = k} := by
  rw [(magSectorEquivE3 Λ N k).finrank_eq, Module.finrank_fintype_fun_eq_card]

/-! ## 5. The four-site spin-`1` window: `dim hw_k = 1, 3, 6, 6, 3` -/

/-- The number of four-site spin-`1` configurations of magnetisation index `0`. -/
private theorem cardMagE3_zero :
    Fintype.card {σ : Fin 4 → Fin (2 + 1) // magSumS σ = 0} = 1 := by decide

/-- The number of four-site spin-`1` configurations of magnetisation index `1`. -/
private theorem cardMagE3_one :
    Fintype.card {σ : Fin 4 → Fin (2 + 1) // magSumS σ = 1} = 4 := by decide

/-- The number of four-site spin-`1` configurations of magnetisation index `2`. -/
private theorem cardMagE3_two :
    Fintype.card {σ : Fin 4 → Fin (2 + 1) // magSumS σ = 2} = 10 := by decide

/-- The number of four-site spin-`1` configurations of magnetisation index `3`. -/
private theorem cardMagE3_three :
    Fintype.card {σ : Fin 4 → Fin (2 + 1) // magSumS σ = 3} = 16 := by decide

/-- The number of four-site spin-`1` configurations of magnetisation index `4`. -/
private theorem cardMagE3_four :
    Fintype.card {σ : Fin 4 → Fin (2 + 1) // magSumS σ = 4} = 19 := by decide

/-- The magnetisation-sector dimensions of the four-site spin-`1` chain,
`dim V_k = 1, 4, 10, 16, 19` for `k = 0, 1, 2, 3, 4` (design note §2.1). -/
theorem finrank_magSectorE3_window :
    Module.finrank ℂ (magSectorE2 (Fin 4) 2 0) = 1
      ∧ Module.finrank ℂ (magSectorE2 (Fin 4) 2 1) = 4
      ∧ Module.finrank ℂ (magSectorE2 (Fin 4) 2 2) = 10
      ∧ Module.finrank ℂ (magSectorE2 (Fin 4) 2 3) = 16
      ∧ Module.finrank ℂ (magSectorE2 (Fin 4) 2 4) = 19 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [finrank_magSectorE3 (Fin 4) 2 0]
    exact cardMagE3_zero
  · rw [finrank_magSectorE3 (Fin 4) 2 1]
    exact cardMagE3_one
  · rw [finrank_magSectorE3 (Fin 4) 2 2]
    exact cardMagE3_two
  · rw [finrank_magSectorE3 (Fin 4) 2 3]
    exact cardMagE3_three
  · rw [finrank_magSectorE3 (Fin 4) 2 4]
    exact cardMagE3_four

/-- The site count of the window, `|Fin 4| · N = 8` for `N = 2`. -/
private theorem cardTimesNE3 : Fintype.card (Fin 4) * 2 = 8 := by
  rw [Fintype.card_fin]

/-- **Gate E3 target**: the highest-weight dimensions of the four-site spin-`1` window,
`dim hw_k = 1, 3, 6, 6, 3` for `k = 0, 1, 2, 3, 4`.

These are the multiplicities `k_S` of the total-spin sectors `S = 4, 3, 2, 1, 0` of `(ℂ³)^{⊗4}`
(design note §1: `k_4 = 1`, `k_3 = 3`, `k_2 = 6`, `k_1 = 6`, `k_0 = 3`, with
`Σ_S (2S+1) k_S = 81`), which is exactly the dimensional reduction `81 → 1 + 3 + 6 + 6 + 3` that
the Knabe window bound `ĥ² ≥ (2/5) ĥ` will be checked on. -/
theorem finrank_highestWeightE3_window :
    Module.finrank ℂ (highestWeightE2 (Fin 4) 2 0) = 1
      ∧ Module.finrank ℂ (highestWeightE2 (Fin 4) 2 1) = 3
      ∧ Module.finrank ℂ (highestWeightE2 (Fin 4) 2 2) = 6
      ∧ Module.finrank ℂ (highestWeightE2 (Fin 4) 2 3) = 6
      ∧ Module.finrank ℂ (highestWeightE2 (Fin 4) 2 4) = 3 := by
  obtain ⟨hV0, hV1, hV2, hV3, hV4⟩ := finrank_magSectorE3_window
  have h0 : Module.finrank ℂ (highestWeightE2 (Fin 4) 2 0) = 1 := by
    rw [highestWeightE3_zero (Fin 4) 2]
    exact hV0
  have h1 : Module.finrank ℂ (magSectorE2 (Fin 4) 2 0)
        + Module.finrank ℂ (highestWeightE2 (Fin 4) 2 1)
      = Module.finrank ℂ (magSectorE2 (Fin 4) 2 1) :=
    finrank_magSector_add_finrank_highestWeightE3 (Fin 4) 2 0 (by rw [cardTimesNE3]; omega)
  have h2 : Module.finrank ℂ (magSectorE2 (Fin 4) 2 1)
        + Module.finrank ℂ (highestWeightE2 (Fin 4) 2 2)
      = Module.finrank ℂ (magSectorE2 (Fin 4) 2 2) :=
    finrank_magSector_add_finrank_highestWeightE3 (Fin 4) 2 1 (by rw [cardTimesNE3]; omega)
  have h3 : Module.finrank ℂ (magSectorE2 (Fin 4) 2 2)
        + Module.finrank ℂ (highestWeightE2 (Fin 4) 2 3)
      = Module.finrank ℂ (magSectorE2 (Fin 4) 2 3) :=
    finrank_magSector_add_finrank_highestWeightE3 (Fin 4) 2 2 (by rw [cardTimesNE3]; omega)
  have h4 : Module.finrank ℂ (magSectorE2 (Fin 4) 2 3)
        + Module.finrank ℂ (highestWeightE2 (Fin 4) 2 4)
      = Module.finrank ℂ (magSectorE2 (Fin 4) 2 4) :=
    finrank_magSector_add_finrank_highestWeightE3 (Fin 4) 2 3 (by rw [cardTimesNE3]; omega)
  rw [hV0, hV1] at h1
  rw [hV1, hV2] at h2
  rw [hV2, hV3] at h3
  rw [hV3, hV4] at h4
  exact ⟨h0, by omega, by omega, by omega, by omega⟩

end LatticeSystem.Quantum.AKLTSl2LadderSectorsE3
