import LatticeSystem.Quantum.SpinS.AndersonTowerNumerator
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergU1
import LatticeSystem.Quantum.SpinS.BoseEinsteinCondensate

/-!
# Tasaki §5.3 Theorem 5.2 (BEC low-lying tower states): XY-planar numerator bound (PR-4b)

This file discharges the **XY-planar variational-numerator bound** of the Bose–Einstein-condensation
tower (`tasaki_5_2_bec_tower`, Tasaki §5.3, eq. (5.3.4)) at half filling.  The route is the
definitional Hamiltonian split (route (i) of the design note `math-thm52-pr4b-zz-numerator.md`):
`Ĥ_XY = Ĥ_Heis − Ĥ_ZZ` (with `Ĥ_ZZ = Σ_{x,y} J_{xy} Ŝ³_x Ŝ³_y`), coming for free from
`spinSDotXXZ_eq_spinSDot_add` at anisotropy `λ = 0`.  Because the tower operator
`A = (Ô_L^{sgn M})^{|M|}` is identical to the Anderson-tower operator, the double commutator is
linear in the Hamiltonian, so the pure-XY numerator splits as
`⟨Φ, [Aᴴ, [2 Ĥ_XY, A]] Φ⟩ = 2 ⟨Φ, [Aᴴ, [Ĥ_Heis, A]] Φ⟩ − 2 ⟨Φ, [Aᴴ, [Ĥ_ZZ, A]] Φ⟩`.  The
Heisenberg term is bounded verbatim by the Anderson-tower asset `tower_numerator_bound`; the
residual `Ĥ_ZZ` term is bounded here by a reduced replica of the Anderson-tower numerator chain (the
Hamiltonian-agnostic order-word bricks — `plain_orderWord_re_bound`,
`orderCommutator_insert_left_mulVec_eq`, `dotProduct_orderWord_totalSpinSOp3_mid_eq`,
`orderScalar_norm_le`, the split-independent R2 engine `r2_split_independent` — are imported and
reused, not re-proved).

The `Ĥ_ZZ` locality is obtained directly from `iterOrderComm_norm_le_of_localSum`: `Ĥ_ZZ` is a sum
of two-site-supported bond operators `Ŝ³_x Ŝ³_y`, so its iterated order-density commutators decay by
`(4N/V)` per step, and the `Ĥ_ZZ` single/double commutators are just two such iterated commutators.
The resulting aggregates are bounded by the *same* constants `24 d N³` and `96 d N⁴ / V` as the
Heisenberg chain (the `Ŝ³ Ŝ³` leaf is smaller than the `Ŝ_x·Ŝ_y` leaf), so the final `Ĥ_ZZ`
numerator bound has the identical moment-factor shape as `tower_numerator_bound`.  This is a reduced
replica of the Heisenberg chain; a follow-up refactor genericizing the chain over the bond operator
(to remove the duplication) is deferred to a later PR (design note §PR-4b no-duplicate note).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §5.1 eq. (5.1.5), §5.3 Theorem 5.2, eqs. (5.3.2)/(5.3.4), pp. 140–141 (Koma–Tasaki [21]); the
Anderson-tower numerator engine is `tower_numerator_bound` (§4.2.2 Theorem 4.6).  The
pre-implementation mathematical derivation is `.self-local/docs/math-thm52-pr4b-zz-numerator.md`.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {d L N : ℕ}

/-! ### The longitudinal (ZZ) Hamiltonian and its local-decay class -/

/-- The **longitudinal (ZZ) Hamiltonian** `Ĥ_ZZ = Σ_{x,y} J_{xy} Ŝ³_x Ŝ³_y` — the difference
`Ĥ_Heis − Ĥ_XY` produced by the `λ = 0` XXZ split (`spinSDotXXZ_eq_spinSDot_add`). -/
noncomputable def zzHamiltonianS (d L N : ℕ) [NeZero L] : ManyBodyOpS (HypercubicTorus d L) N :=
  ∑ x : HypercubicTorus d L, ∑ y : HypercubicTorus d L,
    torusNNCoupling d L x y • (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N))

/-- **The XY = Heisenberg − ZZ decomposition** (route (i)).  Since `xyHamiltonianS` is the XXZ
Hamiltonian at anisotropy `λ = 0` and single-ion field `D = 0`, each bond term is
`spinSDot − Ŝ³_x Ŝ³_y` (`spinSDotXXZ_eq_spinSDot_add` at `λ = 0`), so the bond sum is
`heisenbergHamiltonianS − zzHamiltonianS`. -/
theorem xyHamiltonianS_eq_heisenberg_sub_zz (d L : ℕ) [NeZero L] :
    xyHamiltonianS d L
      = heisenbergHamiltonianS (torusNNCoupling d L) 1 - zzHamiltonianS d L 1 := by
  rw [xyHamiltonianS, anisotropicHeisenbergS_def, singleIonAnisotropyS_zero, add_zero,
    heisenbergHamiltonianS_def, zzHamiltonianS, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [spinSDotXXZ_eq_spinSDot_add, smul_add, zero_sub, neg_one_smul, smul_neg, sub_eq_add_neg]

/-- The ℓ¹-aggregate of `Ĥ_ZZ`'s bond decomposition: `Σ_{x,y} ‖J‖ ‖Ŝ³_x Ŝ³_y‖`. -/
noncomputable def zzAggregate (d L N : ℕ) [NeZero L] : ℝ :=
  ∑ p : HypercubicTorus d L × HypercubicTorus d L,
    ‖torusNNCoupling d L p.1 p.2‖
      * manyBodyOperatorNormS (onSiteS p.1 (spinSOp3 N) * onSiteS p.2 (spinSOp3 N))

/-- The ZZ aggregate is nonnegative (a sum of products of norms). -/
theorem zzAggregate_nonneg (d L N : ℕ) [NeZero L] : 0 ≤ zzAggregate d L N :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (manyBodyOperatorNormS_nonneg _))

/-- **Iterated-commutator decay of `Ĥ_ZZ`.**  As a sum of two-site-supported bond operators
`Ŝ³_x Ŝ³_y`, every iterated order-density commutator of `Ĥ_ZZ` along a word `u` decays by
`(4N/V)^{|u|}` times the ℓ¹-aggregate (`iterOrderComm_norm_le_of_localSum` with `smax = 2`). -/
theorem zzHamiltonianS_iterOrderComm_norm_le (d L N : ℕ) [NeZero L] (hN : 1 ≤ N) (u : List Bool) :
    manyBodyOperatorNormS (iterOrderComm u (zzHamiltonianS d L N))
      ≤ (2 * 2 * (N : ℝ) / (L : ℝ) ^ d) ^ u.length * zzAggregate d L N := by
  have hH : zzHamiltonianS d L N
      = ∑ p : HypercubicTorus d L × HypercubicTorus d L,
          torusNNCoupling d L p.1 p.2 • (onSiteS p.1 (spinSOp3 N) * onSiteS p.2 (spinSOp3 N)) := by
    rw [zzHamiltonianS, ← Finset.sum_product', Finset.univ_product_univ]
  rw [hH]
  have hsupp : ∀ p : HypercubicTorus d L × HypercubicTorus d L,
      p ∈ (Finset.univ : Finset (HypercubicTorus d L × HypercubicTorus d L)) →
      SupportedOn ({p.1, p.2} : Finset (HypercubicTorus d L))
        (onSiteS p.1 (spinSOp3 N) * onSiteS p.2 (spinSOp3 N)) := by
    intro p _
    have h1 : ({p.1} : Finset (HypercubicTorus d L)) ⊆ {p.1, p.2} :=
      Finset.singleton_subset_iff.mpr (Finset.mem_insert_self p.1 {p.2})
    have h2 : ({p.2} : Finset (HypercubicTorus d L)) ⊆ {p.1, p.2} :=
      Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self p.2))
    exact ((onSiteS_supportedOn p.1 (spinSOp3 N)).mono h1).mul
      ((onSiteS_supportedOn p.2 (spinSOp3 N)).mono h2)
  have hbd := iterOrderComm_norm_le_of_localSum hN u
    (Finset.univ : Finset (HypercubicTorus d L × HypercubicTorus d L))
    (fun p => torusNNCoupling d L p.1 p.2)
    (fun p => onSiteS p.1 (spinSOp3 N) * onSiteS p.2 (spinSOp3 N))
    (fun p => ({p.1, p.2} : Finset (HypercubicTorus d L))) 2 hsupp
    (fun p _ => (Finset.card_insert_le _ _).trans (by simp))
  simpa [zzAggregate] using hbd

/-- **The ZZ aggregate is `≤ d N² V / 2`.**  The `≤ 2dV` nonzero bonds each carry
`‖Ŝ³_x Ŝ³_y‖ ≤ (N/2)² = N²/4`. -/
theorem zzAggregate_le (d L N : ℕ) [NeZero L] :
    zzAggregate d L N ≤ (d : ℝ) * (N : ℝ) ^ 2 * (L : ℝ) ^ d / 2 := by
  have hleaf : ∀ p : HypercubicTorus d L × HypercubicTorus d L,
      manyBodyOperatorNormS (onSiteS p.1 (spinSOp3 N) * onSiteS p.2 (spinSOp3 N))
        ≤ (N : ℝ) ^ 2 / 4 := by
    intro p
    refine le_trans (manyBodyOperatorNormS_mul_le _ _) ?_
    have h1 := onSiteS_spinSOp3_manyBodyOperatorNormS_le (N := N) p.1
    have h2 := onSiteS_spinSOp3_manyBodyOperatorNormS_le (N := N) p.2
    nlinarith [h1, h2, manyBodyOperatorNormS_nonneg (onSiteS p.1 (spinSOp3 N)),
      manyBodyOperatorNormS_nonneg (onSiteS p.2 (spinSOp3 N)), Nat.cast_nonneg (α := ℝ) N]
  calc zzAggregate d L N
      ≤ ∑ p : HypercubicTorus d L × HypercubicTorus d L,
          ‖torusNNCoupling d L p.1 p.2‖ * ((N : ℝ) ^ 2 / 4) := by
        refine Finset.sum_le_sum (fun p _ => ?_)
        exact mul_le_mul_of_nonneg_left (hleaf p) (norm_nonneg _)
    _ = ((N : ℝ) ^ 2 / 4)
          * ∑ p : HypercubicTorus d L × HypercubicTorus d L, ‖torusNNCoupling d L p.1 p.2‖ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring)
    _ ≤ ((N : ℝ) ^ 2 / 4) * (2 * (d : ℝ) * (L : ℝ) ^ d) :=
        mul_le_mul_of_nonneg_left (torusNNCoupling_total_norm_le d L) (by positivity)
    _ = (d : ℝ) * (N : ℝ) ^ 2 * (L : ℝ) ^ d / 2 := by ring

/-- The **ZZ double commutator** `d̂_ZZ = [ô⁺, [Ĥ_ZZ, ô⁻]]` (ZZ analogue of `orderDoubleComm`). -/
noncomputable def zzDoubleComm (d L N : ℕ) [NeZero L] : ManyBodyOpS (HypercubicTorus d L) N :=
  staggeredOrderDensityOpS d L N true
      * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N false
        - staggeredOrderDensityOpS d L N false * zzHamiltonianS d L N)
    - (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N false
        - staggeredOrderDensityOpS d L N false * zzHamiltonianS d L N)
      * staggeredOrderDensityOpS d L N true

/-- `d̂_ZZ` is (minus) the twice-iterated order-density commutator of `Ĥ_ZZ`. -/
theorem zzDoubleComm_eq_neg_iterOrderComm (d L N : ℕ) [NeZero L] :
    zzDoubleComm d L N
      = -orderComm true (orderComm false (zzHamiltonianS d L N)) := by
  rw [zzDoubleComm, orderComm, orderComm]; noncomm_ring

/-- The g₀ constant carried by `d̂_ZZ` in the local-decay class: `(4N/V)² · zzAggregate`. -/
noncomputable def zzDoubleCommAggregate (d L N : ℕ) [NeZero L] : ℝ :=
  (2 * 2 * (N : ℝ) / (L : ℝ) ^ d) ^ 2 * zzAggregate d L N

/-- The g₀ constant carried by `[Ĥ_ZZ, ô⁺]` in the local-decay class: `(4N/V) · zzAggregate`. -/
noncomputable def zzSingleCommAggregate (d L N : ℕ) [NeZero L] : ℝ :=
  (2 * 2 * (N : ℝ) / (L : ℝ) ^ d) * zzAggregate d L N

/-- **`d̂_ZZ` lies in the local-decay class** (`ζ = 2`, `o₀ = N`, `g₀ = zzDoubleCommAggregate`): the
ZZ analogue of `isR2LocalUpTo_orderDoubleComm`, obtained directly from the iterated-commutator decay
of `Ĥ_ZZ` (two extra commutator levels). -/
theorem isR2LocalUpTo_zzDoubleComm (d L N : ℕ) [NeZero L] (hN : 1 ≤ N) (K : ℕ) :
    IsR2LocalUpTo K 2 (N : ℝ) (zzDoubleCommAggregate d L N) (zzDoubleComm d L N) := by
  refine ⟨?_, fun u _ => ?_⟩
  · rw [zzDoubleCommAggregate]
    exact mul_nonneg (by positivity) (zzAggregate_nonneg d L N)
  have heq : iterOrderComm u (zzDoubleComm d L N)
      = (-1 : ℂ) • iterOrderComm (false :: true :: u) (zzHamiltonianS d L N) := by
    rw [zzDoubleComm_eq_neg_iterOrderComm,
      show (-orderComm true (orderComm false (zzHamiltonianS d L N)) : ManyBodyOpS _ _)
          = (-1 : ℂ) • orderComm true (orderComm false (zzHamiltonianS d L N)) from by
        rw [neg_one_smul],
      iterOrderComm_smul, ← iterOrderComm_cons, ← iterOrderComm_cons]
  rw [heq, manyBodyOperatorNormS_smul, show ‖(-1 : ℂ)‖ = 1 from by norm_num, one_mul]
  refine le_trans (zzHamiltonianS_iterOrderComm_norm_le d L N hN (false :: true :: u)) ?_
  rw [zzDoubleCommAggregate, List.length_cons, List.length_cons]
  apply le_of_eq
  ring

/-- **`[Ĥ_ZZ, ô⁺]` lies in the local-decay class** (`ζ = 2`, `o₀ = N`,
`g₀ = zzSingleCommAggregate`): ZZ analogue of `isR2LocalUpTo_heisenbergRaisingComm`, one level. -/
theorem isR2LocalUpTo_zzSingleComm (d L N : ℕ) [NeZero L] (hN : 1 ≤ N) (K : ℕ) :
    IsR2LocalUpTo K 2 (N : ℝ) (zzSingleCommAggregate d L N)
      (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
        - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N) := by
  refine ⟨?_, fun u _ => ?_⟩
  · rw [zzSingleCommAggregate]
    exact mul_nonneg (by positivity) (zzAggregate_nonneg d L N)
  have heq : iterOrderComm u (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
        - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
      = (-1 : ℂ) • iterOrderComm (true :: u) (zzHamiltonianS d L N) := by
    rw [show (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N : ManyBodyOpS _ _)
          = (-1 : ℂ) • orderComm true (zzHamiltonianS d L N) from by
        rw [orderComm, neg_one_smul, neg_sub],
      iterOrderComm_smul, ← iterOrderComm_cons]
  rw [heq, manyBodyOperatorNormS_smul, show ‖(-1 : ℂ)‖ = 1 from by norm_num, one_mul]
  refine le_trans (zzHamiltonianS_iterOrderComm_norm_le d L N hN (true :: u)) ?_
  rw [zzSingleCommAggregate, List.length_cons]
  apply le_of_eq
  ring

/-- **The ZZ double aggregate is `≤ 96 d N⁴ / V`** (matching the Heisenberg `orderDoubleComm`
aggregate), so the ZZ numerator has the identical moment-factor shape. -/
theorem zzDoubleCommAggregate_le (d L N : ℕ) [NeZero L] (hN : 1 ≤ N) :
    zzDoubleCommAggregate d L N ≤ 96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d := by
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hVne : (L : ℝ) ^ d ≠ 0 := hVpos.ne'
  have hagg := zzAggregate_le d L N
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  rw [zzDoubleCommAggregate]
  have h1 : (2 * 2 * (N : ℝ) / (L : ℝ) ^ d) ^ 2 * zzAggregate d L N
      ≤ (2 * 2 * (N : ℝ) / (L : ℝ) ^ d) ^ 2 * ((d : ℝ) * (N : ℝ) ^ 2 * (L : ℝ) ^ d / 2) :=
    mul_le_mul_of_nonneg_left hagg (by positivity)
  refine le_trans h1 ?_
  have hcalc : (2 * 2 * (N : ℝ) / (L : ℝ) ^ d) ^ 2 * ((d : ℝ) * (N : ℝ) ^ 2 * (L : ℝ) ^ d / 2)
      = 8 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d := by field_simp; ring
  rw [hcalc]
  gcongr
  norm_num

/-- **The ZZ single aggregate is `≤ 24 d N³`** (matching the Heisenberg `[Ĥ, ô⁺]` aggregate). -/
theorem zzSingleCommAggregate_le (d L N : ℕ) [NeZero L] (hN : 1 ≤ N) :
    zzSingleCommAggregate d L N ≤ 24 * (d : ℝ) * (N : ℝ) ^ 3 := by
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hVne : (L : ℝ) ^ d ≠ 0 := hVpos.ne'
  have hagg := zzAggregate_le d L N
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  rw [zzSingleCommAggregate]
  have h1 : (2 * 2 * (N : ℝ) / (L : ℝ) ^ d) * zzAggregate d L N
      ≤ (2 * 2 * (N : ℝ) / (L : ℝ) ^ d) * ((d : ℝ) * (N : ℝ) ^ 2 * (L : ℝ) ^ d / 2) :=
    mul_le_mul_of_nonneg_left hagg (by positivity)
  refine le_trans h1 ?_
  have hcalc : (2 * 2 * (N : ℝ) / (L : ℝ) ^ d) * ((d : ℝ) * (N : ℝ) ^ 2 * (L : ℝ) ^ d / 2)
      = 2 * (d : ℝ) * (N : ℝ) ^ 3 := by field_simp
  rw [hcalc]
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) d) (pow_nonneg hNnn 3)]

/-! ### The Jacobi mechanism surfacing `d̂_ZZ` -/

/-- **`Ĥ_ZZ` commutes with the order commutator.**  `[ô⁺, ô⁻] = (2/V²) Ŝ³_tot`, and `Ĥ_ZZ`
conserves total `Ŝ³` (it is diagonal), so `[Ĥ_ZZ, [ô⁺, ô⁻]] = 0`. -/
theorem zzHamiltonianS_commutator_totalSpinSOp3 (d L N : ℕ) [NeZero L] :
    zzHamiltonianS d L N * totalSpinSOp3 (HypercubicTorus d L) N
        - totalSpinSOp3 (HypercubicTorus d L) N * zzHamiltonianS d L N = 0 := by
  rw [zzHamiltonianS, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub,
    sub_eq_zero.mpr (onSiteS_spinSOp3_mul_onSiteS_spinSOp3_commute_totalSpinSOp3 x y N).eq,
    smul_zero]

/-- **`Ĥ_ZZ` commutes with `[ô⁺, ô⁻]`.**  Rewrites `[ô⁺, ô⁻]` as `(2/V²) Ŝ³_tot` and cancels via
`zzHamiltonianS_commutator_totalSpinSOp3`. -/
theorem zz_orderCommutator_commute (d L N : ℕ) [NeZero L] :
    zzHamiltonianS d L N
        * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
      - (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
        * zzHamiltonianS d L N = 0 := by
  rw [staggeredOrderDensity_commutator_eq, smul_smul, mul_smul_comm, smul_mul_assoc, ← smul_sub,
    zzHamiltonianS_commutator_totalSpinSOp3, smul_zero]

/-- **`[[Ĥ_ZZ, ô⁺], ô⁻] = −d̂_ZZ`.**  Jacobi identity plus `[Ĥ_ZZ, [ô⁺, ô⁻]] = 0`. -/
theorem zz_order_nested_eq_neg_zzDoubleComm (d L N : ℕ) [NeZero L] :
    (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
        * staggeredOrderDensityOpS d L N false
      - staggeredOrderDensityOpS d L N false
        * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
      = -zzDoubleComm d L N := by
  have hjac : (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
        * staggeredOrderDensityOpS d L N false
      - staggeredOrderDensityOpS d L N false
        * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
      = (zzHamiltonianS d L N
            * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
              - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
          - (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
              - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
            * zzHamiltonianS d L N)
        - zzDoubleComm d L N := by
    rw [zzDoubleComm]; noncomm_ring
  rw [hjac, zz_orderCommutator_commute, zero_sub]

/-! ### The ZZ single-term R2 bounds (reduced replica of the Heisenberg chain) -/

/-- **ZZ S1 single-term bound.**  Lemma R2 applied to `d̂_ZZ` (local-decay class,
`g₀ ≤ 96 d N⁴/V`): `|Re⟨Φ, ô^{wₗ} d̂_ZZ ô^{wᵣ} Φ⟩| ≤ 3·(96 d N⁴/V)·mf(|wₗ|+|wᵣ|)`. -/
theorem zzDoubleComm_word_re_bound (d L N : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (wl wr : List Bool)
    (hcond : 3 * (N : ℝ) * ((wl.length + wr.length : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((wl.length + wr.length : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (orderWordProd d L N wl * zzDoubleComm d L N
        * orderWordProd d L N wr).mulVec Φ).re|
      ≤ 3 * (96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d)
          * momentFactor d L N Φ (wl.length + wr.length) := by
  have hbd := r2_split_independent d L N hN Φ hsing (q₀ := q₀) (ζ := (2 : ℝ)) (o₀ := (N : ℝ))
    hq₀ hm0 hratio (by positivity) (wl.length + wr.length) hcond hbudget wl wr
    (zzDoubleComm d L N) (zzDoubleCommAggregate d L N) rfl
    (isR2LocalUpTo_zzDoubleComm d L N hN _)
  refine le_trans hbd ?_
  gcongr
  · exact momentFactor_nonneg d L N Φ _
  · exact zzDoubleCommAggregate_le d L N hN

/-- **ZZ S2/S3 single-term bound.**  Lemma R2 applied to `[Ĥ_ZZ, ô⁺]` (local-decay class,
`g₀ ≤ 24 d N³`): `|Re⟨Φ, ô^{wₗ} [Ĥ_ZZ,ô⁺] ô^{wᵣ} Φ⟩| ≤ 3·(24 d N³)·mf(|wₗ|+|wᵣ|)`. -/
theorem zzSingleComm_word_re_bound (d L N : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (wl wr : List Bool)
    (hcond : 3 * (N : ℝ) * ((wl.length + wr.length : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((wl.length + wr.length : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (orderWordProd d L N wl
        * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
        * orderWordProd d L N wr).mulVec Φ).re|
      ≤ 3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (wl.length + wr.length) := by
  have hbd := r2_split_independent d L N hN Φ hsing (q₀ := q₀) (ζ := (2 : ℝ)) (o₀ := (N : ℝ))
    hq₀ hm0 hratio (by positivity) (wl.length + wr.length) hcond hbudget wl wr
    (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
      - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
    (zzSingleCommAggregate d L N) rfl (isR2LocalUpTo_zzSingleComm d L N hN _)
  refine le_trans hbd ?_
  gcongr
  · exact momentFactor_nonneg d L N Φ _
  · exact zzSingleCommAggregate_le d L N hN

/-- **Commutator-power expansion of `[Ĥ_ZZ, (ô⁺)^M]`** (ZZ analogue of
`heisenberg_orderDensityPow_commutator_eq`). -/
theorem zz_orderDensityPow_commutator_eq (d L N M : ℕ) [NeZero L] :
    zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true ^ M
        - staggeredOrderDensityOpS d L N true ^ M * zzHamiltonianS d L N
      = ∑ j ∈ Finset.range M, staggeredOrderDensityOpS d L N true ^ j
          * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
          * staggeredOrderDensityOpS d L N true ^ (M - 1 - j) :=
  commutator_pow_eq_sum _ _ M

/-- **The ZZ numerator double commutator as a single sum over insertion positions** (ZZ analogue of
`numerator_eq_sum_j`). -/
theorem zz_numerator_eq_sum_j (d L N M : ℕ) [NeZero L] :
    staggeredOrderDensityOpS d L N false ^ M
        * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true ^ M
          - staggeredOrderDensityOpS d L N true ^ M * zzHamiltonianS d L N)
      - (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true ^ M
          - staggeredOrderDensityOpS d L N true ^ M * zzHamiltonianS d L N)
        * staggeredOrderDensityOpS d L N false ^ M
      = ∑ j ∈ Finset.range M,
          (staggeredOrderDensityOpS d L N false ^ M
              * (staggeredOrderDensityOpS d L N true ^ j
                * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
                  - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
                * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
            - (staggeredOrderDensityOpS d L N true ^ j
                * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
                  - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
                * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
              * staggeredOrderDensityOpS d L N false ^ M) := by
  rw [zz_orderDensityPow_commutator_eq, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]

/-- **ZZ S1 single-term bound (powers form)** (ZZ analogue of `s1_term_bound`). -/
theorem zz_s1_term_bound (d L N M j k : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (hj : j < M) (hk : k < M)
    (hcond : 3 * (N : ℝ) * ((2 * M - 2 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((2 * M - 2 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ k
        * staggeredOrderDensityOpS d L N true ^ j * zzDoubleComm d L N
        * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)).mulVec Φ).re|
      ≤ 3 * (96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d)
          * momentFactor d L N Φ (2 * M - 2) := by
  set wl := List.replicate k false ++ List.replicate j true with hwldef
  set wr := List.replicate (M - 1 - j) true ++ List.replicate (M - 1 - k) false with hwrdef
  have hwl : orderWordProd d L N wl = staggeredOrderDensityOpS d L N false ^ k
      * staggeredOrderDensityOpS d L N true ^ j := by
    rw [hwldef, orderWordProd_mul_append, orderWordProd_replicate, orderWordProd_replicate]
  have hwr : orderWordProd d L N wr = staggeredOrderDensityOpS d L N true ^ (M - 1 - j)
      * staggeredOrderDensityOpS d L N false ^ (M - 1 - k) := by
    rw [hwrdef, orderWordProd_mul_append, orderWordProd_replicate, orderWordProd_replicate]
  have hlen : wl.length + wr.length = 2 * M - 2 := by
    simp only [hwldef, hwrdef, List.length_append, List.length_replicate]; omega
  have hop : staggeredOrderDensityOpS d L N false ^ k
        * staggeredOrderDensityOpS d L N true ^ j * zzDoubleComm d L N
        * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
      = orderWordProd d L N wl * zzDoubleComm d L N * orderWordProd d L N wr := by
    rw [hwl, hwr]; noncomm_ring
  rw [hop]
  have hbd := zzDoubleComm_word_re_bound d L N hN hL Φ hsing hq₀ hm0 hratio wl wr
    (by rw [hlen]; exact hcond) (by rw [hlen]; exact hbudget)
  rwa [hlen] at hbd

/-- **ZZ S2/S3 term-1 leaf** (ZZ analogue of `s23_term1_bound`). -/
theorem zz_s23_term1_bound (d L N : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (wl wm wr : List Bool)
    (hcond : 3 * (N : ℝ) * ((wl.length + (wm.length + wr.length) : ℕ) : ℝ) ^ 2
        ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((wl.length + (wm.length + wr.length) : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (orderWordProd d L N wl
        * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
        * (orderWordProd d L N wm
          * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
          * orderWordProd d L N wr)).mulVec Φ).re|
      ≤ ‖(((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge wr)‖
        * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3)
            * momentFactor d L N Φ (wl.length + (wm.length + wr.length))) := by
  rw [orderCommutator_insert_left_mulVec_eq d L N Φ hsing
      (orderWordProd d L N wl
        * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)) wm wr,
    dotProduct_smul, smul_eq_mul]
  set s := (((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge wr) with hs
  have hVim : (((L : ℂ) ^ d)⁻¹).im = 0 := by
    rw [show ((L : ℂ) ^ d)⁻¹ = (((((L : ℝ) ^ d)⁻¹ : ℝ)) : ℂ) by push_cast; ring]
    exact Complex.ofReal_im _
  have hsim : s.im = 0 := by rw [hs]; simp [Complex.mul_im, Complex.mul_re, hVim, mCharge_im]
  set Z := star Φ ⬝ᵥ (orderWordProd d L N wl
      * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
        - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
      * (orderWordProd d L N wm * orderWordProd d L N wr)).mulVec Φ with hZ
  have hre : (s * Z).re = s.re * Z.re := by rw [Complex.mul_re, hsim, zero_mul, sub_zero]
  rw [hre, abs_mul]
  refine mul_le_mul ?_ ?_ (abs_nonneg _) (norm_nonneg _)
  · simpa using RCLike.abs_re_le_norm s
  · rw [hZ, ← orderWordProd_mul_append]
    have h := zzSingleComm_word_re_bound d L N hN hL Φ hsing hq₀ hm0 hratio wl (wm ++ wr)
      (by rw [List.length_append]; exact hcond) (by rw [List.length_append]; exact hbudget)
    simpa only [List.length_append] using h

/-- **ZZ S2/S3 term-3 leaf** (ZZ analogue of `s23_term3_bound`). -/
theorem zz_s23_term3_bound (d L N : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (wl wm wr : List Bool)
    (hcond : 3 * (N : ℝ) * (((wl ++ wm).length + wr.length : ℕ) : ℝ) ^ 2
        ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : (((wl ++ wm).length + wr.length : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (orderWordProd d L N wl
        * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
        * (orderWordProd d L N wm
          * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
          * orderWordProd d L N wr)).mulVec Φ).re|
      ≤ ‖(((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹ * 2) * (starRingEnd ℂ) (mCharge (wl.reverse.map not))‖
        * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3)
            * momentFactor d L N Φ ((wl ++ wm).length + wr.length)) := by
  set Y := orderWordProd d L N wm
    * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
      - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
    * orderWordProd d L N wr with hY
  rw [staggeredOrderDensity_commutator_eq, smul_smul, mul_smul_comm, smul_mul_assoc,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    dotProduct_orderWord_totalSpinSOp3_mid_eq d L N Φ hsing wl Y]
  set s := (((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹ * 2)
    * (starRingEnd ℂ) (mCharge (wl.reverse.map not)) with hs
  have hVim : (((L : ℂ) ^ d)⁻¹).im = 0 := by
    rw [show ((L : ℂ) ^ d)⁻¹ = (((((L : ℝ) ^ d)⁻¹ : ℝ)) : ℂ) by push_cast; ring]
    exact Complex.ofReal_im _
  have hsim : s.im = 0 := by
    rw [hs]
    simp [Complex.mul_im, Complex.mul_re, hVim, mCharge_im, Complex.conj_im, Complex.conj_re]
  set Z := star Φ ⬝ᵥ (orderWordProd d L N wl * Y).mulVec Φ with hZ
  have hre : (s * Z).re = s.re * Z.re := by rw [Complex.mul_re, hsim, zero_mul, sub_zero]
  rw [← mul_assoc, ← hs, hre, abs_mul]
  refine mul_le_mul ?_ ?_ (abs_nonneg _) (norm_nonneg _)
  · simpa using RCLike.abs_re_le_norm s
  · rw [hZ, hY]
    convert zzSingleComm_word_re_bound d L N hN hL Φ hsing hq₀ hm0 hratio (wl ++ wm) wr
      hcond hbudget using 4
    rw [orderWordProd_mul_append]; noncomm_ring

/-! ### The ZZ nested-sum collection (reduced replica) -/

/-- **ZZ S1 middle-term bound (sandwiched)** (ZZ analogue of `s1_middle_bound`). -/
theorem zz_s1_middle_bound (d L N M j k : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (hj : j < M) (hk : k < M)
    (hcond : 3 * (N : ℝ) * ((2 * M - 2 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((2 * M - 2 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ k
        * (staggeredOrderDensityOpS d L N true ^ j * (- zzDoubleComm d L N)
          * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)).mulVec Φ).re|
      ≤ 3 * (96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d)
          * momentFactor d L N Φ (2 * M - 2) := by
  rw [show staggeredOrderDensityOpS d L N false ^ k
        * (staggeredOrderDensityOpS d L N true ^ j * (- zzDoubleComm d L N)
          * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
      = - (staggeredOrderDensityOpS d L N false ^ k
          * staggeredOrderDensityOpS d L N true ^ j * zzDoubleComm d L N
          * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)
          * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)) from by noncomm_ring,
    Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re, abs_neg]
  exact zz_s1_term_bound d L N M j k hN hL Φ hsing hq₀ hm0 hratio hj hk hcond hbudget

/-- A per-`l` ZZ S2 term equals a `zz_s23_term1_bound`-shaped operator (ZZ analogue of
`s2_lterm_eq`). -/
theorem zz_s2_lterm_eq (d L N j k l r : ℕ) [NeZero L] :
    staggeredOrderDensityOpS d L N false ^ k * staggeredOrderDensityOpS d L N true ^ j
        * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
        * (staggeredOrderDensityOpS d L N true ^ l
          * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
          * staggeredOrderDensityOpS d L N true ^ (r - 1 - l))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
      = orderWordProd d L N (List.replicate k false ++ List.replicate j true)
        * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
        * (orderWordProd d L N (List.replicate l true)
          * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
          * orderWordProd d L N (List.replicate (r - 1 - l) true
            ++ List.replicate (M - 1 - k) false)) := by
  rw [orderWordProd_mul_append, orderWordProd_replicate, orderWordProd_replicate,
    orderWordProd_replicate, orderWordProd_mul_append, orderWordProd_replicate,
    orderWordProd_replicate]
  noncomm_ring

/-- A per-`l` ZZ S3 term equals a `zz_s23_term3_bound`-shaped operator (ZZ analogue of
`s3_lterm_eq`). -/
theorem zz_s3_lterm_eq (d L N j k l : ℕ) [NeZero L] :
    staggeredOrderDensityOpS d L N false ^ k
        * (staggeredOrderDensityOpS d L N true ^ l
          * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
          * staggeredOrderDensityOpS d L N true ^ (j - 1 - l))
        * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
        * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
      = orderWordProd d L N (List.replicate k false ++ List.replicate l true)
        * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
        * (orderWordProd d L N (List.replicate (j - 1 - l) true)
          * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
          * orderWordProd d L N (List.replicate (M - 1 - j) true
            ++ List.replicate (M - 1 - k) false)) := by
  rw [orderWordProd_mul_append, orderWordProd_replicate, orderWordProd_replicate,
    orderWordProd_replicate, orderWordProd_mul_append, orderWordProd_replicate,
    orderWordProd_replicate]
  noncomm_ring

/-- **Per-`l` ZZ S2 bound (uniform in `l`)** (ZZ analogue of `s2_lterm_bound`). -/
theorem zz_s2_lterm_bound (d L N M j k l : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (hj : j < M) (hk : k < M) (hl : l < M - 1 - j)
    (hcond : 3 * (N : ℝ) * ((2 * M - 3 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((2 * M - 3 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ k * staggeredOrderDensityOpS d L N true ^ j
        * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
        * (staggeredOrderDensityOpS d L N true ^ l
          * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
          * staggeredOrderDensityOpS d L N true ^ (M - 1 - j - 1 - l))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)).mulVec Φ).re|
      ≤ ((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
        * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (2 * M - 3)) := by
  have hwrlen : (List.replicate (M - 1 - j - 1 - l) true
      ++ List.replicate (M - 1 - k) false).length ≤ 2 * M := by
    simp only [List.length_append, List.length_replicate]; omega
  have hlen : (List.replicate k false ++ List.replicate j true).length
      + ((List.replicate l true).length
        + (List.replicate (M - 1 - j - 1 - l) true ++ List.replicate (M - 1 - k) false).length)
      = 2 * M - 3 := by
    simp only [List.length_append, List.length_replicate]; omega
  rw [zz_s2_lterm_eq d L N j k l (M - 1 - j)]
  refine le_trans (zz_s23_term1_bound d L N hN hL Φ hsing hq₀ hm0 hratio
    (List.replicate k false ++ List.replicate j true) (List.replicate l true)
    (List.replicate (M - 1 - j - 1 - l) true ++ List.replicate (M - 1 - k) false)
    (by rw [hlen]; exact hcond) (by rw [hlen]; exact hbudget)) ?_
  rw [hlen]
  refine mul_le_mul_of_nonneg_right ?_
    (mul_nonneg (by positivity) (momentFactor_nonneg d L N Φ _))
  refine (orderScalar_norm_le d L _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hwrlen) (by norm_num)

/-- **Per-`l` ZZ S3 bound (uniform in `l`)** (ZZ analogue of `s3_lterm_bound`). -/
theorem zz_s3_lterm_bound (d L N M j k l : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (hj : j < M) (hk : k < M) (hl : l < j)
    (hcond : 3 * (N : ℝ) * ((2 * M - 3 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((2 * M - 3 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ k
        * (staggeredOrderDensityOpS d L N true ^ l
          * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
          * staggeredOrderDensityOpS d L N true ^ (j - 1 - l))
        * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
        * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)).mulVec Φ).re|
      ≤ ((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
        * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (2 * M - 3)) := by
  have hlen : ((List.replicate k false ++ List.replicate l true)
        ++ List.replicate (j - 1 - l) true).length
      + (List.replicate (M - 1 - j) true ++ List.replicate (M - 1 - k) false).length
      = 2 * M - 3 := by
    simp only [List.length_append, List.length_replicate]; omega
  rw [zz_s3_lterm_eq d L N j k l]
  refine le_trans (zz_s23_term3_bound d L N hN hL Φ hsing hq₀ hm0 hratio
    (List.replicate k false ++ List.replicate l true) (List.replicate (j - 1 - l) true)
    (List.replicate (M - 1 - j) true ++ List.replicate (M - 1 - k) false)
    (by rw [hlen]; exact hcond) (by rw [hlen]; exact hbudget)) ?_
  rw [hlen]
  refine mul_le_mul_of_nonneg_right ?_
    (mul_nonneg (by positivity) (momentFactor_nonneg d L N Φ _))
  rw [norm_mul, Complex.norm_conj,
    show ‖((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹ * 2‖
      = ((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * 2 from by
      simp only [norm_mul, norm_inv, norm_pow, Complex.norm_natCast, Complex.norm_two]]
  have hm : ‖mCharge ((List.replicate k false ++ List.replicate l true).reverse.map not)‖
      ≤ 2 * (M : ℝ) := by
    refine (mCharge_norm_le _).trans ?_
    rw [List.length_map, List.length_reverse, List.length_append, List.length_replicate,
      List.length_replicate]
    exact_mod_cast (by omega : k + l ≤ 2 * M)
  have hV : (0 : ℝ) ≤ ((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ := by positivity
  nlinarith [hm, hV, norm_nonneg (mCharge ((List.replicate k false
    ++ List.replicate l true).reverse.map not)),
    mul_le_mul_of_nonneg_left hm hV]

/-- The sandwiched ZZ S2 part is the `l`-sum of the per-`l` operators (ZZ analogue of
`s2_part_eq`). -/
theorem zz_s2_part_eq (d L N j k r : ℕ) [NeZero L] :
    staggeredOrderDensityOpS d L N false ^ k * (staggeredOrderDensityOpS d L N true ^ j
        * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
        * (staggeredOrderDensityOpS d L N true ^ r * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true ^ r))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
      = ∑ l ∈ Finset.range r, staggeredOrderDensityOpS d L N false ^ k
          * staggeredOrderDensityOpS d L N true ^ j
          * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
          * (staggeredOrderDensityOpS d L N true ^ l
            * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
              - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
            * staggeredOrderDensityOpS d L N true ^ (r - 1 - l))
          * staggeredOrderDensityOpS d L N false ^ (M - 1 - k) := by
  rw [pow_right_commutator_eq_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun l _ => by noncomm_ring)

/-- **ZZ S2 part bound** (ZZ analogue of `s2_part_bound`). -/
theorem zz_s2_part_bound (d L N M j k : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (hj : j < M) (hk : k < M)
    (hcond : 3 * (N : ℝ) * ((2 * M - 3 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((2 * M - 3 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ k * (staggeredOrderDensityOpS d L N true ^ j
        * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
        * (staggeredOrderDensityOpS d L N true ^ (M - 1 - j) * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false
            * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)).mulVec Φ).re|
      ≤ (M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
        * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (2 * M - 3))) := by
  rw [zz_s2_part_eq d L N j k (M - 1 - j)]
  refine le_trans (abs_re_dotProduct_sum_le d L N Φ _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun l hl => zz_s2_lterm_bound d L N M j k l hN hL Φ hsing hq₀
    hm0 hratio hj hk (Finset.mem_range.mp hl) hcond hbudget)) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : M - 1 - j ≤ M))
    (mul_nonneg (by positivity) (mul_nonneg (by positivity) (momentFactor_nonneg d L N Φ _)))

/-- **ZZ S3 part operator identity** (ZZ analogue of `s3_part_eq`). -/
theorem zz_s3_part_eq (d L N j k : ℕ) [NeZero L] :
    staggeredOrderDensityOpS d L N false ^ k
        * ((staggeredOrderDensityOpS d L N true ^ j * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true ^ j)
          * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
          * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
      = ∑ l ∈ Finset.range j, staggeredOrderDensityOpS d L N false ^ k
          * (staggeredOrderDensityOpS d L N true ^ l
            * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
              - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
            * staggeredOrderDensityOpS d L N true ^ (j - 1 - l))
          * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
          * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)
          * staggeredOrderDensityOpS d L N false ^ (M - 1 - k) := by
  rw [pow_right_commutator_eq_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun l _ => by noncomm_ring)

/-- **ZZ S3 part bound** (ZZ analogue of `s3_part_bound`). -/
theorem zz_s3_part_bound (d L N M j k : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (hj : j < M) (hk : k < M)
    (hcond : 3 * (N : ℝ) * ((2 * M - 3 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget : ((2 * M - 3 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ k
        * ((staggeredOrderDensityOpS d L N true ^ j * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true ^ j)
          * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
          * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)).mulVec Φ).re|
      ≤ (M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
        * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (2 * M - 3))) := by
  rw [zz_s3_part_eq d L N j k]
  refine le_trans (abs_re_dotProduct_sum_le d L N Φ _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun l hl => zz_s3_lterm_bound d L N M j k l hN hL Φ hsing hq₀
    hm0 hratio hj hk (Finset.mem_range.mp hl) hcond hbudget)) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : j ≤ M))
    (mul_nonneg (by positivity) (mul_nonneg (by positivity) (momentFactor_nonneg d L N Φ _)))

/-- **Per-`j` three-way ZZ split with `d̂_ZZ` surfaced** (ZZ analogue of `Tj_orderMinus_decomp`). -/
theorem zz_Tj_orderMinus_decomp (d L N j r : ℕ) [NeZero L] :
    (staggeredOrderDensityOpS d L N true ^ j
        * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
        * staggeredOrderDensityOpS d L N true ^ r) * staggeredOrderDensityOpS d L N false
      - staggeredOrderDensityOpS d L N false * (staggeredOrderDensityOpS d L N true ^ j
        * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
        * staggeredOrderDensityOpS d L N true ^ r)
      = staggeredOrderDensityOpS d L N true ^ j
          * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
          * (staggeredOrderDensityOpS d L N true ^ r * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true ^ r)
        + staggeredOrderDensityOpS d L N true ^ j * (- zzDoubleComm d L N)
          * staggeredOrderDensityOpS d L N true ^ r
        + (staggeredOrderDensityOpS d L N true ^ j * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true ^ j)
          * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
            - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
          * staggeredOrderDensityOpS d L N true ^ r := by
  rw [mul_mul_commutator_decomp, zz_order_nested_eq_neg_zzDoubleComm]

/-- **Per-`(j,k)` ZZ term bound** (ZZ analogue of `tower_jk_term_bound`). -/
theorem zz_tower_jk_term_bound (d L N M j k : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (hj : j < M) (hk : k < M)
    (hcond2 : 3 * (N : ℝ) * ((2 * M - 2 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget2 : ((2 * M - 2 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2)
    (hcond3 : 3 * (N : ℝ) * ((2 * M - 3 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget3 : ((2 * M - 3 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ k
        * ((staggeredOrderDensityOpS d L N true ^ j
              * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
                - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
              * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
            * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false
            * (staggeredOrderDensityOpS d L N true ^ j
              * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
                - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
              * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)).mulVec Φ).re|
      ≤ 3 * (96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d) * momentFactor d L N Φ (2 * M - 2)
        + ((M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
            * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (2 * M - 3)))
          + (M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
            * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (2 * M - 3)))) := by
  rw [show staggeredOrderDensityOpS d L N false ^ k
        * ((staggeredOrderDensityOpS d L N true ^ j
              * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
                - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
              * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
            * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false
            * (staggeredOrderDensityOpS d L N true ^ j
              * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
                - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
              * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)))
        * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
      = staggeredOrderDensityOpS d L N false ^ k
          * (staggeredOrderDensityOpS d L N true ^ j * (- zzDoubleComm d L N)
            * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
          * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
        + (staggeredOrderDensityOpS d L N false ^ k * (staggeredOrderDensityOpS d L N true ^ j
            * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
              - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
            * (staggeredOrderDensityOpS d L N true ^ (M - 1 - j)
                * staggeredOrderDensityOpS d L N false
              - staggeredOrderDensityOpS d L N false
                * staggeredOrderDensityOpS d L N true ^ (M - 1 - j)))
            * staggeredOrderDensityOpS d L N false ^ (M - 1 - k)
          + staggeredOrderDensityOpS d L N false ^ k
            * ((staggeredOrderDensityOpS d L N true ^ j * staggeredOrderDensityOpS d L N false
                - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true ^ j)
              * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true
                - staggeredOrderDensityOpS d L N true * zzHamiltonianS d L N)
              * staggeredOrderDensityOpS d L N true ^ (M - 1 - j))
            * staggeredOrderDensityOpS d L N false ^ (M - 1 - k))
      from by rw [zz_Tj_orderMinus_decomp d L N j (M - 1 - j)]; noncomm_ring,
    Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add,
    Complex.add_re, Complex.add_re]
  refine (abs_add_le _ _).trans (add_le_add ?_ ((abs_add_le _ _).trans (add_le_add ?_ ?_)))
  · exact zz_s1_middle_bound d L N M j k hN hL Φ hsing hq₀ hm0 hratio hj hk hcond2 hbudget2
  · exact zz_s2_part_bound d L N M j k hN hL Φ hsing hq₀ hm0 hratio hj hk hcond3 hbudget3
  · exact zz_s3_part_bound d L N M j k hN hL Φ hsing hq₀ hm0 hratio hj hk hcond3 hbudget3

/-- **ZZ numerator double-commutator bound** (ZZ analogue of `tower_numerator_bound`; identical RHS
shape).  Bounds `⟨Φ, [(ô⁻)^M, [Ĥ_ZZ, (ô⁺)^M]] Φ⟩` by the `M²` per-`(j,k)` terms. -/
theorem zz_tower_numerator_bound (d L N M : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L N Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1))
    (hcond2 : 3 * (N : ℝ) * ((2 * M - 2 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget2 : ((2 * M - 2 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2)
    (hcond3 : 3 * (N : ℝ) * ((2 * M - 3 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget3 : ((2 * M - 3 : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ M
        * (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true ^ M
          - staggeredOrderDensityOpS d L N true ^ M * zzHamiltonianS d L N)
      - (zzHamiltonianS d L N * staggeredOrderDensityOpS d L N true ^ M
          - staggeredOrderDensityOpS d L N true ^ M * zzHamiltonianS d L N)
        * staggeredOrderDensityOpS d L N false ^ M).mulVec Φ).re|
      ≤ (M : ℝ) * ((M : ℝ) * (3 * (96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d)
            * momentFactor d L N Φ (2 * M - 2)
        + ((M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
            * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (2 * M - 3)))
          + (M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
            * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (2 * M - 3)))))) := by
  rw [zz_numerator_eq_sum_j]
  refine (abs_re_dotProduct_sum_le d L N Φ (Finset.range M) _).trans ?_
  refine le_trans (Finset.sum_le_card_nsmul (Finset.range M) _
    ((M : ℝ) * (3 * (96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d) * momentFactor d L N Φ (2 * M - 2)
        + ((M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
            * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (2 * M - 3)))
          + (M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
            * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (2 * M - 3)))))) ?_)
    (le_of_eq (by rw [Finset.card_range, nsmul_eq_mul]))
  intro j hj
  rw [orderMinusPow_commutator_eq]
  refine (abs_re_dotProduct_neg_sum_le d L N Φ (Finset.range M) _).trans ?_
  refine le_trans (Finset.sum_le_card_nsmul (Finset.range M) _
    (3 * (96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d) * momentFactor d L N Φ (2 * M - 2)
      + ((M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
          * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (2 * M - 3)))
        + (M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
          * (3 * (24 * (d : ℝ) * (N : ℝ) ^ 3) * momentFactor d L N Φ (2 * M - 3)))))
    ?_) (le_of_eq (by rw [Finset.card_range, nsmul_eq_mul]))
  intro k hk
  exact zz_tower_jk_term_bound d L N M j k hN hL Φ hsing hq₀ hm0 hratio
    (Finset.mem_range.mp hj) (Finset.mem_range.mp hk) hcond2 hbudget2 hcond3 hbudget3

/-! ### The XY-planar numerator bound (PR-4b deliverable) -/

/-- **XY-planar variational numerator bound** (design-note math (2.1), the PR-4b deliverable).  For
the half-filling XY tower (`N = 1`), the pure-XY variational numerator with `Ĥ' = 2 Ĥ_XY` splits by
`Ĥ_XY = Ĥ_Heis − Ĥ_ZZ` and Hamiltonian-linearity into `2 · (Heisenberg numerator) − 2 · (ZZ
numerator)`; the triangle inequality with `tower_numerator_bound` (Anderson-tower Theorem 4.6) and
`zz_tower_numerator_bound` — which have the *identical* moment-factor right-hand side — bounds it by
`4` copies of that common `O(M²/V)` right-hand side.  This is the `Term1` numerator consumed by the
PR-5 half-filling tower assembly.

Reference: Tasaki §5.3 Theorem 5.2, eq. (5.3.4), p. 141; math note
`.self-local/docs/math-thm52-pr4b-zz-numerator.md` §2 eq. (2.1). -/
theorem xy_tower_numerator_bound (d L M : ℕ) [NeZero L] (hL : 2 ≤ L)
    (Φ : (HypercubicTorus d L → Fin 2) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec Φ = 0) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hm0 : 0 < phatMoment d L 1 Φ 0)
    (hratio : ∀ n, 2 * q₀ * phatMoment d L 1 Φ n ≤ phatMoment d L 1 Φ (n + 1))
    (hcond2 : 3 * ((1 : ℕ) : ℝ) * ((2 * M - 2 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget2 : ((2 * M - 2 : ℕ) : ℝ)
        * ((2 * 2 * ((1 : ℕ) : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2)
    (hcond3 : 3 * ((1 : ℕ) : ℝ) * ((2 * M - 3 : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudget3 : ((2 * M - 3 : ℕ) : ℝ)
        * ((2 * 2 * ((1 : ℕ) : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2) :
    |(star Φ ⬝ᵥ (staggeredOrderDensityOpS d L 1 false ^ M
        * (((2 : ℂ) • xyHamiltonianS d L) * staggeredOrderDensityOpS d L 1 true ^ M
          - staggeredOrderDensityOpS d L 1 true ^ M * ((2 : ℂ) • xyHamiltonianS d L))
      - (((2 : ℂ) • xyHamiltonianS d L) * staggeredOrderDensityOpS d L 1 true ^ M
          - staggeredOrderDensityOpS d L 1 true ^ M * ((2 : ℂ) • xyHamiltonianS d L))
        * staggeredOrderDensityOpS d L 1 false ^ M).mulVec Φ).re|
      ≤ 4 * ((M : ℝ) * ((M : ℝ) * (3 * (96 * (d : ℝ) * ((1 : ℕ) : ℝ) ^ 4 / (L : ℝ) ^ d)
            * momentFactor d L 1 Φ (2 * M - 2)
        + ((M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
            * (3 * (24 * (d : ℝ) * ((1 : ℕ) : ℝ) ^ 3) * momentFactor d L 1 Φ (2 * M - 3)))
          + (M : ℝ) * (((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (2 * (M : ℝ)))
            * (3 * (24 * (d : ℝ) * ((1 : ℕ) : ℝ) ^ 3)
              * momentFactor d L 1 Φ (2 * M - 3))))))) := by
  have hnum : staggeredOrderDensityOpS d L 1 false ^ M
        * (((2 : ℂ) • xyHamiltonianS d L) * staggeredOrderDensityOpS d L 1 true ^ M
          - staggeredOrderDensityOpS d L 1 true ^ M * ((2 : ℂ) • xyHamiltonianS d L))
      - (((2 : ℂ) • xyHamiltonianS d L) * staggeredOrderDensityOpS d L 1 true ^ M
          - staggeredOrderDensityOpS d L 1 true ^ M * ((2 : ℂ) • xyHamiltonianS d L))
        * staggeredOrderDensityOpS d L 1 false ^ M
      = (2 : ℂ) • (staggeredOrderDensityOpS d L 1 false ^ M
            * (heisenbergHamiltonianS (torusNNCoupling d L) 1
                * staggeredOrderDensityOpS d L 1 true ^ M
              - staggeredOrderDensityOpS d L 1 true ^ M
                * heisenbergHamiltonianS (torusNNCoupling d L) 1)
          - (heisenbergHamiltonianS (torusNNCoupling d L) 1
                * staggeredOrderDensityOpS d L 1 true ^ M
              - staggeredOrderDensityOpS d L 1 true ^ M
                * heisenbergHamiltonianS (torusNNCoupling d L) 1)
            * staggeredOrderDensityOpS d L 1 false ^ M)
        - (2 : ℂ) • (staggeredOrderDensityOpS d L 1 false ^ M
            * (zzHamiltonianS d L 1 * staggeredOrderDensityOpS d L 1 true ^ M
              - staggeredOrderDensityOpS d L 1 true ^ M * zzHamiltonianS d L 1)
          - (zzHamiltonianS d L 1 * staggeredOrderDensityOpS d L 1 true ^ M
              - staggeredOrderDensityOpS d L 1 true ^ M * zzHamiltonianS d L 1)
            * staggeredOrderDensityOpS d L 1 false ^ M) := by
    rw [xyHamiltonianS_eq_heisenberg_sub_zz]
    simp only [smul_sub, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
    abel
  rw [hnum, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.smul_mulVec,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, Complex.sub_re]
  have h2re : ∀ z : ℂ, ((2 : ℂ) * z).re = 2 * z.re := fun z => by simp [Complex.mul_re]
  rw [h2re, h2re]
  have hHeis := tower_numerator_bound d L 1 M le_rfl hL Φ hsing hq₀ hm0 hratio
    hcond2 hbudget2 hcond3 hbudget3
  have hZZ := zz_tower_numerator_bound d L 1 M le_rfl hL Φ hsing hq₀ hm0 hratio
    hcond2 hbudget2 hcond3 hbudget3
  rcases abs_le.mp hHeis with ⟨hh1, hh2⟩
  rcases abs_le.mp hZZ with ⟨hz1, hz2⟩
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

end LatticeSystem.Quantum
