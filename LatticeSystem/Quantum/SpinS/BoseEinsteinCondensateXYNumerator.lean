import LatticeSystem.Quantum.SpinS.AndersonTowerNumerator
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergU1
import LatticeSystem.Quantum.SpinS.BoseEinsteinCondensate

/-!
# Tasaki §5.3 Theorem 5.2 (BEC low-lying tower states): XY-planar numerator bound

This file discharges the **XY-planar variational-numerator bound** of the Bose–Einstein-condensation
tower (`tasaki_5_2_bec_tower`, Tasaki §5.3, eq. (5.3.4)) at half filling.  The route is the
definitional Hamiltonian split (route (i) of the design note `math-thm52-pr4b-zz-numerator.md`):
`Ĥ_XY = Ĥ_Heis − Ĥ_ZZ` (with `Ĥ_ZZ = Σ_{x,y} J_{xy} Ŝ³_x Ŝ³_y`), coming for free from
`spinSDotXXZ_eq_spinSDot_add` at anisotropy `λ = 0`.  Because the tower operator
`A = (Ô_L^{sgn M})^{|M|}` is identical to the Anderson-tower operator, the double commutator is
linear in the Hamiltonian, so the pure-XY numerator splits as
`⟨Φ, [Aᴴ, [2 Ĥ_XY, A]] Φ⟩ = 2 ⟨Φ, [Aᴴ, [Ĥ_Heis, A]] Φ⟩ − 2 ⟨Φ, [Aᴴ, [Ĥ_ZZ, A]] Φ⟩`.  The
Heisenberg term is bounded verbatim by the Anderson-tower asset `tower_numerator_bound`; the
residual `Ĥ_ZZ` term is bounded here by instantiating the Hamiltonian-agnostic numerator collection
`tower_numerator_bound_of_word_bounds` with the two `Ĥ_ZZ` order-word bounds proved below, which the
split-independent R2 engine `r2_split_independent` supplies.

The `Ĥ_ZZ` locality is obtained directly from `iterOrderComm_norm_le_of_localSum`: `Ĥ_ZZ` is a sum
of two-site-supported bond operators `Ŝ³_x Ŝ³_y`, so its iterated order-density commutators decay by
`(4N/V)` per step, and the `Ĥ_ZZ` single/double commutators are just two such iterated commutators.
The resulting aggregates are bounded by the *same* constants `24 d N³` and `96 d N⁴ / V` as the
Heisenberg instantiation (the `Ŝ³ Ŝ³` leaf is smaller than the `Ŝ_x·Ŝ_y` leaf), so the final `Ĥ_ZZ`
numerator bound has the identical moment-factor shape as `tower_numerator_bound`, which is exactly
what lets `xy_tower_numerator_bound` combine the two bounds into a single right-hand side.

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

/-! ### The ZZ word bounds (inputs to the generic numerator engine) -/

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

/-! ### The ZZ numerator bound -/

/-- **ZZ numerator double-commutator bound.**  The ★-variational numerator
`⟨Φ, [(ô⁻)^M, [Ĥ_ZZ, (ô⁺)^M]] Φ⟩` is bounded by `M²` copies of the per-insertion bound: the generic
collection `tower_numerator_bound_of_word_bounds` applied to `Ĥ_ZZ`, with `d̂_ZZ` as the double
commutator (`[[Ĥ_ZZ,ô⁺],ô⁻] = −d̂_ZZ`) and the two Lemma R2 word bounds
`zzDoubleComm_word_re_bound` (`c₁ = 96 d N⁴/V`) and `zzSingleComm_word_re_bound` (`c₂ = 24 d N³`)
as its hypotheses.  Those constants coincide with the Heisenberg ones, so the right-hand side has
the same shape as `tower_numerator_bound` — which is what lets `xy_tower_numerator_bound` add the
two bounds.  Reference: Tasaki §5.3 Theorem 5.2, eq. (5.3.4), p. 141. -/
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
  exact tower_numerator_bound_of_word_bounds d L N M Φ hsing
    (zzHamiltonianS d L N) _ (zzDoubleComm d L N) rfl
    (zz_order_nested_eq_neg_zzDoubleComm d L N) (by positivity)
    (fun wl wr hc hb =>
      zzDoubleComm_word_re_bound d L N hN hL Φ hsing hq₀ hm0 hratio wl wr hc hb)
    (fun wl wr hc hb =>
      zzSingleComm_word_re_bound d L N hN hL Φ hsing hq₀ hm0 hratio wl wr hc hb)
    hcond2 hbudget2 hcond3 hbudget3

/-! ### The XY-planar numerator bound -/

/-- **XY-planar variational numerator bound** (design-note math (2.1)).  For the half-filling XY
tower (`N = 1`), the pure-XY variational numerator with `Ĥ' = 2 Ĥ_XY` splits by
`Ĥ_XY = Ĥ_Heis − Ĥ_ZZ` and Hamiltonian-linearity into `2 · (Heisenberg numerator) − 2 · (ZZ
numerator)`; the triangle inequality with `tower_numerator_bound` (Anderson-tower Theorem 4.6) and
`zz_tower_numerator_bound` — both instantiations of the same generic engine
`tower_numerator_bound_of_word_bounds`, hence with the *identical* moment-factor right-hand side —
bounds it by `4` copies of that common `O(M²/V)` right-hand side.  This numerator is consumed by
the half-filling tower assembly in `BoseEinsteinCondensateTower`.

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
