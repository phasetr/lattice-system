/-
Tasaki §4.2.2 Theorem 4.8 (Tanaka symmetry-breaking state), arc PR2 [N1] — the same-sign double
commutators `[ô^±, [Ĥ, ô^±]]` in the local-decay class.

The 1-axis order operator `ô^{(1)} = (ô⁺ + ô⁻)/2` (`staggeredOrderOp1S`) generates the Tanaka
tower, whose double commutator `d̂^{(1)} = [ô^{(1)}, [Ĥ, ô^{(1)}]]` expands (eqs. (4.2.67)/(4.2.68))
into the Theorem 4.6 mixed-sign piece `d̂ = [ô⁺, [Ĥ, ô⁻]]` (`orderDoubleComm`), its mirror, and the
two **same-sign** pieces `[ô⁺, [Ĥ, ô⁺]]` and `[ô⁻, [Ĥ, ô⁻]]`.  The mixed-sign piece already lies in
the local-decay class (`isR2LocalUpTo_orderDoubleComm`); this file adds the same-sign pieces.

Rather than re-deriving the full per-bond double-commutator support decomposition, we reuse the
generic recursion `IsR2LocalUpTo.orderComm_mem`: one more order-density commutator of a depth-`≥1`
local operator lowers the depth by one and contracts the aggregate by `2ζo₀/V`.  The single
Heisenberg commutator `[Ĥ, ô⁺]` is already in the class (`isR2LocalUpTo_heisenbergRaisingComm`); we
add the lowering mirror `[Ĥ, ô⁻]` and then apply `orderComm` once to reach the same-sign double
commutator.

This file is downstream of `AndersonTowerLocalDecay`.  It touches no crux ([N2], the 1-axis
numerator's binomial cancellation) — only the reusable non-crux local-decay layer.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, eqs. (4.2.67)–(4.2.68), pp. 111–112 (Tanaka [62]).
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerLocalDecay

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {d L N : ℕ}

/-! ### The single lowering commutator `[Ĥ, ô⁻]` lies in the local-decay class -/

/-- The bond–order lowering commutator `[Ŝ_x·Ŝ_y, Ô_L⁻]` is supported on the bond `{x, y}` (lowering
mirror of `spinSDot_staggeredRaising_commutator_supportedOn`). -/
theorem spinSDot_staggeredLowering_commutator_supportedOn (A : Λ → Bool) (x y : Λ) (hxy : x ≠ y) :
    SupportedOn ({x, y} : Finset Λ)
      (spinSDot x y N * staggeredLoweringOpS A N - staggeredLoweringOpS A N * spinSDot x y N) := by
  rw [spinSDot_commutator_staggeredLoweringOpS_support A x y hxy]
  have hx : ({x} : Finset Λ) ⊆ {x, y} :=
    Finset.singleton_subset_iff.mpr (Finset.mem_insert_self x {y})
  have hy : ({y} : Finset Λ) ⊆ {x, y} :=
    Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
  have hSx : SupportedOn ({x, y} : Finset Λ) (spinSSiteOpMinus x N) :=
    (onSiteS_supportedOn x (spinSOpMinus N)).mono hx
  have hSy : SupportedOn ({x, y} : Finset Λ) (spinSSiteOpMinus y N) :=
    (onSiteS_supportedOn y (spinSOpMinus N)).mono hy
  have hdot := spinSDot_supportedOn (N := N) x y
  exact (((hdot.mul hSx).sub (hSx.mul hdot)).smul _).add
    (((hdot.mul hSy).sub (hSy.mul hdot)).smul _)

/-- The single Heisenberg–order commutator `[Ĥ, ô⁻]` as a bond sum (offDiag, diagonal `J = 0`):
`[Ĥ, ô⁻] = ∑_{x≠y} (V⁻¹ J_{xy}) · [Ŝ_x·Ŝ_y, Ô⁻]` (lowering mirror of
`heisenbergRaisingComm_eq_offDiag_sum`). -/
theorem heisenbergLoweringComm_eq_offDiag_sum [NeZero L] (hL : 2 ≤ L) :
    heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N false
        - staggeredOrderDensityOpS d L N false * heisenbergHamiltonianS (torusNNCoupling d L) N
      = ∑ p ∈ Finset.univ.filter
          (fun p : HypercubicTorus d L × HypercubicTorus d L => p.1 ≠ p.2),
          (((L : ℂ) ^ d)⁻¹ * torusNNCoupling d L p.1 p.2)
            • (spinSDot p.1 p.2 N * staggeredLoweringOpS (torusParitySublattice d L) N
              - staggeredLoweringOpS (torusParitySublattice d L) N * spinSDot p.1 p.2 N) := by
  have hH : heisenbergHamiltonianS (torusNNCoupling d L) N
      = ∑ p : HypercubicTorus d L × HypercubicTorus d L,
          torusNNCoupling d L p.1 p.2 • spinSDot p.1 p.2 N := by
    rw [heisenbergHamiltonianS_def, ← Finset.sum_product', Finset.univ_product_univ]
  rw [show staggeredOrderDensityOpS d L N false
      = ((L : ℂ) ^ d)⁻¹ • staggeredLoweringOpS (torusParitySublattice d L) N from rfl,
    mul_smul_comm, smul_mul_assoc, ← smul_sub, hH, commutator_sum_smul_left, Finset.smul_sum,
    Finset.sum_congr rfl (fun p _ => smul_smul (((L : ℂ) ^ d)⁻¹)
      (torusNNCoupling d L p.1 p.2) (spinSDot p.1 p.2 N * staggeredLoweringOpS
        (torusParitySublattice d L) N - staggeredLoweringOpS (torusParitySublattice d L) N
        * spinSDot p.1 p.2 N))]
  refine (Finset.sum_filter_of_ne (fun p _ hfne => ?_)).symm
  intro hpe
  apply hfne
  rw [show torusNNCoupling d L p.1 p.2 = 0 from by
    rw [hpe]; exact torusNNCoupling_self_eq_zero d L hL p.2, mul_zero, zero_smul]

/-- The ℓ¹-aggregate carried by `[Ĥ, ô⁻]`'s quasi-local decomposition (lowering mirror of
`heisenbergRaisingCommAggregate`). -/
noncomputable def heisenbergLoweringCommAggregate (d L N : ℕ) [NeZero L] : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p : HypercubicTorus d L × HypercubicTorus d L => p.1 ≠ p.2),
    ‖((L : ℂ) ^ d)⁻¹ * torusNNCoupling d L p.1 p.2‖
      * manyBodyOperatorNormS
        (spinSDot p.1 p.2 N * staggeredLoweringOpS (torusParitySublattice d L) N
          - staggeredLoweringOpS (torusParitySublattice d L) N * spinSDot p.1 p.2 N)

/-- **`G = [Ĥ, ô⁻]` lies in the local-decay class** (`ζ = 2`, `o₀ = N`, `g₀` the bond aggregate):
lowering mirror of `isR2LocalUpTo_heisenbergRaisingComm`. -/
theorem isR2LocalUpTo_heisenbergLoweringComm [NeZero L] (hL : 2 ≤ L) (hN : 1 ≤ N) (K : ℕ) :
    IsR2LocalUpTo K 2 (N : ℝ) (heisenbergLoweringCommAggregate d L N)
      (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N false
        - staggeredOrderDensityOpS d L N false
          * heisenbergHamiltonianS (torusNNCoupling d L) N) := by
  refine ⟨Finset.sum_nonneg
    (fun p _ => mul_nonneg (norm_nonneg _) (manyBodyOperatorNormS_nonneg _)), fun u _ => ?_⟩
  rw [heisenbergLoweringComm_eq_offDiag_sum hL]
  have hbd := iterOrderComm_norm_le_of_localSum hN u
    (Finset.univ.filter (fun p : HypercubicTorus d L × HypercubicTorus d L => p.1 ≠ p.2))
    (fun p => ((L : ℂ) ^ d)⁻¹ * torusNNCoupling d L p.1 p.2)
    (fun p => spinSDot p.1 p.2 N * staggeredLoweringOpS (torusParitySublattice d L) N
      - staggeredLoweringOpS (torusParitySublattice d L) N * spinSDot p.1 p.2 N)
    (fun p => ({p.1, p.2} : Finset (HypercubicTorus d L))) 2
    (fun p hp => spinSDot_staggeredLowering_commutator_supportedOn _ p.1 p.2
      (Finset.mem_filter.mp hp).2)
    (fun p _ => (Finset.card_insert_le _ _).trans (by simp))
  simpa [heisenbergLoweringCommAggregate] using hbd

/-- **The single-commutator lowering aggregate is `≤ 24 d N³`.**  `≤ 2dV` bonds × `V⁻¹·12N³`
(lowering mirror of `heisenbergRaisingCommAggregate_le`). -/
theorem heisenbergLoweringCommAggregate_le [NeZero L] (hL : 2 ≤ L) (hN : 1 ≤ N) :
    heisenbergLoweringCommAggregate d L N ≤ 24 * (d : ℝ) * (N : ℝ) ^ 3 := by
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hVc : ‖((L : ℂ) ^ d)⁻¹‖ = ((L : ℝ) ^ d)⁻¹ := by
    simp only [norm_inv, norm_pow, Complex.norm_natCast]
  calc heisenbergLoweringCommAggregate d L N
      ≤ ∑ p ∈ Finset.univ.filter
          (fun p : HypercubicTorus d L × HypercubicTorus d L => p.1 ≠ p.2),
          ((L : ℝ) ^ d)⁻¹ * ‖torusNNCoupling d L p.1 p.2‖ * (12 * (N : ℝ) ^ 3) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        rw [norm_mul, hVc]
        exact mul_le_mul_of_nonneg_left
          (spinSDot_commutator_staggeredLoweringOpS_norm_le _ p.1 p.2
            (Finset.mem_filter.mp hp).2 hN) (by positivity)
    _ = ((L : ℝ) ^ d)⁻¹ * (12 * (N : ℝ) ^ 3)
          * ∑ p ∈ Finset.univ.filter
            (fun p : HypercubicTorus d L × HypercubicTorus d L => p.1 ≠ p.2),
            ‖torusNNCoupling d L p.1 p.2‖ := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun p _ => by ring)
    _ ≤ ((L : ℝ) ^ d)⁻¹ * (12 * (N : ℝ) ^ 3) * (2 * (d : ℝ) * (L : ℝ) ^ d) := by
        have hsub : (∑ p ∈ Finset.univ.filter
              (fun p : HypercubicTorus d L × HypercubicTorus d L => p.1 ≠ p.2),
              ‖torusNNCoupling d L p.1 p.2‖)
            ≤ ∑ p : HypercubicTorus d L × HypercubicTorus d L, ‖torusNNCoupling d L p.1 p.2‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (hsub.trans (torusNNCoupling_total_norm_le d L))
          (by positivity)
    _ = 24 * (d : ℝ) * (N : ℝ) ^ 3 := by field_simp; ring

/-! ### The same-sign double commutators `[ô^±, [Ĥ, ô^±]]` in the local-decay class -/

/-- The single Heisenberg–order commutator `[Ĥ, ô^b]` (`b = true` raising, `b = false` lowering),
in a sign-generic form so the same-sign double commutator can be written uniformly. -/
noncomputable def heisenbergSignComm (d L N : ℕ) [NeZero L] (b : Bool) :
    ManyBodyOpS (HypercubicTorus d L) N :=
  heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N b
    - staggeredOrderDensityOpS d L N b * heisenbergHamiltonianS (torusNNCoupling d L) N

/-- The ℓ¹-aggregate carried by `[Ĥ, ô^b]`: the raising or lowering bond aggregate as `b` selects
between them. -/
noncomputable def heisenbergSignCommAggregate (d L N : ℕ) [NeZero L] (b : Bool) : ℝ :=
  if b then heisenbergRaisingCommAggregate d L N else heisenbergLoweringCommAggregate d L N

/-- **`[Ĥ, ô^b]` lies in the local-decay class** (`ζ = 2`, `o₀ = N`): the raising
(`isR2LocalUpTo_heisenbergRaisingComm`) and lowering (`isR2LocalUpTo_heisenbergLoweringComm`) cases
packaged uniformly. -/
theorem isR2LocalUpTo_heisenbergSignComm [NeZero L] (hL : 2 ≤ L) (hN : 1 ≤ N) (b : Bool) (K : ℕ) :
    IsR2LocalUpTo K 2 (N : ℝ) (heisenbergSignCommAggregate d L N b)
      (heisenbergSignComm d L N b) := by
  cases b with
  | false =>
    simpa [heisenbergSignComm, heisenbergSignCommAggregate] using
      isR2LocalUpTo_heisenbergLoweringComm hL hN K
  | true =>
    simpa [heisenbergSignComm, heisenbergSignCommAggregate] using
      isR2LocalUpTo_heisenbergRaisingComm hL hN K

/-- **The single-commutator aggregate is `≤ 24 d N³`** for either sign. -/
theorem heisenbergSignCommAggregate_le [NeZero L] (hL : 2 ≤ L) (hN : 1 ≤ N) (b : Bool) :
    heisenbergSignCommAggregate d L N b ≤ 24 * (d : ℝ) * (N : ℝ) ^ 3 := by
  cases b with
  | false =>
    rw [heisenbergSignCommAggregate, if_neg (by simp)]
    exact heisenbergLoweringCommAggregate_le hL hN
  | true =>
    rw [heisenbergSignCommAggregate, if_pos rfl]
    exact heisenbergRaisingCommAggregate_le hL hN

/-- The per-volume **same-sign** double commutator `[ô^b, [Ĥ, ô^b]]` (both order operators equal),
the `1`-axis analogue of the mixed-sign `orderDoubleComm = [ô⁺, [Ĥ, ô⁻]]`.  It is
`orderComm b (heisenbergSignComm d L N b)` by definition of `orderComm`. -/
noncomputable def orderDoubleCommSameSign (d L N : ℕ) [NeZero L] (b : Bool) :
    ManyBodyOpS (HypercubicTorus d L) N :=
  staggeredOrderDensityOpS d L N b * heisenbergSignComm d L N b
    - heisenbergSignComm d L N b * staggeredOrderDensityOpS d L N b

/-- The ℓ¹-aggregate for the same-sign double commutator: one extra `orderComm` decay factor
`2ζo₀/V = 2·2·N/V` times the single-commutator aggregate. -/
noncomputable def orderDoubleCommSameSignAggregate (d L N : ℕ) [NeZero L] (b : Bool) : ℝ :=
  (2 * 2 * (N : ℝ)) / (L : ℝ) ^ d * heisenbergSignCommAggregate d L N b

/-- **The same-sign double commutator lies in the local-decay class** (`ζ = 2`, `o₀ = N`, `g₀` its
aggregate), for either sign.  Obtained from `[Ĥ, ô^b] ∈` class (at depth `K + 1`) by the recursion
`IsR2LocalUpTo.orderComm_mem` (one `orderComm b` step). -/
theorem isR2LocalUpTo_orderDoubleCommSameSign [NeZero L] (hL : 2 ≤ L) (hN : 1 ≤ N) (b : Bool)
    (K : ℕ) :
    IsR2LocalUpTo K 2 (N : ℝ) (orderDoubleCommSameSignAggregate d L N b)
      (orderDoubleCommSameSign d L N b) := by
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hdecay : (0 : ℝ) ≤ (2 * 2 * (N : ℝ)) / (L : ℝ) ^ d := by positivity
  exact (isR2LocalUpTo_heisenbergSignComm hL hN b (K + 1)).orderComm_mem b hdecay

/-- **The same-sign double-commutator aggregate is `≤ 96 d N⁴ / V`** for either sign — the same
`O(1/V)` bound as the mixed-sign `orderDoubleCommAggregate`. -/
theorem orderDoubleCommSameSignAggregate_le [NeZero L] (hL : 2 ≤ L) (hN : 1 ≤ N) (b : Bool) :
    orderDoubleCommSameSignAggregate d L N b ≤ 96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d := by
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hsingle := heisenbergSignCommAggregate_le (d := d) hL hN b
  rw [orderDoubleCommSameSignAggregate]
  have hkey : (2 * 2 * (N : ℝ)) / (L : ℝ) ^ d * heisenbergSignCommAggregate d L N b
      ≤ (2 * 2 * (N : ℝ)) / (L : ℝ) ^ d * (24 * (d : ℝ) * (N : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left hsingle (by positivity)
  refine hkey.trans (le_of_eq ?_)
  field_simp
  ring

/-! ### The charge-neutral mirror double commutator `[ô⁻, [Ĥ, ô⁺]]` in the local-decay class -/

/-- The per-volume **mirror** double commutator `d̂' = [ô⁻, [Ĥ, ô⁺]]`, the missing charge-neutral
partner of the Theorem 4.6 mixed-sign piece `orderDoubleComm = [ô⁺, [Ĥ, ô⁻]]`.  Together they form
the charge-`0` block `G₀` of the `1`-axis double commutator `d̃ = [ô^{(1)}, [Ĥ, ô^{(1)}]]`. -/
noncomputable def orderDoubleCommMirror (d L N : ℕ) [NeZero L] :
    ManyBodyOpS (HypercubicTorus d L) N :=
  staggeredOrderDensityOpS d L N false * heisenbergSignComm d L N true
    - heisenbergSignComm d L N true * staggeredOrderDensityOpS d L N false

/-- The ℓ¹-aggregate for the mirror double commutator: one extra `orderComm` decay factor
`2ζo₀/V = 2·2·N/V` times the single raising-commutator aggregate (mirror of
`orderDoubleCommSameSignAggregate`). -/
noncomputable def orderDoubleCommMirrorAggregate (d L N : ℕ) [NeZero L] : ℝ :=
  (2 * 2 * (N : ℝ)) / (L : ℝ) ^ d * heisenbergSignCommAggregate d L N true

/-- **The mirror double commutator lies in the local-decay class** (`ζ = 2`, `o₀ = N`, `g₀` its
aggregate).  Obtained from `[Ĥ, ô⁺] ∈` class (at depth `K + 1`) by the recursion
`IsR2LocalUpTo.orderComm_mem` with a lowering `orderComm false` step. -/
theorem isR2LocalUpTo_orderDoubleCommMirror [NeZero L] (hL : 2 ≤ L) (hN : 1 ≤ N) (K : ℕ) :
    IsR2LocalUpTo K 2 (N : ℝ) (orderDoubleCommMirrorAggregate d L N)
      (orderDoubleCommMirror d L N) := by
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hdecay : (0 : ℝ) ≤ (2 * 2 * (N : ℝ)) / (L : ℝ) ^ d := by positivity
  exact (isR2LocalUpTo_heisenbergSignComm hL hN true (K + 1)).orderComm_mem false hdecay

/-- **The mirror double-commutator aggregate is `≤ 96 d N⁴ / V`** — the same `O(1/V)` bound as the
mixed-sign and same-sign pieces. -/
theorem orderDoubleCommMirrorAggregate_le [NeZero L] (hL : 2 ≤ L) (hN : 1 ≤ N) :
    orderDoubleCommMirrorAggregate d L N ≤ 96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d := by
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hsingle := heisenbergSignCommAggregate_le (d := d) hL hN true
  rw [orderDoubleCommMirrorAggregate]
  have hkey : (2 * 2 * (N : ℝ)) / (L : ℝ) ^ d * heisenbergSignCommAggregate d L N true
      ≤ (2 * 2 * (N : ℝ)) / (L : ℝ) ^ d * (24 * (d : ℝ) * (N : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left hsingle (by positivity)
  refine hkey.trans (le_of_eq ?_)
  field_simp
  ring

end LatticeSystem.Quantum
