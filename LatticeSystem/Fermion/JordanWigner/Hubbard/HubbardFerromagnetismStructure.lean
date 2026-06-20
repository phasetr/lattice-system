import LatticeSystem.Fermion.JordanWigner.Hubbard.MielkeTheorems
import LatticeSystem.Fermion.JordanWigner.Hubbard.GroundSubspaceAtFilling
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinLoweringTowerGeneral
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJGroundWeightReindex
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Tasaki §11.1.1: ground-state structure of a ferromagnetic Hubbard model (Proposition 11.2)

When a Hubbard model exhibits saturated ferromagnetism (Definition 11.1, `isSaturatedFerromagnet`),
its ground states simplify drastically: they are exactly the `(2S_max + 1)`-fold `SU(2)` multiplet
built from the lowest-energy all-up Slater state (Tasaki eq. (11.1.4)).  This file proves
**Proposition 11.2**: for the all-to-all Hubbard model `hubbardHamiltonian N t U` at filling `N + 1`
(all `N + 1` sites singly occupied), the ground eigenspace is a maximal-spin multiplet of total spin
`S_max = (N + 1)/2`.

The proof is the standard SU(2)-multiplet argument, mirroring
`generalFlatBand_connected_isMaximalSpinMultiplet` (§11.3.4) and
`tJ_halfFilling_isMaximalSpinMultiplet` (§11.5.3):

* **Lower bound** `finrank G ≥ N + 2`.  A nonzero highest-weight max-spin vector `u ∈ G`
  (extracted from the top `Ŝ³`-weight block, which is nonzero because the raising operator `Ŝ⁺`
  embeds every weight block of the max-spin subspace `G` into the next-higher one) generates, via
  the SU(2) lowering tower `highestWeight_spinMultiplet_general`, `N + 2` linearly independent
  ground states `(Ŝ⁻)^k u`, all of which stay in `G` (`Ŝ⁻`-invariance).
* **Upper bound** `finrank G ≤ N + 2`.  `G` decomposes into its `N + 2` `Ŝ³`-weight blocks
  (weights `−S_max, …, S_max`; off-grid weights vanish because `G` is pinned to the
  `(N+1)`-electron sector).  The raising operator `Ŝ⁺` injects each block into the next (every
  block of `G` is max-spin, so `Ŝ⁺v = 0` would force the weight to be `S_max`), so all blocks have
  dimension at most that of the top block, which is `≤ 1` (a top-weight state is highest-weight,
  hence determined up to scale).  Hence `finrank G ≤ (N + 2)·1`.

The maximal-spin condition (the second half of `IsMaximalSpinMultipletSubmodule`) is supplied
verbatim by the hypothesis `hferro`.

The hypotheses `hJ` (Hermitian hopping `star (t i j) = t j i`) and `hU` (real `star U = U`) are
added relative to Tasaki's bare statement: they are needed for the SU(2) invariance lemma
`fermionTotalSpinMinus_commute_hubbardHamiltonian` (the lowering operator commutes with the
Hamiltonian), and they hold for the physical Hubbard model, so the strengthening is sound.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §11.1.1, Proposition 11.2, eq. (11.1.4), pp. 377–378.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum Module
open scoped BigOperators

variable {N : ℕ} (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)

/-- **The `E₀`-eigenspace of the Hubbard model at electron filling `Ne`**: the
`hubbardHamiltonian`-eigenspace at energy `E₀`, intersected with the `Ne`-electron number sector.
No hard-core constraint is imposed, so for `E₀` the true ground energy this captures *every* ground
state (relevant for the general — possibly doubly occupied — Hubbard ground states of §11.1). -/
noncomputable def hubbardEigenspaceAt (E₀ : ℂ) (Ne : ℕ) :
    Submodule ℂ ((Fin (2 * N + 2) → Fin 2) → ℂ) :=
  Module.End.eigenspace (hubbardHamiltonian N t U).mulVecLin E₀ ⊓
    Module.End.eigenspace (fermionTotalNumber (2 * N + 1)).mulVecLin (Ne : ℂ)

/-- **The `E₀`-eigenspace at half filling `N + 1`**: the special case `Ne = N + 1` of
`hubbardEigenspaceAt`, the natural filling for saturated ferromagnetism (Proposition 11.2). -/
noncomputable def hubbardEigenspaceAtFilling (E₀ : ℂ) :
    Submodule ℂ ((Fin (2 * N + 2) → Fin 2) → ℂ) :=
  hubbardEigenspaceAt t U E₀ (N + 1)

/-! ## Membership, invariance and weight decomposition of the eigenspace -/

/-- **Unfolded membership in `hubbardEigenspaceAtFilling`.**  `v ∈ G` iff `v` is an `H`-eigenvector
at `E₀` and an `N̂`-eigenvector at `N + 1`. -/
theorem mem_hubbardEigenspaceAtFilling {E₀ : ℂ}
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ} :
    v ∈ hubbardEigenspaceAtFilling t U E₀ ↔
      (hubbardHamiltonian N t U).mulVec v = E₀ • v ∧
        (fermionTotalNumber (2 * N + 1)).mulVec v = ((N + 1 : ℕ) : ℂ) • v := by
  rw [hubbardEigenspaceAtFilling, hubbardEigenspaceAt, Submodule.mem_inf,
    Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply,
    Matrix.mulVecLin_apply]

/-- **`Ŝ³` preserves the eigenspace `G`.**  `Ŝ³` commutes with `Ĥ` (SU(2) invariance, no Hermiticity
needed) and with `N̂`, so it maps the `E₀`-energy `(N+1)`-electron eigenspace into itself. -/
theorem fermionTotalSpinZ_mulVec_mem_hubbardEigenspaceAtFilling {E₀ : ℂ}
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ} (hv : v ∈ hubbardEigenspaceAtFilling t U E₀) :
    (fermionTotalSpinZ N).mulVec v ∈ hubbardEigenspaceAtFilling t U E₀ := by
  rw [mem_hubbardEigenspaceAtFilling] at hv ⊢
  obtain ⟨hH, hN⟩ := hv
  refine ⟨?_, ?_⟩
  · have hcomm : Commute (hubbardHamiltonian N t U) (fermionTotalSpinZ N) :=
      (fermionTotalSpinZ_commute_hubbardHamiltonian N t U).symm
    rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hH, Matrix.mulVec_smul]
  · have hcomm : Commute (fermionTotalNumber (2 * N + 1)) (fermionTotalSpinZ N) :=
      (fermionTotalSpinZ_commute_fermionTotalNumber N).symm
    rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hN, Matrix.mulVec_smul]

/-- **`Ŝ⁺` preserves the eigenspace `G`.**  `Ŝ⁺` commutes with `Ĥ` (SU(2) invariance, no Hermiticity
needed) and with `N̂`, so it maps `G` into itself. -/
theorem fermionTotalSpinPlus_mulVec_mem_hubbardEigenspaceAtFilling {E₀ : ℂ}
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ} (hv : v ∈ hubbardEigenspaceAtFilling t U E₀) :
    (fermionTotalSpinPlus N).mulVec v ∈ hubbardEigenspaceAtFilling t U E₀ := by
  rw [mem_hubbardEigenspaceAtFilling] at hv ⊢
  obtain ⟨hH, hN⟩ := hv
  refine ⟨?_, ?_⟩
  · have hcomm : Commute (hubbardHamiltonian N t U) (fermionTotalSpinPlus N) :=
      (fermionTotalSpinPlus_commute_hubbardHamiltonian N t U).symm
    rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hH, Matrix.mulVec_smul]
  · have hcomm : Commute (fermionTotalNumber (2 * N + 1)) (fermionTotalSpinPlus N) :=
      (fermionTotalSpinPlus_commute_fermionTotalNumber N).symm
    rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hN, Matrix.mulVec_smul]

/-- **`Ŝ⁻` preserves the eigenspace `G`.**  `Ŝ⁻` commutes with `Ĥ` (SU(2) invariance, needing
Hermitian hopping `hJ` and real `hU`) and with `N̂`, so it maps `G` into itself. -/
theorem fermionTotalSpinMinus_mulVec_mem_hubbardEigenspaceAtFilling
    (hJ : ∀ i j, star (t i j) = t j i) (hU : star U = U) {E₀ : ℂ}
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ} (hv : v ∈ hubbardEigenspaceAtFilling t U E₀) :
    (fermionTotalSpinMinus N).mulVec v ∈ hubbardEigenspaceAtFilling t U E₀ := by
  rw [mem_hubbardEigenspaceAtFilling] at hv ⊢
  obtain ⟨hH, hN⟩ := hv
  refine ⟨?_, ?_⟩
  · have hcomm : Commute (hubbardHamiltonian N t U) (fermionTotalSpinMinus N) :=
      (fermionTotalSpinMinus_commute_hubbardHamiltonian N t U (hJ := hJ) (hU := hU)).symm
    rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hH, Matrix.mulVec_smul]
  · have hcomm : Commute (fermionTotalNumber (2 * N + 1)) (fermionTotalSpinMinus N) :=
      (fermionTotalSpinMinus_commute_fermionTotalNumber N).symm
    rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hN, Matrix.mulVec_smul]

/-- **Off-weight blocks vanish.**  If `μ` is not one of the `N + 2` half-integer weights
`a − (N+1)/2` (`a ∈ Fin (N+2)`), then `G ⊓ eigenspace Ŝ³ μ = ⊥`: a vector there is an `N̂ = N+1`
eigenstate and an `Ŝ³ = μ` eigenstate, so each supported configuration has electron number `N+1`
and `Ŝ³` count `μ = (#↑) − (N+1)/2`, placing `μ` in the weight set — contradiction unless the
vector is `0`. -/
theorem hubbardEigenspaceAtFilling_inf_eigenspace_eq_bot {E₀ : ℂ} (μ : ℂ)
    (hμ : ∀ a : Fin (N + 1 + 1), μ ≠ (((a : ℝ) - ((N + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ)) :
    hubbardEigenspaceAtFilling t U E₀ ⊓
      Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin μ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨hvG, hveig⟩ := hv
  rw [mem_hubbardEigenspaceAtFilling] at hvG
  obtain ⟨_, hN⟩ := hvG
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hveig
  funext w
  rw [Pi.zero_apply]
  by_cases hNum : (∑ j : Fin (2 * N + 2), ((w j).val : ℂ)) = ((N + 1 : ℕ) : ℂ)
  · refine mulVec_apply_eq_zero_of_spinZ_ne v μ hveig w (fun hcount => ?_)
    set aup : ℕ := ∑ i : Fin (N + 1), (w (spinfulIndex N i 0)).val with haup
    set adown : ℕ := ∑ i : Fin (N + 1), (w (spinfulIndex N i 1)).val with hadown
    have hupC : (∑ i : Fin (N + 1), ((w (spinfulIndex N i 0)).val : ℂ)) = (aup : ℂ) := by
      rw [haup, Nat.cast_sum]
    have hdownC : (∑ i : Fin (N + 1), ((w (spinfulIndex N i 1)).val : ℂ)) = (adown : ℂ) := by
      rw [hadown, Nat.cast_sum]
    have hreindex : (∑ j : Fin (2 * N + 2), ((w j).val : ℂ)) = (aup : ℂ) + (adown : ℂ) := by
      rw [sum_spinful_reindex N (fun k => ((w k).val : ℂ)),
        Finset.sum_congr rfl
          (fun i _ => Fin.sum_univ_two (fun r => ((w (spinfulIndex N i r)).val : ℂ))),
        Finset.sum_add_distrib, hupC, hdownC]
    have hsplitC : (aup : ℂ) + (adown : ℂ) = ((N + 1 : ℕ) : ℂ) := by rw [← hreindex]; exact hNum
    have hnat : aup + adown = N + 1 := by exact_mod_cast hsplitC
    have hadownC : (adown : ℂ) = ((N + 1 : ℕ) : ℂ) - (aup : ℂ) :=
      eq_sub_of_add_eq (by rw [add_comm]; exact hsplitC)
    refine hμ ⟨aup, by omega⟩ ?_
    rw [← hcount, hupC, hdownC, hadownC]
    push_cast
    ring
  · exact mulVec_apply_eq_zero_of_number_ne N v ((N + 1 : ℕ) : ℂ) hN w hNum

/-- **Finite `Ŝ³` weight decomposition.**  `G = ⨆ a : Fin (N+2), G ⊓ eigenspace Ŝ³ (a − (N+1)/2)`:
the supremum of `G` over all `Ŝ³` eigenspaces collapses to the `N + 2` occurring half-integer
weights (off-weight blocks are `⊥` by `hubbardEigenspaceAtFilling_inf_eigenspace_eq_bot`). -/
theorem hubbardEigenspaceAtFilling_eq_iSup_weight {E₀ : ℂ} :
    hubbardEigenspaceAtFilling t U E₀ =
      ⨆ a : Fin (N + 1 + 1), hubbardEigenspaceAtFilling t U E₀ ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin
          (((a : ℝ) - ((N + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) := by
  refine le_antisymm ?_ (iSup_le (fun _ => inf_le_left))
  have hinv : ∀ x ∈ hubbardEigenspaceAtFilling t U E₀,
      (fermionTotalSpinZ N).mulVecLin x ∈ hubbardEigenspaceAtFilling t U E₀ := by
    intro x hx
    rw [Matrix.mulVecLin_apply]
    exact fermionTotalSpinZ_mulVec_mem_hubbardEigenspaceAtFilling t U hx
  have htop : ⨆ μ : ℂ,
      Module.End.genEigenspace (fermionTotalSpinZ N).mulVecLin μ 1 = ⊤ := by
    have heq : ⨆ μ : ℂ, Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin μ = ⊤ := by
      rw [eq_top_iff, ← (Pi.basisFun ℂ (Fin (2 * N + 2) → Fin 2)).span_eq, Submodule.span_le]
      rintro _ ⟨c, rfl⟩
      set μc : ℂ := (((∑ i : Fin (N + 1), ((c (spinfulIndex N i 0)).val : ℂ)) -
          (∑ i : Fin (N + 1), ((c (spinfulIndex N i 1)).val : ℂ))) / 2) with hμc
      refine Submodule.mem_iSup_of_mem μc ?_
      rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
      funext w
      rw [fermionTotalSpinZ_mulVec_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hwc : w = c
      · subst hwc; rfl
      · have hzero : (Pi.basisFun ℂ (Fin (2 * N + 2) → Fin 2) c) w = 0 := by
          simp [Pi.basisFun_apply, hwc]
        rw [hzero, mul_zero, mul_zero]
    simpa only [Module.End.genEigenspace_one] using heq
  have hdecomp := Submodule.eq_iSup_inf_genEigenspace
    (p := hubbardEigenspaceAtFilling t U E₀)
    (f := (fermionTotalSpinZ N).mulVecLin) 1 hinv htop
  rw [show (⨆ μ : ℂ, hubbardEigenspaceAtFilling t U E₀ ⊓
        Module.End.genEigenspace (fermionTotalSpinZ N).mulVecLin μ 1) =
      ⨆ μ : ℂ, hubbardEigenspaceAtFilling t U E₀ ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin μ from by
      simp only [Module.End.genEigenspace_one]] at hdecomp
  refine hdecomp.le.trans (iSup_le (fun μ => ?_))
  by_cases hμ : ∃ a : Fin (N + 1 + 1), μ = (((a : ℝ) - ((N + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ)
  · obtain ⟨a, rfl⟩ := hμ
    exact le_iSup_of_le a le_rfl
  · rw [hubbardEigenspaceAtFilling_inf_eigenspace_eq_bot t U μ (not_exists.mp hμ)]
    exact bot_le

/-! ## Raising is injective on the max-spin weight blocks below the top -/

/-- **`Ŝ⁺` is injective on a max-spin weight block below the top.**  A nonzero maximal-spin vector
`v` (`(Ŝ_tot)² v = S_max(S_max + 1) v`, `S_max = (N+1)/2`) at real weight `Ŝ³ v = sz • v` with
`−S_max ≤ sz < S_max` is *not* annihilated by `Ŝ⁺`: were `Ŝ⁺v = 0`, `v` would be a highest-weight
state, forcing `S_max(S_max + 1) = sz(sz + 1)` (general highest-weight Casimir), i.e. `sz = S_max`
(ruled out by `sz < S_max`) or `sz = −(S_max + 1)` (ruled out by `sz ≥ −S_max`). -/
theorem fermionTotalSpinPlus_mulVec_ne_zero_of_maxSpin (v : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hv : v ≠ 0) (sz : ℝ)
    (hsz : (fermionTotalSpinZ N).mulVec v = ((sz : ℝ) : ℂ) • v)
    (hcas : (fermionTotalSpinSquared N).mulVec v =
      (((N + 1 : ℕ) : ℂ) / 2 * (((N + 1 : ℕ) : ℂ) / 2 + 1)) • v)
    (hlow : -(((N + 1 : ℕ) : ℝ) / 2) ≤ sz) (hhigh : sz < ((N + 1 : ℕ) : ℝ) / 2) :
    (fermionTotalSpinPlus N).mulVec v ≠ 0 := by
  intro htop
  have hcas' := fermionTotalSpinSquared_mulVec_of_isTop_general N v ((sz : ℝ) : ℂ) htop hsz
  rw [hcas] at hcas'
  -- `(S_max(S_max+1)) • v = (sz(sz+1)) • v` with `v ≠ 0` gives the scalar equation
  have hscalar : ((N + 1 : ℕ) : ℂ) / 2 * (((N + 1 : ℕ) : ℂ) / 2 + 1)
      = ((sz : ℝ) : ℂ) * (((sz : ℝ) : ℂ) + 1) := by
    by_contra hscne
    exact hv (by
      have := sub_eq_zero.mpr hcas'
      rw [← sub_smul] at this
      exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hscne))
  set S : ℝ := ((N + 1 : ℕ) : ℝ) / 2 with hS
  have hSc : ((N + 1 : ℕ) : ℂ) / 2 = (S : ℂ) := by rw [hS]; push_cast; ring
  rw [hSc] at hscalar
  have hrealeq : S * (S + 1) = sz * (sz + 1) := by
    have hc : ((S * (S + 1) : ℝ) : ℂ) = ((sz * (sz + 1) : ℝ) : ℂ) := by
      push_cast
      linear_combination hscalar
    exact_mod_cast hc
  -- `S(S+1) = sz(sz+1)` ⟹ `(S - sz)(S + sz + 1) = 0`
  have hfactor : (S - sz) * (S + sz + 1) = 0 := by nlinarith [hrealeq]
  rcases mul_eq_zero.mp hfactor with h | h
  · exact absurd (by linarith [sub_eq_zero.mp h] : S ≤ sz) (by linarith [hhigh])
  · linarith [hlow]

/-! ## Upper bound: the top block is one-dimensional and lower blocks embed into it -/

/-- **A maximally up-filled configuration is the all-up configuration.**  If a configuration `w` has
`N + 1` up-occupied sites (out of `N + 1`) and `0` down-occupied sites, then it is the all-up
configuration `k ↦ if k even then 1 else 0`: every up-orbital (even index) is occupied and every
down-orbital (odd index) is empty. -/
private theorem config_eq_allUp_of_counts (w : Fin (2 * N + 2) → Fin 2)
    (hup : (∑ i : Fin (N + 1), (w (spinfulIndex N i 0)).val) = N + 1)
    (hdown : (∑ i : Fin (N + 1), (w (spinfulIndex N i 1)).val) = 0) :
    w = (fun k : Fin (2 * N + 2) => if k.val % 2 = 0 then 1 else 0) := by
  have hupOne : ∀ i : Fin (N + 1), w (spinfulIndex N i 0) = 1 := by
    intro i
    have hle : ∀ j : Fin (N + 1), (w (spinfulIndex N j 0)).val ≤ 1 := fun j =>
      Nat.lt_succ_iff.mp (w (spinfulIndex N j 0)).isLt
    have hsum_le : (∑ j : Fin (N + 1), (w (spinfulIndex N j 0)).val)
        ≤ ∑ _j : Fin (N + 1), 1 := Finset.sum_le_sum (fun j _ => hle j)
    have hcard : (∑ _j : Fin (N + 1), 1) = N + 1 := by simp
    have heq : ∀ j : Fin (N + 1), (w (spinfulIndex N j 0)).val = 1 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨j₀, hj₀⟩ := hcon
      have hj₀lt : (w (spinfulIndex N j₀ 0)).val < 1 := lt_of_le_of_ne (hle j₀) hj₀
      have : (∑ j : Fin (N + 1), (w (spinfulIndex N j 0)).val) < ∑ _j : Fin (N + 1), 1 :=
        Finset.sum_lt_sum (fun j _ => hle j) ⟨j₀, Finset.mem_univ _, hj₀lt⟩
      rw [hcard, hup] at this
      exact lt_irrefl _ this
    exact Fin.ext (by rw [heq i, Fin.val_one])
  have hdownZero : ∀ i : Fin (N + 1), w (spinfulIndex N i 1) = 0 := by
    intro i
    have : (w (spinfulIndex N i 1)).val = 0 := by
      by_contra hcon
      have hpos : 0 < (w (spinfulIndex N i 1)).val := Nat.pos_of_ne_zero hcon
      have : 0 < (∑ j : Fin (N + 1), (w (spinfulIndex N j 1)).val) :=
        Finset.sum_pos' (fun j _ => Nat.zero_le _) ⟨i, Finset.mem_univ _, hpos⟩
      rw [hdown] at this
      exact lt_irrefl _ this
    exact Fin.ext this
  funext k
  obtain ⟨i, r, hir⟩ : ∃ (i : Fin (N + 1)) (r : Fin 2), k = spinfulIndex N i r := by
    refine ⟨⟨k.val / 2, (Nat.div_lt_iff_lt_mul (by norm_num)).mpr (by have := k.isLt; omega)⟩,
      ⟨k.val % 2, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
    apply Fin.ext; simp only [spinfulIndex]; omega
  subst hir
  by_cases hr : r = 0
  · subst hr
    rw [hupOne i, if_pos (by simp [spinfulIndex])]
  · have hr1 : r = 1 := by omega
    subst hr1
    have hodd : (spinfulIndex N i 1).val % 2 = 1 := by simp [spinfulIndex]
    rw [hdownZero i, if_neg (by omega)]

/-- **The top `Ŝ³`-weight space is one-dimensional.**  The whole `(N+1)`-electron, `Ŝ³ = S_max`
weight space (no Hamiltonian involved) is at most one-dimensional: `Ŝ³ = S_max = (N+1)/2` with
`N̂ = N+1` forces `N̂_↑ = N+1`, `N̂_↓ = 0`, i.e. every supported configuration is the all-up one.
The evaluation at the all-up configuration is therefore an injective linear map into `ℂ`. -/
theorem hubbardEigenspaceAtFilling_top_block_finrank_le_one {E₀ : ℂ} :
    finrank ℂ ↥(hubbardEigenspaceAtFilling t U E₀ ⊓
      Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin
        ((((N + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ)) ≤ 1 := by
  classical
  set B := hubbardEigenspaceAtFilling t U E₀ ⊓
    Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin
      ((((N + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) with hB
  set cAllUp : Fin (2 * N + 2) → Fin 2 := fun k => if k.val % 2 = 0 then 1 else 0 with hcAllUp
  -- evaluation at the all-up configuration
  let proj : ↥B →ₗ[ℂ] ℂ :=
    { toFun := fun v => (v : (Fin (2 * N + 2) → Fin 2) → ℂ) cAllUp
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl }
  refine LinearMap.finrank_le_finrank_of_injective (f := proj) ?_ |>.trans ?_
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv0
    apply Subtype.ext
    have hv0' : (v : (Fin (2 * N + 2) → Fin 2) → ℂ) cAllUp = 0 := by
      simpa [proj] using hv0
    have hvN : (fermionTotalNumber (2 * N + 1)).mulVec (v : (Fin (2 * N + 2) → Fin 2) → ℂ)
        = ((N + 1 : ℕ) : ℂ) • (v : (Fin (2 * N + 2) → Fin 2) → ℂ) :=
      (mem_hubbardEigenspaceAtFilling t U).mp (Submodule.mem_inf.mp v.2).1 |>.2
    have hvZ : (fermionTotalSpinZ N).mulVec (v : (Fin (2 * N + 2) → Fin 2) → ℂ)
        = ((((N + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) • (v : (Fin (2 * N + 2) → Fin 2) → ℂ) := by
      have := (Submodule.mem_inf.mp v.2).2
      rwa [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at this
    funext w
    rw [ZeroMemClass.coe_zero, Pi.zero_apply]
    by_cases hwAllUp : w = cAllUp
    · rw [hwAllUp]; exact hv0'
    -- a non-all-up configuration has either wrong electron number or wrong `Ŝ³` count
    by_cases hNum : (∑ j : Fin (2 * N + 2), ((w j).val : ℂ)) = ((N + 1 : ℕ) : ℂ)
    · refine mulVec_apply_eq_zero_of_spinZ_ne (v : (Fin (2 * N + 2) → Fin 2) → ℂ)
        ((((N + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) hvZ w (fun hcount => ?_)
      -- electron count split into up/down
      set aup : ℕ := ∑ i : Fin (N + 1), (w (spinfulIndex N i 0)).val with haup
      set adown : ℕ := ∑ i : Fin (N + 1), (w (spinfulIndex N i 1)).val with hadown
      have hupC : (∑ i : Fin (N + 1), ((w (spinfulIndex N i 0)).val : ℂ)) = (aup : ℂ) := by
        rw [haup, Nat.cast_sum]
      have hdownC : (∑ i : Fin (N + 1), ((w (spinfulIndex N i 1)).val : ℂ)) = (adown : ℂ) := by
        rw [hadown, Nat.cast_sum]
      have hreindex : (∑ j : Fin (2 * N + 2), ((w j).val : ℂ)) = (aup : ℂ) + (adown : ℂ) := by
        rw [sum_spinful_reindex N (fun k => ((w k).val : ℂ)),
          Finset.sum_congr rfl
            (fun i _ => Fin.sum_univ_two (fun r => ((w (spinfulIndex N i r)).val : ℂ))),
          Finset.sum_add_distrib, hupC, hdownC]
      have hsumC : (aup : ℂ) + (adown : ℂ) = ((N + 1 : ℕ) : ℂ) := by rw [← hreindex]; exact hNum
      have hsumN : aup + adown = N + 1 := by exact_mod_cast hsumC
      -- the `Ŝ³` count being `(N+1)/2` forces `aup - adown = N+1`
      have hcountC : ((aup : ℂ) - (adown : ℂ)) / 2 = ((((N + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) := by
        rw [← hupC, ← hdownC]; exact hcount
      have hdiffN : aup = N + 1 ∧ adown = 0 := by
        have hhalf : (((((N + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) = ((N + 1 : ℕ) : ℂ) / 2 := by
          push_cast; ring
        have hdiffC : (aup : ℂ) - (adown : ℂ) = ((N + 1 : ℕ) : ℂ) := by
          have hc2 : (aup : ℂ) - (adown : ℂ) = 2 * (((aup : ℂ) - (adown : ℂ)) / 2) := by ring
          rw [hc2, hcountC, hhalf]; ring
        have : (aup : ℤ) - (adown : ℤ) = (N + 1 : ℤ) := by exact_mod_cast hdiffC
        omega
      -- so `w` must be the all-up configuration: every site is up-occupied, down-empty
      refine absurd ?_ hwAllUp
      rw [hcAllUp]
      exact config_eq_allUp_of_counts w (haup ▸ hdiffN.1) (hadown ▸ hdiffN.2)
    · exact mulVec_apply_eq_zero_of_number_ne N (v : (Fin (2 * N + 2) → Fin 2) → ℂ)
        ((N + 1 : ℕ) : ℂ) hvN w hNum
  · rw [Module.finrank_self]

/-- **A weight block below the top embeds into the next-higher one.**  For `a : Fin (N+2)` with
`a.val < N + 1`, the raising operator `Ŝ⁺` maps the weight-`a` block of `G` injectively into the
weight-`(a+1)` block: it preserves `G` (SU(2) invariance), raises the `Ŝ³` weight by one, and is
injective there because every block vector is max-spin (`hferro`) at a weight below `S_max`.  Hence
`finrank (block a) ≤ finrank (block (a+1))`. -/
theorem hubbardEigenspaceAtFilling_block_finrank_le_succ {E₀ : ℂ}
    (hferro : ∀ v ∈ hubbardEigenspaceAtFilling t U E₀,
      (fermionTotalSpinSquared N).mulVec v
        = (((N + 1 : ℕ) : ℂ) / 2 * (((N + 1 : ℕ) : ℂ) / 2 + 1)) • v)
    (a : ℕ) (ha : a < N + 1) :
    finrank ℂ ↥(hubbardEigenspaceAtFilling t U E₀ ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin
          ((((a : ℝ) - ((N + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ)) ≤
      finrank ℂ ↥(hubbardEigenspaceAtFilling t U E₀ ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin
          ((((a + 1 : ℝ) - ((N + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ)) := by
  set sz : ℝ := (a : ℝ) - ((N + 1 : ℕ) : ℝ) / 2 with hsz
  set Glo := hubbardEigenspaceAtFilling t U E₀ ⊓
    Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin
      (((((a : ℝ) - ((N + 1 : ℕ) : ℝ) / 2 : ℝ))) : ℂ) with hGlo
  set Ghi := hubbardEigenspaceAtFilling t U E₀ ⊓
    Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin
      ((((a + 1 : ℝ) - ((N + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) with hGhi
  have hszeq : (((((a : ℝ) - ((N + 1 : ℕ) : ℝ) / 2 : ℝ))) : ℂ) = ((sz : ℝ) : ℂ) := by rw [hsz]
  have hweight : ∀ w : ↥Glo, (fermionTotalSpinZ N).mulVec w.val = ((sz : ℝ) : ℂ) • w.val := by
    intro w
    have := Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp w.property).2
    rw [Matrix.mulVecLin_apply, hszeq] at this
    exact this
  have hmem : ∀ w : ↥Glo, ((fermionTotalSpinPlus N).mulVecLin.comp Glo.subtype) w ∈ Ghi := by
    intro w
    have hwG := (Submodule.mem_inf.mp w.property).1
    change (fermionTotalSpinPlus N).mulVec w.val ∈ Ghi
    rw [hGhi, Submodule.mem_inf, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    refine ⟨fermionTotalSpinPlus_mulVec_mem_hubbardEigenspaceAtFilling t U hwG, ?_⟩
    rw [show ((((a + 1 : ℝ) - ((N + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ)
        = (((sz + 1 : ℝ)) : ℂ) from by rw [hsz]; push_cast; ring]
    exact fermionTotalSpinZ_mulVec_fermionTotalSpinPlus_mulVec N sz (hweight w)
  refine LinearMap.finrank_le_finrank_of_injective
    (f := LinearMap.codRestrict Ghi ((fermionTotalSpinPlus N).mulVecLin.comp Glo.subtype) hmem) ?_
  intro w w' hww'
  have hval : (fermionTotalSpinPlus N).mulVec w.val = (fermionTotalSpinPlus N).mulVec w'.val := by
    have := congrArg Subtype.val hww'
    simpa [LinearMap.codRestrict, LinearMap.comp_apply, Matrix.mulVecLin_apply] using this
  have hdiff : (fermionTotalSpinPlus N).mulVec (w.val - w'.val) = 0 := by
    rw [Matrix.mulVec_sub, hval, sub_self]
  have hdsz : (fermionTotalSpinZ N).mulVec (w.val - w'.val)
      = ((sz : ℝ) : ℂ) • (w.val - w'.val) := by
    rw [Matrix.mulVec_sub, hweight w, hweight w', smul_sub]
  by_contra hne
  have hd0 : w.val - w'.val ≠ 0 := fun h => hne (Subtype.ext (sub_eq_zero.mp h))
  -- the difference lies in `G` and is max-spin (`hferro`)
  have hdG : w.val - w'.val ∈ hubbardEigenspaceAtFilling t U E₀ :=
    Submodule.sub_mem _ (Submodule.mem_inf.mp w.property).1 (Submodule.mem_inf.mp w'.property).1
  have hcas := hferro _ hdG
  refine fermionTotalSpinPlus_mulVec_ne_zero_of_maxSpin (w.val - w'.val) hd0 sz hdsz hcas
    ?_ ?_ hdiff
  · rw [hsz]; have : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a; linarith
  · rw [hsz]; have : (a : ℝ) < ((N + 1 : ℕ) : ℝ) := by exact_mod_cast ha
    have hpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
    linarith

/-- **Every weight block of `G` has dimension `≤ 1`.**  By downward induction from the top block
(`hubbardEigenspaceAtFilling_top_block_finrank_le_one`) using the single-step embedding
(`hubbardEigenspaceAtFilling_block_finrank_le_succ`): the weight-`a` block embeds into the
weight-`(a+1)` block, and the top block (`a = N+1`) is `≤ 1`. -/
theorem hubbardEigenspaceAtFilling_block_finrank_le_one {E₀ : ℂ}
    (hferro : ∀ v ∈ hubbardEigenspaceAtFilling t U E₀,
      (fermionTotalSpinSquared N).mulVec v
        = (((N + 1 : ℕ) : ℂ) / 2 * (((N + 1 : ℕ) : ℂ) / 2 + 1)) • v)
    (a : Fin (N + 1 + 1)) :
    finrank ℂ ↥(hubbardEigenspaceAtFilling t U E₀ ⊓
      Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin
        ((((a : ℝ) - ((N + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ)) ≤ 1 := by
  -- prove `finrank (block (N+1-j)) ≤ 1` for all `j`, then specialise
  suffices h : ∀ j : ℕ, j ≤ N + 1 →
      finrank ℂ ↥(hubbardEigenspaceAtFilling t U E₀ ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin
          (((((N + 1 - j : ℕ) : ℝ)) - ((N + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ)) ≤ 1 by
    have hja : (a : ℕ) ≤ N + 1 := Nat.lt_succ_iff.mp a.isLt
    have := h (N + 1 - (a : ℕ)) (Nat.sub_le _ _)
    rwa [show ((N + 1 - (N + 1 - (a : ℕ)) : ℕ) : ℝ) = ((a : ℕ) : ℝ) from by
      rw [Nat.sub_sub_self hja]] at this
  intro j
  induction j with
  | zero =>
    intro _
    have heq : (((N + 1 - 0 : ℕ) : ℝ) - ((N + 1 : ℕ) : ℝ) / 2)
        = (((N + 1 : ℕ) : ℝ) / 2 : ℝ) := by push_cast; ring
    rw [heq]
    exact hubbardEigenspaceAtFilling_top_block_finrank_le_one t U
  | succ j ih =>
    intro hj
    have hjle : j ≤ N + 1 := Nat.le_of_succ_le hj
    have hstep := hubbardEigenspaceAtFilling_block_finrank_le_succ t U hferro (N + 1 - (j + 1))
      (by omega)
    have hnat : N + 1 - (j + 1) + 1 = N + 1 - j := by omega
    have hidx : ((N + 1 - (j + 1) : ℕ) : ℝ) + 1 = ((N + 1 - j : ℕ) : ℝ) := by
      rw [← hnat]; push_cast; ring
    rw [hidx] at hstep
    exact le_trans hstep (ih hjle)

/-! ## Upper and lower bounds on the dimension -/

/-- **Upper bound `finrank G ≤ N + 2`.**  `G` is the internal direct sum of its `N + 2` `Ŝ³`-weight
blocks (`hubbardEigenspaceAtFilling_eq_iSup_weight` + independence of the `Ŝ³` eigenspaces), each of
dimension `≤ 1` (`hubbardEigenspaceAtFilling_block_finrank_le_one`), so
`finrank G = ∑ finrank (block) ≤ (N + 2)·1`. -/
theorem hubbardEigenspaceAtFilling_finrank_le {E₀ : ℂ}
    (hferro : ∀ v ∈ hubbardEigenspaceAtFilling t U E₀,
      (fermionTotalSpinSquared N).mulVec v
        = (((N + 1 : ℕ) : ℂ) / 2 * (((N + 1 : ℕ) : ℂ) / 2 + 1)) • v) :
    finrank ℂ ↥(hubbardEigenspaceAtFilling t U E₀) ≤ N + 2 := by
  classical
  set T := (fermionTotalSpinZ N).mulVecLin with hT
  set wt : Fin (N + 1 + 1) → ℂ := fun a => ((((a : ℝ) - ((N + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) with hwt
  set B : Fin (N + 1 + 1) → Submodule ℂ ((Fin (2 * N + 2) → Fin 2) → ℂ) :=
    fun a => hubbardEigenspaceAtFilling t U E₀ ⊓ Module.End.eigenspace T (wt a) with hB
  have hsup : ⨆ a, B a = hubbardEigenspaceAtFilling t U E₀ :=
    (hubbardEigenspaceAtFilling_eq_iSup_weight t U).symm
  have hwt_inj : Function.Injective wt := by
    intro a a' h
    simp only [hwt] at h
    have hr : ((a : ℝ) - ((N + 1 : ℕ) : ℝ) / 2) = ((a' : ℝ) - ((N + 1 : ℕ) : ℝ) / 2) := by
      exact_mod_cast h
    exact Fin.ext (by exact_mod_cast (by linarith : (a : ℝ) = (a' : ℝ)))
  have hindep : iSupIndep B :=
    ((Module.End.eigenspaces_iSupIndep T).comp hwt_inj).mono (fun a => inf_le_right)
  have hinj : Function.Injective (DirectSum.coeLinearMap B) := hindep.dfinsupp_lsum_injective
  have hrange : LinearMap.range (DirectSum.coeLinearMap B) = hubbardEigenspaceAtFilling t U E₀ := by
    rw [DirectSum.range_coeLinearMap]; exact hsup
  have hfr : finrank ℂ ↥(hubbardEigenspaceAtFilling t U E₀) = ∑ a, finrank ℂ ↥(B a) := by
    rw [← hrange, ← (LinearEquiv.ofInjective (DirectSum.coeLinearMap B) hinj).finrank_eq,
      Module.finrank_directSum]
  rw [hfr]
  calc ∑ a, finrank ℂ ↥(B a)
      ≤ ∑ _a : Fin (N + 1 + 1), 1 :=
        Finset.sum_le_sum (fun a _ =>
          hubbardEigenspaceAtFilling_block_finrank_le_one t U hferro a)
    _ = N + 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

/-- **Lower bound `finrank G ≥ N + 2`.**  Extract a nonzero highest-weight max-spin vector `u ∈ G`
at the top weight `S_max`: the top block of `G` is nonzero (every nonzero block embeds, via `Ŝ⁺`,
into
the next-higher one, so the top block dominates the nonzero block guaranteed by `G ≠ ⊥`), and a
top-weight vector is highest-weight (`Ŝ⁺u` lies in the vanishing weight-`S_max+1` block).  The SU(2)
lowering tower `highestWeight_spinMultiplet_general` then yields `N + 2` linearly independent ground
states `(Ŝ⁻)^k u`, all in `G` (`Ŝ⁻`-invariance), so `finrank G ≥ N + 2`. -/
theorem hubbardEigenspaceAtFilling_finrank_ge
    (hJ : ∀ i j, star (t i j) = t j i) (hU : star U = U) {E₀ : ℂ}
    (hne : hubbardEigenspaceAtFilling t U E₀ ≠ ⊥)
    (hferro : ∀ v ∈ hubbardEigenspaceAtFilling t U E₀,
      (fermionTotalSpinSquared N).mulVec v
        = (((N + 1 : ℕ) : ℂ) / 2 * (((N + 1 : ℕ) : ℂ) / 2 + 1)) • v) :
    N + 2 ≤ finrank ℂ ↥(hubbardEigenspaceAtFilling t U E₀) := by
  classical
  set G := hubbardEigenspaceAtFilling t U E₀ with hG
  -- the top block is nonzero: some block is nonzero (`G ≠ ⊥`), and every block embeds into the top
  have htopBlockNe : (G ⊓ Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin
      ((((N + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ)) ≠ ⊥ := by
    intro htopbot
    -- if the top block is `⊥` then all blocks are `⊥` (the embedding chain), so `G = ⊥`
    have hallbot : ∀ a : Fin (N + 1 + 1), (G ⊓ Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin
        ((((a : ℝ) - ((N + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ)) = ⊥ := by
      intro a
      rw [← Submodule.finrank_eq_zero]
      have htop0 : finrank ℂ ↥(G ⊓ Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin
          ((((N + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ)) = 0 := by
        rw [Submodule.finrank_eq_zero]; exact htopbot
      -- `finrank (block a) ≤ finrank (top block) = 0` by chaining the single-step embeddings
      have hchain : ∀ j : ℕ, j ≤ N + 1 →
          finrank ℂ ↥(G ⊓ Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin
            (((((N + 1 - j : ℕ) : ℝ)) - ((N + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ)) ≤
          finrank ℂ ↥(G ⊓ Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin
            ((((N + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ)) := by
        intro j
        induction j with
        | zero => intro _; rw [show (((N + 1 - 0 : ℕ) : ℝ) - ((N + 1 : ℕ) : ℝ) / 2)
            = (((N + 1 : ℕ) : ℝ) / 2 : ℝ) from by push_cast; ring]
        | succ j ih =>
          intro hj
          have hjle : j ≤ N + 1 := Nat.le_of_succ_le hj
          have hstep := hubbardEigenspaceAtFilling_block_finrank_le_succ t U hferro
            (N + 1 - (j + 1)) (by omega)
          have hnat : N + 1 - (j + 1) + 1 = N + 1 - j := by omega
          have hc : ((N + 1 - (j + 1) : ℕ) : ℝ) + 1 = ((N + 1 - j : ℕ) : ℝ) := by
            rw [← hnat]; push_cast; ring
          rw [hc] at hstep
          exact le_trans hstep (ih hjle)
      have hja : (a : ℕ) ≤ N + 1 := Nat.lt_succ_iff.mp a.isLt
      have := hchain (N + 1 - (a : ℕ)) (Nat.sub_le _ _)
      rw [show ((N + 1 - (N + 1 - (a : ℕ)) : ℕ) : ℝ) = ((a : ℕ) : ℝ) from by
        rw [Nat.sub_sub_self hja], htop0, Nat.le_zero] at this
      exact this
    refine hne ?_
    rw [hG, hubbardEigenspaceAtFilling_eq_iSup_weight t U]
    refine le_antisymm (iSup_le (fun a => ?_)) bot_le
    rw [← hG]
    exact (hallbot a).le
  -- extract a nonzero top-weight vector `u ∈ G`
  obtain ⟨u, hutop, hune⟩ := Submodule.exists_mem_ne_zero_of_ne_bot htopBlockNe
  have huG : u ∈ G := (Submodule.mem_inf.mp hutop).1
  have huZ : (fermionTotalSpinZ N).mulVec u = ((((N + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) • u := by
    have := (Submodule.mem_inf.mp hutop).2
    rwa [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at this
  -- `u` is a highest-weight vector: `Ŝ⁺u` is in the vanishing weight-`S_max+1` block
  have huHW : (fermionTotalSpinPlus N).mulVec u = 0 := by
    have hmem : (fermionTotalSpinPlus N).mulVec u ∈ G ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin
          (((((N + 1 : ℕ) : ℝ) / 2 + 1 : ℝ)) : ℂ) := by
      refine Submodule.mem_inf.mpr ⟨fermionTotalSpinPlus_mulVec_mem_hubbardEigenspaceAtFilling
        t U huG, ?_⟩
      rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
      exact fermionTotalSpinZ_mulVec_fermionTotalSpinPlus_mulVec N (((N + 1 : ℕ) : ℝ) / 2) huZ
    have hbot : G ⊓ Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin
        (((((N + 1 : ℕ) : ℝ) / 2 + 1 : ℝ)) : ℂ) = ⊥ := by
      rw [hG]
      refine hubbardEigenspaceAtFilling_inf_eigenspace_eq_bot t U _ (fun a hcon => ?_)
      have hreal : (((N + 1 : ℕ) : ℝ) / 2 + 1) = ((a : ℝ) - ((N + 1 : ℕ) : ℝ) / 2) := by
        exact_mod_cast hcon
      have hale : (a : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
        have : (a : ℕ) ≤ N + 1 := Nat.lt_succ_iff.mp a.isLt
        exact_mod_cast this
      have hpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
      linarith
    rw [hbot, Submodule.mem_bot] at hmem
    exact hmem
  -- `Ŝ³ u = (L/2) u` with `L = N+1`
  have huszL : (fermionTotalSpinZ N).mulVec u = (((N + 1 : ℕ) : ℂ) / 2) • u := by
    rw [huZ]; congr 1; push_cast; ring
  obtain ⟨hLI, _⟩ := highestWeight_spinMultiplet_general N (N + 1) u hune huHW huszL
  -- every tower member stays in `G` (`Ŝ⁻`-invariance, as a power)
  have hmem : ∀ k : Fin (N + 1 + 1),
      ((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec u ∈ G := by
    intro k
    induction (k : ℕ) with
    | zero => rw [pow_zero, Matrix.one_mulVec]; exact huG
    | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      exact fermionTotalSpinMinus_mulVec_mem_hubbardEigenspaceAtFilling t U hJ hU ih
  have hGLI : LinearIndependent ℂ (fun k : Fin (N + 1 + 1) =>
      (⟨((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec u, hmem k⟩ : G)) :=
    LinearIndependent.of_comp G.subtype hLI
  have := hGLI.fintype_card_le_finrank
  simpa using this

/-! ## Tasaki Proposition 11.2 -/

/-- **Tasaki Proposition 11.2 (ground states of a ferromagnetic Hubbard model).**  Let `E₀` be a
genuine half-filling ground energy of the all-to-all Hubbard model `hubbardHamiltonian N t U`: its
`(N + 1)`-electron eigenspace is nonzero (`hne`) and `E₀` is minimal among all energies with a
nonzero `(N + 1)`-electron eigenspace (`hmin`, using the real part as the physical eigenvalue order,
`hubbardHamiltonian` being Hermitian).  If, moreover, the model is ferromagnetic at this ground
energy — every ground state is an `(Ŝ_tot)²`-eigenvector at `S_max(S_max + 1)`, `S_max = (N + 1)/2`
(`hferro`, Definition 11.1 specialised to the ground eigenspace) — then the ground eigenspace is the
`(N + 2)`-fold maximal-spin multiplet (Tasaki eq. (11.1.4)): its dimension is exactly
`N + 2 = 2 S_max + 1`.

The hypotheses `hJ` (Hermitian hopping `star (t i j) = t j i`) and `hU` (real `star U = U`) are
added relative to Tasaki's bare statement; they are needed for the SU(2)-invariance of the lowering
operator (`fermionTotalSpinMinus_commute_hubbardHamiltonian`) and hold for the physical Hubbard
model, so the strengthening is sound.  The minimality hypotheses `hmin` is recorded as part of the
physical setup (it pins `E₀` to a genuine ground energy) but is not needed for the conclusion, which
follows from `hne` and `hferro` alone.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §11.1.1, Proposition 11.2, eq. (11.1.4), pp. 377–378. -/
theorem hubbard_proposition_11_2 (hJ : ∀ i j, star (t i j) = t j i) (hU : star U = U) (E₀ : ℂ)
    (hne : hubbardEigenspaceAtFilling t U E₀ ≠ ⊥)
    (hmin : ∀ E : ℂ, hubbardEigenspaceAtFilling t U E ≠ ⊥ → E₀.re ≤ E.re)
    (hferro : ∀ v ∈ hubbardEigenspaceAtFilling t U E₀,
      (fermionTotalSpinSquared N).mulVec v
        = (((N + 1 : ℕ) : ℂ) / 2 * (((N + 1 : ℕ) : ℂ) / 2 + 1)) • v) :
    IsMaximalSpinMultipletSubmodule N (hubbardEigenspaceAtFilling t U E₀) (N + 1) := by
  -- `hmin` pins `E₀` to a genuine ground energy (physical setup); the dimension/spin conclusion
  -- below uses only `hne` and `hferro`.
  have _hmin := hmin
  refine ⟨le_antisymm (hubbardEigenspaceAtFilling_finrank_le t U hferro)
    (hubbardEigenspaceAtFilling_finrank_ge t U hJ hU hne hferro), ?_⟩
  intro v hv
  exact hferro v hv

end LatticeSystem.Fermion
