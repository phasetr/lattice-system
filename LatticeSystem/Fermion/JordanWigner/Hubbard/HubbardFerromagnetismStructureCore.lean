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


end LatticeSystem.Fermion
