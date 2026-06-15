import LatticeSystem.Fermion.JordanWigner.Hubbard.TJHalfFillingGroundEnergy
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJExchangeBondHalf
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Tasaki 11.5.3: a half-filling ground state is annihilated by every bond (Theorem 11.26 PR3i-2)

A ground state `v` of the half-filling t-J model is annihilated by `tJExchange` (the ground energy
is `0` and `Ĥ_tJ = J·tJExchange` on the filling sector), and `tJExchange = Σ_{⟨x,y⟩} bond_xy` is a
sum
of positive-semidefinite singlet projectors `bond_xy = ½ Δ_xy† Δ_xy`.  Hence `⟨v, tJExchange v⟩ = 0`
forces `⟨v, bond_xy v⟩ = 0` on every bond, so `Δ_xy v = 0` and `bond_xy v = 0`:

* `tJ_ground_tJExchange_mulVec_eq_zero` — `tJExchange v = 0` for `v` in the half-filling ground
  subspace;
* `tJ_ground_bond_mulVec_eq_zero` — `(¼ n̂_x n̂_y − Ŝ_x·Ŝ_y) v = 0` for every adjacent bond `⟨x,y⟩`.

With the half-spin-swap action (`tJExchangeBond_mulVec_tJConfigOf_full`, PR3i-1) this gives the
spin-swap invariance of the ground amplitudes on every bond — the input to the degeneracy bound.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.3, Theorem 11.26 (pp. 445–447).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph
open scoped BigOperators ComplexOrder

variable {N : ℕ}

/-- The single Heisenberg bond operator `¼ n̂_x n̂_y − Ŝ_x·Ŝ_y` (the `tJExchange` summand). -/
private noncomputable def hBond (N : ℕ) (x y : Fin (N + 1)) : Matrix (Fin (2 * N + 2) → Fin 2)
    (Fin (2 * N + 2) → Fin 2) ℂ :=
  (1 / 4 : ℂ) • (fermionSiteNumber N x * fermionSiteNumber N y) - fermionSpinDot N x y

/-- `tJExchange` is the adjacency-weighted sum of the bond operators (definitional). -/
private theorem tJExchange_eq_sum_hBond (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj] :
    tJExchange N G = ∑ x, ∑ y, (if G.Adj x y then hBond N x y else 0) := rfl

/-- A half-filling ground state is annihilated by `tJExchange`: on the filling sector
`Ĥ_tJ = J·tJExchange` and the ground energy is `0`, so `J·tJExchange v = 0` with `J > 0`. -/
theorem tJ_ground_tJExchange_mulVec_eq_zero (τ J : ℝ) (hJ : 0 < J)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hv : v ∈ groundSubmoduleAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) (N + 1)) :
    (tJExchange N (cycleGraph (N + 1))).mulVec v = 0 := by
  obtain ⟨⟨hH, hNmem⟩, hhc⟩ := hv
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply,
    tJ_groundEnergyAtFilling_eq_zero τ J hJ, Complex.ofReal_zero, zero_smul] at hH
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hNmem
  have hkey := tJHamiltonian_mulVec_eq_smul_tJExchange_of_filling (cycleGraph (N + 1)) τ J hhc hNmem
  rw [hH] at hkey
  have hJne : (J : ℂ) ≠ 0 := by exact_mod_cast hJ.ne'
  exact (smul_eq_zero.mp hkey.symm).resolve_left hJne

/-- The bond inner product `⟨v, bond_xy v⟩` is nonnegative (the bond is positive-semidefinite). -/
private theorem hBond_dotProduct_nonneg (x y : Fin (N + 1)) (hxy : x ≠ y)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    0 ≤ star v ⬝ᵥ (hBond N x y).mulVec v :=
  (tJExchangeBond_posSemidef x y hxy).dotProduct_mulVec_nonneg v

/-- **Every bond annihilates a half-filling ground state.**  For an adjacent pair `⟨x,y⟩`,
`(¼ n̂_x n̂_y − Ŝ_x·Ŝ_y) v = 0` — the bond inner product is a nonnegative summand of
`⟨v, tJExchange v⟩ = 0`, hence `0`, so `Δ_xy v = 0` and the bond annihilates `v`. -/
theorem tJ_ground_bond_mulVec_eq_zero (τ J : ℝ) (hJ : 0 < J)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hv : v ∈ groundSubmoduleAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) (N + 1))
    (x y : Fin (N + 1)) (hadj : (cycleGraph (N + 1)).Adj x y) :
    ((1 / 4 : ℂ) • (fermionSiteNumber N x * fermionSiteNumber N y) -
      fermionSpinDot N x y).mulVec v = 0 := by
  classical
  set G := cycleGraph (N + 1) with hG
  -- the bond inner product as the `(x,y)` summand of `⟨v, tJExchange v⟩`
  have hsum : star v ⬝ᵥ (tJExchange N G).mulVec v
      = ∑ a, ∑ b, (if G.Adj a b then star v ⬝ᵥ (hBond N a b).mulVec v else 0) := by
    rw [tJExchange_eq_sum_hBond, Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : G.Adj a b
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, Matrix.zero_mulVec, dotProduct_zero]
  have htot : star v ⬝ᵥ (tJExchange N G).mulVec v = 0 := by
    rw [tJ_ground_tJExchange_mulVec_eq_zero τ J hJ hv, dotProduct_zero]
  -- each summand is nonnegative
  have hinner_nonneg : ∀ b ∈ Finset.univ, (0 : ℂ) ≤
      (if G.Adj x b then star v ⬝ᵥ (hBond N x b).mulVec v else 0) := by
    intro b _
    by_cases h : G.Adj x b
    · rw [if_pos h]; exact hBond_dotProduct_nonneg x b h.ne v
    · rw [if_neg h]
  have hrow_nonneg : ∀ a ∈ Finset.univ, (0 : ℂ) ≤
      ∑ b, (if G.Adj a b then star v ⬝ᵥ (hBond N a b).mulVec v else 0) := by
    intro a _
    refine Finset.sum_nonneg fun b _ => ?_
    by_cases h : G.Adj a b
    · rw [if_pos h]; exact hBond_dotProduct_nonneg a b h.ne v
    · rw [if_neg h]
  -- `0 ≤ ⟨v, bond_xy v⟩ ≤ (x-row inner sum) ≤ total = 0`
  have hxyle : star v ⬝ᵥ (hBond N x y).mulVec v ≤
      ∑ b, (if G.Adj x b then star v ⬝ᵥ (hBond N x b).mulVec v else 0) := by
    have := Finset.single_le_sum hinner_nonneg (Finset.mem_univ y)
    rwa [if_pos hadj] at this
  have hrowle : (∑ b, (if G.Adj x b then star v ⬝ᵥ (hBond N x b).mulVec v else 0)) ≤
      ∑ a, ∑ b, (if G.Adj a b then star v ⬝ᵥ (hBond N a b).mulVec v else 0) :=
    Finset.single_le_sum hrow_nonneg (Finset.mem_univ x)
  have hbondzero : star v ⬝ᵥ (hBond N x y).mulVec v = 0 := by
    refine le_antisymm ?_ (hBond_dotProduct_nonneg x y hadj.ne v)
    calc star v ⬝ᵥ (hBond N x y).mulVec v ≤ _ := hxyle
      _ ≤ _ := hrowle
      _ = 0 := by rw [← hsum]; exact htot
  -- `⟨v, bond_xy v⟩ = ½ ‖Δ_xy v‖²`, so `Δ_xy v = 0`, hence `bond_xy v = 0`
  have hΔ : (tJSingletAnnihilation N x y).mulVec v = 0 := by
    have hb : hBond N x y = (1 / 2 : ℂ) •
        ((tJSingletAnnihilation N x y)ᴴ * tJSingletAnnihilation N x y) :=
      tJExchangeBond_eq_half_singletNormSq x y hadj.ne
    rw [hb, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hbondzero
    have hhalf : (1 / 2 : ℂ) ≠ 0 := by norm_num
    have h0 : star v ⬝ᵥ ((tJSingletAnnihilation N x y)ᴴ *
        tJSingletAnnihilation N x y).mulVec v = 0 :=
      (mul_eq_zero.mp hbondzero).resolve_left hhalf
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.star_mulVec] at h0
    exact dotProduct_star_self_eq_zero.mp h0
  rw [tJExchangeBond_eq_half_singletNormSq x y hadj.ne, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, hΔ, Matrix.mulVec_zero, smul_zero]

end LatticeSystem.Fermion
