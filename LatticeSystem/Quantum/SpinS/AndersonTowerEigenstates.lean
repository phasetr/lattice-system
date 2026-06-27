/-
Tasaki §4.2.2 Corollary 4.7 (the tower of low-lying energy eigenstates).

Building on Theorem 4.6 (`tower_lowLying_energy_bound`, proved in `AndersonTowerTheorem46`): for each
nonzero magnetization `M` the lowest energy eigenstate in the `Ŝ_tot^{(3)}` sector `μ₀+M` is low-lying.
This file develops the magnetization-sector tools for the torus tower; the first piece is the
magnetization eigenvalue shift of the tower trial state.
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerTheorem46
import LatticeSystem.Quantum.SpinS.MagSectorEmbedding
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorMarshallCore
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueEigenvector

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

variable {d L N : ℕ}

/-- **Magnetization shift of an order-density power.**  If `Ŝ_tot^{(3)} v = λ v` then
`Ŝ_tot^{(3)} ((ô^b)^m v) = (λ + m·ε_b) (ô^b)^m v` (`ε_true = +1`, `ε_false = −1`): each order
density `ô^b` shifts the total magnetization by `ε_b`, so `m` of them shift by `m·ε_b`.  This
places the tower trial state `(ô^±)^M Φ` in the magnetization sector `μ₀ ± M`. -/
theorem totalSpinSOp3_mulVec_orderDensityPow_eigenvec [NeZero L] (b : Bool) (m : ℕ)
    {v : (HypercubicTorus d L → Fin (N + 1)) → ℂ} {lam : ℂ}
    (hv : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec v = lam • v) :
    (totalSpinSOp3 (HypercubicTorus d L) N).mulVec
        ((staggeredOrderDensityOpS d L N b ^ m).mulVec v)
      = (lam + (m : ℂ) * (if b then (1 : ℂ) else (-1 : ℂ)))
          • (staggeredOrderDensityOpS d L N b ^ m).mulVec v := by
  induction m with
  | zero => simpa using hv
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec,
      totalSpinSOp3_mulVec_orderDensity_eigenvec d L N b ih, Matrix.mulVec_mulVec, ← pow_succ']
    congr 1
    push_cast
    ring

/-- **The tower state lies in the magnetization sector `μ₀ + M`.**  If `Ŝ_tot^{(3)} Φ = μ₀ Φ` then
`Ŝ_tot^{(3)} (towerState M Φ) = (μ₀ + M) (towerState M Φ)`: the raising/lowering tower shifts the
total magnetization by `M` (the scalar `V^{|M|}` in `towerState` does not change the eigenvalue). -/
theorem totalSpinSOp3_mulVec_towerState_eigenvec [NeZero L] (M : ℤ)
    {Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ} {μ₀ : ℂ}
    (hΦ : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = μ₀ • Φ) :
    (totalSpinSOp3 (HypercubicTorus d L) N).mulVec
        (towerState (torusParitySublattice d L) N M Φ)
      = (μ₀ + (M : ℂ)) • towerState (torusParitySublattice d L) N M Φ := by
  rcases lt_or_ge M 0 with hM | hM
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, M = -(m : ℤ) := ⟨M.natAbs, by omega⟩
    have hmpos : 1 ≤ m := by omega
    rw [towerState_neg_eq_smul d L N m hmpos, Matrix.mulVec_smul,
      totalSpinSOp3_mulVec_orderDensityPow_eigenvec false m hΦ, smul_smul, smul_smul]
    congr 1
    rw [if_neg (by decide)]
    push_cast
    ring
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, M = (m : ℤ) := ⟨M.natAbs, by omega⟩
    rw [towerState_pos_eq_smul, Matrix.mulVec_smul,
      totalSpinSOp3_mulVec_orderDensityPow_eigenvec true m hΦ, smul_smul, smul_smul]
    congr 1
    rw [if_pos rfl]
    push_cast
    ring

/-- **Magnetization-sector minimum energy eigenvector.**  For real coupling `J` and a nonempty
magnetization sector `K`, the Heisenberg Hamiltonian has a nonzero eigenstate `ψ` whose energy is
the minimum eigenvalue of the sector-restricted (Hermitian) matrix and which lies in the
`Ŝ_tot^{(3)}` eigenspace of eigenvalue `|V|·N/2 − K`.  Built by lifting the restricted matrix's min
eigenvector (`exists_nonzero_eigenvector_hermitianMinEigenvalue`) via
`heisenbergHamiltonianS_mulVec_magSectorEmbedding`. -/
theorem heisenbergHamiltonianS_magSector_min_eigenvector {V : Type*} [Fintype V] [DecidableEq V]
    {J : V → V → ℂ} (hJ : ∀ x y, star (J x y) = J x y) (N K : ℕ)
    [Nonempty (magConfigS V N K)] :
    ∃ ψ : (V → Fin (N + 1)) → ℂ, ψ ≠ 0 ∧
      (heisenbergHamiltonianS J N).mulVec ψ
        = ((hermitianMinEigenvalue
            (heisenbergHamiltonianSMatrixOnMagSector_isHermitian N K hJ) : ℝ) : ℂ) • ψ ∧
      (totalSpinSOp3 V N).mulVec ψ
        = (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (K : ℂ)) • ψ := by
  obtain ⟨v, hv0, hveig⟩ :=
    exists_nonzero_eigenvector_hermitianMinEigenvalue
      (heisenbergHamiltonianSMatrixOnMagSector_isHermitian N K hJ)
  refine ⟨magSectorEmbedding v, ?_, heisenbergHamiltonianS_mulVec_magSectorEmbedding J v hveig, ?_⟩
  · intro hψ0
    obtain ⟨τ, hτ⟩ := Function.ne_iff.mp hv0
    apply hτ
    have hval : magSectorEmbedding v τ.1 = v τ := magSectorEmbedding_apply_of_mem v τ.2
    rw [Pi.zero_apply, ← hval, hψ0, Pi.zero_apply]
  · rw [← mem_magSubspaceS_iff]
    exact magSectorEmbedding_mem_magSubspaceS v

/-- **Norm is preserved by the sector embedding.**  `⟨emb w, emb w⟩ = ⟨w, w⟩`: the zero-extension
outside the sector contributes nothing, and the sector sum reindexes to the `magConfigS` subtype. -/
theorem magSectorEmbedding_dotProduct_self {V : Type*} [Fintype V] [DecidableEq V] {M : ℕ}
    (w : magConfigS V N M → ℂ) :
    star (magSectorEmbedding w) ⬝ᵥ magSectorEmbedding w = star w ⬝ᵥ w := by
  simp only [dotProduct]
  rw [show (∑ ρ : V → Fin (N + 1),
        star (magSectorEmbedding w) ρ * magSectorEmbedding w ρ)
      = ∑ ρ ∈ Finset.univ.filter (fun ρ : V → Fin (N + 1) => magSumS ρ = M),
          star (magSectorEmbedding w) ρ * magSectorEmbedding w ρ from
    (Finset.sum_filter_of_ne (fun ρ _ hne => by
      by_contra h
      apply hne
      rw [magSectorEmbedding_apply_of_not_mem w h, mul_zero])).symm]
  rw [Finset.sum_subtype (Finset.univ.filter (fun ρ : V → Fin (N + 1) => magSumS ρ = M))
    (p := fun ρ => magSumS ρ = M) (fun ρ => by simp [Finset.mem_filter])
    (fun ρ => star (magSectorEmbedding w) ρ * magSectorEmbedding w ρ)]
  refine Finset.sum_congr rfl (fun ρ' _ => ?_)
  rw [Pi.star_apply, Pi.star_apply, magSectorEmbedding_apply_subtype]

/-- **Energy quadratic form is preserved by the sector embedding.**
`⟨emb w, Ĥ (emb w)⟩ = ⟨w, R w⟩` where `R` is the sector-restricted Hamiltonian: off-sector terms
vanish and the sector sum reindexes, matching `Ĥ (emb w) τ.1 = R w τ`
(`heisenbergHamiltonianS_mulVec_magSectorEmbedding_apply_subtype`). -/
theorem magSectorEmbedding_dotProduct_heisenberg {V : Type*} [Fintype V] [DecidableEq V]
    (J : V → V → ℂ) {M : ℕ} (w : magConfigS V N M → ℂ) :
    star (magSectorEmbedding w) ⬝ᵥ (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding w)
      = star w ⬝ᵥ (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec w := by
  simp only [dotProduct]
  rw [show (∑ ρ : V → Fin (N + 1), star (magSectorEmbedding w) ρ
        * (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding w) ρ)
      = ∑ ρ ∈ Finset.univ.filter (fun ρ : V → Fin (N + 1) => magSumS ρ = M),
          star (magSectorEmbedding w) ρ
            * (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding w) ρ from
    (Finset.sum_filter_of_ne (fun ρ _ hne => by
      by_contra h
      apply hne
      rw [Pi.star_apply, magSectorEmbedding_apply_of_not_mem w h, star_zero, zero_mul])).symm]
  rw [Finset.sum_subtype (Finset.univ.filter (fun ρ : V → Fin (N + 1) => magSumS ρ = M))
    (p := fun ρ => magSumS ρ = M) (fun ρ => by simp [Finset.mem_filter])
    (fun ρ => star (magSectorEmbedding w) ρ
      * (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding w) ρ)]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Pi.star_apply, Pi.star_apply, magSectorEmbedding_apply_subtype,
    heisenbergHamiltonianS_mulVec_magSectorEmbedding_apply_subtype]

/-- **Sector minimum energy bounds the trial Rayleigh quotient.**  For a vector `ψ` in the
magnetization-`K` sector (eigenspace eigenvalue `|V|·N/2 − K`), the sector-restricted minimum energy
times `‖ψ‖²` is `≤ ⟨ψ, Ĥ ψ⟩`: restrict `ψ`, apply the variational lower bound to the restricted
matrix, and transport along the two embedding bridges. -/
theorem tower_sectorMin_mul_le {V : Type*} [Fintype V] [DecidableEq V]
    {J : V → V → ℂ} (hJ : ∀ x y, star (J x y) = J x y) {K : ℕ}
    [Nonempty (magConfigS V N K)] {ψ : (V → Fin (N + 1)) → ℂ}
    (hmem : ψ ∈ magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (K : ℂ))) :
    hermitianMinEigenvalue (heisenbergHamiltonianSMatrixOnMagSector_isHermitian N K hJ)
        * (star ψ ⬝ᵥ ψ).re
      ≤ (star ψ ⬝ᵥ (heisenbergHamiltonianS J N).mulVec ψ).re := by
  have hemb : magSectorEmbedding (magSectorRestriction (M := K) ψ) = ψ :=
    magSectorEmbedding_magSectorRestriction_of_mem_magSubspaceS hmem
  have hvar := hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec
    (heisenbergHamiltonianSMatrixOnMagSector_isHermitian N K hJ) (magSectorRestriction (M := K) ψ)
  rw [show rayleighOnVec (heisenbergHamiltonianSMatrixOnMagSector J N K)
        (magSectorRestriction (M := K) ψ)
      = (star (magSectorRestriction (M := K) ψ)
          ⬝ᵥ (heisenbergHamiltonianSMatrixOnMagSector J N K).mulVec
            (magSectorRestriction (M := K) ψ)).re from rfl,
    ← magSectorEmbedding_dotProduct_self (magSectorRestriction (M := K) ψ),
    ← magSectorEmbedding_dotProduct_heisenberg J (magSectorRestriction (M := K) ψ), hemb] at hvar
  exact hvar

/-- A nonzero coordinate of a `Ŝ_tot^{(3)}` eigenvector pins down its magnetization eigenvalue:
if `v ∈ magSubspaceS V N c` and `v σ ≠ 0` then `magEigenvalueS σ = c`. -/
theorem magEigenvalueS_of_mem_magSubspaceS {V : Type*} [Fintype V] [DecidableEq V] {c : ℂ}
    {v : (V → Fin (N + 1)) → ℂ} (hv : v ∈ magSubspaceS V N c)
    {σ : V → Fin (N + 1)} (hσ : v σ ≠ 0) : magEigenvalueS σ = c := by
  rw [mem_magSubspaceS_iff] at hv
  have hcg := congrFun hv σ
  rw [totalSpinSOp3_mulVec_apply_eq_magEigenvalueS_mul] at hcg
  exact mul_right_cancel₀ hσ hcg

/-- **Tasaki Corollary 4.7 (the tower of low-lying energy eigenstates), PROVED.**  Discharges the
former `tower_lowLying_eigenstates` axiom: for a total-spin-singlet ground state `Φ` with long-range
order and each `M ≠ 0` with `|M| ≤ C₁ L^{d/2}` and nonzero tower state, there is a genuine Ĥ-energy
eigenstate `Ψ` in the `Ŝ_tot^{(3)}` sector `M` with `E₀ < E_M ≤ E₀ + C₂ M²/L^d` (the rigorous
Anderson tower).  `Ψ` is the minimum-energy eigenstate of `Ĥ` restricted to the sector of the tower
state
(`heisenbergHamiltonianS_magSector_min_eigenvector`); its energy is `≤ Rayleigh(towerState)`
(`tower_sectorMin_mul_le`) `≤ E₀ + C₂M²/L^d` (Theorem 4.6); the strict gap uses the
ground-sector-exclusion premise (every ground eigenstate is a singlet). -/
theorem tower_lowLying_eigenstates (d N : ℕ) (hd : 1 ≤ d) (q₀ : ℝ) (hq₀ : 0 < q₀) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (L : ℕ) [NeZero L], 2 ≤ L → Even L →
        ∀ (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ : ℂ) (M : ℤ),
          (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Φ = E₀ • Φ →
          (∀ E : ℂ, ∀ Ψ : (HypercubicTorus d L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
            (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) →
          Φ ≠ 0 →
          (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0 →
          (totalSpinSOp1 (HypercubicTorus d L) N).mulVec Φ = 0 →
          (∀ E : ℂ, ∀ Ψ : (HypercubicTorus d L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
            (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Ψ = E • Ψ →
            E.re = E₀.re → (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Ψ = 0) →
          q₀ ≤ (star Φ ⬝ᵥ ((staggeredOrderOpS (torusParitySublattice d L) N *
              staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ)).re /
              ((star Φ ⬝ᵥ Φ).re * ((L : ℝ) ^ d) ^ 2) →
          M ≠ 0 →
          (M.natAbs : ℝ) ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 2) →
          towerState (torusParitySublattice d L) N M Φ ≠ 0 →
          ∃ (Ψ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E_M : ℂ),
            Ψ ≠ 0 ∧
            (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Ψ = E_M • Ψ ∧
            E₀.re < E_M.re ∧ E_M.re ≤ E₀.re + C₂ * (M : ℝ) ^ 2 / (L : ℝ) ^ d ∧
            (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Ψ = (M : ℂ) • Ψ := by
  obtain ⟨C₁, C₂, hC1, hC2, hbound⟩ := tower_lowLying_energy_bound d N hd q₀ hq₀
  refine ⟨C₁, C₂, hC1, hC2, ?_⟩
  intro L _ hL hLeven Φ E₀ M hev hmin hΦ hsing3 hsing1 hexcl hlro hM0 hMbound htower
  -- towerState lies in the Ŝ³-sector M (μ₀ = 0)
  have htowerMem : towerState (torusParitySublattice d L) N M Φ
      ∈ magSubspaceS (HypercubicTorus d L) N (M : ℂ) := by
    rw [mem_magSubspaceS_iff]
    have hsh := totalSpinSOp3_mulVec_towerState_eigenvec M (μ₀ := 0)
      (by rw [zero_smul]; exact hsing3)
    rwa [zero_add] at hsh
  -- a support point σ₀ of towerState fixes the sector label K
  obtain ⟨σ₀, hσ₀⟩ := Function.ne_iff.mp htower
  have hσ₀' : towerState (torusParitySublattice d L) N M Φ σ₀ ≠ 0 := by simpa using hσ₀
  set K := magSumS σ₀ with hK
  have hKM : magEigenvalueS σ₀ = (M : ℂ) := magEigenvalueS_of_mem_magSubspaceS htowerMem hσ₀'
  have hcardeq : ((Fintype.card (HypercubicTorus d L) : ℂ) * (N : ℂ) / 2) - (K : ℂ) = (M : ℂ) := by
    rw [hK, ← magEigenvalueS_def σ₀]; exact hKM
  haveI : Nonempty (magConfigS (HypercubicTorus d L) N K) := ⟨⟨σ₀, rfl⟩⟩
  -- the sector minimum-energy eigenvector
  obtain ⟨Ψ, hΨ0, hΨeig, hΨsec⟩ :=
    heisenbergHamiltonianS_magSector_min_eigenvector (torusNNCoupling_real d L) N K
  rw [hcardeq] at hΨsec
  set μmin := hermitianMinEigenvalue
    (heisenbergHamiltonianSMatrixOnMagSector_isHermitian N K (torusNNCoupling_real d L)) with hμ
  refine ⟨Ψ, (μmin : ℂ), hΨ0, hΨeig, ?_, ?_, hΨsec⟩
  · -- strict gap E₀.re < μmin
    have hge : E₀.re ≤ μmin := by simpa using hmin (μmin : ℂ) Ψ hΨ0 hΨeig
    refine lt_of_le_of_ne hge (fun heq => ?_)
    have hz := hexcl (μmin : ℂ) Ψ hΨ0 hΨeig (by rw [Complex.ofReal_re]; exact heq.symm)
    rw [hΨsec] at hz
    exact (smul_ne_zero (by exact_mod_cast hM0) hΨ0) hz
  · -- E_M = μmin ≤ E₀.re + C₂M²/V
    have hdenpos : 0 < (star (towerState (torusParitySublattice d L) N M Φ) ⬝ᵥ
        towerState (torusParitySublattice d L) N M Φ).re :=
      (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr htower)).1
    have hvar := tower_sectorMin_mul_le (torusNNCoupling_real d L) (K := K)
      (ψ := towerState (torusParitySublattice d L) N M Φ) (by rw [hcardeq]; exact htowerMem)
    rw [← hμ] at hvar
    have hray := hbound L hL hLeven Φ E₀ M hev hmin hΦ hsing3 hsing1 hlro hMbound htower
    rw [div_le_iff₀ hdenpos] at hray
    have hμle : μmin ≤ (star (towerState (torusParitySublattice d L) N M Φ) ⬝ᵥ
        (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec
          (towerState (torusParitySublattice d L) N M Φ)).re
        / (star (towerState (torusParitySublattice d L) N M Φ) ⬝ᵥ
          towerState (torusParitySublattice d L) N M Φ).re := by
      rw [le_div_iff₀ hdenpos]; linarith [hvar]
    simp only [Complex.ofReal_re]
    calc μmin ≤ _ := hμle
      _ ≤ E₀.re + C₂ * (M : ℝ) ^ 2 / (L : ℝ) ^ d := by
          rw [div_le_iff₀ hdenpos]; linarith [hray]

end LatticeSystem.Quantum
