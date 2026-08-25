import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetismCenteredSector
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveHalfFillingDischarge

/-!
# §10.2.3 (Theorem 10.8): the transported sector ground state carries Theorem 10.4's Casimir value

The Shiba transport of §10.2.3 (`LiebShenQiuShibaTransport.lean`) delivers, from a spin-singlet
ground state of the symmetric **attractive** Hubbard model on the `N̂ = Ne` electron-number sector,
a unique ground state `ψ` of the symmetric **repulsive** model on the spin-`z` sector
`Ŝ³ = (Ne − (N+1))/2`, sitting at half filling.  Theorem 10.8's superconducting bound is evaluated
on the attractive ground state `φ = Ûᴴψ`; the Shiba transport turns it into a spin correlation on
`ψ`, so it needs `ψ`'s total spin, which is what Theorem 10.4 fixes for the half-filling ground
multiplet: `Ŝ² = S₀(S₀+1)` at `S₀ = L/2`, `L := sublatticeImbalance A`.

The bridge is the tower exponent `k = |A| − Ne/2`: the lowering tower of a highest-weight
half-filling ground vector reaches the weight `L/2 − k`, which is exactly the transported sector's
parameter `(Ne − (N+1))/2`.  Feeding that match to the two-sided pinch
`liebRepulsive_sectorGroundEnergy_eq_groundEnergy` identifies the sector ground energy with the
half-filling ground energy, which places `ψ` itself inside the half-filling ground submodule, where
Theorem 10.4's Casimir clause applies.

* `liebShenQiu_towerExponent_weight_eq` — the weight arithmetic `L/2 − (|A| − Ne/2)
  = (Ne − (N+1))/2` under `2|B| ≤ Ne ≤ 2|A|` and `Even Ne`;
* `liebShenQiu_sectorGround_mem_halfFillingGround` — the transported sector ground state lies in the
  `(N+1)`-electron ground submodule;
* `liebShenQiu_casimir_eq` — hence `Ŝ² ψ = S₀(S₀+1) ψ`.

Theorem 10.5 (`theorem_10_5_shen_qiu_tian_transverse_sign`) is **not** used here: only Theorem
10.4's ground-multiplet data (via `liebRepulsive_symmetric_halfFilling`) and the highest-weight
tower enter directly at this layer (Theorem 10.4's own proof pulls in
`repulsiveSpinZSector_ground_unique`, Theorem 10.2, and Theorem 10.3), so the transverse-correlation
layer of §10.2.2 stays out of the Theorem 10.8 route.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed.,
Springer 2020, §10.2.2 (Theorem 10.4, p. 350) and §10.2.3 (Theorem 10.8, p. 359,
eqs. (10.2.21)/(10.2.22)).
-/

namespace LatticeSystem.Fermion

open Matrix Module LatticeSystem.Quantum LatticeSystem.Math

/-! ## The tower exponent of a half-filling electron-number sector -/

/-- **The tower exponent `k = |A| − Ne/2` reaches the transported sector.**  For an even electron
number `Ne` with `2|B| ≤ Ne ≤ 2|A|`, the lowering-tower weight `L/2 − k` at `k = |A| − Ne/2`
(`L := ||A| − |B||`) equals the spin-`z` parameter `(Ne − (N+1))/2` of the sector the Shiba
transport lands in.  The two-sided bound makes both `|B| ≤ Ne/2 ≤ |A|` and hence `L = |A| − |B|`,
after which the identity is the linear arithmetic of `|A| + |B| = N + 1`. -/
theorem liebShenQiu_towerExponent_weight_eq (N : ℕ) (A : Finset (Fin (N + 1))) (Ne : ℕ)
    (hb : 2 * (bipartitionComplement A).card ≤ Ne) (ha : Ne ≤ 2 * A.card) (hNe : Even Ne) :
    (sublatticeImbalance A : ℂ) / 2 - ((A.card - Ne / 2 : ℕ) : ℂ)
      = ((Ne : ℂ) - ((N : ℂ) + 1)) / 2 := by
  have hcard := bipartitionComplement_card_add N A
  have hpar : Ne % 2 = 0 := Nat.even_iff.mp hNe
  have hLnat := sublatticeImbalance_add_bipartitionComplement_card A (by omega)
  have hknat : (A.card - Ne / 2) + Ne / 2 = A.card := by omega
  have hNenat : 2 * (Ne / 2) = Ne := by omega
  have hL : (sublatticeImbalance A : ℂ) + ((bipartitionComplement A).card : ℂ) = (A.card : ℂ) := by
    exact_mod_cast hLnat
  have hk : ((A.card - Ne / 2 : ℕ) : ℂ) + ((Ne / 2 : ℕ) : ℂ) = (A.card : ℂ) := by
    exact_mod_cast hknat
  have hAB : (A.card : ℂ) + ((bipartitionComplement A).card : ℂ) = (N : ℂ) + 1 := by
    exact_mod_cast hcard
  have hhalf : 2 * ((Ne / 2 : ℕ) : ℂ) = (Ne : ℂ) := by exact_mod_cast hNenat
  linear_combination hL / 2 - hk - hAB / 2 + hhalf / 2

/-! ## The transported sector ground state sits in the half-filling ground submodule -/

/-- **The transported sector ground state is a half-filling ground state.**  If `ψ` is the unique
ground state of the symmetric repulsive Hamiltonian on the spin-`z` sector `Ŝ³ = m` reached by the
tower exponent `k ≤ L` (`hkm : L/2 − k = m`) and carries the half-filling number eigenvalue `hψN`,
then `ψ` lies in the `(N+1)`-electron `E₀`-ground submodule: the two-sided pinch
`liebRepulsive_sectorGroundEnergy_eq_groundEnergy` identifies the sector ground energy `E` with
`E₀.re`, and `hE₀` turns `ψ`'s `E`-eigen-equation into an `E₀`-eigen-equation. -/
theorem liebShenQiu_sectorGround_mem_halfFillingGround (N : ℕ) (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT : ∀ i j, T i j = T j i)
    (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hmin : ∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1) ≠ ⊥ → E₀.re ≤ E.re)
    (hE₀ : ((E₀.re : ℝ) : ℂ) = E₀)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ} (hw0 : w ≠ 0)
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w)
    (k : ℕ) (hk : k ≤ sublatticeImbalance A)
    {m : ℂ} (hkm : (sublatticeImbalance A : ℂ) / 2 - (k : ℂ) = m)
    {E : ℝ} {ψ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)}
    (hGS : IsUniqueGroundStateOn (spinZSectorEuclidean N m)
      (symmetricRepulsiveHubbardHamiltonian N T U) E ψ)
    (hψN : Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1)) ψ = ((N : ℂ) + 1) • ψ) :
    ψ.ofLp ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) := by
  have hE := liebRepulsive_sectorGroundEnergy_eq_groundEnergy N A T hT U E₀ hmin hE₀ hcas hw0 hwG
    hz k hk hkm hGS hψN
  have hEE₀ : ((E : ℝ) : ℂ) = E₀ := by rw [hE]; exact hE₀
  obtain ⟨-, -, hψeig, -, -⟩ := hGS
  obtain ⟨u, rfl⟩ : ∃ u : (Fin (2 * N + 2) → Fin 2) → ℂ, ψ = WithLp.toLp 2 u :=
    ⟨WithLp.ofLp ψ, rfl⟩
  rw [← mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul] at hψeig hψN
  rw [WithLp.ofLp_toLp, hubbardGroundSubmoduleAtElectronNumber, Submodule.mem_inf,
    Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply,
    Matrix.mulVecLin_apply]
  refine ⟨?_, ?_⟩
  · rw [← hEE₀]
    exact hψeig
  · push_cast
    exact hψN

/-! ## Theorem 10.4's Casimir value on the transported sector ground state -/

/-- **The transported sector ground state has total spin `S₀ = L/2`.**  Under the model hypotheses
of Theorem 10.4 (symmetric bipartite connected hopping, on-site repulsion), the unique ground state
`ψ` of the symmetric repulsive Hamiltonian on the spin-`z` sector `Ŝ³ = m` reached by a tower
exponent `k ≤ L`, at half filling, satisfies `Ŝ²_tot ψ = S₀(S₀+1) ψ`.

Theorem 10.4 (`liebRepulsive_symmetric_halfFilling`) supplies the half-filling ground energy `E₀`
together with the nonvanishing, minimality and Casimir clauses; its ground submodule contains a
highest-weight vector (`liebRepulsive_ground_exists_topWeight`) whose tower drives the pinch, and
`liebShenQiu_sectorGround_mem_halfFillingGround` places `ψ` in that submodule, where the Casimir
clause applies verbatim. -/
theorem liebShenQiu_casimir_eq (N : ℕ) (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT : ∀ i j, T i j = T j i)
    (hbip : HoppingRespectsBipartition A T)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU : ∀ x, 0 < U x)
    (k : ℕ) (hk : k ≤ sublatticeImbalance A)
    {m : ℂ} (hkm : (sublatticeImbalance A : ℂ) / 2 - (k : ℂ) = m)
    {E : ℝ} {ψ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)}
    (hGS : IsUniqueGroundStateOn (spinZSectorEuclidean N m)
      (symmetricRepulsiveHubbardHamiltonian N T U) E ψ)
    (hψN : Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1)) ψ = ((N : ℂ) + 1) • ψ) :
    (fermionTotalSpinSquared N).mulVec ψ.ofLp = liebRepulsiveSpinCasimir A • ψ.ofLp := by
  obtain ⟨E₀, hne, hmin, hcas, -⟩ := liebRepulsive_symmetric_halfFilling N T hT hbip hT_conn U hU
  obtain ⟨w, hw0, hwG, -, hz⟩ := liebRepulsive_ground_exists_topWeight N A T U E₀ hcas hne
  exact hcas _ (liebShenQiu_sectorGround_mem_halfFillingGround N A T hT U E₀ hmin
    (liebRepulsive_groundEnergy_eq_ofReal N T hT U E₀ hne) hcas hw0 hwG hz k hk hkm hGS hψN)

end LatticeSystem.Fermion
