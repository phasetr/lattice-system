import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveCasimirPinning
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveSU2Invariance
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveFullSectorUnique
import LatticeSystem.Fermion.JordanWigner.Hubbard.BipartiteSpectrum
import LatticeSystem.Math.AngularMomentum.Multiplet
import LatticeSystem.Math.InvariantSubmoduleEigenvector
import LatticeSystem.Math.CommutingHermitianEigenvector
import LatticeSystem.Math.MatrixAnalysis.PiEuclideanEigenBridge

/-!
# SU(2) weight transport and the sector energy ladder (Tasaki §10.2.2, PR-14a)

Nineteenth installment of the Theorem 10.4 discharge arc (issue #5320). This file assembles the
first half (PR-14a) of the arc's final assembly step: for every admissible `Ŝ³` sector of the
physical symmetric repulsive Hamiltonian, the sector's unique ground state is a
`liebRepulsiveSpinCasimir A`-eigenvector of `Ŝ²`, all admissible sectors share the same ground
energy `E₀`, and `E₀` is minimal over the whole `(N+1)`-electron sector. The complementary weight
confinement + `finrank` count (PR-14b) and the axiom discharge itself (PR-15) are **not** in this
file's scope.

## Route

Reuses `ham_su2_multiplet_companion` (`Math/AngularMomentum/Multiplet.lean:56`) rather than the
highest-weight tower `highestWeight_spinMultiplet_general`, per the arc's main-agent decision
(the companion lemma manufactures the top state internally and carries the `Ĥ`/`N̂` eigenvalues
along, so no separate highest-weight certificate is needed). See the design round's "Route note"
for the full argument against the tower route.

## Contents (this file, PR-14a scope)

* `liebRepulsive_su2_weight_transport` — specializes `ham_su2_multiplet_companion` to the physical
  symmetric repulsive Hamiltonian: from a joint `(Ĥ, N̂, Ŝ³, Ŝ²)`-eigenvector of spin `J`, produces
  a nonzero companion at every weight `J − k` (`k ≤ 2J`) with the same `Ĥ` and `N̂` eigenvalues
  (steps 2/3 of the design round's closing argument).
* `liebRepulsive_admissibleSector_groundState_casimir_eigenvector` — per-admissible-sector step
  (step 1): the unique ground state on `numberSpinZSectorEuclidean` at an admissible `Ŝ³` value is
  an `Ŝ²`-eigenvector at `liebRepulsiveSpinCasimir A`, via `exists_unique_casimir_sector_strict_min`
  + `casimirSelector_strict_min_unique` + PR-13b's `s = 0` selector pinning.
* `liebRepulsive_multipletCompanion_capstone` — the PR-14a capstone: a single ground energy `E₀`
  such that every admissible `Ŝ³` sector has a unique ground state at `E₀` carrying the Casimir
  eigenvalue `liebRepulsiveSpinCasimir A`, and `E₀` is minimal over the whole `(N+1)`-electron
  sector (conjunct (ii) of `theorem_10_4_lieb_repulsive_half_filling`,
  `LiebRepulsive.lean:134`, restricted to the symmetric disjunct).

The weight of the sector indexed by `nUp` is `m = (2 nUp − (N+1))/2` (`liebHalfFillingSpinZVal`),
and admissibility of `nUp` is, in up-count form, `|A'ᶜ| ≤ nUp ≤ |A'|` for the oriented sublattice
`A' = liebOrientedSublattice A` (`liebRepulsive_mem_tasaki23GroundStateSectors_iff`). The two
extreme admissible sectors carry the weights `±S₀`, `S₀ = sublatticeImbalance A / 2`, and the
transport index reaching the sector `nUp` from the top sector is `k = |A'| − nUp`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.2 (Theorem 10.4), pp. 350–353.
-/

namespace LatticeSystem.Fermion

open Matrix Module Module.End LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators ComplexOrder

variable {N : ℕ}

/-! ## Step 2/3: SU(2) weight transport for the physical Hamiltonian -/

/-- **SU(2) weight transport, specialized to the physical symmetric repulsive Hamiltonian.** From
a nonzero joint eigenvector `Φ` of `(Ĥ, N̂, Ŝ³, Ŝ²)` at weight `m₀` and Casimir `J(J+1)`, for
every `k ≤ 2J` there is a nonzero companion `Ψ` at weight `J − k` with the same `Ĥ`- and
`N̂`-eigenvalues (energy `E` and electron number `Ne`). Built from `ham_su2_multiplet_companion`
(`Multiplet.lean:56`), applied twice via its transport clause: once to `A = symmetricRepulsive...`,
once to `A = fermionTotalNumber`, using `symmetricRepulsiveHubbardHamiltonian_mul_tJTotalSpinOne`/
`Two` (`LiebRepulsiveSU2Invariance.lean`) and `fermionTotalNumber_mul_tJTotalSpinOne`/`Two`
(`LiebAttractiveFullSectorUnique.lean`, generic in the Hamiltonian). The companion's weight is
measured from the top of the multiplet, exactly as in the generic lemma; the seed weight `m₀`
enters only through the quantization `J − m₀ ∈ ℤ≥0` used internally. -/
theorem liebRepulsive_su2_weight_transport
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT_symm : ∀ x y, T x y = T y x)
    (U : Fin (N + 1) → ℝ)
    {Φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)} {Jr m₀ : ℝ} {E : ℂ} {Ne : ℂ}
    (hΦ : Φ ≠ 0) (hJ : 0 ≤ Jr)
    (hsq : Matrix.toEuclideanLin (fermionTotalSpinSquared N) Φ
      = ((Jr * (Jr + 1) : ℝ) : ℂ) • Φ)
    (h3 : Matrix.toEuclideanLin (fermionTotalSpinZ N) Φ = (m₀ : ℂ) • Φ)
    (hH : Matrix.toEuclideanLin (symmetricRepulsiveHubbardHamiltonian N T U) Φ = E • Φ)
    (hNe : Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1)) Φ = Ne • Φ) :
    ∀ k : ℕ, (k : ℝ) ≤ 2 * Jr →
      ∃ Ψ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2), Ψ ≠ 0 ∧
        Matrix.toEuclideanLin (fermionTotalSpinSquared N) Ψ = ((Jr * (Jr + 1) : ℝ) : ℂ) • Ψ ∧
        Matrix.toEuclideanLin (fermionTotalSpinZ N) Ψ = ((Jr - k : ℝ) : ℂ) • Ψ ∧
        Matrix.toEuclideanLin (symmetricRepulsiveHubbardHamiltonian N T U) Ψ = E • Ψ ∧
        Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1)) Ψ = Ne • Ψ := by
  obtain ⟨Φ', rfl⟩ : ∃ w : (Fin (2 * N + 2) → Fin 2) → ℂ, Φ = WithLp.toLp 2 w :=
    ⟨WithLp.ofLp Φ, rfl⟩
  intro k hk
  have hΦ' : Φ' ≠ 0 := by
    rw [ne_eq, ← WithLp.toLp_eq_zero (p := 2)]
    exact hΦ
  have hsq' : (tJTotalSpinOne N * tJTotalSpinOne N + tJTotalSpinTwo N * tJTotalSpinTwo N
        + fermionTotalSpinZ N * fermionTotalSpinZ N).mulVec Φ'
      = ((Jr * (Jr + 1) : ℝ) : ℂ) • Φ' := by
    rw [← fermionTotalSpinSquared_eq_cartesianSqSum]
    exact (mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul _ _ _).mpr hsq
  have h3' : (fermionTotalSpinZ N).mulVec Φ' = (m₀ : ℂ) • Φ' :=
    (mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul _ _ _).mpr h3
  have hH' : (symmetricRepulsiveHubbardHamiltonian N T U).mulVec Φ' = E • Φ' :=
    (mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul _ _ _).mpr hH
  have hNe' : (fermionTotalNumber (2 * N + 1)).mulVec Φ' = Ne • Φ' :=
    (mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul _ _ _).mpr hNe
  obtain ⟨Ψ, hΨne, hΨsq, hΨ3, hclause⟩ :=
    ham_su2_multiplet_companion (tJTotalSpinOne N) (tJTotalSpinTwo N) (fermionTotalSpinZ N)
      (tJTotalSpinOne_isHermitian N) (tJTotalSpinTwo_isHermitian N) (tJTotalSpin_su2_12 N)
      (tJTotalSpin_su2_23 N) (tJTotalSpin_su2_31 N) hΦ' hJ hsq' h3' k hk
  refine ⟨WithLp.toLp 2 Ψ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ne_eq, WithLp.toLp_eq_zero]
    exact hΨne
  · rw [fermionTotalSpinSquared_eq_cartesianSqSum]
    exact (mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul _ _ _).mp hΨsq
  · exact (mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul _ _ _).mp hΨ3
  · exact (mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul _ _ _).mp
      (hclause _ E (symmetricRepulsiveHubbardHamiltonian_mul_tJTotalSpinOne N T U hT_symm)
        (symmetricRepulsiveHubbardHamiltonian_mul_tJTotalSpinTwo N T U hT_symm) hH')
  · exact (mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul _ _ _).mp
      (hclause _ Ne (fermionTotalNumber_mul_tJTotalSpinOne N)
        (fermionTotalNumber_mul_tJTotalSpinTwo N) hNe')

/-- **Weight transport into a named `Ŝ³` sector.** Packaging of
`liebRepulsive_su2_weight_transport` for the two call sites of the closing argument: given the
index `k` reaching the sector `q` from the top of the multiplet (`J − k = (2q − (N+1))/2`), the
companion lands in `numberSpinZSectorEuclidean N (N+1) (liebHalfFillingSpinZVal N q)` and keeps the
energy eigenvalue `E`. -/
private theorem liebRepulsive_transport_to_sector (N q k : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT_symm : ∀ x y, T x y = T y x)
    (U : Fin (N + 1) → ℝ)
    {Φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)} {Jr m₀ : ℝ} {E : ℂ}
    (hΦ : Φ ≠ 0) (hJ : 0 ≤ Jr)
    (hsq : Matrix.toEuclideanLin (fermionTotalSpinSquared N) Φ
      = ((Jr * (Jr + 1) : ℝ) : ℂ) • Φ)
    (h3 : Matrix.toEuclideanLin (fermionTotalSpinZ N) Φ = ((m₀ : ℝ) : ℂ) • Φ)
    (hH : Matrix.toEuclideanLin (symmetricRepulsiveHubbardHamiltonian N T U) Φ = E • Φ)
    (hNum : Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1)) Φ = ((N : ℂ) + 1) • Φ)
    (hk : (k : ℝ) ≤ 2 * Jr) (hq : Jr - (k : ℝ) = (2 * (q : ℝ) - ((N : ℝ) + 1)) / 2) :
    ∃ Ψ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2), Ψ ≠ 0 ∧
      Ψ ∈ numberSpinZSectorEuclidean N ((N : ℂ) + 1) (liebHalfFillingSpinZVal N q) ∧
      Matrix.toEuclideanLin (symmetricRepulsiveHubbardHamiltonian N T U) Ψ = E • Ψ := by
  obtain ⟨Ψ, hΨne, -, hΨ3, hΨH, hΨN⟩ :=
    liebRepulsive_su2_weight_transport T hT_symm U hΦ hJ hsq h3 hH hNum k hk
  have hval : ((Jr - (k : ℝ) : ℝ) : ℂ) = liebHalfFillingSpinZVal N q := by
    rw [hq, liebHalfFillingSpinZVal]
    push_cast
    ring
  refine ⟨Ψ, hΨne, ?_, hΨH⟩
  rw [numberSpinZSectorEuclidean, Submodule.mem_inf, spinZSectorEuclidean]
  exact ⟨Module.End.mem_eigenspace_iff.mpr hΨN,
    Module.End.mem_eigenspace_iff.mpr (by rw [hΨ3, hval])⟩

/-! ## Step 1: per-admissible-sector ground state is a Casimir eigenvector -/

/-- **Per-admissible-sector step (step 1 of the design round's closing argument).** For an
admissible `Ŝ³` value (indexed by `nUp`, `1 ≤ |A|`, `1 ≤ |B|`), the unique ground state `φ` of the
physical symmetric repulsive Hamiltonian on `numberSpinZSectorEuclidean N (N+1) m₀` is an
`Ŝ²`-eigenvector at `liebRepulsiveSpinCasimir A`. Combines
`repulsiveSpinZSector_ground_unique_on_numberSpinZSector`
(`LiebRepulsiveSectorBridgeFinal.lean:148`) with `exists_unique_casimir_sector_strict_min`
(`LiebRepulsiveCasimirSector.lean:116`), `casimirSelector_strict_min_unique`
(`LiebRepulsiveCasimirPinning.lean:63`), and the `s = 0` selector pinning
`symmetricHomotopy_casimirSelector_zero_eq_liebRepulsiveSpinCasimir`
(`LiebRepulsiveCasimirPinning.lean:339`), whose homotopy coupling is irrelevant here and is
instantiated at `λ = 1`. -/
theorem liebRepulsive_admissibleSector_groundState_casimir_eigenvector
    (N Ne : ℕ) (hNe_even : Even Ne) (hNe_pos : 0 < Ne) (hNe_lt : Ne < 2 * (N + 1))
    (nUp : ℕ) (hnUp : nUp ≤ N + 1) (hNe2 : Ne = 2 * nUp)
    {A : Finset (Fin (N + 1))} (hA : 1 ≤ A.card) (hB : 1 ≤ (bipartitionComplement A).card)
    (hM : (N + 1 - nUp) ∈ tasaki23GroundStateSectors
      (fun x => decide (x ∈ liebOrientedSublattice A)) 1)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT_symm : ∀ x y, T x y = T y x) (hbip : HoppingRespectsBipartition A T)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU_pos : ∀ x, 0 < U x) :
    ∃ (E : ℝ) (φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)),
      IsUniqueGroundStateOn
          (numberSpinZSectorEuclidean N ((N : ℂ) + 1) (((Ne : ℂ) - ((N : ℂ) + 1)) / 2))
          (symmetricRepulsiveHubbardHamiltonian N T U) E φ ∧
        Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ = liebRepulsiveSpinCasimir A • φ := by
  obtain ⟨E, φ, hGS⟩ := repulsiveSpinZSector_ground_unique_on_numberSpinZSector N Ne hNe_even
    hNe_pos hNe_lt (A := A) T hT_symm hbip hT_conn U hU_pos
  refine ⟨E, φ, hGS, ?_⟩
  obtain ⟨c, hcne, hcmem, hcmin, hcstrict⟩ :=
    exists_unique_casimir_sector_strict_min
      (symmetricRepulsiveHubbardHamiltonian_isHermitian N T hT_symm U)
      (fermionTotalNumber_commute_symmetricRepulsiveHubbardHamiltonian N T U).symm
      (fermionTotalSpinZ_commute_symmetricRepulsiveHubbardHamiltonian N T U).symm
      (fermionTotalSpinSquared_commute_symmetricRepulsiveHubbardHamiltonian N T hT_symm U).symm
      hGS
  obtain ⟨cs, hsel, -, hc0⟩ :=
    symmetricHomotopy_casimirSelector_zero_eq_liebRepulsiveSpinCasimir N Ne hNe_even hNe_pos
      hNe_lt nUp hnUp hNe2 hA hB hM T hT_symm hbip hT_conn U hU_pos (lam := 1) one_pos
  have h0 := hsel 0 (by norm_num)
  rw [symmetricHomotopyHamiltonian_zero] at h0
  have hcc : c = cs 0 :=
    casimirSelector_strict_min_unique ⟨hcne, hcmin, hcstrict⟩
      ⟨h0.1, rfl, fun c' hne hK => h0.2 c' hne hK⟩
  rw [numberSpinZCasimirSectorEuclidean, Submodule.mem_inf] at hcmem
  rw [Module.End.mem_eigenspace_iff.mp hcmem.2, hcc, hc0]

/-! ## Admissible-sector arithmetic -/

/-- A sublattice and its bipartition complement partition the site set: `|S| + |Sᶜ| = N + 1`. -/
private theorem bipartitionComplement_card_add (N : ℕ) (S : Finset (Fin (N + 1))) :
    S.card + (bipartitionComplement S).card = N + 1 := by
  rw [bipartitionComplement_eq_compl, Finset.card_add_card_compl, Fintype.card_fin]

/-- **Admissibility in up-count form.** Tasaki's Theorem 2.3 admissible-sector condition on the
down-count `N + 1 − nUp` (`tasaki23GroundStateSectors … 1 = Finset.Icc (min |A'| |A'ᶜ|)
(max |A'| |A'ᶜ|)` at the oriented sublattice `A'`) is, in terms of the up-count `nUp`, the two-sided
bound `|A'ᶜ| ≤ nUp ≤ |A'|`; the orientation `|A'ᶜ| ≤ |A'|` resolves the `min`/`max` and
`|A'| + |A'ᶜ| = N + 1` flips the interval. -/
private theorem liebRepulsive_mem_tasaki23GroundStateSectors_iff (N : ℕ)
    (A : Finset (Fin (N + 1))) {nUp : ℕ} (hnUp : nUp ≤ N + 1) :
    (N + 1 - nUp) ∈ tasaki23GroundStateSectors
        (fun x => decide (x ∈ liebOrientedSublattice A)) 1 ↔
      ((bipartitionComplement (liebOrientedSublattice A)).card ≤ nUp ∧
        nUp ≤ (liebOrientedSublattice A).card) := by
  have hcard := bipartitionComplement_card_add N (liebOrientedSublattice A)
  have horient := liebOrientedSublattice_horient A
  rw [tasaki23GroundStateSectors_mem_iff, liebSublattice_filter_true, liebSublattice_filter_false,
    min_eq_right horient, max_eq_left horient]
  omega

/-! ## Step 3: the sector energy ladder -/

/-- **The sector energy ladder (one direction).** If the admissible sector `nUp₁` has a ground state
`φ₁` of spin `S₀ = sublatticeImbalance A / 2` at energy `E₁`, then every admissible sector `nUp₂`
has ground energy `E₂ ≤ E₁`: the SU(2) companion of `φ₁` at the transport index
`k = |A'| − nUp₂` is a nonzero energy-`E₁` eigenvector inside the sector `nUp₂`, so `E₂`, being the
ground eigenvalue there, cannot exceed `E₁`. The sublattice cardinalities enter only numerically
(`hcard`, `himb`, `horient`), so the lemma is stated at bare naturals `cA`, `cB`. -/
private theorem liebRepulsive_sector_energy_le (N cA cB nUp₁ nUp₂ : ℕ)
    {A : Finset (Fin (N + 1))}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT_symm : ∀ x y, T x y = T y x)
    (U : Fin (N + 1) → ℝ)
    (hcard : cA + cB = N + 1) (himb : sublatticeImbalance A = cA - cB) (horient : cB ≤ cA)
    (hlow : cB ≤ nUp₂) (hhigh : nUp₂ ≤ cA)
    {E₁ E₂ : ℝ} {φ₁ φ₂ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)}
    (hGS₁ : IsUniqueGroundStateOn
      (numberSpinZSectorEuclidean N ((N : ℂ) + 1) (liebHalfFillingSpinZVal N nUp₁))
      (symmetricRepulsiveHubbardHamiltonian N T U) E₁ φ₁)
    (hcas₁ : Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ₁
      = liebRepulsiveSpinCasimir A • φ₁)
    (hGS₂ : IsUniqueGroundStateOn
      (numberSpinZSectorEuclidean N ((N : ℂ) + 1) (liebHalfFillingSpinZVal N nUp₂))
      (symmetricRepulsiveHubbardHamiltonian N T U) E₂ φ₂) :
    E₂ ≤ E₁ := by
  obtain ⟨hmem₁, hnorm₁, heig₁, -, -⟩ := hGS₁
  have hφ₁ne : φ₁ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm₁
    exact zero_ne_one hnorm₁
  rw [numberSpinZSectorEuclidean, Submodule.mem_inf, spinZSectorEuclidean] at hmem₁
  have hnum₁ : Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1)) φ₁ = ((N : ℂ) + 1) • φ₁ :=
    Module.End.mem_eigenspace_iff.mp hmem₁.1
  have h3₁ : Matrix.toEuclideanLin (fermionTotalSpinZ N) φ₁
      = (((2 * (nUp₁ : ℝ) - ((N : ℝ) + 1)) / 2 : ℝ) : ℂ) • φ₁ := by
    rw [Module.End.mem_eigenspace_iff.mp hmem₁.2, liebHalfFillingSpinZVal]
    push_cast
    ring_nf
  have hLcast : ((sublatticeImbalance A : ℕ) : ℝ) = (cA : ℝ) - (cB : ℝ) := by
    rw [himb, Nat.cast_sub horient]
  have hS₀ : (0 : ℝ) ≤ (sublatticeImbalance A : ℝ) / 2 := by positivity
  have hsq₁ : Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ₁
      = (((sublatticeImbalance A : ℝ) / 2 * ((sublatticeImbalance A : ℝ) / 2 + 1) : ℝ) : ℂ)
        • φ₁ := by
    rw [hcas₁, liebRepulsiveSpinCasimir]
    push_cast
    ring_nf
  have hkcast : ((cA - nUp₂ : ℕ) : ℝ) = (cA : ℝ) - (nUp₂ : ℝ) := Nat.cast_sub hhigh
  have hlow' : (cB : ℝ) ≤ (nUp₂ : ℝ) := by exact_mod_cast hlow
  have hcard' : (cA : ℝ) + (cB : ℝ) = (N : ℝ) + 1 := by exact_mod_cast hcard
  obtain ⟨Ψ, hΨne, hΨmem, hΨH⟩ :=
    liebRepulsive_transport_to_sector N nUp₂ (cA - nUp₂) T hT_symm U hφ₁ne hS₀ hsq₁ h3₁ heig₁
      hnum₁ (by rw [hkcast, hLcast]; linarith) (by rw [hkcast, hLcast]; linarith)
  exact hGS₂.2.2.2.1.2 E₁ ⟨Ψ, hΨmem, hΨne, hΨH⟩

/-! ## Step 4: minimality over the whole `(N+1)`-electron sector -/

/-- **Global minimality of the admissible-sector ground energy.** If every admissible `Ŝ³` sector
has ground energy `E₀`, then no `(N+1)`-electron eigenvalue of the physical Hamiltonian lies below
`E₀`: the ground submodule at such an eigenvalue `E` is invariant under `Ŝ²` and `Ŝ³`, hence
contains a joint eigenvector (`exists_joint_eigenvector_in_invariant_submodule`); its spin `J` and
weight `m` are real (`isHermitian_mulVec_eigenvalue_eq_ofReal`,
`Matrix.posSemidef_mulVec_eigenvalue_nonneg`) and satisfy the quantization
`J − m ∈ ℤ≥0` (`angMom_sub_mem_nat`) together with the up-count bookkeeping
`m = (2 nUp − (N+1))/2` (`attractiveHubbard_up_down_mulVec_of_number_spinZ` +
`mulVec_apply_eq_zero_of_upNumber_ne`), so `J = (2p − (N+1))/2` for a natural `p`; transporting to
the sector `q = min p cA` — admissible because `cB ≤ p` follows from `J ≥ 0` — produces an
energy-`E` eigenvector there, and `E₀` is the ground eigenvalue of that sector. Only the numerical
data `cA + cB = N + 1`, `cB ≤ cA` of the sublattice cardinalities is used. -/
private theorem liebRepulsive_groundEnergy_le_of_electronNumber (N cA cB : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT_symm : ∀ x y, T x y = T y x)
    (U : Fin (N + 1) → ℝ)
    (hcard : cA + cB = N + 1) (horient : cB ≤ cA)
    {E₀ : ℝ}
    (hfam : ∀ q : ℕ, cB ≤ q → q ≤ cA →
      ∃ φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
        IsUniqueGroundStateOn
          (numberSpinZSectorEuclidean N ((N : ℂ) + 1) (liebHalfFillingSpinZVal N q))
          (symmetricRepulsiveHubbardHamiltonian N T U) E₀ φ) :
    ∀ E : ℂ,
      hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1) ≠ ⊥ →
      E₀ ≤ E.re := by
  intro E hG
  -- the ground submodule is invariant under the two commuting charges `Ŝ²` and `Ŝ³`
  have hinv : ∀ B : ManyBodyOp (Fin (2 * N + 2)),
      Commute B (symmetricRepulsiveHubbardHamiltonian N T U) →
      Commute B (fermionTotalNumber (2 * N + 1)) →
      hubbardGroundSubmoduleAtElectronNumber (symmetricRepulsiveHubbardHamiltonian N T U)
          E (N + 1) ≤
        (hubbardGroundSubmoduleAtElectronNumber (symmetricRepulsiveHubbardHamiltonian N T U)
          E (N + 1)).comap B.mulVecLin := by
    intro B hBH hBN x hx
    rw [hubbardGroundSubmoduleAtElectronNumber, Submodule.mem_inf] at hx
    rw [Submodule.mem_comap, Matrix.mulVecLin_apply, hubbardGroundSubmoduleAtElectronNumber,
      Submodule.mem_inf]
    exact ⟨mulVec_mem_eigenspace_of_commute hBH hx.1, mulVec_mem_eigenspace_of_commute hBN hx.2⟩
  have hcomm : Commute (fermionTotalSpinSquared N).mulVecLin (fermionTotalSpinZ N).mulVecLin := by
    have h := (fermionTotalSpinSquared_commute_fermionTotalSpinZ N).eq
    have h1 : (fermionTotalSpinSquared N).mulVecLin * (fermionTotalSpinZ N).mulVecLin
        = (fermionTotalSpinSquared N * fermionTotalSpinZ N).mulVecLin := by
      rw [Matrix.mulVecLin_mul]
      rfl
    have h2 : (fermionTotalSpinZ N).mulVecLin * (fermionTotalSpinSquared N).mulVecLin
        = (fermionTotalSpinZ N * fermionTotalSpinSquared N).mulVecLin := by
      rw [Matrix.mulVecLin_mul]
      rfl
    exact h1.trans ((congrArg Matrix.mulVecLin h).trans h2.symm)
  obtain ⟨lam, mu, v, hvmem, hvne, hvsq, hv3⟩ :=
    exists_joint_eigenvector_in_invariant_submodule
      (fermionTotalSpinSquared N).mulVecLin (fermionTotalSpinZ N).mulVecLin
      (hubbardGroundSubmoduleAtElectronNumber (symmetricRepulsiveHubbardHamiltonian N T U)
        E (N + 1))
      (hinv _ (fermionTotalSpinSquared_commute_symmetricRepulsiveHubbardHamiltonian N T hT_symm U)
        (fermionTotalSpinSquared_commute_fermionTotalNumber N))
      (hinv _ (fermionTotalSpinZ_commute_symmetricRepulsiveHubbardHamiltonian N T U)
        (fermionTotalSpinZ_commute_fermionTotalNumber N))
      hcomm hG
  rw [hubbardGroundSubmoduleAtElectronNumber, Submodule.mem_inf] at hvmem
  have hHv : (symmetricRepulsiveHubbardHamiltonian N T U).mulVec v = E • v := by
    have h := Module.End.mem_eigenspace_iff.mp hvmem.1
    rwa [Matrix.mulVecLin_apply] at h
  have hNv : (fermionTotalNumber (2 * N + 1)).mulVec v = ((N + 1 : ℕ) : ℂ) • v := by
    have h := Module.End.mem_eigenspace_iff.mp hvmem.2
    rwa [Matrix.mulVecLin_apply] at h
  have hvsq' : (fermionTotalSpinSquared N).mulVec v = lam • v := by
    rwa [Matrix.mulVecLin_apply] at hvsq
  have hv3' : (fermionTotalSpinZ N).mulVec v = mu • v := by
    rwa [Matrix.mulVecLin_apply] at hv3
  -- all three eigenvalues are real, and the Casimir one is nonnegative
  obtain ⟨Er, hEr⟩ := isHermitian_mulVec_eigenvalue_eq_ofReal
    (symmetricRepulsiveHubbardHamiltonian_isHermitian N T hT_symm U) hvne hHv
  obtain ⟨mur, hmur⟩ := isHermitian_mulVec_eigenvalue_eq_ofReal
    (fermionTotalSpinZ_isHermitian N) hvne hv3'
  obtain ⟨lamr, hlamr⟩ := isHermitian_mulVec_eigenvalue_eq_ofReal
    (fermionTotalSpinSquared_isHermitian N) hvne hvsq'
  have hv3r : (fermionTotalSpinZ N).mulVec v = (mur : ℂ) • v := by rw [hmur]; exact hv3'
  have hvsqr : (fermionTotalSpinSquared N).mulVec v = (lamr : ℂ) • v := by
    rw [hlamr]; exact hvsq'
  have hlam0 : 0 ≤ lamr :=
    Matrix.posSemidef_mulVec_eigenvalue_nonneg (fermionTotalSpinSquared_posSemidef N) hvne hvsqr
  -- the spin label `J ≥ 0` with `J (J + 1) = lam`
  set Jr : ℝ := (Real.sqrt (1 + 4 * lamr) - 1) / 2 with hJrdef
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (1 + 4 * lamr) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + 4 * lamr by linarith)
    rwa [Real.sqrt_one] at h
  have hJr0 : 0 ≤ Jr := by rw [hJrdef]; linarith
  have hJrsq : Jr * (Jr + 1) = lamr := by
    have hs : Real.sqrt (1 + 4 * lamr) ^ 2 = 1 + 4 * lamr := Real.sq_sqrt (by linarith)
    rw [hJrdef]
    nlinarith [hs]
  have hcart : (tJTotalSpinOne N * tJTotalSpinOne N + tJTotalSpinTwo N * tJTotalSpinTwo N
        + fermionTotalSpinZ N * fermionTotalSpinZ N).mulVec v
      = ((Jr * (Jr + 1) : ℝ) : ℂ) • v := by
    rw [← fermionTotalSpinSquared_eq_cartesianSqSum, hJrsq]
    exact hvsqr
  -- the weight is a half-integer of the right parity: `mur = (2 nUp − (N+1))/2`
  obtain ⟨hup, -⟩ :=
    attractiveHubbard_up_down_mulVec_of_number_spinZ (N + 1) ((mur : ℝ) : ℂ) hNv hv3r
  obtain ⟨w, hw⟩ := Function.ne_iff.mp hvne
  rw [Pi.zero_apply] at hw
  have hsum : (∑ i : Fin (N + 1), ((w (spinfulIndex N i 0)).val : ℂ))
      = (((N + 1 : ℕ) : ℂ) / 2 + (mur : ℂ)) := by
    by_contra hne
    exact hw (mulVec_apply_eq_zero_of_upNumber_ne v _ hup w hne)
  set nUp : ℕ := ∑ i : Fin (N + 1), (w (spinfulIndex N i 0)).val with hnUpdef
  have hnUpcast : ((nUp : ℕ) : ℂ) = ∑ i : Fin (N + 1), ((w (spinfulIndex N i 0)).val : ℂ) := by
    rw [hnUpdef]
    push_cast
    rfl
  have hmurval : (nUp : ℝ) = ((N : ℝ) + 1) / 2 + mur := by
    have hc : ((nUp : ℕ) : ℂ) = (((N : ℝ) + 1) / 2 + mur : ℝ) := by
      rw [hnUpcast, hsum]
      push_cast
      ring
    exact_mod_cast hc
  have hnUpN : nUp ≤ N + 1 := by
    have h : nUp ≤ ∑ _i : Fin (N + 1), 1 :=
      Finset.sum_le_sum fun i _ => Fin.is_le (w (spinfulIndex N i 0))
    simpa using h
  -- quantization: `Jr − mur` is a natural number, so `Jr = (2 p − (N+1))/2`
  obtain ⟨n, hn⟩ := angMom_sub_mem_nat (tJTotalSpinOne N) (tJTotalSpinTwo N) (fermionTotalSpinZ N)
    (tJTotalSpinOne_isHermitian N) (tJTotalSpinTwo_isHermitian N) (tJTotalSpin_su2_12 N)
    (tJTotalSpin_su2_23 N) (tJTotalSpin_su2_31 N) hvne hJr0 hcart hv3r
  set p : ℕ := nUp + n with hpdef
  have hJrp : Jr = (2 * (p : ℝ) - ((N : ℝ) + 1)) / 2 := by
    rw [hpdef]
    push_cast
    linarith
  have hNp : N + 1 ≤ 2 * p := by
    have h0 := hJr0
    rw [hJrp] at h0
    have h : ((N + 1 : ℕ) : ℝ) ≤ ((2 * p : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h
  have hpcB : cB ≤ p := by omega
  -- transport into the admissible sector `q = min p cA`
  set q : ℕ := min p cA with hqdef
  have hq1 : cB ≤ q := le_min hpcB horient
  have hq2 : q ≤ cA := min_le_right p cA
  have hqp : q ≤ p := min_le_left p cA
  have hpq : N + 1 ≤ p + q := by
    rcases min_cases p cA with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [hqdef, he] <;> omega
  have hqcast : ((p - q : ℕ) : ℝ) = (p : ℝ) - (q : ℝ) := Nat.cast_sub hqp
  have hpq' : ((N : ℝ) + 1) ≤ (p : ℝ) + (q : ℝ) := by
    have h : ((N + 1 : ℕ) : ℝ) ≤ ((p + q : ℕ) : ℝ) := by exact_mod_cast hpq
    push_cast at h
    linarith
  -- the Euclidean-carrier form of the four eigen-equations
  have hvne' : (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) ≠ 0 := by
    rw [ne_eq, WithLp.toLp_eq_zero]
    exact hvne
  have hsqE : Matrix.toEuclideanLin (fermionTotalSpinSquared N) (WithLp.toLp 2 v)
      = ((Jr * (Jr + 1) : ℝ) : ℂ) • (WithLp.toLp 2 v) :=
    (mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul _ _ _).mp (by rw [hJrsq]; exact hvsqr)
  have h3E : Matrix.toEuclideanLin (fermionTotalSpinZ N) (WithLp.toLp 2 v)
      = ((mur : ℝ) : ℂ) • (WithLp.toLp 2 v) :=
    (mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul _ _ _).mp hv3r
  have hHE : Matrix.toEuclideanLin (symmetricRepulsiveHubbardHamiltonian N T U)
      (WithLp.toLp 2 v) = E • (WithLp.toLp 2 v) :=
    (mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul _ _ _).mp hHv
  have hNE : Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1)) (WithLp.toLp 2 v)
      = ((N : ℂ) + 1) • (WithLp.toLp 2 v) :=
    (mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul _ _ _).mp
      (by rw [hNv, Nat.cast_add, Nat.cast_one])
  obtain ⟨Ψ, hΨne, hΨmem, hΨH⟩ :=
    liebRepulsive_transport_to_sector N q (p - q) T hT_symm U hvne' hJr0 hsqE h3E hHE hNE
      (by rw [hqcast, hJrp]; linarith) (by rw [hqcast, hJrp]; ring)
  obtain ⟨φ, hGS⟩ := hfam q hq1 hq2
  have hEre : E.re = Er := by rw [← hEr]; simp
  rw [hEre]
  refine hGS.2.2.2.1.2 Er ⟨Ψ, hΨmem, hΨne, ?_⟩
  rw [hΨH, hEr]

/-! ## PR-14a capstone -/

/-- **The PR-14a capstone.** For the physical symmetric repulsive Hubbard model at half-filling
(`1 ≤ |A|`, `1 ≤ |B|`), there is a single ground energy `E₀` such that every admissible `Ŝ³`
sector (indexed by `nUp` with `(N+1-nUp) ∈ tasaki23GroundStateSectors …`) has a unique ground state
at that energy, carrying the Casimir eigenvalue `liebRepulsiveSpinCasimir A`; moreover `E₀` is
minimal over the whole `(N+1)`-electron sector (conjunct (ii) of
`theorem_10_4_lieb_repulsive_half_filling`, `LiebRepulsive.lean:134`, symmetric disjunct only).
The energy-ladder equality across admissible sectors (step 3) is
`liebRepulsive_sector_energy_le` applied in both directions against the top sector `nUp = |A'|`;
global minimality (step 4) is `liebRepulsive_groundEnergy_le_of_electronNumber`.

PR-14b's weight confinement and `finrank` count (the remaining two conjuncts of Theorem 10.4) are
**not** part of this capstone. -/
theorem liebRepulsive_multipletCompanion_capstone
    (N : ℕ) {A : Finset (Fin (N + 1))} (hA : 1 ≤ A.card) (hB : 1 ≤ (bipartitionComplement A).card)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT_symm : ∀ x y, T x y = T y x)
    (hbip : HoppingRespectsBipartition A T) (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU_pos : ∀ x, 0 < U x) :
    ∃ E₀ : ℝ,
      (∀ nUp : ℕ, nUp ≤ N + 1 →
        (N + 1 - nUp) ∈ tasaki23GroundStateSectors
            (fun x => decide (x ∈ liebOrientedSublattice A)) 1 →
        ∃ φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
          IsUniqueGroundStateOn
              (numberSpinZSectorEuclidean N ((N : ℂ) + 1) (liebHalfFillingSpinZVal N nUp))
              (symmetricRepulsiveHubbardHamiltonian N T U) E₀ φ ∧
            Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ
              = liebRepulsiveSpinCasimir A • φ) ∧
      ∀ E : ℂ,
        hubbardGroundSubmoduleAtElectronNumber
            (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1) ≠ ⊥ →
        E₀ ≤ E.re := by
  classical
  obtain ⟨hcApos, hcBpos⟩ := liebOrientedSublattice_card_pos A hA hB
  have horient := liebOrientedSublattice_horient A
  have hcard := bipartitionComplement_card_add N (liebOrientedSublattice A)
  have himb : sublatticeImbalance A
      = (liebOrientedSublattice A).card - (bipartitionComplement (liebOrientedSublattice A)).card :=
    by rw [← liebOrientedSublattice_sublatticeImbalance_eq A, sublatticeImbalance]; omega
  -- every admissible sector carries a unique ground state at its own energy, of spin `S₀`
  have hsector : ∀ nUp : ℕ, (bipartitionComplement (liebOrientedSublattice A)).card ≤ nUp →
      nUp ≤ (liebOrientedSublattice A).card →
      ∃ (E : ℝ) (φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)),
        IsUniqueGroundStateOn
            (numberSpinZSectorEuclidean N ((N : ℂ) + 1) (liebHalfFillingSpinZVal N nUp))
            (symmetricRepulsiveHubbardHamiltonian N T U) E φ ∧
          Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ
            = liebRepulsiveSpinCasimir A • φ := by
    intro nUp h1 h2
    obtain ⟨E, φ, hGS, hcas⟩ :=
      liebRepulsive_admissibleSector_groundState_casimir_eigenvector N (2 * nUp)
        ⟨nUp, two_mul nUp⟩ (by omega) (by omega) nUp (by omega) rfl hA hB
        ((liebRepulsive_mem_tasaki23GroundStateSectors_iff N A (by omega)).mpr ⟨h1, h2⟩)
        T hT_symm hbip hT_conn U hU_pos
    refine ⟨E, φ, ?_, hcas⟩
    rwa [← liebHalfFillingSpinZVal_eq_of_two_mul N nUp (2 * nUp) rfl] at hGS
  obtain ⟨E₀, φ₀, hGS₀, hcas₀⟩ := hsector (liebOrientedSublattice A).card horient le_rfl
  have hfam : ∀ nUp : ℕ, (bipartitionComplement (liebOrientedSublattice A)).card ≤ nUp →
      nUp ≤ (liebOrientedSublattice A).card →
      ∃ φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
        IsUniqueGroundStateOn
            (numberSpinZSectorEuclidean N ((N : ℂ) + 1) (liebHalfFillingSpinZVal N nUp))
            (symmetricRepulsiveHubbardHamiltonian N T U) E₀ φ ∧
          Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ
            = liebRepulsiveSpinCasimir A • φ := by
    intro nUp h1 h2
    obtain ⟨E, φ, hGS, hcas⟩ := hsector nUp h1 h2
    have hle : E ≤ E₀ :=
      liebRepulsive_sector_energy_le N _ _ _ nUp T hT_symm U hcard himb horient h1 h2
        hGS₀ hcas₀ hGS
    have hge : E₀ ≤ E :=
      liebRepulsive_sector_energy_le N _ _ nUp _ T hT_symm U hcard himb horient horient le_rfl
        hGS hcas hGS₀
    have hEeq : E = E₀ := le_antisymm hle hge
    subst hEeq
    exact ⟨φ, hGS, hcas⟩
  refine ⟨E₀, ?_, ?_⟩
  · intro nUp hnUp hM
    obtain ⟨h1, h2⟩ := (liebRepulsive_mem_tasaki23GroundStateSectors_iff N A hnUp).mp hM
    exact hfam nUp h1 h2
  · exact liebRepulsive_groundEnergy_le_of_electronNumber N _ _ T hT_symm U hcard horient
      fun q h1 h2 => (hfam q h1 h2).imp fun _ h => h.1

end LatticeSystem.Fermion
