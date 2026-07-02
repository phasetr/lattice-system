import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveFullSectorSU2Algebra
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBalancedSectorGround
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveSectorVariational
import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandMultiplet
import LatticeSystem.Math.AngularMomentum.SpinHalfSector

/-!
# The balanced-block ground energy equals the full `Ne`-sector ground energy (Tasaki §10.2.1)

Toward discharging `theorem_10_2_lieb_attractive_unique_singlet`, this file lifts the balanced
(`Ŝ³ = 0`) sector minimum energy `E_bal` of the attractive Hubbard model to the full `Ne`-electron
sector minimum `E_full` and proves `E_bal = E_full` (for `Ne = 2k` even).

* `E_full ≤ E_bal`: a balanced ground `φ` (`N̂_↑ φ = N̂_↓ φ = k φ`, energy `E_bal`) lies in the full
  `Ne`-sector (`N̂ φ = Ne φ`, since `N̂ = N̂_↑ + N̂_↓`), so the full-sector variational minimum
  `E_full` is at most its energy.
* `E_bal ≤ E_full`: a full-sector ground vector, compressed, feeds the generic angular-momentum
  engine (`LatticeSystem.Math.ham_eigenstate_spin_zero_or_half`, Tasaki Theorem A.17): it yields a
  compressed eigenstate `Φ` with `Ŝ³_W Φ = 0` or `Ŝ³_W Φ = ½ Φ`.  For **even** `Ne` the `½` branch
  is impossible (`N̂_↑ = (Ne+1)/2` is not an integer), forcing `Ŝ³_W Φ = 0`; lifting `Φ` to the Fock
  space gives a nonzero **balanced** state at energy `E_full`, so `E_bal ≤ E_full`.

This is the parity mirror of the odd-`Ne` t-J route
`tJ_perronFrobeniusMin_le_hermitianMinEigenvalue` (`TJGroundEnergyGe.lean`): the odd case kills the
`Ŝ³ = 0` branch, the even case kills the `Ŝ³ = ½` branch.

## Main results

* `attractiveHubbard_up_down_mulVec_of_number_spinZ` — from `N̂ Ψ = Ne Ψ` and `Ŝ³ Ψ = m Ψ`, the
  spin-number eigenvalues `N̂_↑ Ψ = (Ne/2 + m) Ψ`, `N̂_↓ Ψ = (Ne/2 − m) Ψ`.
* `attractiveHubbard_number_even_spinZ_half_eq_zero` — the even-`Ne` parity obstruction: no nonzero
  `N̂ = Ne`, `Ŝ³ = ½` state exists.
* `attractiveHubbard_balanced_energy_eq_number_sector` — **`E_bal = E_full`**.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.1 (Theorem 10.2), §10.2.4; Appendix A.3.2 Theorem A.17.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **The spin-number eigenvalues of a joint `N̂`/`Ŝ³` eigenstate.**  If `N̂ Ψ = Ne Ψ` and
`Ŝ³ Ψ = m Ψ`, then `N̂_↑ Ψ = (Ne/2 + m) Ψ` and `N̂_↓ Ψ = (Ne/2 − m) Ψ`, from
`N̂ = N̂_↑ + N̂_↓` and `Ŝ³ = ½(N̂_↑ − N̂_↓)`. -/
theorem attractiveHubbard_up_down_mulVec_of_number_spinZ (Ne : ℕ) (m : ℂ)
    {Ψ : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hN : (fermionTotalNumber (2 * N + 1)).mulVec Ψ = (Ne : ℂ) • Ψ)
    (hSz : (fermionTotalSpinZ N).mulVec Ψ = m • Ψ) :
    (fermionTotalUpNumber N).mulVec Ψ = ((Ne : ℂ) / 2 + m) • Ψ ∧
      (fermionTotalDownNumber N).mulVec Ψ = ((Ne : ℂ) / 2 - m) • Ψ := by
  have hsum : (fermionTotalUpNumber N).mulVec Ψ + (fermionTotalDownNumber N).mulVec Ψ
      = (Ne : ℂ) • Ψ := by
    rw [← Matrix.add_mulVec, ← fermionTotalNumber_eq_up_add_down, hN]
  have hdiff : (fermionTotalUpNumber N).mulVec Ψ - (fermionTotalDownNumber N).mulVec Ψ
      = (2 * m) • Ψ := by
    have hz : (fermionTotalSpinZ N).mulVec Ψ = (1 / 2 : ℂ)
        • ((fermionTotalUpNumber N).mulVec Ψ - (fermionTotalDownNumber N).mulVec Ψ) := by
      rw [fermionTotalSpinZ, Matrix.smul_mulVec, Matrix.sub_mulVec]
    rw [hSz] at hz
    have h2 := congrArg (fun z => (2 : ℂ) • z) hz
    simp only [smul_smul] at h2
    rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num, one_smul] at h2
    exact h2.symm
  refine ⟨?_, ?_⟩
  · have e : (fermionTotalUpNumber N).mulVec Ψ = (1 / 2 : ℂ)
        • (((fermionTotalUpNumber N).mulVec Ψ + (fermionTotalDownNumber N).mulVec Ψ)
            + ((fermionTotalUpNumber N).mulVec Ψ - (fermionTotalDownNumber N).mulVec Ψ)) := by
      module
    rw [e, hsum, hdiff]; module
  · have e : (fermionTotalDownNumber N).mulVec Ψ = (1 / 2 : ℂ)
        • (((fermionTotalUpNumber N).mulVec Ψ + (fermionTotalDownNumber N).mulVec Ψ)
            - ((fermionTotalUpNumber N).mulVec Ψ - (fermionTotalDownNumber N).mulVec Ψ)) := by
      module
    rw [e, hsum, hdiff]; module

/-- **Even-`Ne` parity obstruction.**  For even `Ne`, there is no nonzero state with `N̂ Ψ = Ne Ψ`
and `Ŝ³ Ψ = ½ Ψ`: it would force `N̂_↑ Ψ = ((Ne+1)/2) Ψ`, but the up-count is an integer while
`(Ne+1)/2` is a half-integer. -/
theorem attractiveHubbard_number_even_spinZ_half_eq_zero (Ne : ℕ) (hNe_even : Even Ne)
    {Ψ : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hN : (fermionTotalNumber (2 * N + 1)).mulVec Ψ = (Ne : ℂ) • Ψ)
    (hSz : (fermionTotalSpinZ N).mulVec Ψ = ((1 / 2 : ℝ) : ℂ) • Ψ) : Ψ = 0 := by
  have hup := (attractiveHubbard_up_down_mulVec_of_number_spinZ Ne ((1 / 2 : ℝ) : ℂ) hN hSz).1
  funext w
  refine mulVec_apply_eq_zero_of_upNumber_ne Ψ ((Ne : ℂ) / 2 + ((1 / 2 : ℝ) : ℂ)) hup w ?_
  intro hc
  obtain ⟨mm, hmm⟩ := hNe_even
  set s : ℕ := ∑ i : Fin (N + 1), (w (spinfulIndex N i 0)).val with hs
  have hcast : (∑ i : Fin (N + 1), ((w (spinfulIndex N i 0)).val : ℂ)) = (s : ℂ) := by
    rw [hs]; push_cast; rfl
  rw [hcast] at hc
  have hcr : (s : ℂ) = ((Ne : ℂ) + 1) / 2 := by rw [hc]; push_cast; ring
  have hnat : ((2 * s : ℕ) : ℂ) = ((Ne + 1 : ℕ) : ℂ) := by push_cast; rw [hcr]; ring
  have h2 : 2 * s = Ne + 1 := by exact_mod_cast hnat
  omega

/-- **Sector minimum is at most any sector eigenvalue.**  For a Hermitian operator `A` and a nonzero
vector `v` supported on the `P`-sector that is an `A`-eigenvector at real `E`, the `P`-sector
compression minimum `E_P` satisfies `E_P ≤ E`. -/
theorem configSector_minEnergy_le_of_eigenvector
    (P : (Fin (2 * N + 2) → Fin 2) → Prop) [DecidablePred P] [Nonempty (configSector N P)]
    {A : ManyBodyOp (Fin (2 * N + 2))} (hA : A.IsHermitian)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ} {E : ℝ}
    (hsupp : ∀ w, ¬ P w → v w = 0) (hv0 : v ≠ 0) (heig : A.mulVec v = (E : ℂ) • v) :
    hermitianMinEigenvalue (configSectorCompress_isHermitian P hA) ≤ E := by
  classical
  have hq : 0 < (dotProduct (star v) v).re := by
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hv0
    rw [Pi.zero_apply] at hi₀
    have hsum : dotProduct (star v) v = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.star_apply, RCLike.star_def]
      push_cast
      exact Finset.sum_congr rfl (fun i _ => by rw [Complex.normSq_eq_conj_mul_self])
    rw [hsum, Complex.ofReal_re]
    exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _)
      ⟨i₀, Finset.mem_univ _, Complex.normSq_pos.mpr hi₀⟩
  have hray : rayleighOnVec A v = E * (dotProduct (star v) v).re := by
    unfold rayleighOnVec
    rw [heig, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  have hvar := configSector_minEnergy_mul_le_rayleighOnVec_of_isHermitian P hA hsupp
  rw [hray] at hvar
  exact le_of_mul_le_mul_right hvar hq

/-- **`E_bal = E_full` (Tasaki §10.2.1).**  For even electron number `Ne = 2k` and an attractive
Hubbard model with symmetric real hopping `T`, the balanced (`Ŝ³ = 0`) sector-compression minimum
energy `E_bal` equals the full `Ne`-electron sector-compression minimum energy `E_full`.

The `E_full ≤ E_bal` half is the balanced-into-full variational inclusion; the `E_bal ≤ E_full` half
lifts a full-sector ground state through the generic Theorem A.17 engine
(`ham_eigenstate_spin_zero_or_half`) to a balanced state at energy `E_full`, the even-`Ne` parity
mirror of the odd-`Ne` t-J route `tJ_perronFrobeniusMin_le_hermitianMinEigenvalue`. -/
theorem attractiveHubbard_balanced_energy_eq_number_sector (k Ne : ℕ) (hNe : Ne = 2 * k)
    (hNe_even : Even Ne) [Nonempty (hubbardBalancedConfig N k)]
    [Nonempty (hubbardSectorConfig N Ne)]
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT_symm : ∀ i j, T i j = T j i) :
    hermitianMinEigenvalue (configSectorCompress_isHermitian (hubbardBalancedSectorPred N k)
        (attractiveHubbardHamiltonian_isHermitian T U hT_symm))
      = hermitianMinEigenvalue (configSectorCompress_isHermitian (hubbardNumberSectorPred N Ne)
        (attractiveHubbardHamiltonian_isHermitian T U hT_symm)) := by
  classical
  set hHerm := attractiveHubbardHamiltonian_isHermitian T U hT_symm with hHermd
  set hHfull := configSectorCompress_isHermitian (hubbardNumberSectorPred N Ne) hHerm with hHfulld
  set hHbal := configSectorCompress_isHermitian (hubbardBalancedSectorPred N k) hHerm with hHbald
  set Efull := hermitianMinEigenvalue hHfull with hEfulld
  set Ebal := hermitianMinEigenvalue hHbal with hEbald
  refine le_antisymm ?_ ?_
  · -- `E_bal ≤ E_full`: engine gives an `Ŝ³ = 0` companion at `E_full`, which is balanced.
    obtain ⟨c, hc0, hceig⟩ := exists_nonzero_eigenvector_hermitianMinEigenvalue hHfull
    obtain ⟨Φ, hΦ0, hΦeig, hΦspin⟩ := LatticeSystem.Math.ham_eigenstate_spin_zero_or_half
      (configSectorCompress N (hubbardNumberSectorPred N Ne) (attractiveHubbardHamiltonian N T U))
      (configSectorCompress N (hubbardNumberSectorPred N Ne) (tJTotalSpinOne N))
      (configSectorCompress N (hubbardNumberSectorPred N Ne) (tJTotalSpinTwo N))
      (configSectorCompress N (hubbardNumberSectorPred N Ne) (fermionTotalSpinZ N))
      hHfull
      (configSectorCompress_isHermitian _ (tJTotalSpinOne_isHermitian N))
      (configSectorCompress_isHermitian _ (tJTotalSpinTwo_isHermitian N))
      (configSectorCompress_isHermitian _ (fermionTotalSpinZ_isHermitian N))
      (configSectorNumberCompress_attractive_commute_one Ne T U hT_symm)
      (configSectorNumberCompress_attractive_commute_two Ne T U hT_symm)
      (configSectorNumberCompress_attractive_commute_three Ne T U)
      (configSectorNumberCompress_su2_12 Ne) (configSectorNumberCompress_su2_23 Ne)
      (configSectorNumberCompress_su2_31 Ne) hc0 hceig
    -- Lift `Φ` to the Fock space.
    set Ψ := configSectorExpansion N (hubbardNumberSectorPred N Ne) Φ with hΨd
    have hΨ0 : Ψ ≠ 0 := configSectorExpansion_ne_zero (hubbardNumberSectorPred N Ne) hΦ0
    have hΨW : Ψ ∈ hubbardSectorWSubmodule N Ne := hubbardSectorExpansion_mem Ne Φ
    have hΨN : (fermionTotalNumber (2 * N + 1)).mulVec Ψ = (Ne : ℂ) • Ψ :=
      (mem_hubbardSectorWSubmodule_iff Ne).mp hΨW
    have hΨeig : (attractiveHubbardHamiltonian N T U).mulVec Ψ = (Efull : ℂ) • Ψ := by
      have hApres : ∀ w, ¬ hubbardNumberSectorPred N Ne w →
          (attractiveHubbardHamiltonian N T U).mulVec Ψ w = 0 :=
        hubbardNumberSector_supported_of_mem Ne
          (preservesHubbardSectorW_attractive Ne T U Ψ hΨW)
      exact configSectorExpansion_of_compress_eigen (hubbardNumberSectorPred N Ne) hApres hΦeig
    -- `Ŝ³ Ψ = 0` (the `½` branch is killed by even-`Ne` parity).
    have hΨSz : (fermionTotalSpinZ N).mulVec Ψ = (0 : ℂ) • Ψ := by
      rcases hΦspin with h0 | hhalf
      · exact configSectorExpansion_of_compress_eigen (hubbardNumberSectorPred N Ne)
          (hubbardNumberSector_supported_of_mem Ne
            (preservesHubbardSectorW_fermionTotalSpinZ Ne Ψ hΨW))
          (h0.trans (zero_smul ℂ Φ).symm)
      · exfalso
        apply hΨ0
        have hΨhalf : (fermionTotalSpinZ N).mulVec Ψ = ((1 / 2 : ℝ) : ℂ) • Ψ :=
          configSectorExpansion_of_compress_eigen (hubbardNumberSectorPred N Ne)
            (hubbardNumberSector_supported_of_mem Ne
              (preservesHubbardSectorW_fermionTotalSpinZ Ne Ψ hΨW)) hhalf
        exact attractiveHubbard_number_even_spinZ_half_eq_zero Ne hNe_even hΨN hΨhalf
    -- Balanced spin-number eigenvalues, hence balanced support.
    obtain ⟨hΨup, hΨdn⟩ :=
      attractiveHubbard_up_down_mulVec_of_number_spinZ Ne (0 : ℂ) hΨN hΨSz
    have hk : (Ne : ℂ) / 2 + 0 = (k : ℂ) := by rw [hNe]; push_cast; ring
    have hk' : (Ne : ℂ) / 2 - 0 = (k : ℂ) := by rw [hNe]; push_cast; ring
    rw [hk] at hΨup
    rw [hk'] at hΨdn
    have hsupp : ∀ w, ¬ hubbardBalancedSectorPred N k w → Ψ w = 0 := by
      intro w hw
      by_cases hupw : (∑ i : Fin (N + 1), (w (spinfulIndex N i 0)).val) = k
      · have hdnw : (∑ i : Fin (N + 1), (w (spinfulIndex N i 1)).val) ≠ k := fun h => hw ⟨hupw, h⟩
        exact mulVec_apply_eq_zero_of_downNumber_ne Ψ (k : ℂ) hΨdn w
          (fun hcast => hdnw (by exact_mod_cast hcast))
      · exact mulVec_apply_eq_zero_of_upNumber_ne Ψ (k : ℂ) hΨup w
          (fun hcast => hupw (by exact_mod_cast hcast))
    exact configSector_minEnergy_le_of_eigenvector (hubbardBalancedSectorPred N k) hHerm
      hsupp hΨ0 hΨeig
  · -- `E_full ≤ E_bal`: a balanced ground lies in the full `Ne`-sector.
    obtain ⟨φ, hφ0, hφup, hφdn, hφeig⟩ := exists_attractive_balanced_ground k T U hT_symm
    have hφN : (fermionTotalNumber (2 * N + 1)).mulVec φ = (Ne : ℂ) • φ := by
      rw [fermionTotalNumber_eq_up_add_down, Matrix.add_mulVec, hφup, hφdn, ← add_smul,
        show (k : ℂ) + (k : ℂ) = (Ne : ℂ) by rw [hNe]; push_cast; ring]
    have hsupp : ∀ w, ¬ hubbardNumberSectorPred N Ne w → φ w = 0 := fun w hw =>
      mulVec_apply_eq_zero_of_number_ne N φ (Ne : ℂ) hφN w
        (fun hcast => hw (by exact_mod_cast hcast))
    exact configSector_minEnergy_le_of_eigenvector (hubbardNumberSectorPred N Ne) hHerm
      hsupp hφ0 hφeig

end LatticeSystem.Fermion
