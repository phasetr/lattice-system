import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowUVariationalCore

/-!
# Generic fixed-sector variational tools (Tasaki §10.2.4)

Layer PR40e-pre2a toward discharging `theorem_10_2_lieb_attractive_unique_singlet`. The Lieb
spin-reflection-positivity squeeze argument runs inside a fixed configuration sector, against the
**sector-compression** minimum eigenvalue `E_P` (not the full `hermitianMinEigenvalue`). The two
facts are completely generic in both the operator `A : ManyBodyOp` (they use only Hermiticity) and
the sector predicate `P` (they use only support on `P`), so this module states them for an
arbitrary decidable predicate `P`, taking the sector-support hypotheses directly. Instantiating at
`hubbardNumberSectorPred N Ne` recovers the electron-number sector; at `hubbardBalancedSectorPred`
the balanced (`Ŝ³ = 0`) sector needed by PR40f.

* `configSector_minEnergy_mul_le_rayleighOnVec_of_isHermitian` — sector variational lower bound:
  any `P`-supported vector `v` has Rayleigh quotient `≥ E_P · ‖v‖²`.
* `mulVec_eq_smul_of_configSector_rayleighOnVec_eq_min` — the converse for sector ground states:
  if a `P`-supported vector attains the sector minimum, it is an `A`-eigenvector at `E_P`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4 (Lemma 10.10), pp. 363–367.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **Generic sector variational lower bound.** For a Hermitian operator `A`, any vector `v`
supported on the `P`-sector (`v w = 0` whenever `¬ P w`) has Rayleigh quotient at least
`E_P · ‖v‖²`, where `E_P` is the minimum eigenvalue of the `P`-sector compression of `A`. -/
theorem configSector_minEnergy_mul_le_rayleighOnVec_of_isHermitian
    (P : (Fin (2 * N + 2) → Fin 2) → Prop) [DecidablePred P] [Nonempty (configSector N P)]
    {A : ManyBodyOp (Fin (2 * N + 2))} (hA : A.IsHermitian)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hsupp : ∀ w, ¬ P w → v w = 0) :
    (hermitianMinEigenvalue (configSectorCompress_isHermitian P hA)) *
        (dotProduct (star v) v).re ≤ rayleighOnVec A v := by
  set hHW := configSectorCompress_isHermitian P hA with hHWd
  set c := configSectorCoeff N P v with hc
  have hexp : v = configSectorExpansion N P c :=
    configSector_completeness P v hsupp
  have hcc : (dotProduct (star c) c).re = (dotProduct (star v) v).re := by
    rw [hc, ← configSectorExpansion_dotProduct_self P, ← hexp]
  have hvar := hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec hHW c
  rw [hcc] at hvar
  calc hermitianMinEigenvalue hHW * (dotProduct (star v) v).re
      ≤ rayleighOnVec (configSectorCompress N P A) c := hvar
    _ = rayleighOnVec A v := by rw [rayleighOnVec_configSectorCompress, ← hexp]

/-- **Generic sector ground-state eigenvector recovery.** For a Hermitian operator `A` that keeps
the lift of a `P`-supported vector `v` supported on the `P`-sector, if `v`'s Rayleigh quotient
attains the minimum `E_P · ‖v‖²` then `v` is an `A`-eigenvector at `E_P`. -/
theorem mulVec_eq_smul_of_configSector_rayleighOnVec_eq_min
    (P : (Fin (2 * N + 2) → Fin 2) → Prop) [DecidablePred P] [Nonempty (configSector N P)]
    {A : ManyBodyOp (Fin (2 * N + 2))} (hA : A.IsHermitian)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hsupp : ∀ w, ¬ P w → v w = 0)
    (hApres : ∀ w, ¬ P w → A.mulVec v w = 0)
    (heq : rayleighOnVec A v =
      (hermitianMinEigenvalue (configSectorCompress_isHermitian P hA)) *
        (dotProduct (star v) v).re) :
    A.mulVec v
      = ((hermitianMinEigenvalue (configSectorCompress_isHermitian P hA) : ℝ) : ℂ) • v := by
  set hHW := configSectorCompress_isHermitian P hA with hHWd
  set c := configSectorCoeff N P v with hc
  have hexp : v = configSectorExpansion N P c :=
    configSector_completeness P v hsupp
  have hcc : (dotProduct (star c) c).re = (dotProduct (star v) v).re := by
    rw [hc, ← configSectorExpansion_dotProduct_self P, ← hexp]
  -- The compression Rayleigh quotient attains its minimum at `c`.
  have heqc : rayleighOnVec (configSectorCompress N P A) c =
      hermitianMinEigenvalue hHW * (dotProduct (star c) c).re := by
    rw [rayleighOnVec_configSectorCompress, ← hexp, heq, hcc]
  -- Hence `c` is a compression eigenvector at `E_P`.
  have hceig : (configSectorCompress N P A).mulVec c
      = ((hermitianMinEigenvalue hHW : ℝ) : ℂ) • c :=
    mulVec_eq_smul_of_rayleighOnVec_eq_min hHW heqc
  -- Lift to `A` and rewrite `v = expansion c`.
  have hApres' : ∀ w, ¬ P w →
      A.mulVec (configSectorExpansion N P c) w = 0 := by
    rw [← hexp]; exact hApres
  have hlift := configSectorExpansion_of_compress_eigen P hApres' hceig
  rw [← hexp] at hlift
  rw [hlift, hexp]

end LatticeSystem.Fermion
