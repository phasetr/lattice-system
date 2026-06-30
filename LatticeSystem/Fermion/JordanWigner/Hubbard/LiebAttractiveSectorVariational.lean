import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowUVariationalCore

/-!
# Generic fixed-sector variational tools (Tasaki §10.2.4)

Layer PR40e-pre2a toward discharging `theorem_10_2_lieb_attractive_unique_singlet`. The Lieb
spin-reflection-positivity squeeze argument runs inside the fixed electron-number sector, against
the **sector-compression** minimum eigenvalue `E_Ne` (not the full `hermitianMinEigenvalue`). The
existing sector tools (`hubbardSector_minEnergy_mul_le_rayleighOnVec`) are stated for the uniform
Hubbard Hamiltonian only; the attractive site-dependent Hamiltonian needs the same facts.

Both facts are completely generic in the operator (they only use Hermiticity and number
conservation), so this module states them for an arbitrary `A : ManyBodyOp`:

* `hubbardSector_minEnergy_mul_le_rayleighOnVec_of_isHermitian` — sector variational lower bound:
  any `Ne`-electron vector `v` has Rayleigh quotient `≥ E_Ne · ‖v‖²`.
* `mulVec_eq_smul_of_hubbardSector_rayleighOnVec_eq_min` — the converse for sector ground states:
  if an `Ne`-electron vector attains the sector minimum, it is an `A`-eigenvector at `E_Ne`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4 (Lemma 10.10), pp. 363–367.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **Generic sector variational lower bound.** For a Hermitian operator `A`, any vector `v` in the
`Ne`-electron sector (`N̂ v = Ne·v`) has Rayleigh quotient at least `E_Ne · ‖v‖²`, where `E_Ne` is
the minimum eigenvalue of the sector compression of `A`. -/
theorem hubbardSector_minEnergy_mul_le_rayleighOnVec_of_isHermitian
    (Ne : ℕ) [Nonempty (hubbardSectorConfig N Ne)]
    {A : ManyBodyOp (Fin (2 * N + 2))} (hA : A.IsHermitian)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hv : (fermionTotalNumber (2 * N + 1)).mulVec v = (Ne : ℂ) • v) :
    (hermitianMinEigenvalue (hubbardSectorCompress_isHermitian Ne hA)) *
        (dotProduct (star v) v).re ≤ rayleighOnVec A v := by
  set hHW := hubbardSectorCompress_isHermitian Ne hA with hHWd
  set c := hubbardSectorCoeff N Ne v with hc
  have hexp : v = hubbardSectorExpansion N Ne c := hubbardSector_completeness Ne v hv
  have hcc : (dotProduct (star c) c).re = (dotProduct (star v) v).re := by
    rw [hc, ← hubbardSectorExpansion_dotProduct_self Ne, ← hexp]
  have hvar := hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec hHW c
  rw [hcc] at hvar
  calc hermitianMinEigenvalue hHW * (dotProduct (star v) v).re
      ≤ rayleighOnVec (hubbardSectorCompress N Ne A) c := hvar
    _ = rayleighOnVec A v := by rw [rayleighOnVec_hubbardSectorCompress, ← hexp]

/-- **Generic sector ground-state eigenvector recovery.** For a Hermitian operator `A` that
preserves the `Ne`-electron sector, any `Ne`-electron vector `v` whose Rayleigh quotient attains the
minimum `E_Ne · ‖v‖²` is an `A`-eigenvector at `E_Ne`. -/
theorem mulVec_eq_smul_of_hubbardSector_rayleighOnVec_eq_min
    (Ne : ℕ) [Nonempty (hubbardSectorConfig N Ne)]
    {A : ManyBodyOp (Fin (2 * N + 2))} (hA : A.IsHermitian)
    (hAW : PreservesHubbardSectorW N Ne A)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hv : (fermionTotalNumber (2 * N + 1)).mulVec v = (Ne : ℂ) • v)
    (heq : rayleighOnVec A v =
      (hermitianMinEigenvalue (hubbardSectorCompress_isHermitian Ne hA)) *
        (dotProduct (star v) v).re) :
    A.mulVec v
      = ((hermitianMinEigenvalue (hubbardSectorCompress_isHermitian Ne hA) : ℝ) : ℂ) • v := by
  set hHW := hubbardSectorCompress_isHermitian Ne hA with hHWd
  set c := hubbardSectorCoeff N Ne v with hc
  have hexp : v = hubbardSectorExpansion N Ne c := hubbardSector_completeness Ne v hv
  have hcc : (dotProduct (star c) c).re = (dotProduct (star v) v).re := by
    rw [hc, ← hubbardSectorExpansion_dotProduct_self Ne, ← hexp]
  -- The compression Rayleigh quotient attains its minimum at `c`.
  have heqc : rayleighOnVec (hubbardSectorCompress N Ne A) c =
      hermitianMinEigenvalue hHW * (dotProduct (star c) c).re := by
    rw [rayleighOnVec_hubbardSectorCompress, ← hexp, heq, hcc]
  -- Hence `c` is a compression eigenvector at `E_Ne`.
  have hceig : (hubbardSectorCompress N Ne A).mulVec c
      = ((hermitianMinEigenvalue hHW : ℝ) : ℂ) • c :=
    mulVec_eq_smul_of_rayleighOnVec_eq_min hHW heqc
  -- Lift to `A` and rewrite `v = expansion c`.
  have hlift := mulVec_hubbardSectorExpansion_of_compress_eigen Ne hAW hceig
  rw [← hexp] at hlift
  rw [hlift, hexp]

end LatticeSystem.Fermion
