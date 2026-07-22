import LatticeSystem.Quantum.SpinS.AKLTKnabe.BlockDischargeE6c

/-!
# Gate E6 (part d): the evaluated rows of the two sector blocks

Part d of the Gate E6 landing (Issue #5094, Tasaki §7.1.4).  Section 7: the ninety
evaluated-row lemmas `rowEq*E6` of the sector blocks.  Imports `BlockDischargeE6c`.
-/

namespace LatticeSystem.Quantum.AKLTSl2BlockDischargeE6

open LatticeSystem.Quantum
open LatticeSystem.Quantum.AKLTSl2SubmoduleProbeE2
open LatticeSystem.Quantum.AKLTSl2LadderSectorsE3
open LatticeSystem.Quantum.AKLTSl2WindowReductionE4
open LatticeSystem.Quantum.AKLTSl2HighestWeightBoundE5
open LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential
open scoped ComplexOrder

/-! ## 7. The evaluated rows of the two sector blocks -/

/-- Row `0` of the block `ĥ|V_1`, with its rational entries evaluated. -/
theorem rowEqV1r0E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 1 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((5 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 0 1) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 1 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 0 1) := by
  have h := rowV1E6 μ u hsupp heig (spinConfig 0 0 0 1)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `1` of the block `ĥ|V_1`, with its rational entries evaluated. -/
theorem rowEqV1r1E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 1 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 0 1) +
      ((2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 1 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 0 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 1 0) := by
  have h := rowV1E6 μ u hsupp heig (spinConfig 0 0 1 0)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `2` of the block `ĥ|V_1`, with its rational entries evaluated. -/
theorem rowEqV1r2E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 1 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 1 0) +
      ((2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 0 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 0 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 0 0) := by
  have h := rowV1E6 μ u hsupp heig (spinConfig 0 1 0 0)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `3` of the block `ĥ|V_1`, with its rational entries evaluated. -/
theorem rowEqV1r3E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 1 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 0 0) +
      ((5 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 0 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 0 0) := by
  have h := rowV1E6 μ u hsupp heig (spinConfig 1 0 0 0)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `0` of the block `ĥ|V_2`, with its rational entries evaluated. -/
theorem rowEqV2r0E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 2 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((13 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 0 2) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 1 1) +
      ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 2 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 0 2) := by
  have h := rowV2E6 μ u hsupp heig (spinConfig 0 0 0 2)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `1` of the block `ĥ|V_2`, with its rational entries evaluated. -/
theorem rowEqV2r1E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 2 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 0 2) +
      ((13 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 1 1) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 2 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 0 1)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 1 1) := by
  have h := rowV2E6 μ u hsupp heig (spinConfig 0 0 1 1)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `2` of the block `ĥ|V_2`, with its rational entries evaluated. -/
theorem rowEqV2r2E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 2 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 0 2) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 1 1) +
      ((4 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 2 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 1 0) +
      ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 0 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 2 0) := by
  have h := rowV2E6 μ u hsupp heig (spinConfig 0 0 2 0)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `3` of the block `ĥ|V_2`, with its rational entries evaluated. -/
theorem rowEqV2r3E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 2 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 1 1) +
      ((3 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 0 1) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 1 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 0 1)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 0 1) := by
  have h := rowV2E6 μ u hsupp heig (spinConfig 0 1 0 1)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `4` of the block `ĥ|V_2`, with its rational entries evaluated. -/
theorem rowEqV2r4E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 2 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 2 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 0 1) +
      ((5 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 1 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 0 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 1 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 1 0) := by
  have h := rowV2E6 μ u hsupp heig (spinConfig 0 1 1 0)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `5` of the block `ĥ|V_2`, with its rational entries evaluated. -/
theorem rowEqV2r5E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 2 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 2 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 1 0) +
      ((4 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 0 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 0 0) +
      ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 0 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 0 0) := by
  have h := rowV2E6 μ u hsupp heig (spinConfig 0 2 0 0)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `6` of the block `ĥ|V_2`, with its rational entries evaluated. -/
theorem rowEqV2r6E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 2 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 0 1) +
      ((2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 0 1) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 1 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 0 1) := by
  have h := rowV2E6 μ u hsupp heig (spinConfig 1 0 0 1)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `7` of the block `ĥ|V_2`, with its rational entries evaluated. -/
theorem rowEqV2r7E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 2 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 1 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 0 1) +
      ((3 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 1 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 0 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 1 0) := by
  have h := rowV2E6 μ u hsupp heig (spinConfig 1 0 1 0)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `8` of the block `ĥ|V_2`, with its rational entries evaluated. -/
theorem rowEqV2r8E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 2 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 0 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 1 0) +
      ((13 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 0 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 0 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 0 0) := by
  have h := rowV2E6 μ u hsupp heig (spinConfig 1 1 0 0)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `9` of the block `ĥ|V_2`, with its rational entries evaluated. -/
theorem rowEqV2r9E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 2 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 0 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 0 0) +
      ((13 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 0 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 0 0) := by
  have h := rowV2E6 μ u hsupp heig (spinConfig 2 0 0 0)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `0` of the block `ĥ|V_3`, with its rational entries evaluated. -/
theorem rowEqV3r0E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 3 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 1 2) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 2 1) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 0 2)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 1 2) := by
  have h := rowV3E6 μ u hsupp heig (spinConfig 0 0 1 2)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `1` of the block `ĥ|V_3`, with its rational entries evaluated. -/
theorem rowEqV3r1E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 3 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 1 2) +
      ((5 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 2 1) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 1 1) +
      ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 0 1)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 2 1) := by
  have h := rowV3E6 μ u hsupp heig (spinConfig 0 0 2 1)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `2` of the block `ĥ|V_3`, with its rational entries evaluated. -/
theorem rowEqV3r2E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 3 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 1 2) +
      ((7 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 0 2) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 1 1) +
      ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 2 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 0 2)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 0 2) := by
  have h := rowV3E6 μ u hsupp heig (spinConfig 0 1 0 2)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `3` of the block `ĥ|V_3`, with its rational entries evaluated. -/
theorem rowEqV3r3E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 3 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 2 1) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 0 2) +
      ((11 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 1 1) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 2 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 0 1) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 1 1)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 1 1) := by
  have h := rowV3E6 μ u hsupp heig (spinConfig 0 1 1 1)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `4` of the block `ĥ|V_3`, with its rational entries evaluated. -/
theorem rowEqV3r4E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 3 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 0 2) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 1 1) +
      ((7 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 2 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 1 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 2 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 2 0) := by
  have h := rowV3E6 μ u hsupp heig (spinConfig 0 1 2 0)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `5` of the block `ĥ|V_3`, with its rational entries evaluated. -/
theorem rowEqV3r5E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 3 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 2 1) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 1 1) +
      ((5 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 0 1) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 1 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 0 1) +
      ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 0 1)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 0 1) := by
  have h := rowV3E6 μ u hsupp heig (spinConfig 0 2 0 1)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `6` of the block `ĥ|V_3`, with its rational entries evaluated. -/
theorem rowEqV3r6E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 3 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 2 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 0 1) +
      ((7 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 1 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 1 0) +
      ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 1 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 1 0) := by
  have h := rowV3E6 μ u hsupp heig (spinConfig 0 2 1 0)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `7` of the block `ĥ|V_3`, with its rational entries evaluated. -/
theorem rowEqV3r7E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 3 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 0 2) +
      ((5 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 0 2) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 1 1) +
      ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 2 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 0 2) := by
  have h := rowV3E6 μ u hsupp heig (spinConfig 1 0 0 2)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `8` of the block `ĥ|V_3`, with its rational entries evaluated. -/
theorem rowEqV3r8E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 3 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 1 1) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 0 2) +
      ((5 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 1 1) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 2 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 0 1)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 1 1) := by
  have h := rowV3E6 μ u hsupp heig (spinConfig 1 0 1 1)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `9` of the block `ĥ|V_3`, with its rational entries evaluated. -/
theorem rowEqV3r9E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 3 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 2 0) +
      ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 0 2) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 1 1) +
      ((5 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 2 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 1 0) +
      ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 2 0 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 2 0) := by
  have h := rowV3E6 μ u hsupp heig (spinConfig 1 0 2 0)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `10` of the block `ĥ|V_3`, with its rational entries evaluated. -/
theorem rowEqV3r10E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 3 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 0 1) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 1 1) +
      ((5 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 0 1) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 1 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 0 1)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 0 1) := by
  have h := rowV3E6 μ u hsupp heig (spinConfig 1 1 0 1)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `11` of the block `ĥ|V_3`, with its rational entries evaluated. -/
theorem rowEqV3r11E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 3 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 1 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 2 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 0 1) +
      ((11 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 1 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 2 0 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 1 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 1 0) := by
  have h := rowV3E6 μ u hsupp heig (spinConfig 1 1 1 0)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `12` of the block `ĥ|V_3`, with its rational entries evaluated. -/
theorem rowEqV3r12E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 3 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 2 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 1 0) +
      ((5 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 2 0 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 1 0 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 2 0 0) := by
  have h := rowV3E6 μ u hsupp heig (spinConfig 1 2 0 0)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `13` of the block `ĥ|V_3`, with its rational entries evaluated. -/
theorem rowEqV3r13E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 3 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 0 1) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 0 1) +
      ((5 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 0 1) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 1 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 0 1) := by
  have h := rowV3E6 μ u hsupp heig (spinConfig 2 0 0 1)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `14` of the block `ĥ|V_3`, with its rational entries evaluated. -/
theorem rowEqV3r14E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 3 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 1 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 1 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 0 1) +
      ((7 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 1 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 1 0 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 1 0) := by
  have h := rowV3E6 μ u hsupp heig (spinConfig 2 0 1 0)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `15` of the block `ĥ|V_3`, with its rational entries evaluated. -/
theorem rowEqV3r15E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 3 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 2 0 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 1 0) +
      ((2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 1 0 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 1 0 0) := by
  have h := rowV3E6 μ u hsupp heig (spinConfig 2 1 0 0)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `0` of the block `ĥ|V_4`, with its rational entries evaluated. -/
theorem rowEqV4r0E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 4 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((13 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 2 2) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 1 2) +
      ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 0 2)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 2 2) := by
  have h := rowV4E6 μ u hsupp heig (spinConfig 0 0 2 2)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `1` of the block `ĥ|V_4`, with its rational entries evaluated. -/
theorem rowEqV4r1E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 4 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 2 2) +
      ((5 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 1 2) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 2 1) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 0 2) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 1 2)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 1 2) := by
  have h := rowV4E6 μ u hsupp heig (spinConfig 0 1 1 2)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `2` of the block `ĥ|V_4`, with its rational entries evaluated. -/
theorem rowEqV4r2E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 4 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 1 2) +
      ((3 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 2 1) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 1 1) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 2 1)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 2 1) := by
  have h := rowV4E6 μ u hsupp heig (spinConfig 0 1 2 1)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `3` of the block `ĥ|V_4`, with its rational entries evaluated. -/
theorem rowEqV4r3E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 4 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 0 2 2) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 1 2) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 0 2) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 1 1) +
      ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 2 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 0 2) +
      ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 0 2)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 0 2) := by
  have h := rowV4E6 μ u hsupp heig (spinConfig 0 2 0 2)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `4` of the block `ĥ|V_4`, with its rational entries evaluated. -/
theorem rowEqV4r4E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 4 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 2 1) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 0 2) +
      ((4 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 1 1) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 2 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 1 1) +
      ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 1 1)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 1 1) := by
  have h := rowV4E6 μ u hsupp heig (spinConfig 0 2 1 1)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `5` of the block `ĥ|V_4`, with its rational entries evaluated. -/
theorem rowEqV4r5E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 4 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 0 2) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 1 1) +
      ((4 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 2 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 2 0) +
      ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 2 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 2 0) := by
  have h := rowV4E6 μ u hsupp heig (spinConfig 0 2 2 0)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `6` of the block `ĥ|V_4`, with its rational entries evaluated. -/
theorem rowEqV4r6E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 4 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 1 2) +
      ((3 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 1 2) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 2 1) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 0 2)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 1 2) := by
  have h := rowV4E6 μ u hsupp heig (spinConfig 1 0 1 2)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `7` of the block `ĥ|V_4`, with its rational entries evaluated. -/
theorem rowEqV4r7E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 4 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 1 2 1) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 1 2) +
      ((7 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 2 1) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 1 1) +
      ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 2 0 1)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 2 1) := by
  have h := rowV4E6 μ u hsupp heig (spinConfig 1 0 2 1)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `8` of the block `ĥ|V_4`, with its rational entries evaluated. -/
theorem rowEqV4r8E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 4 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 0 2) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 1 2) +
      ((4 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 0 2) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 1 1) +
      ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 2 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 0 2)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 0 2) := by
  have h := rowV4E6 μ u hsupp heig (spinConfig 1 1 0 2)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `9` of the block `ĥ|V_4`, with its rational entries evaluated. -/
theorem rowEqV4r9E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 4 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 1 1) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 2 1) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 0 2) +
      ((2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 1 1) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 2 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 2 0 1) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 1 1)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 1 1) := by
  have h := rowV4E6 μ u hsupp heig (spinConfig 1 1 1 1)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `10` of the block `ĥ|V_4`, with its rational entries evaluated. -/
theorem rowEqV4r10E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 4 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 2 0) +
      ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 0 2) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 1 1) +
      ((4 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 2 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 2 1 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 2 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 2 0) := by
  have h := rowV4E6 μ u hsupp heig (spinConfig 1 1 2 0)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `11` of the block `ĥ|V_4`, with its rational entries evaluated. -/
theorem rowEqV4r11E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 4 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 0 2 1) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 1 1) +
      ((7 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 2 0 1) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 2 1 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 1 0 1)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 2 0 1) := by
  have h := rowV4E6 μ u hsupp heig (spinConfig 1 2 0 1)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `12` of the block `ĥ|V_4`, with its rational entries evaluated. -/
theorem rowEqV4r12E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 4 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 2 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 2 0 1) +
      ((3 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 2 1 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 1 1 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 2 1 0) := by
  have h := rowV4E6 μ u hsupp heig (spinConfig 1 2 1 0)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `13` of the block `ĥ|V_4`, with its rational entries evaluated. -/
theorem rowEqV4r13E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 4 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 0 2) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 0 2) +
      ((4 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 0 2) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 1 1) +
      ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 2 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 0 2) := by
  have h := rowV4E6 μ u hsupp heig (spinConfig 2 0 0 2)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `14` of the block `ĥ|V_4`, with its rational entries evaluated. -/
theorem rowEqV4r14E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 4 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 1 1) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 1 1) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 0 2) +
      ((4 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 1 1) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 2 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 1 0 1)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 1 1) := by
  have h := rowV4E6 μ u hsupp heig (spinConfig 2 0 1 1)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `15` of the block `ĥ|V_4`, with its rational entries evaluated. -/
theorem rowEqV4r15E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 4 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 0 2 2 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 1 2 0) +
      ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 0 2) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 1 1) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 2 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 1 1 0) +
      ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 2 0 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 2 0) := by
  have h := rowV4E6 μ u hsupp heig (spinConfig 2 0 2 0)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `16` of the block `ĥ|V_4`, with its rational entries evaluated. -/
theorem rowEqV4r16E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 4 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 2 0 1) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 1 1) +
      ((3 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 1 0 1) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 1 1 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 1 0 1) := by
  have h := rowV4E6 μ u hsupp heig (spinConfig 2 1 0 1)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `17` of the block `ĥ|V_4`, with its rational entries evaluated. -/
theorem rowEqV4r17E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 4 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 1 2 1 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 2 0) +
      ((1 / 2 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 1 0 1) +
      ((5 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 1 1 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 2 0 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 1 1 0) := by
  have h := rowV4E6 μ u hsupp heig (spinConfig 2 1 1 0)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

/-- Row `18` of the block `ĥ|V_4`, with its rational entries evaluated. -/
theorem rowEqV4r18E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 4 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) :
    ((1 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 0 2 0) +
      ((1 / 3 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 1 1 0) +
      ((13 / 6 : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 2 0 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u (spinConfig 2 2 0 0) := by
  have h := rowV4E6 μ u hsupp heig (spinConfig 2 2 0 0)
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry,
    spinConfig0E6, spinConfig1E6, spinConfig2E6, spinConfig3E6, finVal0E6, finVal1E6,
    finVal2E6, fin3EqIffE6] at h ⊢
  linear_combination h

end LatticeSystem.Quantum.AKLTSl2BlockDischargeE6
