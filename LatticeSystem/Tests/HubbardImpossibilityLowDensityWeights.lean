import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardFerromagnetismStructure
import LatticeSystem.Fermion.JordanWigner.Hubbard.SaturatedFerromagnetism
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJAllUpProperties
import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaGroundStateCore

/-!
# Test coverage for Theorem 11.4 PR-7a (general-filling weight machinery)

Continues the numbering of `LatticeSystem.Tests.HubbardImpossibilityLowDensity` (Red 1–31) and
`LatticeSystem.Tests.HubbardImpossibilityLowDensityRoth` (Red 32–41) in a sibling module, per the
PR-6 precedent: the first module is already past the 700-line review trigger.

The three checks pin the `Ŝ³`-weight machinery of `hubbardEigenspaceAt` and the `SU(2)`
raising-chain existence lemma `exists_topWeight_of_maxSpin`:

- **Red 42** — the generalisation guard: `mem_hubbardEigenspaceAt` and
  `fermionTotalSpinZ_mulVec_mem_hubbardEigenspaceAt` at a filling `Ne` that is *not* `N + 1`, so a
  proof that silently kept the half filling hard-coded cannot typecheck against it.
- **Red 43** — the consumption guard for `exists_topWeight_of_maxSpin`, at a fixture (again a
  filling that is not `N + 1`) at which both of its hypotheses are *proved* rather than posited:
  the returned vector carries the top weight `+S`.
- **Red 44** — a standalone sharpness counterexample for the strict-weight hypothesis of
  `fermionTotalSpinPlus_mulVec_ne_zero_of_maxSpin`; it references none of the generalised names and
  says nothing about the filling.
-/

namespace LatticeSystem.Tests.HubbardImpossibilityLowDensityWeights

open LatticeSystem.Fermion
open LatticeSystem.Quantum

/-- **Red 42 (generalisation guard: the weight machinery at a filling `Ne ≠ N + 1`).** At
`N := 1`, `Ne := 1` (so `Ne ≠ N + 1 = 2`), the generalised membership lemma
`mem_hubbardEigenspaceAt` and the generalised `Ŝ³`-invariance lemma
`fermionTotalSpinZ_mulVec_mem_hubbardEigenspaceAt` must hold at the *stated* filling `Ne`, not at a
silently retained `N + 1`. A generalisation that dropped `Ne` and kept `N + 1` hard-coded would
fail to typecheck against this statement (the ambient type `Fin 4 → Fin 2 → ℂ` fixes `N = 1`, and
`Ne := 1 ≠ 2`). -/
example {v : (Fin 4 → Fin 2) → ℂ} {E₀ : ℂ}
    (hv : v ∈ hubbardEigenspaceAt (0 : Matrix (Fin 2) (Fin 2) ℂ) (0 : ℂ) E₀ 1) :
    (hubbardHamiltonian 1 0 0).mulVec v = E₀ • v ∧
      (fermionTotalNumber 3).mulVec v = ((1 : ℕ) : ℂ) • v ∧
      (fermionTotalSpinZ 1).mulVec v ∈
        hubbardEigenspaceAt (0 : Matrix (Fin 2) (Fin 2) ℂ) (0 : ℂ) E₀ 1 := by
  obtain ⟨hH, hN⟩ := (mem_hubbardEigenspaceAt (0 : Matrix (Fin 2) (Fin 2) ℂ) (0 : ℂ)).mp hv
  exact ⟨hH, hN,
    fermionTotalSpinZ_mulVec_mem_hubbardEigenspaceAt (0 : Matrix (Fin 2) (Fin 2) ℂ) (0 : ℂ) hv⟩

/-- **Red 43 (`exists_topWeight_of_maxSpin`: the returned vector carries the top weight `+S`).**
At `t := 0`, `U := 0`, `N := 1`, `E₀ := 0`, `Ne := 1` — again a filling that is not `N + 1`, so
`S = Ne/2 = 1/2` — both hypotheses of the lemma are *discharged* here instead of posited, which is
what keeps the check from being vacuous:

* `hne` by exhibiting a single ↑ electron on site `0`: the fixture Hamiltonian vanishes, so that
  basis vector is an `E₀ = 0` eigenvector in the one-electron sector;
* `hferro` because a one-electron sector is a spin-`1/2` doublet: each of the two `Ŝ³`-weight
  blocks `∓1/2` of the eigenspace is annihilated by the ladder operator that would carry it off the
  `Ne = 1` weight grid (`hubbardEigenspaceAt_inf_eigenspace_eq_bot`), which pins its Casimir
  eigenvalue to `S(S+1) = 3/4`.

The conclusion then guards that the returned `u` satisfies `Ŝ³u = (1/2)u`, i.e. the weight `+S`
and not some other weight of the multiplet. What it does *not* guard is where the lemma's internal
raising induction starts: the hypotheses `hferro`/`hne` speak about the eigenspace as a whole and
say nothing about individual weight blocks, so no fixture can force the chain to run a prescribed
number of steps. -/
example :
    ∃ u, u ∈ hubbardEigenspaceAt (0 : Matrix (Fin 2) (Fin 2) ℂ) (0 : ℂ) (0 : ℂ) 1 ∧ u ≠ 0 ∧
      (fermionTotalSpinZ 1).mulVec u = ((1 / 2 : ℝ) : ℂ) • u := by
  have hH0 : hubbardHamiltonian 1 (0 : Matrix (Fin 2) (Fin 2) ℂ) (0 : ℂ) = 0 := by
    simp [hubbardHamiltonian, hubbardKinetic, hubbardOnSiteInteraction]
  -- non-vacuity: one ↑ electron on site `0`
  have hne : hubbardEigenspaceAt (0 : Matrix (Fin 2) (Fin 2) ℂ) (0 : ℂ) (0 : ℂ) 1 ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    refine ⟨basisVec (fun j : Fin (2 * 1 + 2) => if j.val = 0 then (1 : Fin 2) else 0), ?_, ?_⟩
    · rw [mem_hubbardEigenspaceAt]
      refine ⟨by rw [hH0, Matrix.zero_mulVec, zero_smul], ?_⟩
      rw [fermionTotalNumber_mulVec_basisVec, ← Nat.cast_sum]
      exact congrArg (fun n : ℕ => (n : ℂ) • _) (by decide)
    · intro hzero
      have h1 := congrFun hzero (fun j : Fin (2 * 1 + 2) => if j.val = 0 then (1 : Fin 2) else 0)
      rw [basisVec_self, Pi.zero_apply] at h1
      exact one_ne_zero h1
  -- maximal spin: the one-electron sector is a spin-`1/2` doublet
  have hJ : ∀ i j : Fin (1 + 1),
      star ((0 : Matrix (Fin 2) (Fin 2) ℂ) i j) = (0 : Matrix (Fin 2) (Fin 2) ℂ) j i := by
    intro i j; simp
  have hblock : ∀ (a : Fin (1 + 1)) (w : (Fin (2 * 1 + 2) → Fin 2) → ℂ),
      w ∈ hubbardEigenspaceAt (0 : Matrix (Fin 2) (Fin 2) ℂ) (0 : ℂ) (0 : ℂ) 1 ⊓
        Module.End.eigenspace (fermionTotalSpinZ 1).mulVecLin
          (((a : ℝ) - ((1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) →
      (fermionTotalSpinSquared 1).mulVec w = ((3 : ℂ) / 4) • w := by
    intro a w hw
    obtain ⟨hwG, hwZ⟩ := Submodule.mem_inf.mp hw
    rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hwZ
    fin_cases a
    · -- lowest weight `−1/2`: `Ŝ⁻w` would sit at the off-grid weight `−3/2`, hence vanishes
      have hwZ' : (fermionTotalSpinZ 1).mulVec w = ((-(1 / 2) : ℝ) : ℂ) • w := by
        rw [hwZ]; norm_num
      have hminus : (fermionTotalSpinMinus 1).mulVec w = 0 := by
        have hoff : ∀ b : Fin (1 + 1),
            ((-(3 / 2) : ℝ) : ℂ) ≠ (((b : ℝ) - ((1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) := by
          intro b hcon
          rw [Complex.ofReal_inj, Nat.cast_one] at hcon
          have hb : (0 : ℝ) ≤ ((b : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith
        have hmem : (fermionTotalSpinMinus 1).mulVec w ∈
            hubbardEigenspaceAt (0 : Matrix (Fin 2) (Fin 2) ℂ) (0 : ℂ) (0 : ℂ) 1 ⊓
              Module.End.eigenspace (fermionTotalSpinZ 1).mulVecLin ((-(3 / 2) : ℝ) : ℂ) := by
          refine Submodule.mem_inf.mpr
            ⟨fermionTotalSpinMinus_mulVec_mem_hubbardEigenspaceAt _ _ hJ (star_zero ℂ) hwG, ?_⟩
          rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
          have h := fermionTotalSpinZ_mulVec_spinMinusPow_general 1 w ((-(1 / 2) : ℝ) : ℂ) 1 hwZ'
          rw [pow_one] at h
          rw [h]
          norm_num
        rw [hubbardEigenspaceAt_inf_eigenspace_eq_bot _ _ 1 _ hoff, Submodule.mem_bot] at hmem
        exact hmem
      have hMP : fermionTotalSpinMinus 1 * fermionTotalSpinPlus 1
          = fermionTotalSpinPlus 1 * fermionTotalSpinMinus 1 - (2 : ℂ) • fermionTotalSpinZ 1 := by
        have h := fermionTotalSpinPlus_commutator_fermionTotalSpinMinus 1
        rw [← h]; abel
      have hexp : (fermionTotalSpinSquared 1).mulVec w
          = (fermionTotalSpinPlus 1).mulVec ((fermionTotalSpinMinus 1).mulVec w)
            - (2 : ℂ) • ((fermionTotalSpinZ 1).mulVec w)
            + (fermionTotalSpinZ 1).mulVec ((fermionTotalSpinZ 1).mulVec w + w) := by
        unfold fermionTotalSpinSquared
        rw [hMP, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
          ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
      rw [hexp, hminus, Matrix.mulVec_zero, Matrix.mulVec_add, hwZ', Matrix.mulVec_smul, hwZ']
      push_cast
      module
    · -- top weight `+1/2`: `Ŝ⁺w` would sit at the off-grid weight `+3/2`, hence vanishes
      have hwZ' : (fermionTotalSpinZ 1).mulVec w = ((1 / 2 : ℝ) : ℂ) • w := by
        rw [hwZ]; norm_num
      have hplus : (fermionTotalSpinPlus 1).mulVec w = 0 := by
        have hoff : ∀ b : Fin (1 + 1),
            (((3 / 2 : ℝ)) : ℂ) ≠ (((b : ℝ) - ((1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) := by
          intro b hcon
          rw [Complex.ofReal_inj, Nat.cast_one] at hcon
          have hb : ((b : ℕ) : ℝ) ≤ 1 := by
            exact_mod_cast Nat.lt_succ_iff.mp b.isLt
          linarith
        have hmem : (fermionTotalSpinPlus 1).mulVec w ∈
            hubbardEigenspaceAt (0 : Matrix (Fin 2) (Fin 2) ℂ) (0 : ℂ) (0 : ℂ) 1 ⊓
              Module.End.eigenspace (fermionTotalSpinZ 1).mulVecLin (((3 / 2 : ℝ)) : ℂ) := by
          refine Submodule.mem_inf.mpr
            ⟨fermionTotalSpinPlus_mulVec_mem_hubbardEigenspaceAt _ _ hwG, ?_⟩
          rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply,
            show (((3 / 2 : ℝ)) : ℂ) = (((1 / 2 : ℝ) + 1 : ℝ) : ℂ) from by norm_num]
          exact fermionTotalSpinZ_mulVec_fermionTotalSpinPlus_mulVec 1 (1 / 2 : ℝ) hwZ'
        rw [hubbardEigenspaceAt_inf_eigenspace_eq_bot _ _ 1 _ hoff, Submodule.mem_bot] at hmem
        exact hmem
      rw [fermionTotalSpinSquared_mulVec_of_isTop_general 1 w ((1 / 2 : ℝ) : ℂ) hplus hwZ']
      push_cast
      norm_num
  have hferro : ∀ v ∈ hubbardEigenspaceAt (0 : Matrix (Fin 2) (Fin 2) ℂ) (0 : ℂ) (0 : ℂ) 1,
      (fermionTotalSpinSquared 1).mulVec v
        = (((1 : ℕ) : ℂ) / 2 * (((1 : ℕ) : ℂ) / 2 + 1)) • v := by
    have hle : hubbardEigenspaceAt (0 : Matrix (Fin 2) (Fin 2) ℂ) (0 : ℂ) (0 : ℂ) 1
        ≤ Module.End.eigenspace (fermionTotalSpinSquared 1).mulVecLin ((3 : ℂ) / 4) := by
      conv_lhs => rw [hubbardEigenspaceAt_eq_iSup_weight]
      refine iSup_le (fun a => ?_)
      intro w hw
      rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
      exact hblock a w hw
    intro v hv
    have h := hle hv
    rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at h
    rw [h]
    norm_num
  obtain ⟨u, hu1, hu2, hu3⟩ :=
    exists_topWeight_of_maxSpin (0 : Matrix (Fin 2) (Fin 2) ℂ) (0 : ℂ) 1 hferro hne
  refine ⟨u, hu1, hu2, ?_⟩
  rw [hu3]
  norm_num

/-- **Red 44 (sharpness of `sz < S`: a top-weight vector is annihilated by `Ŝ⁺`).** Standalone,
referencing none of the generalised lemma's names, mirroring the PR-5 Red 22 / PR-5b Red 30
discipline. At `N := 0` (`S := (N + 1)/2 = 1/2`), the all-up state `|↑⟩` satisfies both the `Ŝ³`
weight and the `(Ŝ_tot)²` max-spin hypotheses that
`fermionTotalSpinPlus_mulVec_ne_zero_of_maxSpin` needs, at exactly `sz = S` (the boundary the
hypothesis `hhigh : sz < S` excludes), and yet `Ŝ⁺ |↑⟩ = 0`. So the conclusion `Ŝ⁺ v ≠ 0` genuinely
fails once `sz < S` is weakened to `sz ≤ S`: `hhigh` is load-bearing, not decoration. -/
example :
    hubbardAllUpState 0 ≠ 0 ∧
      (fermionTotalSpinZ 0).mulVec (hubbardAllUpState 0) =
        (((0 + 1 : ℕ) : ℂ) / 2) • hubbardAllUpState 0 ∧
      (fermionTotalSpinSquared 0).mulVec (hubbardAllUpState 0) =
        (((0 + 1 : ℕ) : ℂ) / 2 * (((0 + 1 : ℕ) : ℂ) / 2 + 1)) • hubbardAllUpState 0 ∧
      (fermionTotalSpinPlus 0).mulVec (hubbardAllUpState 0) = 0 :=
  ⟨hubbardAllUpState_ne_zero 0, fermionTotalSpinZ_mulVec_allUpState 0,
    fermionTotalSpinSquared_mulVec_allUpState 0, fermionTotalSpinPlus_mulVec_allUpState 0⟩

end LatticeSystem.Tests.HubbardImpossibilityLowDensityWeights
