import LatticeSystem.Quantum.SpinS.AKLTKnabe.BlockDischargeE6d

/-!
# Gate E6 (capstone): discharging the highest-weight blocks and the unconditional window

Capstone of the Gate E6 landing (Issue #5094, Tasaki §7.1.4).  Sections 8-9:
discharging `KnabeBlockBoundE5 1..4` and the unconditional capstone
`akltWindow3HKnabePosSemidefE6`.  Imports `BlockDischargeE6d`, the tip of the E6a-E6d chain.
-/

namespace LatticeSystem.Quantum.AKLTSl2BlockDischargeE6

open LatticeSystem.Quantum
open LatticeSystem.Quantum.AKLTSl2SubmoduleProbeE2
open LatticeSystem.Quantum.AKLTSl2LadderSectorsE3
open LatticeSystem.Quantum.AKLTSl2WindowReductionE4
open LatticeSystem.Quantum.AKLTSl2HighestWeightBoundE5
open LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential
open scoped ComplexOrder

/-! ## 8. Discharging `KnabeBlockBoundE5 1` and `KnabeBlockBoundE5 2` -/

/-- **Gate E6, block `k = 1`, discharged.**  Every eigenvalue of the open three-bond AKLT
window `ĥ` on the highest-weight space `hw_1` satisfies `0 ≤ μ² − (2/5) μ`, because it is
already an eigenvalue on the ambient magnetisation sector `V_1` (of dimension 4), where
the *linear* bound `ĥ ≥ 2/5` holds (`quadV1E6`).  Tasaki §7.1.4, pp. 188–190;
Knabe 1988. -/
theorem knabeBlockBoundE5One : KnabeBlockBoundE5 1 := by
  intro μ u hu hu0 heig
  have huV : u ∈ magSectorE2 (Fin 4) 2 1 := (Submodule.mem_inf.mp hu).1
  have hsupp := (mem_magSectorE3_iff (Fin 4) 2 1 u).mp huV
  have e0 := rowEqV1r0E6 μ u hsupp heig
  have e1 := rowEqV1r1E6 μ u hsupp heig
  have e2 := rowEqV1r2E6 μ u hsupp heig
  have e3 := rowEqV1r3E6 μ u hsupp heig
  have hex : ∃ σ : SpinConfig, WithLp.ofLp u σ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hu0 (WithLp.ofLp_injective 2 (funext fun σ => ?_))
    rw [hcon σ]
    rfl
  obtain ⟨σ, hσ⟩ := hex
  have hσk : magSumS σ = 1 := by
    by_contra hc
    exact hσ (hsupp σ hc)
  have hne : WithLp.ofLp u (spinConfig 0 0 0 1) ≠ 0 ∨ WithLp.ofLp u (spinConfig 0 0 1 0) ≠ 0 ∨
      WithLp.ofLp u (spinConfig 0 1 0 0) ≠ 0 ∨ WithLp.ofLp u (spinConfig 1 0 0 0) ≠ 0 := by
    rcases eqOfMagSumSOneE6 σ hσk with h | h | h | h
    · rw [h] at hσ
      exact Or.inl hσ
    · rw [h] at hσ
      exact Or.inr (Or.inl hσ)
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inl hσ))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (hσ)))
  have hμ := blockBoundV1E6 μ _ _ _ _ e0 e1 e2 e3 hne
  nlinarith [hμ]

/-- **Gate E6, block `k = 2`, discharged.**  Every eigenvalue of the open three-bond AKLT
window `ĥ` on the highest-weight space `hw_2` satisfies `0 ≤ μ² − (2/5) μ`, because it is
already an eigenvalue on the ambient magnetisation sector `V_2` (of dimension 10), where
the *linear* bound `ĥ ≥ 2/5` holds (`quadV2E6`).  Tasaki §7.1.4, pp. 188–190;
Knabe 1988. -/
theorem knabeBlockBoundE5Two : KnabeBlockBoundE5 2 := by
  intro μ u hu hu0 heig
  have huV : u ∈ magSectorE2 (Fin 4) 2 2 := (Submodule.mem_inf.mp hu).1
  have hsupp := (mem_magSectorE3_iff (Fin 4) 2 2 u).mp huV
  have e0 := rowEqV2r0E6 μ u hsupp heig
  have e1 := rowEqV2r1E6 μ u hsupp heig
  have e2 := rowEqV2r2E6 μ u hsupp heig
  have e3 := rowEqV2r3E6 μ u hsupp heig
  have e4 := rowEqV2r4E6 μ u hsupp heig
  have e5 := rowEqV2r5E6 μ u hsupp heig
  have e6 := rowEqV2r6E6 μ u hsupp heig
  have e7 := rowEqV2r7E6 μ u hsupp heig
  have e8 := rowEqV2r8E6 μ u hsupp heig
  have e9 := rowEqV2r9E6 μ u hsupp heig
  have hex : ∃ σ : SpinConfig, WithLp.ofLp u σ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hu0 (WithLp.ofLp_injective 2 (funext fun σ => ?_))
    rw [hcon σ]
    rfl
  obtain ⟨σ, hσ⟩ := hex
  have hσk : magSumS σ = 2 := by
    by_contra hc
    exact hσ (hsupp σ hc)
  have hne : WithLp.ofLp u (spinConfig 0 0 0 2) ≠ 0 ∨ WithLp.ofLp u (spinConfig 0 0 1 1) ≠ 0 ∨
      WithLp.ofLp u (spinConfig 0 0 2 0) ≠ 0 ∨ WithLp.ofLp u (spinConfig 0 1 0 1) ≠ 0 ∨
      WithLp.ofLp u (spinConfig 0 1 1 0) ≠ 0 ∨ WithLp.ofLp u (spinConfig 0 2 0 0) ≠ 0 ∨
      WithLp.ofLp u (spinConfig 1 0 0 1) ≠ 0 ∨ WithLp.ofLp u (spinConfig 1 0 1 0) ≠ 0 ∨
      WithLp.ofLp u (spinConfig 1 1 0 0) ≠ 0 ∨ WithLp.ofLp u (spinConfig 2 0 0 0) ≠ 0 := by
    rcases eqOfMagSumSTwoE6 σ hσk with h | h | h | h | h | h | h | h | h | h
    · rw [h] at hσ
      exact Or.inl hσ
    · rw [h] at hσ
      exact Or.inr (Or.inl hσ)
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inl hσ))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inl hσ)))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hσ))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hσ)))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hσ))))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hσ)))))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hσ))))))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hσ)))))))))
  have hμ := blockBoundV2E6 μ _ _ _ _ _ _ _ _ _ _ e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 hne
  nlinarith [hμ]

/-- **Gate E6, block `k = 3`, discharged.**  Every eigenvalue of the open three-bond AKLT
window `ĥ` on the highest-weight space `hw_3` satisfies `0 ≤ μ² − (2/5) μ`, because it is
already an eigenvalue on the ambient magnetisation sector `V_3` (of dimension 16), where
the Knabe quadratic form `ĥ² − (2/5) ĥ` is positive semidefinite (`quad2V3E6`); the
sector carries the AKLT zero modes, so the linear bound is unavailable there.
Tasaki §7.1.4, pp. 188–190;
Knabe 1988. -/
theorem knabeBlockBoundE5Three : KnabeBlockBoundE5 3 := by
  intro μ u hu hu0 heig
  have huV : u ∈ magSectorE2 (Fin 4) 2 3 := (Submodule.mem_inf.mp hu).1
  have hsupp := (mem_magSectorE3_iff (Fin 4) 2 3 u).mp huV
  have e0 := rowEqV3r0E6 μ u hsupp heig
  have e1 := rowEqV3r1E6 μ u hsupp heig
  have e2 := rowEqV3r2E6 μ u hsupp heig
  have e3 := rowEqV3r3E6 μ u hsupp heig
  have e4 := rowEqV3r4E6 μ u hsupp heig
  have e5 := rowEqV3r5E6 μ u hsupp heig
  have e6 := rowEqV3r6E6 μ u hsupp heig
  have e7 := rowEqV3r7E6 μ u hsupp heig
  have e8 := rowEqV3r8E6 μ u hsupp heig
  have e9 := rowEqV3r9E6 μ u hsupp heig
  have e10 := rowEqV3r10E6 μ u hsupp heig
  have e11 := rowEqV3r11E6 μ u hsupp heig
  have e12 := rowEqV3r12E6 μ u hsupp heig
  have e13 := rowEqV3r13E6 μ u hsupp heig
  have e14 := rowEqV3r14E6 μ u hsupp heig
  have e15 := rowEqV3r15E6 μ u hsupp heig
  have hex : ∃ σ : SpinConfig, WithLp.ofLp u σ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hu0 (WithLp.ofLp_injective 2 (funext fun σ => ?_))
    rw [hcon σ]
    rfl
  obtain ⟨σ, hσ⟩ := hex
  have hσk : magSumS σ = 3 := by
    by_contra hc
    exact hσ (hsupp σ hc)
  have hne : WithLp.ofLp u (spinConfig 0 0 1 2) ≠ 0 ∨ WithLp.ofLp u (spinConfig 0 0 2 1) ≠ 0 ∨
      WithLp.ofLp u (spinConfig 0 1 0 2) ≠ 0 ∨ WithLp.ofLp u (spinConfig 0 1 1 1) ≠ 0 ∨
      WithLp.ofLp u (spinConfig 0 1 2 0) ≠ 0 ∨ WithLp.ofLp u (spinConfig 0 2 0 1) ≠ 0 ∨
      WithLp.ofLp u (spinConfig 0 2 1 0) ≠ 0 ∨ WithLp.ofLp u (spinConfig 1 0 0 2) ≠ 0 ∨
      WithLp.ofLp u (spinConfig 1 0 1 1) ≠ 0 ∨ WithLp.ofLp u (spinConfig 1 0 2 0) ≠ 0 ∨
      WithLp.ofLp u (spinConfig 1 1 0 1) ≠ 0 ∨ WithLp.ofLp u (spinConfig 1 1 1 0) ≠ 0 ∨
      WithLp.ofLp u (spinConfig 1 2 0 0) ≠ 0 ∨ WithLp.ofLp u (spinConfig 2 0 0 1) ≠ 0 ∨
      WithLp.ofLp u (spinConfig 2 0 1 0) ≠ 0 ∨ WithLp.ofLp u (spinConfig 2 1 0 0) ≠ 0 := by
    rcases eqOfMagSumSThreeE6 σ hσk with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
        | h
    · rw [h] at hσ
      exact Or.inl hσ
    · rw [h] at hσ
      exact Or.inr (Or.inl hσ)
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inl hσ))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inl hσ)))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hσ))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hσ)))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hσ))))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hσ)))))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hσ))))))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          hσ)))))))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          hσ))))))))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl hσ)))))))))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl hσ))))))))))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl hσ)))))))))))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inl hσ))))))))))))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (hσ)))))))))))))))
  exact blockBound2V3E6 μ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
    e12 e13 e14 e15 hne

/-- **Gate E6, block `k = 4`, discharged.**  Every eigenvalue of the open three-bond AKLT
window `ĥ` on the highest-weight space `hw_4` satisfies `0 ≤ μ² − (2/5) μ`, because it is
already an eigenvalue on the ambient magnetisation sector `V_4` (of dimension 19), where
the Knabe quadratic form `ĥ² − (2/5) ĥ` is positive semidefinite (`quad2V4E6`); the
sector carries the AKLT zero modes, so the linear bound is unavailable there.
Tasaki §7.1.4, pp. 188–190;
Knabe 1988. -/
theorem knabeBlockBoundE5Four : KnabeBlockBoundE5 4 := by
  intro μ u hu hu0 heig
  have huV : u ∈ magSectorE2 (Fin 4) 2 4 := (Submodule.mem_inf.mp hu).1
  have hsupp := (mem_magSectorE3_iff (Fin 4) 2 4 u).mp huV
  have e0 := rowEqV4r0E6 μ u hsupp heig
  have e1 := rowEqV4r1E6 μ u hsupp heig
  have e2 := rowEqV4r2E6 μ u hsupp heig
  have e3 := rowEqV4r3E6 μ u hsupp heig
  have e4 := rowEqV4r4E6 μ u hsupp heig
  have e5 := rowEqV4r5E6 μ u hsupp heig
  have e6 := rowEqV4r6E6 μ u hsupp heig
  have e7 := rowEqV4r7E6 μ u hsupp heig
  have e8 := rowEqV4r8E6 μ u hsupp heig
  have e9 := rowEqV4r9E6 μ u hsupp heig
  have e10 := rowEqV4r10E6 μ u hsupp heig
  have e11 := rowEqV4r11E6 μ u hsupp heig
  have e12 := rowEqV4r12E6 μ u hsupp heig
  have e13 := rowEqV4r13E6 μ u hsupp heig
  have e14 := rowEqV4r14E6 μ u hsupp heig
  have e15 := rowEqV4r15E6 μ u hsupp heig
  have e16 := rowEqV4r16E6 μ u hsupp heig
  have e17 := rowEqV4r17E6 μ u hsupp heig
  have e18 := rowEqV4r18E6 μ u hsupp heig
  have hex : ∃ σ : SpinConfig, WithLp.ofLp u σ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hu0 (WithLp.ofLp_injective 2 (funext fun σ => ?_))
    rw [hcon σ]
    rfl
  obtain ⟨σ, hσ⟩ := hex
  have hσk : magSumS σ = 4 := by
    by_contra hc
    exact hσ (hsupp σ hc)
  have hne : WithLp.ofLp u (spinConfig 0 0 2 2) ≠ 0 ∨ WithLp.ofLp u (spinConfig 0 1 1 2) ≠ 0 ∨
      WithLp.ofLp u (spinConfig 0 1 2 1) ≠ 0 ∨ WithLp.ofLp u (spinConfig 0 2 0 2) ≠ 0 ∨
      WithLp.ofLp u (spinConfig 0 2 1 1) ≠ 0 ∨ WithLp.ofLp u (spinConfig 0 2 2 0) ≠ 0 ∨
      WithLp.ofLp u (spinConfig 1 0 1 2) ≠ 0 ∨ WithLp.ofLp u (spinConfig 1 0 2 1) ≠ 0 ∨
      WithLp.ofLp u (spinConfig 1 1 0 2) ≠ 0 ∨ WithLp.ofLp u (spinConfig 1 1 1 1) ≠ 0 ∨
      WithLp.ofLp u (spinConfig 1 1 2 0) ≠ 0 ∨ WithLp.ofLp u (spinConfig 1 2 0 1) ≠ 0 ∨
      WithLp.ofLp u (spinConfig 1 2 1 0) ≠ 0 ∨ WithLp.ofLp u (spinConfig 2 0 0 2) ≠ 0 ∨
      WithLp.ofLp u (spinConfig 2 0 1 1) ≠ 0 ∨ WithLp.ofLp u (spinConfig 2 0 2 0) ≠ 0 ∨
      WithLp.ofLp u (spinConfig 2 1 0 1) ≠ 0 ∨ WithLp.ofLp u (spinConfig 2 1 1 0) ≠ 0 ∨
      WithLp.ofLp u (spinConfig 2 2 0 0) ≠ 0 := by
    rcases eqOfMagSumSFourE6 σ hσk with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
        | h | h | h | h
    · rw [h] at hσ
      exact Or.inl hσ
    · rw [h] at hσ
      exact Or.inr (Or.inl hσ)
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inl hσ))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inl hσ)))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hσ))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hσ)))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hσ))))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hσ)))))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hσ))))))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          hσ)))))))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          hσ))))))))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl hσ)))))))))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl hσ))))))))))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl hσ)))))))))))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inl hσ))))))))))))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hσ)))))))))))))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hσ))))))))))))))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hσ)))))))))))))))))
    · rw [h] at hσ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hσ))))))))))))))))))
  exact blockBound2V4E6 μ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
    e11 e12 e13 e14 e15 e16 e17 e18 hne

/-! ## 9. The unconditional capstone -/

/-- **Gate E6 capstone (unconditional).**  The Knabe window inequality

  `ĥ² − (2/5) ĥ ≥ 0`,  i.e.  `ε₃ ≥ 2/5`,

for the open three-bond window `ĥ = P̂₀₁ + P̂₁₂ + P̂₂₃` of Tasaki eq. (7.1.30) with `ℓ = 3`
(pp. 188–190; Knabe 1988).  All five highest-weight blocks are now supplied: `k = 0` by the Gate
E5 lemma `knabeBlockBoundE5_zero`, and `k = 1, 2, 3, 4` by the four sector bounds of this file.

The statement is *verbatim* the one of `akltWindow3H_knabe_posSemidef`, whose current proof goes
through the `81 × 81` rational certificate; this route replaces that certificate by the `sl₂`
reduction of Gates E1b–E5 together with five exact `LDLᵀ` certificates on the magnetisation
sectors, and uses no numerical table. -/
theorem akltWindow3HKnabePosSemidefE6 :
    Matrix.PosSemidef (akltWindow3H * akltWindow3H - ((2 : ℂ) / 5) • akltWindow3H) :=
  akltWindow3H_knabe_posSemidefE5 knabeBlockBoundE5One knabeBlockBoundE5Two
    knabeBlockBoundE5Three knabeBlockBoundE5Four

end LatticeSystem.Quantum.AKLTSl2BlockDischargeE6
