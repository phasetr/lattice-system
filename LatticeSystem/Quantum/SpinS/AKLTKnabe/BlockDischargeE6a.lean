import LatticeSystem.Quantum.SpinS.AKLTKnabe.HighestWeightBoundE5

/-!
# Gate E6 (part a): discharging the highest-weight blocks `k = 1` and `k = 2`

This module (Issue #5094; Tasaki §7.1.4, Knabe's argument, pp. 188–190) is part a of the Gate E6
landing (sections 1-3).
It removes **all four** hypotheses of the Gate E5 conditional capstone
`akltWindow3H_knabe_posSemidefE5`, i.e. the block bounds `KnabeBlockBoundE5 k` for `k = 1, 2, 3,
    4`,
so that the Knabe window inequality is obtained unconditionally.

The simplification found at Gate E5 (report §4) is exploited in a stronger form: for `k ≤ 2` the
*linear* form `ĥ − (2/5)` is already positive semidefinite on the **whole magnetisation sector**
`V_k`, not merely on the highest-weight subspace `hw_k ⊆ V_k`.  Consequently

* **no highest-weight basis and no span argument are needed** for any `k`: the eigenvector `u` is
  only used through its `dim V_k` components (`4, 10, 16, 19`), and the highest-weight hypothesis
  `Ŝ⁺_tot u = 0` is never used;
* **the square `ĥ²` is needed only for `k = 3, 4`**, where the sector carries zero modes.

The chain is:

1. *enumeration* — the configurations `σ : Fin 4 → Fin 3` with `magSumS σ = k` are listed for
   `k = 1, 2` (`4` and `10` of them), by `omega` on `(σ 0).val + (σ 1).val + (σ 2).val + (σ
       3).val`;
2. *restriction* — the eigenvalue equation `ĥ u = μ u`, read componentwise, becomes a linear
    system
   in those `4` (resp. `10`) components, because `u` is supported on the sector;
3. *real and imaginary parts* — the block is a real symmetric rational matrix, so the complex
   system splits into two copies of the same real system;
4. *the sector certificate* — the exact `LDLᵀ` decomposition of `ĥ|V_k − (2/5) I` (all pivots
   strictly positive) is transcribed as a sum-of-squares identity proved by `ring`, giving
   `⟪w, ĥ w⟫ ≥ (2/5)‖w‖²` for every real vector `w` of the sector, hence `μ ≥ 2/5`.

Cross-checked before formalisation by exact rational arithmetic (`fractions.Fraction`, no floating
point): the two sector blocks were recomputed from the operator construction *and* from the frozen
`physicalHEntry` table (agreement on all `6561` entries), the `LDLᵀ` factorisations were verified
by exact reconstruction, and negative controls were taken at several `k` — raising the constant
`2/5` to `23/50` destroys positivity at `k = 2` only (`k = 0, 1` survive), and at the true
    constant
`2/5` the linear form fails exactly at `k = 3, 4`, which is where the AKLT zero modes sit.

For `k = 3, 4` the sectors carry the AKLT zero modes, so the linear form is indefinite there and
the genuine Knabe quadratic form `ĥ² − (2/5) ĥ` is used instead — again on the whole sector
(`V_3` of dimension `16`, `V_4` of dimension `19`), so that *no highest-weight basis and no span
argument occur anywhere on the route*.  The five `LDLᵀ` certificates have `1, 4, 10, 15, 17`
strictly positive pivots; the `1` zero pivot of `V_3` and the `2` of `V_4` are exactly the AKLT
ground states living in those sectors.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.1.3 eq. (7.1.6) p. 182, §7.1.4 eq. (7.1.30) pp. 188–190; S. Knabe, *J. Stat. Phys.*
**52**, 627–638 (1988).
-/

namespace LatticeSystem.Quantum.AKLTSl2BlockDischargeE6

open LatticeSystem.Quantum
open LatticeSystem.Quantum.AKLTSl2SubmoduleProbeE2
open LatticeSystem.Quantum.AKLTSl2LadderSectorsE3
open LatticeSystem.Quantum.AKLTSl2WindowReductionE4
open LatticeSystem.Quantum.AKLTSl2HighestWeightBoundE5
open LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential
open scoped ComplexOrder

/-! ## 1. Enumerating the low magnetisation sectors -/

/-- Two four-site configurations are equal as soon as their four site labels are. -/
private theorem eqSpinConfigE6 (τ : SpinConfig) (a b c d : Fin 3)
    (h0 : (τ 0).val = a.val) (h1 : (τ 1).val = b.val) (h2 : (τ 2).val = c.val)
    (h3 : (τ 3).val = d.val) : τ = spinConfig a b c d := by
  funext i
  fin_cases i
  · exact Fin.ext h0
  · exact Fin.ext h1
  · exact Fin.ext h2
  · exact Fin.ext h3

/-- The magnetisation index of a four-site configuration, written out site by site. -/
private theorem magSumSFourE6 (τ : SpinConfig) :
    magSumS τ = (τ 0).val + (τ 1).val + (τ 2).val + (τ 3).val := by
  rw [magSumS_def]
  exact Fin.sum_univ_four _

/-- Evaluation of a four-site configuration literal at site `0`. -/
theorem spinConfig0E6 (a b c d : Fin 3) : spinConfig a b c d 0 = a := rfl

/-- Evaluation of a four-site configuration literal at site `1`. -/
theorem spinConfig1E6 (a b c d : Fin 3) : spinConfig a b c d 1 = b := rfl

/-- Evaluation of a four-site configuration literal at site `2`. -/
theorem spinConfig2E6 (a b c d : Fin 3) : spinConfig a b c d 2 = c := rfl

/-- Evaluation of a four-site configuration literal at site `3`. -/
theorem spinConfig3E6 (a b c d : Fin 3) : spinConfig a b c d 3 = d := rfl

/-- The natural value of the site label `0`. -/
theorem finVal0E6 : ((0 : Fin 3) : ℕ) = 0 := rfl

/-- The natural value of the site label `1`. -/
theorem finVal1E6 : ((1 : Fin 3) : ℕ) = 1 := rfl

/-- The natural value of the site label `2`. -/
theorem finVal2E6 : ((2 : Fin 3) : ℕ) = 2 := rfl

/-- The three possible values of a site label. -/
private theorem fin3CasesE6 (x : Fin 3) : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by omega

/-- Two site labels are equal exactly when their natural values are; used to let `norm_num`
decide the spectator guards of the bond entries. -/
theorem fin3EqIffE6 (a b : Fin 3) : (a = b) = (a.val = b.val) := by
  apply propext
  constructor
  · intro hab
    rw [hab]
  · exact Fin.ext

/-- **The magnetisation sector `V_1` has exactly 4 configurations.**  This is the only
place where the `4`-dimensionality of the sector enters, and it is settled by `omega`.
-/
theorem eqOfMagSumSOneE6 (τ : SpinConfig) (h : magSumS τ = 1) :
    τ = spinConfig 0 0 0 1 ∨ τ = spinConfig 0 0 1 0 ∨ τ = spinConfig 0 1 0 0 ∨
      τ = spinConfig 1 0 0 0 := by
  rw [magSumSFourE6] at h
  have key : ((τ 0).val = 0 ∧ (τ 1).val = 0 ∧ (τ 2).val = 0 ∧ (τ 3).val = 1) ∨
      ((τ 0).val = 0 ∧ (τ 1).val = 0 ∧ (τ 2).val = 1 ∧ (τ 3).val = 0) ∨
      ((τ 0).val = 0 ∧ (τ 1).val = 1 ∧ (τ 2).val = 0 ∧ (τ 3).val = 0) ∨
      ((τ 0).val = 1 ∧ (τ 1).val = 0 ∧ (τ 2).val = 0 ∧ (τ 3).val = 0) := by omega
  rcases key with ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩
  · exact Or.inl (eqSpinConfigE6 τ 0 0 0 1 p0 p1 p2 p3)
  · exact Or.inr (Or.inl (eqSpinConfigE6 τ 0 0 1 0 p0 p1 p2 p3))
  · exact Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 0 1 0 0 p0 p1 p2 p3)))
  · exact Or.inr (Or.inr (Or.inr ((eqSpinConfigE6 τ 1 0 0 0 p0 p1 p2 p3))))

/-- **The magnetisation sector `V_2` has exactly 10 configurations.**  This is the only
place where the `10`-dimensionality of the sector enters, and it is settled by `omega`.
-/
theorem eqOfMagSumSTwoE6 (τ : SpinConfig) (h : magSumS τ = 2) :
    τ = spinConfig 0 0 0 2 ∨ τ = spinConfig 0 0 1 1 ∨ τ = spinConfig 0 0 2 0 ∨
      τ = spinConfig 0 1 0 1 ∨ τ = spinConfig 0 1 1 0 ∨ τ = spinConfig 0 2 0 0 ∨
      τ = spinConfig 1 0 0 1 ∨ τ = spinConfig 1 0 1 0 ∨ τ = spinConfig 1 1 0 0 ∨
      τ = spinConfig 2 0 0 0 := by
  rw [magSumSFourE6] at h
  rcases fin3CasesE6 (τ 0) with p | p | p
  · have key : ((τ 0).val = 0 ∧ (τ 1).val = 0 ∧ (τ 2).val = 0 ∧ (τ 3).val = 2) ∨
        ((τ 0).val = 0 ∧ (τ 1).val = 0 ∧ (τ 2).val = 1 ∧ (τ 3).val = 1) ∨
        ((τ 0).val = 0 ∧ (τ 1).val = 0 ∧ (τ 2).val = 2 ∧ (τ 3).val = 0) ∨
        ((τ 0).val = 0 ∧ (τ 1).val = 1 ∧ (τ 2).val = 0 ∧ (τ 3).val = 1) ∨
        ((τ 0).val = 0 ∧ (τ 1).val = 1 ∧ (τ 2).val = 1 ∧ (τ 3).val = 0) ∨
        ((τ 0).val = 0 ∧ (τ 1).val = 2 ∧ (τ 2).val = 0 ∧ (τ 3).val = 0) := by omega
    rcases key with ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩ |
        ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩
    · exact Or.inl (eqSpinConfigE6 τ 0 0 0 2 p0 p1 p2 p3)
    · exact Or.inr (Or.inl (eqSpinConfigE6 τ 0 0 1 1 p0 p1 p2 p3))
    · exact Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 0 0 2 0 p0 p1 p2 p3)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 0 1 0 1 p0 p1 p2 p3))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 0 1 1 0 p0 p1 p2 p3)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 0 2 0 0 p0 p1 p2
        p3))))))
  · have key : ((τ 0).val = 1 ∧ (τ 1).val = 0 ∧ (τ 2).val = 0 ∧ (τ 3).val = 1) ∨
        ((τ 0).val = 1 ∧ (τ 1).val = 0 ∧ (τ 2).val = 1 ∧ (τ 3).val = 0) ∨
        ((τ 0).val = 1 ∧ (τ 1).val = 1 ∧ (τ 2).val = 0 ∧ (τ 3).val = 0) := by omega
    rcases key with ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 1 0 0 1 p0 p1
        p2 p3)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 1 0 1
        0 p0 p1 p2 p3))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eqSpinConfigE6
        τ 1 1 0 0 p0 p1 p2 p3)))))))))
  · have key : ((τ 0).val = 2 ∧ (τ 1).val = 0 ∧ (τ 2).val = 0 ∧ (τ 3).val = 0) := by omega
    rcases key with ⟨p0, p1, p2, p3⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ((eqSpinConfigE6 τ 2 0 0 0 p0 p1 p2 p3))))))))))

/-- **The magnetisation sector `V_3` has exactly 16 configurations.**  This is the only
place where the `16`-dimensionality of the sector enters, and it is settled by `omega`.
-/
theorem eqOfMagSumSThreeE6 (τ : SpinConfig) (h : magSumS τ = 3) :
    τ = spinConfig 0 0 1 2 ∨ τ = spinConfig 0 0 2 1 ∨ τ = spinConfig 0 1 0 2 ∨
      τ = spinConfig 0 1 1 1 ∨ τ = spinConfig 0 1 2 0 ∨ τ = spinConfig 0 2 0 1 ∨
      τ = spinConfig 0 2 1 0 ∨ τ = spinConfig 1 0 0 2 ∨ τ = spinConfig 1 0 1 1 ∨
      τ = spinConfig 1 0 2 0 ∨ τ = spinConfig 1 1 0 1 ∨ τ = spinConfig 1 1 1 0 ∨
      τ = spinConfig 1 2 0 0 ∨ τ = spinConfig 2 0 0 1 ∨ τ = spinConfig 2 0 1 0 ∨
      τ = spinConfig 2 1 0 0 := by
  rw [magSumSFourE6] at h
  rcases fin3CasesE6 (τ 0) with pa | pa | pa <;>
    rcases fin3CasesE6 (τ 1) with pb | pb | pb
  · have key : ((τ 0).val = 0 ∧ (τ 1).val = 0 ∧ (τ 2).val = 1 ∧ (τ 3).val = 2) ∨
        ((τ 0).val = 0 ∧ (τ 1).val = 0 ∧ (τ 2).val = 2 ∧ (τ 3).val = 1) := by omega
    rcases key with ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩
    · exact Or.inl (eqSpinConfigE6 τ 0 0 1 2 p0 p1 p2 p3)
    · exact Or.inr (Or.inl (eqSpinConfigE6 τ 0 0 2 1 p0 p1 p2 p3))
  · have key : ((τ 0).val = 0 ∧ (τ 1).val = 1 ∧ (τ 2).val = 0 ∧ (τ 3).val = 2) ∨
        ((τ 0).val = 0 ∧ (τ 1).val = 1 ∧ (τ 2).val = 1 ∧ (τ 3).val = 1) ∨
        ((τ 0).val = 0 ∧ (τ 1).val = 1 ∧ (τ 2).val = 2 ∧ (τ 3).val = 0) := by omega
    rcases key with ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩
    · exact Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 0 1 0 2 p0 p1 p2 p3)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 0 1 1 1 p0 p1 p2 p3))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 0 1 2 0 p0 p1 p2 p3)))))
  · have key : ((τ 0).val = 0 ∧ (τ 1).val = 2 ∧ (τ 2).val = 0 ∧ (τ 3).val = 1) ∨
        ((τ 0).val = 0 ∧ (τ 1).val = 2 ∧ (τ 2).val = 1 ∧ (τ 3).val = 0) := by omega
    rcases key with ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 0 2 0 1 p0 p1 p2
        p3))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 0 2 1 0 p0 p1
        p2 p3)))))))
  · have key : ((τ 0).val = 1 ∧ (τ 1).val = 0 ∧ (τ 2).val = 0 ∧ (τ 3).val = 2) ∨
        ((τ 0).val = 1 ∧ (τ 1).val = 0 ∧ (τ 2).val = 1 ∧ (τ 3).val = 1) ∨
        ((τ 0).val = 1 ∧ (τ 1).val = 0 ∧ (τ 2).val = 2 ∧ (τ 3).val = 0) := by omega
    rcases key with ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 1 0 0
        2 p0 p1 p2 p3))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eqSpinConfigE6
        τ 1 0 1 1 p0 p1 p2 p3)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (eqSpinConfigE6 τ 1 0 2 0 p0 p1 p2 p3))))))))))
  · have key : ((τ 0).val = 1 ∧ (τ 1).val = 1 ∧ (τ 2).val = 0 ∧ (τ 3).val = 1) ∨
        ((τ 0).val = 1 ∧ (τ 1).val = 1 ∧ (τ 2).val = 1 ∧ (τ 3).val = 0) := by omega
    rcases key with ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (eqSpinConfigE6 τ 1 1 0 1 p0 p1 p2 p3)))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (eqSpinConfigE6 τ 1 1 1 0 p0 p1 p2 p3))))))))))))
  · have key : ((τ 0).val = 1 ∧ (τ 1).val = 2 ∧ (τ 2).val = 0 ∧ (τ 3).val = 0) := by omega
    rcases key with ⟨p0, p1, p2, p3⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl (eqSpinConfigE6 τ 1 2 0 0 p0 p1 p2 p3)))))))))))))
  · have key : ((τ 0).val = 2 ∧ (τ 1).val = 0 ∧ (τ 2).val = 0 ∧ (τ 3).val = 1) ∨
        ((τ 0).val = 2 ∧ (τ 1).val = 0 ∧ (τ 2).val = 1 ∧ (τ 3).val = 0) := by omega
    rcases key with ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 2 0 0 1 p0 p1 p2 p3))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 2 0 1 0 p0 p1 p2 p3)))))))))))))))
  · have key : ((τ 0).val = 2 ∧ (τ 1).val = 1 ∧ (τ 2).val = 0 ∧ (τ 3).val = 0) := by omega
    rcases key with ⟨p0, p1, p2, p3⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr ((eqSpinConfigE6 τ 2 1 0 0 p0 p1 p2 p3))))))))))))))))
  · exact absurd h (by omega)

/-- **The magnetisation sector `V_4` has exactly 19 configurations.**  This is the only
place where the `19`-dimensionality of the sector enters, and it is settled by `omega`.
-/
theorem eqOfMagSumSFourE6 (τ : SpinConfig) (h : magSumS τ = 4) :
    τ = spinConfig 0 0 2 2 ∨ τ = spinConfig 0 1 1 2 ∨ τ = spinConfig 0 1 2 1 ∨
      τ = spinConfig 0 2 0 2 ∨ τ = spinConfig 0 2 1 1 ∨ τ = spinConfig 0 2 2 0 ∨
      τ = spinConfig 1 0 1 2 ∨ τ = spinConfig 1 0 2 1 ∨ τ = spinConfig 1 1 0 2 ∨
      τ = spinConfig 1 1 1 1 ∨ τ = spinConfig 1 1 2 0 ∨ τ = spinConfig 1 2 0 1 ∨
      τ = spinConfig 1 2 1 0 ∨ τ = spinConfig 2 0 0 2 ∨ τ = spinConfig 2 0 1 1 ∨
      τ = spinConfig 2 0 2 0 ∨ τ = spinConfig 2 1 0 1 ∨ τ = spinConfig 2 1 1 0 ∨
      τ = spinConfig 2 2 0 0 := by
  rw [magSumSFourE6] at h
  rcases fin3CasesE6 (τ 0) with pa | pa | pa <;>
    rcases fin3CasesE6 (τ 1) with pb | pb | pb
  · have key : ((τ 0).val = 0 ∧ (τ 1).val = 0 ∧ (τ 2).val = 2 ∧ (τ 3).val = 2) := by omega
    rcases key with ⟨p0, p1, p2, p3⟩
    · exact Or.inl (eqSpinConfigE6 τ 0 0 2 2 p0 p1 p2 p3)
  · have key : ((τ 0).val = 0 ∧ (τ 1).val = 1 ∧ (τ 2).val = 1 ∧ (τ 3).val = 2) ∨
        ((τ 0).val = 0 ∧ (τ 1).val = 1 ∧ (τ 2).val = 2 ∧ (τ 3).val = 1) := by omega
    rcases key with ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩
    · exact Or.inr (Or.inl (eqSpinConfigE6 τ 0 1 1 2 p0 p1 p2 p3))
    · exact Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 0 1 2 1 p0 p1 p2 p3)))
  · have key : ((τ 0).val = 0 ∧ (τ 1).val = 2 ∧ (τ 2).val = 0 ∧ (τ 3).val = 2) ∨
        ((τ 0).val = 0 ∧ (τ 1).val = 2 ∧ (τ 2).val = 1 ∧ (τ 3).val = 1) ∨
        ((τ 0).val = 0 ∧ (τ 1).val = 2 ∧ (τ 2).val = 2 ∧ (τ 3).val = 0) := by omega
    rcases key with ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 0 2 0 2 p0 p1 p2 p3))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 0 2 1 1 p0 p1 p2 p3)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 0 2 2 0 p0 p1 p2
        p3))))))
  · have key : ((τ 0).val = 1 ∧ (τ 1).val = 0 ∧ (τ 2).val = 1 ∧ (τ 3).val = 2) ∨
        ((τ 0).val = 1 ∧ (τ 1).val = 0 ∧ (τ 2).val = 2 ∧ (τ 3).val = 1) := by omega
    rcases key with ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 1 0 1 2 p0 p1
        p2 p3)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 1 0 2
        1 p0 p1 p2 p3))))))))
  · have key : ((τ 0).val = 1 ∧ (τ 1).val = 1 ∧ (τ 2).val = 0 ∧ (τ 3).val = 2) ∨
        ((τ 0).val = 1 ∧ (τ 1).val = 1 ∧ (τ 2).val = 1 ∧ (τ 3).val = 1) ∨
        ((τ 0).val = 1 ∧ (τ 1).val = 1 ∧ (τ 2).val = 2 ∧ (τ 3).val = 0) := by omega
    rcases key with ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eqSpinConfigE6
        τ 1 1 0 2 p0 p1 p2 p3)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (eqSpinConfigE6 τ 1 1 1 1 p0 p1 p2 p3))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (eqSpinConfigE6 τ 1 1 2 0 p0 p1 p2 p3)))))))))))
  · have key : ((τ 0).val = 1 ∧ (τ 1).val = 2 ∧ (τ 2).val = 0 ∧ (τ 3).val = 1) ∨
        ((τ 0).val = 1 ∧ (τ 1).val = 2 ∧ (τ 2).val = 1 ∧ (τ 3).val = 0) := by omega
    rcases key with ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (eqSpinConfigE6 τ 1 2 0 1 p0 p1 p2 p3))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl (eqSpinConfigE6 τ 1 2 1 0 p0 p1 p2 p3)))))))))))))
  · have key : ((τ 0).val = 2 ∧ (τ 1).val = 0 ∧ (τ 2).val = 0 ∧ (τ 3).val = 2) ∨
        ((τ 0).val = 2 ∧ (τ 1).val = 0 ∧ (τ 2).val = 1 ∧ (τ 3).val = 1) ∨
        ((τ 0).val = 2 ∧ (τ 1).val = 0 ∧ (τ 2).val = 2 ∧ (τ 3).val = 0) := by omega
    rcases key with ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 2 0 0 2 p0 p1 p2 p3))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 2 0 1 1 p0 p1 p2 p3)))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 2 0 2 0 p0 p1 p2
        p3))))))))))))))))
  · have key : ((τ 0).val = 2 ∧ (τ 1).val = 1 ∧ (τ 2).val = 0 ∧ (τ 3).val = 1) ∨
        ((τ 0).val = 2 ∧ (τ 1).val = 1 ∧ (τ 2).val = 1 ∧ (τ 3).val = 0) := by omega
    rcases key with ⟨p0, p1, p2, p3⟩ | ⟨p0, p1, p2, p3⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 2 1 0 1 p0 p1 p2
        p3)))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eqSpinConfigE6 τ 2 1 1 0 p0 p1 p2
        p3))))))))))))))))))
  · have key : ((τ 0).val = 2 ∧ (τ 1).val = 2 ∧ (τ 2).val = 0 ∧ (τ 3).val = 0) := by omega
    rcases key with ⟨p0, p1, p2, p3⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((eqSpinConfigE6 τ 2 2 0 0 p0 p1
        p2 p3)))))))))))))))))))

/-! ## 2. Restricting a sum over all configurations to a sector -/

/-- **A sum over all `81` configurations of a function supported on `V_1`** collapses to
the 4 sector terms.  This is the only bookkeeping step that touches the ambient space.
-/
private theorem sumRestrictOneE6 (f : SpinConfig → ℂ)
    (hf : ∀ τ : SpinConfig, magSumS τ ≠ 1 → f τ = 0) :
    ∑ τ : SpinConfig, f τ = f (spinConfig 0 0 0 1) + f (spinConfig 0 0 1 0) +
      f (spinConfig 0 1 0 0) + f (spinConfig 1 0 0 0) := by
  classical
  have hzero : ∀ τ ∈ (Finset.univ : Finset SpinConfig), τ ∉ ({ spinConfig 0 0 0 1,
      spinConfig 0 0 1 0, spinConfig 0 1 0 0,
      spinConfig 1 0 0 0} : Finset SpinConfig) → f τ = 0 := by
    intro τ _ hτ
    refine hf τ fun hc => hτ ?_
    rcases eqOfMagSumSOneE6 τ hc with h | h | h | h
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
  have hsplit : ∑ τ ∈ ({ spinConfig 0 0 0 1, spinConfig 0 0 1 0, spinConfig 0 1 0 0,
      spinConfig 1 0 0 0} : Finset SpinConfig), f τ
      = f (spinConfig 0 0 0 1) + f (spinConfig 0 0 1 0) + f (spinConfig 0 1 0 0) +
        f (spinConfig 1 0 0 0) := by
    rw [ Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  exact (Finset.sum_subset (Finset.subset_univ _) hzero).symm.trans hsplit

/-- **A sum over all `81` configurations of a function supported on `V_2`** collapses to
the 10 sector terms.  This is the only bookkeeping step that touches the ambient space.
-/
private theorem sumRestrictTwoE6 (f : SpinConfig → ℂ)
    (hf : ∀ τ : SpinConfig, magSumS τ ≠ 2 → f τ = 0) :
    ∑ τ : SpinConfig, f τ = f (spinConfig 0 0 0 2) + f (spinConfig 0 0 1 1) +
      f (spinConfig 0 0 2 0) + f (spinConfig 0 1 0 1) + f (spinConfig 0 1 1 0) +
      f (spinConfig 0 2 0 0) + f (spinConfig 1 0 0 1) + f (spinConfig 1 0 1 0) +
      f (spinConfig 1 1 0 0) + f (spinConfig 2 0 0 0) := by
  classical
  have hzero : ∀ τ ∈ (Finset.univ : Finset SpinConfig), τ ∉ ({ spinConfig 0 0 0 2,
      spinConfig 0 0 1 1, spinConfig 0 0 2 0, spinConfig 0 1 0 1, spinConfig 0 1 1 0,
      spinConfig 0 2 0 0, spinConfig 1 0 0 1, spinConfig 1 0 1 0, spinConfig 1 1 0 0,
      spinConfig 2 0 0 0} : Finset SpinConfig) → f τ = 0 := by
    intro τ _ hτ
    refine hf τ fun hc => hτ ?_
    rcases eqOfMagSumSTwoE6 τ hc with h | h | h | h | h | h | h | h | h | h
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
  have hsplit : ∑ τ ∈ ({ spinConfig 0 0 0 2, spinConfig 0 0 1 1, spinConfig 0 0 2 0,
      spinConfig 0 1 0 1, spinConfig 0 1 1 0, spinConfig 0 2 0 0, spinConfig 1 0 0 1,
      spinConfig 1 0 1 0, spinConfig 1 1 0 0, spinConfig 2 0 0 0} : Finset SpinConfig), f τ
      = f (spinConfig 0 0 0 2) + f (spinConfig 0 0 1 1) + f (spinConfig 0 0 2 0) +
        f (spinConfig 0 1 0 1) + f (spinConfig 0 1 1 0) + f (spinConfig 0 2 0 0) +
        f (spinConfig 1 0 0 1) + f (spinConfig 1 0 1 0) + f (spinConfig 1 1 0 0) +
        f (spinConfig 2 0 0 0) := by
    rw [ Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  exact (Finset.sum_subset (Finset.subset_univ _) hzero).symm.trans hsplit

/-- **A sum over all `81` configurations of a function supported on `V_3`** collapses to
the 16 sector terms.  This is the only bookkeeping step that touches the ambient space.
-/
private theorem sumRestrictThreeE6 (f : SpinConfig → ℂ)
    (hf : ∀ τ : SpinConfig, magSumS τ ≠ 3 → f τ = 0) :
    ∑ τ : SpinConfig, f τ = f (spinConfig 0 0 1 2) + f (spinConfig 0 0 2 1) +
      f (spinConfig 0 1 0 2) + f (spinConfig 0 1 1 1) + f (spinConfig 0 1 2 0) +
      f (spinConfig 0 2 0 1) + f (spinConfig 0 2 1 0) + f (spinConfig 1 0 0 2) +
      f (spinConfig 1 0 1 1) + f (spinConfig 1 0 2 0) + f (spinConfig 1 1 0 1) +
      f (spinConfig 1 1 1 0) + f (spinConfig 1 2 0 0) + f (spinConfig 2 0 0 1) +
      f (spinConfig 2 0 1 0) + f (spinConfig 2 1 0 0) := by
  classical
  have hzero : ∀ τ ∈ (Finset.univ : Finset SpinConfig), τ ∉ ({ spinConfig 0 0 1 2,
      spinConfig 0 0 2 1, spinConfig 0 1 0 2, spinConfig 0 1 1 1, spinConfig 0 1 2 0,
      spinConfig 0 2 0 1, spinConfig 0 2 1 0, spinConfig 1 0 0 2, spinConfig 1 0 1 1,
      spinConfig 1 0 2 0, spinConfig 1 1 0 1, spinConfig 1 1 1 0, spinConfig 1 2 0 0,
      spinConfig 2 0 0 1, spinConfig 2 0 1 0,
      spinConfig 2 1 0 0} : Finset SpinConfig) → f τ = 0 := by
    intro τ _ hτ
    refine hf τ fun hc => hτ ?_
    rcases eqOfMagSumSThreeE6 τ hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
        | h
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
  have hsplit : ∑ τ ∈ ({ spinConfig 0 0 1 2, spinConfig 0 0 2 1, spinConfig 0 1 0 2,
      spinConfig 0 1 1 1, spinConfig 0 1 2 0, spinConfig 0 2 0 1, spinConfig 0 2 1 0,
      spinConfig 1 0 0 2, spinConfig 1 0 1 1, spinConfig 1 0 2 0, spinConfig 1 1 0 1,
      spinConfig 1 1 1 0, spinConfig 1 2 0 0, spinConfig 2 0 0 1, spinConfig 2 0 1 0,
      spinConfig 2 1 0 0} : Finset SpinConfig), f τ
      = f (spinConfig 0 0 1 2) + f (spinConfig 0 0 2 1) + f (spinConfig 0 1 0 2) +
        f (spinConfig 0 1 1 1) + f (spinConfig 0 1 2 0) + f (spinConfig 0 2 0 1) +
        f (spinConfig 0 2 1 0) + f (spinConfig 1 0 0 2) + f (spinConfig 1 0 1 1) +
        f (spinConfig 1 0 2 0) + f (spinConfig 1 1 0 1) + f (spinConfig 1 1 1 0) +
        f (spinConfig 1 2 0 0) + f (spinConfig 2 0 0 1) + f (spinConfig 2 0 1 0) +
        f (spinConfig 2 1 0 0) := by
    rw [ Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  exact (Finset.sum_subset (Finset.subset_univ _) hzero).symm.trans hsplit

/-- **A sum over all `81` configurations of a function supported on `V_4`** collapses to
the 19 sector terms.  This is the only bookkeeping step that touches the ambient space.
-/
private theorem sumRestrictFourE6 (f : SpinConfig → ℂ)
    (hf : ∀ τ : SpinConfig, magSumS τ ≠ 4 → f τ = 0) :
    ∑ τ : SpinConfig, f τ = f (spinConfig 0 0 2 2) + f (spinConfig 0 1 1 2) +
      f (spinConfig 0 1 2 1) + f (spinConfig 0 2 0 2) + f (spinConfig 0 2 1 1) +
      f (spinConfig 0 2 2 0) + f (spinConfig 1 0 1 2) + f (spinConfig 1 0 2 1) +
      f (spinConfig 1 1 0 2) + f (spinConfig 1 1 1 1) + f (spinConfig 1 1 2 0) +
      f (spinConfig 1 2 0 1) + f (spinConfig 1 2 1 0) + f (spinConfig 2 0 0 2) +
      f (spinConfig 2 0 1 1) + f (spinConfig 2 0 2 0) + f (spinConfig 2 1 0 1) +
      f (spinConfig 2 1 1 0) + f (spinConfig 2 2 0 0) := by
  classical
  have hzero : ∀ τ ∈ (Finset.univ : Finset SpinConfig), τ ∉ ({ spinConfig 0 0 2 2,
      spinConfig 0 1 1 2, spinConfig 0 1 2 1, spinConfig 0 2 0 2, spinConfig 0 2 1 1,
      spinConfig 0 2 2 0, spinConfig 1 0 1 2, spinConfig 1 0 2 1, spinConfig 1 1 0 2,
      spinConfig 1 1 1 1, spinConfig 1 1 2 0, spinConfig 1 2 0 1, spinConfig 1 2 1 0,
      spinConfig 2 0 0 2, spinConfig 2 0 1 1, spinConfig 2 0 2 0, spinConfig 2 1 0 1,
      spinConfig 2 1 1 0, spinConfig 2 2 0 0} : Finset SpinConfig) → f τ = 0 := by
    intro τ _ hτ
    refine hf τ fun hc => hτ ?_
    rcases eqOfMagSumSFourE6 τ hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
        h | h | h | h
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
  have hsplit : ∑ τ ∈ ({ spinConfig 0 0 2 2, spinConfig 0 1 1 2, spinConfig 0 1 2 1,
      spinConfig 0 2 0 2, spinConfig 0 2 1 1, spinConfig 0 2 2 0, spinConfig 1 0 1 2,
      spinConfig 1 0 2 1, spinConfig 1 1 0 2, spinConfig 1 1 1 1, spinConfig 1 1 2 0,
      spinConfig 1 2 0 1, spinConfig 1 2 1 0, spinConfig 2 0 0 2, spinConfig 2 0 1 1,
      spinConfig 2 0 2 0, spinConfig 2 1 0 1, spinConfig 2 1 1 0,
      spinConfig 2 2 0 0} : Finset SpinConfig), f τ
      = f (spinConfig 0 0 2 2) + f (spinConfig 0 1 1 2) + f (spinConfig 0 1 2 1) +
        f (spinConfig 0 2 0 2) + f (spinConfig 0 2 1 1) + f (spinConfig 0 2 2 0) +
        f (spinConfig 1 0 1 2) + f (spinConfig 1 0 2 1) + f (spinConfig 1 1 0 2) +
        f (spinConfig 1 1 1 1) + f (spinConfig 1 1 2 0) + f (spinConfig 1 2 0 1) +
        f (spinConfig 1 2 1 0) + f (spinConfig 2 0 0 2) + f (spinConfig 2 0 1 1) +
        f (spinConfig 2 0 2 0) + f (spinConfig 2 1 0 1) + f (spinConfig 2 1 1 0) +
        f (spinConfig 2 2 0 0) := by
    rw [ Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  exact (Finset.sum_subset (Finset.subset_univ _) hzero).symm.trans hsplit

/-! ## 3. The componentwise form of the eigenvalue equation -/

/-- The eigenvalue equation `ĥ u = μ u` read at a single configuration, with the matrix entries
replaced by the frozen rational model `physicalHEntry` of
`akltWindow3H_apply_eq_physicalHEntry`. -/
private theorem eigenComponentE6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u) (σ : SpinConfig) :
    ∑ τ : SpinConfig, (physicalHEntry σ τ : ℂ) * WithLp.ofLp u τ
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u σ := by
  have h := congrFun (congrArg WithLp.ofLp heig) σ
  rw [ofLp_manyBodyLinE4] at h
  have hlhs : (akltWindow3H.mulVec (WithLp.ofLp u)) σ
      = ∑ τ : SpinConfig, (physicalHEntry σ τ : ℂ) * WithLp.ofLp u τ := by
    change ∑ τ, akltWindow3H σ τ * WithLp.ofLp u τ = _
    exact Finset.sum_congr rfl fun τ _ => by rw [akltWindow3H_apply_eq_physicalHEntry]
  rw [hlhs] at h
  exact h

/-- **The eigenvalue equation restricted to the sector `V_1`.**  Only the 4 components of
`u` inside the sector survive, because `u` vanishes off the sector. -/
theorem rowV1E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 1 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u)
    (σ : SpinConfig) :
    (physicalHEntry σ (spinConfig 0 0 0 1) : ℂ) * WithLp.ofLp u (spinConfig 0 0 0 1) +
      (physicalHEntry σ (spinConfig 0 0 1 0) : ℂ) * WithLp.ofLp u (spinConfig 0 0 1 0) +
      (physicalHEntry σ (spinConfig 0 1 0 0) : ℂ) * WithLp.ofLp u (spinConfig 0 1 0 0) +
      (physicalHEntry σ (spinConfig 1 0 0 0) : ℂ) * WithLp.ofLp u (spinConfig 1 0 0 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u σ := by
  have hz : ∀ τ : SpinConfig, magSumS τ ≠ 1 →
      (physicalHEntry σ τ : ℂ) * WithLp.ofLp u τ = 0 := by
    intro τ hτ
    rw [hsupp τ hτ, mul_zero]
  have h := eigenComponentE6 μ u heig σ
  rw [sumRestrictOneE6 (fun τ => (physicalHEntry σ τ : ℂ) * WithLp.ofLp u τ) hz] at h
  exact h

/-- **The eigenvalue equation restricted to the sector `V_2`.**  Only the 10 components of
`u` inside the sector survive, because `u` vanishes off the sector. -/
theorem rowV2E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 2 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u)
    (σ : SpinConfig) :
    (physicalHEntry σ (spinConfig 0 0 0 2) : ℂ) * WithLp.ofLp u (spinConfig 0 0 0 2) +
      (physicalHEntry σ (spinConfig 0 0 1 1) : ℂ) * WithLp.ofLp u (spinConfig 0 0 1 1) +
      (physicalHEntry σ (spinConfig 0 0 2 0) : ℂ) * WithLp.ofLp u (spinConfig 0 0 2 0) +
      (physicalHEntry σ (spinConfig 0 1 0 1) : ℂ) * WithLp.ofLp u (spinConfig 0 1 0 1) +
      (physicalHEntry σ (spinConfig 0 1 1 0) : ℂ) * WithLp.ofLp u (spinConfig 0 1 1 0) +
      (physicalHEntry σ (spinConfig 0 2 0 0) : ℂ) * WithLp.ofLp u (spinConfig 0 2 0 0) +
      (physicalHEntry σ (spinConfig 1 0 0 1) : ℂ) * WithLp.ofLp u (spinConfig 1 0 0 1) +
      (physicalHEntry σ (spinConfig 1 0 1 0) : ℂ) * WithLp.ofLp u (spinConfig 1 0 1 0) +
      (physicalHEntry σ (spinConfig 1 1 0 0) : ℂ) * WithLp.ofLp u (spinConfig 1 1 0 0) +
      (physicalHEntry σ (spinConfig 2 0 0 0) : ℂ) * WithLp.ofLp u (spinConfig 2 0 0 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u σ := by
  have hz : ∀ τ : SpinConfig, magSumS τ ≠ 2 →
      (physicalHEntry σ τ : ℂ) * WithLp.ofLp u τ = 0 := by
    intro τ hτ
    rw [hsupp τ hτ, mul_zero]
  have h := eigenComponentE6 μ u heig σ
  rw [sumRestrictTwoE6 (fun τ => (physicalHEntry σ τ : ℂ) * WithLp.ofLp u τ) hz] at h
  exact h

/-- **The eigenvalue equation restricted to the sector `V_3`.**  Only the 16 components of
`u` inside the sector survive, because `u` vanishes off the sector. -/
theorem rowV3E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 3 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u)
    (σ : SpinConfig) :
    (physicalHEntry σ (spinConfig 0 0 1 2) : ℂ) * WithLp.ofLp u (spinConfig 0 0 1 2) +
      (physicalHEntry σ (spinConfig 0 0 2 1) : ℂ) * WithLp.ofLp u (spinConfig 0 0 2 1) +
      (physicalHEntry σ (spinConfig 0 1 0 2) : ℂ) * WithLp.ofLp u (spinConfig 0 1 0 2) +
      (physicalHEntry σ (spinConfig 0 1 1 1) : ℂ) * WithLp.ofLp u (spinConfig 0 1 1 1) +
      (physicalHEntry σ (spinConfig 0 1 2 0) : ℂ) * WithLp.ofLp u (spinConfig 0 1 2 0) +
      (physicalHEntry σ (spinConfig 0 2 0 1) : ℂ) * WithLp.ofLp u (spinConfig 0 2 0 1) +
      (physicalHEntry σ (spinConfig 0 2 1 0) : ℂ) * WithLp.ofLp u (spinConfig 0 2 1 0) +
      (physicalHEntry σ (spinConfig 1 0 0 2) : ℂ) * WithLp.ofLp u (spinConfig 1 0 0 2) +
      (physicalHEntry σ (spinConfig 1 0 1 1) : ℂ) * WithLp.ofLp u (spinConfig 1 0 1 1) +
      (physicalHEntry σ (spinConfig 1 0 2 0) : ℂ) * WithLp.ofLp u (spinConfig 1 0 2 0) +
      (physicalHEntry σ (spinConfig 1 1 0 1) : ℂ) * WithLp.ofLp u (spinConfig 1 1 0 1) +
      (physicalHEntry σ (spinConfig 1 1 1 0) : ℂ) * WithLp.ofLp u (spinConfig 1 1 1 0) +
      (physicalHEntry σ (spinConfig 1 2 0 0) : ℂ) * WithLp.ofLp u (spinConfig 1 2 0 0) +
      (physicalHEntry σ (spinConfig 2 0 0 1) : ℂ) * WithLp.ofLp u (spinConfig 2 0 0 1) +
      (physicalHEntry σ (spinConfig 2 0 1 0) : ℂ) * WithLp.ofLp u (spinConfig 2 0 1 0) +
      (physicalHEntry σ (spinConfig 2 1 0 0) : ℂ) * WithLp.ofLp u (spinConfig 2 1 0 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u σ := by
  have hz : ∀ τ : SpinConfig, magSumS τ ≠ 3 →
      (physicalHEntry σ τ : ℂ) * WithLp.ofLp u τ = 0 := by
    intro τ hτ
    rw [hsupp τ hτ, mul_zero]
  have h := eigenComponentE6 μ u heig σ
  rw [sumRestrictThreeE6 (fun τ => (physicalHEntry σ τ : ℂ) * WithLp.ofLp u τ) hz] at h
  exact h

/-- **The eigenvalue equation restricted to the sector `V_4`.**  Only the 19 components of
`u` inside the sector survive, because `u` vanishes off the sector. -/
theorem rowV4E6 (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2)
    (hsupp : ∀ σ : SpinConfig, magSumS σ ≠ 4 → WithLp.ofLp u σ = 0)
    (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u)
    (σ : SpinConfig) :
    (physicalHEntry σ (spinConfig 0 0 2 2) : ℂ) * WithLp.ofLp u (spinConfig 0 0 2 2) +
      (physicalHEntry σ (spinConfig 0 1 1 2) : ℂ) * WithLp.ofLp u (spinConfig 0 1 1 2) +
      (physicalHEntry σ (spinConfig 0 1 2 1) : ℂ) * WithLp.ofLp u (spinConfig 0 1 2 1) +
      (physicalHEntry σ (spinConfig 0 2 0 2) : ℂ) * WithLp.ofLp u (spinConfig 0 2 0 2) +
      (physicalHEntry σ (spinConfig 0 2 1 1) : ℂ) * WithLp.ofLp u (spinConfig 0 2 1 1) +
      (physicalHEntry σ (spinConfig 0 2 2 0) : ℂ) * WithLp.ofLp u (spinConfig 0 2 2 0) +
      (physicalHEntry σ (spinConfig 1 0 1 2) : ℂ) * WithLp.ofLp u (spinConfig 1 0 1 2) +
      (physicalHEntry σ (spinConfig 1 0 2 1) : ℂ) * WithLp.ofLp u (spinConfig 1 0 2 1) +
      (physicalHEntry σ (spinConfig 1 1 0 2) : ℂ) * WithLp.ofLp u (spinConfig 1 1 0 2) +
      (physicalHEntry σ (spinConfig 1 1 1 1) : ℂ) * WithLp.ofLp u (spinConfig 1 1 1 1) +
      (physicalHEntry σ (spinConfig 1 1 2 0) : ℂ) * WithLp.ofLp u (spinConfig 1 1 2 0) +
      (physicalHEntry σ (spinConfig 1 2 0 1) : ℂ) * WithLp.ofLp u (spinConfig 1 2 0 1) +
      (physicalHEntry σ (spinConfig 1 2 1 0) : ℂ) * WithLp.ofLp u (spinConfig 1 2 1 0) +
      (physicalHEntry σ (spinConfig 2 0 0 2) : ℂ) * WithLp.ofLp u (spinConfig 2 0 0 2) +
      (physicalHEntry σ (spinConfig 2 0 1 1) : ℂ) * WithLp.ofLp u (spinConfig 2 0 1 1) +
      (physicalHEntry σ (spinConfig 2 0 2 0) : ℂ) * WithLp.ofLp u (spinConfig 2 0 2 0) +
      (physicalHEntry σ (spinConfig 2 1 0 1) : ℂ) * WithLp.ofLp u (spinConfig 2 1 0 1) +
      (physicalHEntry σ (spinConfig 2 1 1 0) : ℂ) * WithLp.ofLp u (spinConfig 2 1 1 0) +
      (physicalHEntry σ (spinConfig 2 2 0 0) : ℂ) * WithLp.ofLp u (spinConfig 2 2 0 0)
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u σ := by
  have hz : ∀ τ : SpinConfig, magSumS τ ≠ 4 →
      (physicalHEntry σ τ : ℂ) * WithLp.ofLp u τ = 0 := by
    intro τ hτ
    rw [hsupp τ hτ, mul_zero]
  have h := eigenComponentE6 μ u heig σ
  rw [sumRestrictFourE6 (fun τ => (physicalHEntry σ τ : ℂ) * WithLp.ofLp u τ) hz] at h
  exact h

end LatticeSystem.Quantum.AKLTSl2BlockDischargeE6
