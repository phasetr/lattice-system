import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIBoundaryMoveSetsCore
import LatticeSystem.Quantum.SpinS.BipartiteCompleteGraphStructural
import LatticeSystem.Quantum.SpinS.ParityReachableNoParityBondTotal
import LatticeSystem.Quantum.SpinS.ParityReachableNoSingleIonTotal

/-!
# Anisotropic Heisenberg spin-S case (ii) block reachability: lifts and totality (foundation)

Foundational layer extracted from `AnisotropicHeisenbergSpinSCaseIIBlockReachability.lean` for build
speed.  This file proves the lifts from full configurations to parity blocks and the totality of the
parity/ion/bond block reachability on bipartite complete graphs.

The case-(ii) wrappers with total block reachability are kept in the capstone module
`AnisotropicHeisenbergSpinSCaseIIBlockReachability.lean`.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Lifts from full configurations to parity blocks -/

omit [DecidableEq Λ] in
/-- Lift full parity reachability between two representatives of the same
fixed parity block to block-level reachability. -/
theorem parityReachableSOnBlock_of_parityReachableS
    {G : SimpleGraph Λ} {p : ℕ} {σ τ : parityConfigS Λ N p}
    (hreach : ParityReachableS G σ.1 τ.1) :
    parityReachableSOnBlock G σ τ := by
  classical
  rcases τ with ⟨τ, hτ⟩
  change ParityReachableS G σ.1 τ at hreach
  induction hreach with
  | refl =>
      exact parityReachableSOnBlock_refl G σ
  | tail hpre hstep ih =>
      let hρ : magSumS _ % 2 = p := by
        have hp := parityReachableS_magSumS_parity_eq hpre
        rw [hp, σ.2]
      let ρ : parityConfigS Λ N p := ⟨_, hρ⟩
      exact parityReachableSOnBlock_trans (ih hρ)
        (parityReachableSOnBlock_single (σ := ρ) (τ := ⟨_, hτ⟩) hstep)

omit [DecidableEq Λ] in
/-- Lift full ion-only parity reachability between two representatives of the
same fixed parity block to block-level ion-only reachability. -/
theorem ionParityReachableSOnBlock_of_ionParityReachableS
    {G : SimpleGraph Λ} {p : ℕ} {σ τ : parityConfigS Λ N p}
    (hreach : IonParityReachableS G σ.1 τ.1) :
    ionParityReachableSOnBlock G σ τ := by
  classical
  rcases τ with ⟨τ, hτ⟩
  change IonParityReachableS G σ.1 τ at hreach
  induction hreach with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hpre hstep ih =>
      let hρ : magSumS _ % 2 = p := by
        have hp := parityReachableS_magSumS_parity_eq
          (IonParityReachableS.to_parityReachableS hpre)
        rw [hp, σ.2]
      let ρ : parityConfigS Λ N p := ⟨_, hρ⟩
      exact Relation.ReflTransGen.trans (ih hρ)
        (Relation.ReflTransGen.single (show ionParityStepSOnBlock G ρ ⟨_, hτ⟩ from hstep))

omit [DecidableEq Λ] in
/-- Lift full bond-only parity reachability between two representatives of the
same fixed parity block to block-level bond-only reachability. -/
theorem bondParityReachableSOnBlock_of_bondParityReachableS
    {G : SimpleGraph Λ} {p : ℕ} {σ τ : parityConfigS Λ N p}
    (hreach : BondParityReachableS G σ.1 τ.1) :
    bondParityReachableSOnBlock G σ τ := by
  classical
  rcases τ with ⟨τ, hτ⟩
  change BondParityReachableS G σ.1 τ at hreach
  induction hreach with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hpre hstep ih =>
      let hρ : magSumS _ % 2 = p := by
        have hp := parityReachableS_magSumS_parity_eq
          (BondParityReachableS.to_parityReachableS hpre)
        rw [hp, σ.2]
      let ρ : parityConfigS Λ N p := ⟨_, hρ⟩
      exact Relation.ReflTransGen.trans (ih hρ)
        (Relation.ReflTransGen.single (show bondParityStepSOnBlock G ρ ⟨_, hτ⟩ from hstep))

/-! ## Totality on bipartite complete graphs -/

omit [DecidableEq Λ] in
/-- Block-level strict case-(ii) parity reachability totality on the bipartite
complete graph. -/
theorem parityReachableSOnBlock_total_bipartiteCompleteGraph
    (A : Λ → Bool)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    {p : ℕ} (σ' σ : parityConfigS Λ N p) :
    parityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ' := by
  classical
  exact parityReachableSOnBlock_of_parityReachableS
    (parityReachableS_total A hA_ne hB_ne hN (σ.2.trans σ'.2.symm))

omit [DecidableEq Λ] in
/-- Block-level ion-only parity reachability totality on the bipartite complete
graph. -/
theorem ionParityReachableSOnBlock_total_bipartiteCompleteGraph
    (A : Λ → Bool)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    {p : ℕ} (σ' σ : parityConfigS Λ N p) :
    ionParityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ' := by
  classical
  exact ionParityReachableSOnBlock_of_ionParityReachableS
    (ionParityReachableS_total A hA_ne hB_ne hN (σ.2.trans σ'.2.symm))

omit [DecidableEq Λ] in
/-- Block-level bond-only parity reachability totality on the bipartite complete
graph. -/
theorem bondParityReachableSOnBlock_total_bipartiteCompleteGraph
    (A : Λ → Bool)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    {p : ℕ} (σ' σ : parityConfigS Λ N p) :
    bondParityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ' := by
  classical
  exact bondParityReachableSOnBlock_of_bondParityReachableS
    (bondParityReachableS_total A hA_ne hB_ne hN (σ.2.trans σ'.2.symm))

end LatticeSystem.Quantum
