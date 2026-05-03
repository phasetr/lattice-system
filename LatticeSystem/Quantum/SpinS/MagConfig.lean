import LatticeSystem.Quantum.SpinS.Magnetization
import LatticeSystem.Quantum.SpinS.RaiseLower
import LatticeSystem.Quantum.SpinS.BipartiteCompleteGraph
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# The magnetization-`M` configuration subtype
(Tasaki §2.5 Phase B-γ γ-3 final prep)

For the spin-S Marshall–Lieb–Mattis theorem, the irreducibility argument
applies to the dressed Heisenberg matrix restricted to a single
magnetization sector. This module defines the subtype of configurations
with a fixed magnetization sum:

  `magConfigS V N M := { σ : V → Fin (N + 1) // magSumS σ = M }`.

This is the natural index type for the sector-restricted matrix used
in the PF irreducibility application.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The subtype of configurations with magnetization sum `M`. -/
def magConfigS (V : Type*) [Fintype V] (N M : ℕ) :=
  { σ : V → Fin (N + 1) // magSumS σ = M }

omit [DecidableEq V] in
/-- A magConfig has magSumS equal to its tag. -/
theorem magConfigS_magSumS {M : ℕ} (σ : magConfigS V N M) :
    magSumS σ.1 = M := σ.2

instance magConfigS_instDecidableEq {M : ℕ} :
    DecidableEq (magConfigS V N M) := fun _ _ => Subtype.instDecidableEq _ _

instance magConfigS_instFintype {M : ℕ} : Fintype (magConfigS V N M) := by
  unfold magConfigS
  classical
  apply Subtype.fintype

/-! ## Raise/lower step lifted to magConfigS -/

/-- A `RaiseLowerStepS` between two magConfigS in the same sector
(magnetization automatically preserved by the raise/lower step). -/
def RaiseLowerStepSMagSector (G : SimpleGraph V) {M : ℕ}
    (σ τ : magConfigS V N M) : Prop :=
  RaiseLowerStepS G σ.1 τ.1

/-- The reflexive transitive closure of `RaiseLowerStepSMagSector`. -/
def RaiseLowerReachableSMagSector (G : SimpleGraph V) {M : ℕ} :
    magConfigS V N M → magConfigS V N M → Prop :=
  Relation.ReflTransGen (RaiseLowerStepSMagSector G)

omit [DecidableEq V] in
/-- Reflexivity of the magConfigS reachability. -/
theorem RaiseLowerReachableSMagSector.refl
    (G : SimpleGraph V) {M : ℕ} (σ : magConfigS V N M) :
    RaiseLowerReachableSMagSector G σ σ :=
  Relation.ReflTransGen.refl

omit [DecidableEq V] in
/-- A single step is reachable. -/
theorem RaiseLowerReachableSMagSector.single {G : SimpleGraph V} {M : ℕ}
    {σ τ : magConfigS V N M} (h : RaiseLowerStepSMagSector G σ τ) :
    RaiseLowerReachableSMagSector G σ τ :=
  Relation.ReflTransGen.single h

omit [DecidableEq V] in
/-- Transitivity. -/
theorem RaiseLowerReachableSMagSector.trans {G : SimpleGraph V} {M : ℕ}
    {σ τ ρ : magConfigS V N M}
    (h₁ : RaiseLowerReachableSMagSector G σ τ)
    (h₂ : RaiseLowerReachableSMagSector G τ ρ) :
    RaiseLowerReachableSMagSector G σ ρ :=
  Relation.ReflTransGen.trans h₁ h₂

omit [DecidableEq V] in
/-- Tail extension on the subtype. -/
theorem RaiseLowerReachableSMagSector.tail' {G : SimpleGraph V} {M : ℕ}
    {σ τ ρ : magConfigS V N M}
    (h₁ : RaiseLowerReachableSMagSector G σ τ)
    (h₂ : RaiseLowerStepSMagSector G τ ρ) :
    RaiseLowerReachableSMagSector G σ ρ :=
  Relation.ReflTransGen.tail h₁ h₂

/-- Lift `RaiseLowerReachableS` from the full type to the subtype
`magConfigS V N M`: given the chain endpoints both lie in the same
sector, the chain itself stays within the sector (by `magSumS`
preservation along each step). -/
theorem raiseLowerReachableSMagSector_of_raiseLowerReachableS
    {G : SimpleGraph V} {M : ℕ} {σ τ : V → Fin (N + 1)}
    (hσM : magSumS σ = M) (hτM : magSumS τ = M)
    (hreach : RaiseLowerReachableS G σ τ) :
    RaiseLowerReachableSMagSector G ⟨σ, hσM⟩ ⟨τ, hτM⟩ := by
  -- Generalize the target endpoint and its sector-proof.
  suffices h : ∀ (ρ : V → Fin (N + 1))
      (hρM : magSumS ρ = M)
      (_h : RaiseLowerReachableS G σ ρ),
      RaiseLowerReachableSMagSector G ⟨σ, hσM⟩ ⟨ρ, hρM⟩ from
    h τ hτM hreach
  intro ρ hρM hch
  induction hch with
  | refl =>
    -- σ = ρ; the subtypes are equal.
    convert RaiseLowerReachableSMagSector.refl G ⟨σ, hσM⟩
  | @tail b c _hσb hbc ih =>
    -- _hσb : RaiseLowerReachableS G σ b; hbc : RaiseLowerStepS G b c.
    -- ih : ∀ (hbM : magSumS b = M), RaiseLowerReachableSMagSector G ⟨σ, hσM⟩ ⟨b, hbM⟩.
    -- Goal: RaiseLowerReachableSMagSector G ⟨σ, hσM⟩ ⟨c, hρM⟩.
    have hbM : magSumS b = M := by
      have := magSumS_eq_of_raiseLowerStepS hbc
      omega
    apply RaiseLowerReachableSMagSector.tail' (ih hbM)
    exact hbc

/-- **Bipartite reachability for any two configurations in the same
magnetization sector** (lifted to the magConfigS subtype): under the
intermediate-existence hypothesis, any two `magConfigS V N M`
configurations are connected by a `RaiseLowerReachableSMagSector`
chain in the bipartite complete graph.

Proof: combine the full-type bipartite reachability theorem (#823)
with the subtype lifting (#840). -/
theorem raiseLowerReachableSMagSector_bipartiteCompleteGraph
    (A : V → Bool) {M : ℕ}
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (σ σ' : magConfigS V N M) :
    RaiseLowerReachableSMagSector (bipartiteCompleteGraphOf A) σ σ' := by
  have hreach : RaiseLowerReachableS (bipartiteCompleteGraphOf A) σ.1 σ'.1 :=
    raiseLowerReachableS_bipartiteCompleteGraph_of_eq_magSumS A
      h_intermediate (σ.2.trans σ'.2.symm)
  -- Lift to subtype.
  have := raiseLowerReachableSMagSector_of_raiseLowerReachableS σ.2 σ'.2 hreach
  -- this : RaiseLowerReachableSMagSector G ⟨σ.1, σ.2⟩ ⟨σ'.1, σ'.2⟩
  -- which is the same as σ → σ' (via Subtype.eta).
  exact this

end LatticeSystem.Quantum
