import LatticeSystem.Quantum.SpinS.RaiseLower

/-!
# Parity-block reachability relation

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

The off-diagonal moves of the axis-swapped `Ĥ'` within a magnetization-parity block are:

* the **transverse** hop `Ŝ⁺_x Ŝ⁻_y / Ŝ⁻_x Ŝ⁺_y` on a bond (`RaiseLowerStepS`, magnetization
  preserving);
* the **bond parity** hop `Ŝ⁺_x Ŝ⁺_y / Ŝ⁻_x Ŝ⁻_y` on a bond (both sites `±1`, `±2` magnetization);
* the **single-ion** move `(Ŝ⁺_x)² / (Ŝ⁻_x)²` on one site (`±2` magnetization).

`ParityStepS` collects all three; `ParityReachableS` is its reflexive-transitive closure.  Two
configurations connected by `ParityReachableS` lie in the same parity block, and (with strictly
positive step amplitudes, case (i)) give a positive power of the shifted Perron–Frobenius matrix —
the input to parity-block irreducibility.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- A bond parity-hop step: both endpoints of a `G`-edge are raised (or both lowered) by one,
agreeing off the bond.  Magnetization changes by `±2`. -/
def ParityBondStepS (G : SimpleGraph V) (σ σ' : V → Fin (N + 1)) : Prop :=
  ∃ x y : V, G.Adj x y ∧
    (((σ x).val + 1 = (σ' x).val ∧ (σ y).val + 1 = (σ' y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ' y).val + 1 = (σ y).val)) ∧
    ∀ k, k ≠ x → k ≠ y → σ' k = σ k

/-- A single-ion step: one site is raised (or lowered) by two, agreeing off it.  Magnetization
changes by `±2`. -/
def SingleIonStepS (σ σ' : V → Fin (N + 1)) : Prop :=
  ∃ x : V,
    (((σ x).val + 2 = (σ' x).val) ∨ ((σ' x).val + 2 = (σ x).val)) ∧
    ∀ k, k ≠ x → σ' k = σ k

/-- A single parity-block move: a transverse hop, a bond parity hop, or a single-ion `±2` move. -/
def ParityStepS (G : SimpleGraph V) (σ σ' : V → Fin (N + 1)) : Prop :=
  RaiseLowerStepS G σ σ' ∨ ParityBondStepS G σ σ' ∨ SingleIonStepS σ σ'

/-- Reflexive-transitive closure of `ParityStepS`. -/
def ParityReachableS (G : SimpleGraph V) :
    (V → Fin (N + 1)) → (V → Fin (N + 1)) → Prop :=
  Relation.ReflTransGen (ParityStepS G)

omit [Fintype V] [DecidableEq V] in
/-- Reflexivity. -/
theorem ParityReachableS.refl (G : SimpleGraph V) (σ : V → Fin (N + 1)) :
    ParityReachableS G σ σ := Relation.ReflTransGen.refl

omit [Fintype V] [DecidableEq V] in
/-- A single step is reachable. -/
theorem ParityReachableS.single {G : SimpleGraph V} {σ σ' : V → Fin (N + 1)}
    (h : ParityStepS G σ σ') : ParityReachableS G σ σ' := Relation.ReflTransGen.single h

omit [Fintype V] [DecidableEq V] in
/-- Transitivity. -/
theorem ParityReachableS.trans {G : SimpleGraph V} {σ σ' σ'' : V → Fin (N + 1)}
    (h₁ : ParityReachableS G σ σ') (h₂ : ParityReachableS G σ' σ'') :
    ParityReachableS G σ σ'' := Relation.ReflTransGen.trans h₁ h₂

omit [Fintype V] [DecidableEq V] in
/-- A transverse hop is a parity-block move. -/
theorem ParityReachableS.of_raiseLower {G : SimpleGraph V} {σ σ' : V → Fin (N + 1)}
    (h : RaiseLowerStepS G σ σ') : ParityReachableS G σ σ' :=
  Relation.ReflTransGen.single (Or.inl h)

omit [Fintype V] [DecidableEq V] in
/-- A bond parity hop is a parity-block move. -/
theorem ParityReachableS.of_bond {G : SimpleGraph V} {σ σ' : V → Fin (N + 1)}
    (h : ParityBondStepS G σ σ') : ParityReachableS G σ σ' :=
  Relation.ReflTransGen.single (Or.inr (Or.inl h))

omit [Fintype V] [DecidableEq V] in
/-- A single-ion `±2` move is a parity-block move. -/
theorem ParityReachableS.of_singleIon {G : SimpleGraph V} {σ σ' : V → Fin (N + 1)}
    (h : SingleIonStepS σ σ') : ParityReachableS G σ σ' :=
  Relation.ReflTransGen.single (Or.inr (Or.inr h))

end LatticeSystem.Quantum
