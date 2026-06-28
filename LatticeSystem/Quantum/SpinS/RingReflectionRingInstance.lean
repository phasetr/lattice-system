/-
The Dyson–Lieb–Simon decomposition of the (gauged) ring antiferromagnet
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 15).

The gauged ring antiferromagnetic Heisenberg Hamiltonian splits as `H_L + θ(H_L) − Σ crossing`,
where the two crossing bonds of the even ring `Fin (2n)` are `(n−1, n)` and `(2n−1, 0)`, reflected
from the left sites `n−1` and `0`.  After the DLS/Marshall gauge their contribution is the negative
reflection-positive interaction `crossBondInteractionS (n−1) + crossBondInteractionS 0`.  This file
packages, for an arbitrary left-supported `H_L`, the resulting `RPDecomposition`
(`ringCrossingRPDecomposition`), identifies its interaction term, and concludes — via the Gibbs
capstone — that the gauged ring Gibbs weight is reflection positive
(`ring_gibbs_rpTraceWeight`).  The
concrete `H_L` (the left-half bond sum) and the unitary equivalence to the ungauged
`heisenbergHamiltonianS (ringCoupling (2n))` are the next step.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionGibbsCapstone
import LatticeSystem.Quantum.SpinS.MultiSiteDot

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- A two-site dot product `Ŝ_x · Ŝ_y` with both sites in the left half is left-supported. -/
theorem spinSDot_supportedOnLeft {x y : Fin (2 * n)} (hx : (x : ℕ) < n) (hy : (y : ℕ) < n) :
    SupportedOnLeftS n N (spinSDot x y N) := by
  rw [spinSDot_def]
  exact (((onSiteS_supportedOnLeft hx _).mul (onSiteS_supportedOnLeft hy _)).add
      ((onSiteS_supportedOnLeft hx _).mul (onSiteS_supportedOnLeft hy _))).add
    ((onSiteS_supportedOnLeft hx _).mul (onSiteS_supportedOnLeft hy _))

/-- The left site of the crossing bonds of the ring: `0` and `n − 1`. -/
def ringCrossingSite (n : ℕ) [NeZero n] : Fin 2 → Fin (2 * n) :=
  ![⟨0, by have := Nat.pos_of_ne_zero (NeZero.ne n); omega⟩,
    ⟨n - 1, by have := Nat.pos_of_ne_zero (NeZero.ne n); omega⟩]

/-- Value of the first crossing site. -/
@[simp] theorem ringCrossingSite_zero_val (n : ℕ) [NeZero n] :
    (ringCrossingSite n 0 : Fin (2 * n)).val = 0 := rfl

/-- Value of the second crossing site. -/
@[simp] theorem ringCrossingSite_one_val (n : ℕ) [NeZero n] :
    (ringCrossingSite n 1 : Fin (2 * n)).val = n - 1 := rfl

/-- The local spin operators indexed by `Fin 3`. -/
noncomputable def spinSOpFin3 (N : ℕ) : Fin 3 → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  ![spinSOp1 N, spinSOp2 N, spinSOp3 N]

/-- **The DLS decomposition of the gauged ring antiferromagnet** (arbitrary left part `H_L`): its
crossing bonds are the single-site spin operators at sites `0` and `n − 1`. -/
noncomputable def ringCrossingRPDecomposition [NeZero n] (hLeft : ManyBodyOpS (Fin (2 * n)) N)
    (hLeftSupp : SupportedOnLeftS n N hLeft) : RPDecomposition n N where
  hLeft := hLeft
  hLeftSupported := hLeftSupp
  bondιType := Fin 2 × Fin 3
  bondFintype := inferInstance
  bondOp := fun p => onSiteS (ringCrossingSite n p.1) (spinSOpFin3 N p.2)
  bondSupported := fun p => by
    apply onSiteS_supportedOnLeft
    obtain ⟨i, j⟩ := p
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    fin_cases i
    · exact hn
    · exact Nat.sub_lt hn Nat.one_pos

/-- The interaction term of the ring decomposition is the sum of the two gauged crossing-bond
interactions at sites `0` and `n − 1`. -/
theorem ringCrossingRPDecomposition_interaction [NeZero n] (hLeft : ManyBodyOpS (Fin (2 * n)) N)
    (hLeftSupp : SupportedOnLeftS n N hLeft) :
    (ringCrossingRPDecomposition hLeft hLeftSupp).interaction
      = crossBondInteractionS (ringCrossingSite n 0) N
        + crossBondInteractionS (ringCrossingSite n 1) N := by
  rw [RPDecomposition.interaction]
  change (∑ p : Fin 2 × Fin 3, onSiteS (ringCrossingSite n p.1) (spinSOpFin3 N p.2)
      * ringReflectionThetaS n N (onSiteS (ringCrossingSite n p.1) (spinSOpFin3 N p.2))) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [crossBondInteractionS, spinSOpFin3, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- The reconstructed Hamiltonian of the ring decomposition: `H_L + θ(H_L)` minus the two gauged
crossing-bond interactions. -/
theorem ringCrossingRPDecomposition_toHamiltonian [NeZero n] (hLeft : ManyBodyOpS (Fin (2 * n)) N)
    (hLeftSupp : SupportedOnLeftS n N hLeft) :
    (ringCrossingRPDecomposition hLeft hLeftSupp).toHamiltonian
      = hLeft + ringReflectionThetaS n N hLeft
        - (crossBondInteractionS (ringCrossingSite n 0) N
          + crossBondInteractionS (ringCrossingSite n 1) N) := by
  rw [RPDecomposition.toHamiltonian, ringCrossingRPDecomposition_interaction]
  rfl

/-- **The gauged ring Gibbs weight is a reflection-positive trace weight.**  For an arbitrary
left-supported `H_L` and `β ≥ 0`, `exp(-β · (H_L + θ(H_L) − crossing))` is a reflection-positive
trace weight. -/
theorem ring_gibbs_rpTraceWeight [NeZero n] (hLeft : ManyBodyOpS (Fin (2 * n)) N)
    (hLeftSupp : SupportedOnLeftS n N hLeft) {β : ℝ} (hβ : 0 ≤ β) :
    RPTraceWeightS n N
      (NormedSpace.exp (-(β : ℂ) • (ringCrossingRPDecomposition hLeft hLeftSupp).toHamiltonian)) :=
  (ringCrossingRPDecomposition hLeft hLeftSupp).gibbs_rpTraceWeight hβ

end LatticeSystem.Quantum
