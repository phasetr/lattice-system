import LatticeSystem.Quantum.SpinS.AndersonTowerSphereMoment
import LatticeSystem.Quantum.SpinS.AndersonTowerEnergyBoundSU2

/-!
# Tasaki §4.2: the squared order operator `ô²` and its transverse/longitudinal split

This module opens the commutator-contraction arc for Tasaki's Proposition 4.10 (§4.2.2).  It defines
the **rotationally invariant squared order operator**

`ô² = Σ_{α} (ô^{(α)})²  =  (ô^{(1)})² + (ô^{(2)})² + (ô^{(3)})²`

(`orderSqOp`), the main-part operator whose `(M/2)`-th power carries the leading contribution of the
sphere average `∫_{S²} (Ô_L^n)^M dσ(n)` after the ordered product is contracted.  It records the
bridge to the `U(1)`-symmetric order operator `p̂` (`staggeredPhatS`),

`ô² = V² · p̂ + (ô^{(3)})²`,

which lets the transverse part `(ô^{(1)})² + (ô^{(2)})²` be handled through the existing Theorem 4.9
`p̂`-moment machinery, and the auxiliary singlet fact that a total-`Ŝ³`- and `Ŝ¹`-singlet state is
automatically a total-`Ŝ²`-singlet (`Ŝ² = −i[Ŝ³, Ŝ¹]`), needed so that all three Cartesian
total-spin generators annihilate the state in the later commutator-contraction steps.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, Proposition 4.10, eqs. (4.2.31), (4.2.58)–(4.2.60), p.108.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The **rotationally invariant squared order operator** `ô² = Σ_α (ô^{(α)})²`, the sum over the
three spin axes of the squared staggered axis operators (`stagOpVec`).  It is the operator whose
`(M/2)`-th power `(ô²)^{M/2}` provides the leading `(4π/(M+1))`-weighted term of the sphere average
`∫_{S²} (Ô_L^n)^M dσ(n)` once the ordered operator product is contracted via axis commutators. -/
noncomputable def orderSqOp (A : Λ → Bool) (N : ℕ) : ManyBodyOpS Λ N :=
  ∑ α : Fin 3, stagOpVec A N α ^ 2

/-- **Transverse/longitudinal split of `ô²`** (Tasaki eq. (4.2.31) bridge).  On the hypercubic torus
the squared order operator decomposes as `ô² = V² · p̂ + (ô^{(3)})²`, where `V = L^d` is the volume,
`p̂ = staggeredPhatS` is the `U(1)`-symmetric order operator carrying the transverse part
`(ô^{(1)})² + (ô^{(2)})²`, and `(ô^{(3)})² = staggeredOrderOpS²` is the longitudinal part.  The
factor `V²` undoes the per-volume normalisation built into `p̂`. -/
theorem orderSqOp_eq_smul_staggeredPhatS_add_sq (d L N : ℕ) [NeZero L] :
    orderSqOp (torusParitySublattice d L) N
      = ((L : ℂ) ^ d) ^ 2 • staggeredPhatS d L N
          + staggeredOrderOpS (torusParitySublattice d L) N ^ 2 := by
  have hV2ne : ((L : ℂ) ^ d) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (pow_ne_zero d (Nat.cast_ne_zero.mpr (NeZero.ne L)))
  have hexpand : orderSqOp (torusParitySublattice d L) N
      = staggeredOrderOp1S (torusParitySublattice d L) N ^ 2
        + staggeredOrderOp2S (torusParitySublattice d L) N ^ 2
        + staggeredOrderOpS (torusParitySublattice d L) N ^ 2 := by
    simp only [orderSqOp, Fin.sum_univ_three, stagOpVec, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  rw [hexpand, staggeredPhatS_eq_cartesian_sq, smul_smul, mul_inv_cancel₀ hV2ne, one_smul]
  simp only [pow_two]

/-- **Singlet closure of the third total-spin generator.**  If a state `Φ` is annihilated by the
total-spin `3`-axis and `1`-axis generators (`Ŝ³_tot Φ = 0`, `Ŝ¹_tot Φ = 0`), then it is also
annihilated by the `2`-axis generator (`Ŝ²_tot Φ = 0`), via the SU(2) commutator
`Ŝ²_tot = −i[Ŝ³_tot, Ŝ¹_tot]`.  Thus a total-`Ŝ³`/`Ŝ¹`-singlet is a full total-spin singlet, so all
three Cartesian generators can be pushed through the later commutator-contraction words. -/
theorem totalSpinSOp2_mulVec_eq_zero_of_singlet (Φ : (Λ → Fin (N + 1)) → ℂ)
    (h3 : (totalSpinSOp3 Λ N).mulVec Φ = 0) (h1 : (totalSpinSOp1 Λ N).mulVec Φ = 0) :
    (totalSpinSOp2 Λ N).mulVec Φ = 0 := by
  have e : Complex.I • (totalSpinSOp2 Λ N)
      = totalSpinSOp3 Λ N * totalSpinSOp1 Λ N - totalSpinSOp1 Λ N * totalSpinSOp3 Λ N := by
    simp only [totalSpinSOp1, totalSpinSOp2, totalSpinSOp3]
    exact (totalSpinSOp3_commutator_totalSpinSOp1 (Λ := Λ) N).symm
  have key : Complex.I • (totalSpinSOp2 Λ N).mulVec Φ = 0 := by
    rw [← Matrix.smul_mulVec, e, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      h1, h3, Matrix.mulVec_zero, Matrix.mulVec_zero, sub_zero]
  exact (smul_eq_zero.mp key).resolve_left Complex.I_ne_zero

end LatticeSystem.Quantum
