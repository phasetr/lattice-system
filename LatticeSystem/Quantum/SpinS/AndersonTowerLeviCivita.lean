import LatticeSystem.Quantum.SpinS.AndersonTowerEnergyBoundSU2
import LatticeSystem.Quantum.SpinS.AndersonTowerSphereMoment

/-!
# Tasaki §4.2.2 Proposition 4.10: Levi-Civita bookkeeping for the total×order rotation commutators

The swap-band telescoping of the Cartesian order word `cartWord w` (Prop 4.10 arc PR-3.2b) pushes a
total-spin generator `Ŝ^{(γ)}_tot` through the ordered product `∏_j ô^{(w_j)}`, replacing one axis
letter `w_k = β` by the rotated axis `δ` weighted by `i ε_{γβδ}`.  To keep the axis case analysis in
a single place, this module packages:

* the **Levi-Civita scalar** `leviCivita3 : Fin 3 → Fin 3 → Fin 3 → ℂ` (the totally antisymmetric
  symbol with `ε_{012} = 1`), so that the double axis index of the contraction lives in the `ℂ`
  scalar and is folded by `Finset.sum` algebra rather than by hand;
* the **total-spin generator vector** `totalSpinSOpVec γ = Ŝ^{(γ)}_tot` bundling the three Cartesian
  total-spin operators `totalSpinSOp{1,2,3}` over the axis index `Fin 3`;
* the **diagonal rotation commutators** `[Ŝ^{(γ)}_tot, ô^{(γ)}] = 0` (same-axis, hence commuting);
* the **uniform single-letter rotation commutator**
  `[Ŝ^{(γ)}_tot, ô^{(β)}] = i Σ_δ ε_{γβδ} ô^{(δ)}`, which merges the six off-diagonal total×order
  commutators (`AndersonTowerEnergyBoundSU2`) and the three diagonal ones into a single statement.
  The `fin_cases`-driven axis case split is isolated to the proof of this one lemma.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, eqs. (4.2.58)–(4.2.59), p.108; cf. Tasaki, arXiv:1807.05847.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ### The Levi-Civita scalar and the total-spin generator vector -/

/-- The **Levi-Civita symbol** `ε_{γβδ}` on `Fin 3`, valued in `ℂ`: the totally antisymmetric scalar
normalised by `ε_{012} = 1`, taking the value `+1` on the even permutations `(0,1,2)`, `(1,2,0)`,
`(2,0,1)`, the value `−1` on the odd permutations `(0,2,1)`, `(1,0,2)`, `(2,1,0)`, and `0` whenever
two indices coincide.  Carrying the axis double index of the swap-band contraction as this `ℂ`
scalar lets the `Finset.sum` over axes absorb the case analysis. -/
def leviCivita3 : Fin 3 → Fin 3 → Fin 3 → ℂ
  | 0, 1, 2 => 1
  | 1, 2, 0 => 1
  | 2, 0, 1 => 1
  | 0, 2, 1 => -1
  | 1, 0, 2 => -1
  | 2, 1, 0 => -1
  | _, _, _ => 0

/-- The **total-spin generator vector** `γ ↦ Ŝ^{(γ)}_tot`: axis `0` is `totalSpinSOp1`, axis `1` is
`totalSpinSOp2`, axis `2` is `totalSpinSOp3`.  It bundles the three Cartesian total-spin generators
over the axis index `Fin 3`, mirroring the staggered order vector `stagOpVec`, so that the rotation
commutator `[Ŝ^{(γ)}_tot, ô^{(β)}]` can be stated uniformly in the axis indices. -/
noncomputable def totalSpinSOpVec (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ) :
    Fin 3 → ManyBodyOpS Λ N :=
  ![totalSpinSOp1 Λ N, totalSpinSOp2 Λ N, totalSpinSOp3 Λ N]

/-! ### Diagonal (same-axis) rotation commutators `[Ŝ^{(γ)}_tot, ô^{(γ)}] = 0` -/

/-- Per-site step of the diagonal commutator `[Ŝ^{(1)}_x, ô^{(1)}] = 0`: the site-`x` `Ŝ^{(1)}`
commutes with every summand of `ô^{(1)} = Σ_y ε_y Ŝ^{(1)}_y` — off-site by locality, on-site because
`Ŝ^{(1)}` commutes with itself. -/
private theorem spinSSiteOp1_commutator_staggeredOrderOp1S (A : Λ → Bool) (x : Λ) :
    spinSSiteOp1 x N * staggeredOrderOp1S A N - staggeredOrderOp1S A N * spinSSiteOp1 x N = 0 := by
  unfold staggeredOrderOp1S spinSSiteOp1
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_eq_single x]
  · rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, onSiteS_mul_onSiteS_same,
      ← onSiteS_sub, sub_self, onSiteS_zero, smul_zero]
  · intro y _ hyx
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub,
      (onSiteS_commute_of_ne (Ne.symm hyx) (spinSOp1 N) (spinSOp1 N)).eq, sub_self, smul_zero]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- **Diagonal rotation commutator** `[Ŝ^{(1)}_tot, ô_L^{(1)}] = 0` (`ε_{11δ} = 0`). -/
theorem totalSpinSOp1_commutator_staggeredOrderOp1S (A : Λ → Bool) :
    totalSpinSOp1 Λ N * staggeredOrderOp1S A N - staggeredOrderOp1S A N * totalSpinSOp1 Λ N
      = 0 := by
  have hsum : (totalSpinSOp1 Λ N : ManyBodyOpS Λ N) = ∑ x : Λ, spinSSiteOp1 x N := rfl
  rw [hsum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_eq_zero fun x _ => spinSSiteOp1_commutator_staggeredOrderOp1S A x

/-- Per-site step of the diagonal commutator `[Ŝ^{(2)}_x, ô^{(2)}] = 0`. -/
private theorem spinSSiteOp2_commutator_staggeredOrderOp2S (A : Λ → Bool) (x : Λ) :
    spinSSiteOp2 x N * staggeredOrderOp2S A N - staggeredOrderOp2S A N * spinSSiteOp2 x N = 0 := by
  unfold staggeredOrderOp2S spinSSiteOp2
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_eq_single x]
  · rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, onSiteS_mul_onSiteS_same,
      ← onSiteS_sub, sub_self, onSiteS_zero, smul_zero]
  · intro y _ hyx
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub,
      (onSiteS_commute_of_ne (Ne.symm hyx) (spinSOp2 N) (spinSOp2 N)).eq, sub_self, smul_zero]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- **Diagonal rotation commutator** `[Ŝ^{(2)}_tot, ô_L^{(2)}] = 0` (`ε_{22δ} = 0`). -/
theorem totalSpinSOp2_commutator_staggeredOrderOp2S (A : Λ → Bool) :
    totalSpinSOp2 Λ N * staggeredOrderOp2S A N - staggeredOrderOp2S A N * totalSpinSOp2 Λ N
      = 0 := by
  have hsum : (totalSpinSOp2 Λ N : ManyBodyOpS Λ N) = ∑ x : Λ, spinSSiteOp2 x N := rfl
  rw [hsum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_eq_zero fun x _ => spinSSiteOp2_commutator_staggeredOrderOp2S A x

/-- Per-site step of the diagonal commutator `[Ŝ^{(3)}_x, ô^{(3)}] = 0`. -/
private theorem spinSSiteOp3_commutator_staggeredOrderOpS (A : Λ → Bool) (x : Λ) :
    spinSSiteOp3 x N * staggeredOrderOpS A N - staggeredOrderOpS A N * spinSSiteOp3 x N = 0 := by
  unfold staggeredOrderOpS spinSSiteOp3
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_eq_single x]
  · rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, onSiteS_mul_onSiteS_same,
      ← onSiteS_sub, sub_self, onSiteS_zero, smul_zero]
  · intro y _ hyx
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub,
      (onSiteS_commute_of_ne (Ne.symm hyx) (spinSOp3 N) (spinSOp3 N)).eq, sub_self, smul_zero]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- **Diagonal rotation commutator** `[Ŝ^{(3)}_tot, ô_L^{(3)}] = 0` (`ε_{33δ} = 0`). -/
theorem totalSpinSOp3_commutator_staggeredOrderOpS (A : Λ → Bool) :
    totalSpinSOp3 Λ N * staggeredOrderOpS A N - staggeredOrderOpS A N * totalSpinSOp3 Λ N = 0 := by
  have hsum : (totalSpinSOp3 Λ N : ManyBodyOpS Λ N) = ∑ x : Λ, spinSSiteOp3 x N := rfl
  rw [hsum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_eq_zero fun x _ => spinSSiteOp3_commutator_staggeredOrderOpS A x

/-! ### The uniform single-letter rotation commutator -/

/-- **Uniform total×order rotation commutator** `[Ŝ^{(γ)}_tot, ô^{(β)}] = i Σ_δ ε_{γβδ} ô^{(δ)}`.
The single statement collecting the six off-diagonal total×order commutators
(`AndersonTowerEnergyBoundSU2`) and the three diagonal ones: pushing a total-spin generator past a
single staggered axis operator rotates that axis by the Levi-Civita weight `i ε_{γβδ}`.  This is the
one-letter step of the swap-band telescoping (Prop 4.10 arc PR-3.2b-ii); the `fin_cases` axis case
split is confined to this proof. -/
theorem totalSpinSOpVec_commutator_stagOpVec (A : Λ → Bool) (γ β : Fin 3) :
    totalSpinSOpVec Λ N γ * stagOpVec A N β - stagOpVec A N β * totalSpinSOpVec Λ N γ
      = Complex.I • ∑ δ : Fin 3, leviCivita3 γ β δ • stagOpVec A N δ := by
  fin_cases γ <;> fin_cases β <;>
    simp only [totalSpinSOpVec, stagOpVec, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Fin.sum_univ_three, leviCivita3]
  · rw [totalSpinSOp1_commutator_staggeredOrderOp1S]; module
  · rw [totalSpinSOp1_commutator_staggeredOrderOp2S]; module
  · rw [totalSpinSOp1_commutator_staggeredOrderOpS]; module
  · rw [totalSpinSOp2_commutator_staggeredOrderOp1S]; module
  · rw [totalSpinSOp2_commutator_staggeredOrderOp2S]; module
  · rw [totalSpinSOp2_commutator_staggeredOrderOpS]; module
  · rw [totalSpinSOp3_commutator_staggeredOrderOp1S]; module
  · rw [totalSpinSOp3_commutator_staggeredOrderOp2S]; module
  · rw [totalSpinSOp3_commutator_staggeredOrderOpS]; module

end LatticeSystem.Quantum
