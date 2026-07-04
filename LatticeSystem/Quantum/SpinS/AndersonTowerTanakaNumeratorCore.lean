/-
Tasaki §4.2.2 Theorem 4.8 (Tanaka symmetry-breaking state), crux sub-arc PR-C — the charge
`{−2, 0, +2}` decomposition of the `1`-axis double commutator.

The Anderson-tower numerator inserts, at each of the `M²` telescoping positions
(`double_commutator_pow_eq_double_sum`, eq. (4.2.71)), the single physical double commutator
`d̃ = [ô^{(1)}, [Ĥ, ô^{(1)}]]` of the `1`-axis order density `ô^{(1)} = ô⁺ + ô⁻` (working with the
scale-invariant summed density `Ã = ô⁺ + ô⁻`, the volume factor already dropped in PR-A).  Because
`Ã = ô⁺ + ô⁻` mixes the two magnetization charges, `d̃` is *not* charge homogeneous; it splits into
four physical pieces, grouped by net `Ŝ_tot^{(3)}`-charge into three blocks (eq. (4.2.67)):

* charge `+2`: `G₊ = [ô⁺, [Ĥ, ô⁺]]` (`orderDoubleCommSameSign true`);
* charge `−2`: `G₋ = [ô⁻, [Ĥ, ô⁻]]` (`orderDoubleCommSameSign false`);
* charge `0`:  `G₀ = [ô⁺, [Ĥ, ô⁻]] + [ô⁻, [Ĥ, ô⁺]]` (`orderDoubleComm + orderDoubleCommMirror`).

Each piece is charge homogeneous, so the crux (PR-D) can apply the cross-charge selection rule
(`dotProduct_word_sandwich_eq_zero_of_charge_ne`) block by block and count the surviving words with
a central binomial coefficient.  Every piece already lies in the local-decay class (its
`IsR2LocalUpTo` membership was built in PR2/PR-B: `isR2LocalUpTo_orderDoubleCommSameSign`,
`isR2LocalUpTo_orderDoubleComm`, `isR2LocalUpTo_orderDoubleCommMirror`), so PR-D reuses the
word-generic leaf bound verbatim.

This file provides only the charge decomposition and its per-piece charge homogeneity; it touches
none of the crux core (the `Nat.choose` counting / Pascal ratio, deferred to PR-D).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, eqs. (4.2.67)/(4.2.71), pp. 111–112 (Tanaka [62]).
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerSameSignDecay
import LatticeSystem.Quantum.SpinS.AndersonTowerOrderSumExpansion

namespace LatticeSystem.Quantum

open Matrix

variable {d L N : ℕ}

/-! ### Charge homogeneity of a commutator bracket -/

/-- **Charge homogeneity of a bracket.**  If a charge operator `S` commutes with `X` and `Y` up to
the scalar charges `a` and `b` (`[S, X] = a X`, `[S, Y] = b Y`), then it commutes with the bracket
`X Y − Y X` up to the summed charge, `[S, X Y − Y X] = (a + b)(X Y − Y X)`.  Applies
`commutator_smul_of_smul` to each of the two products. -/
private theorem commutator_bracket_smul {n : Type*} [Fintype n]
    {S X Y : Matrix n n ℂ} {a b : ℂ} (hX : S * X - X * S = a • X) (hY : S * Y - Y * S = b • Y) :
    S * (X * Y - Y * X) - (X * Y - Y * X) * S = (a + b) • (X * Y - Y * X) := by
  have hXY := commutator_smul_of_smul hX hY
  have hYX := commutator_smul_of_smul hY hX
  rw [show S * (X * Y - Y * X) - (X * Y - Y * X) * S
        = (S * (X * Y) - (X * Y) * S) - (S * (Y * X) - (Y * X) * S) from by noncomm_ring,
    hXY, hYX, add_comm b a, smul_sub]

/-- **Charge of the single Heisenberg–order commutator** `[Ŝ_tot^{(3)}, [Ĥ, ô^c]] = ε_c [Ĥ, ô^c]`
(`ε_true = +1`, `ε_false = −1`): since `Ĥ` is charge neutral (`[Ŝ_tot^{(3)}, Ĥ] = 0`) and `ô^c`
carries charge `ε_c`, the commutator `[Ĥ, ô^c]` inherits charge `ε_c`. -/
theorem totalSpinSOp3_commutator_heisenbergSignComm (d L N : ℕ) [NeZero L] (c : Bool) :
    totalSpinSOp3 (HypercubicTorus d L) N * heisenbergSignComm d L N c
        - heisenbergSignComm d L N c * totalSpinSOp3 (HypercubicTorus d L) N
      = (if c then (1 : ℂ) else (-1 : ℂ)) • heisenbergSignComm d L N c := by
  have hH : totalSpinSOp3 (HypercubicTorus d L) N * heisenbergHamiltonianS (torusNNCoupling d L) N
        - heisenbergHamiltonianS (torusNNCoupling d L) N * totalSpinSOp3 (HypercubicTorus d L) N
      = (0 : ℂ) • heisenbergHamiltonianS (torusNNCoupling d L) N := by
    have h := heisenbergHamiltonianS_commutator_totalSpinSOp3 (torusNNCoupling d L) N
    rw [zero_smul, ← neg_sub, h, neg_zero]
  have h := commutator_bracket_smul hH (totalSpinSOp3_commutator_orderDensity d L N c)
  rw [zero_add] at h
  exact h

/-! ### The charge decomposition of `d̃ = [Ã, [Ĥ, Ã]]` -/

/-- The **`1`-axis double commutator** `d̃ = [Ã, [Ĥ, Ã]]` of the scale-invariant summed order
density `Ã = ô⁺ + ô⁻`, `d̃ = Ã (Ĥ Ã − Ã Ĥ) − (Ĥ Ã − Ã Ĥ) Ã`.  This is exactly the middle operator
inserted at each telescoping position of `double_commutator_pow_eq_double_sum` (eq. (4.2.71)) with
`A = Ã`, `H = Ĥ`. -/
noncomputable def orderDensitySumDoubleComm (d L N : ℕ) [NeZero L] :
    ManyBodyOpS (HypercubicTorus d L) N :=
  (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false)
      * (heisenbergHamiltonianS (torusNNCoupling d L) N
          * (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false)
        - (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false)
          * heisenbergHamiltonianS (torusNNCoupling d L) N)
    - (heisenbergHamiltonianS (torusNNCoupling d L) N
          * (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false)
        - (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false)
          * heisenbergHamiltonianS (torusNNCoupling d L) N)
      * (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false)

/-- **Charge `{−2, 0, +2}` decomposition** (eq. (4.2.67)): the `1`-axis double commutator splits
into its four physical pieces `d̃ = G₊ + [ô⁺, [Ĥ, ô⁻]] + [ô⁻, [Ĥ, ô⁺]] + G₋`, grouped by net charge
into `G₊` (charge `+2`), `G₀ = orderDoubleComm + orderDoubleCommMirror` (charge `0`), and `G₋`
(charge `−2`).  Proved by bilinear expansion of `Ã = ô⁺ + ô⁻`. -/
theorem orderDensitySumDoubleComm_eq_charge_pieces (d L N : ℕ) [NeZero L] :
    orderDensitySumDoubleComm d L N
      = orderDoubleCommSameSign d L N true + orderDoubleComm d L N
        + orderDoubleCommMirror d L N + orderDoubleCommSameSign d L N false := by
  rw [orderDensitySumDoubleComm, orderDoubleCommSameSign, orderDoubleCommSameSign, orderDoubleComm,
    orderDoubleCommMirror, heisenbergSignComm, heisenbergSignComm]
  noncomm_ring

/-! ### Per-piece charge homogeneity -/

/-- **`G₊ = [ô⁺, [Ĥ, ô⁺]]` and `G₋ = [ô⁻, [Ĥ, ô⁻]]` are charge homogeneous**:
`[Ŝ_tot^{(3)}, orderDoubleCommSameSign b] = (2 ε_b) orderDoubleCommSameSign b` (`+2` for `b = true`,
`−2` for `b = false`).  Both `ô^b` and `[Ĥ, ô^b]` carry charge `ε_b`, so the bracket carries
`2 ε_b`. -/
theorem totalSpinSOp3_commutator_orderDoubleCommSameSign (d L N : ℕ) [NeZero L] (b : Bool) :
    totalSpinSOp3 (HypercubicTorus d L) N * orderDoubleCommSameSign d L N b
        - orderDoubleCommSameSign d L N b * totalSpinSOp3 (HypercubicTorus d L) N
      = (if b then (2 : ℂ) else (-2 : ℂ)) • orderDoubleCommSameSign d L N b := by
  have h := commutator_bracket_smul (totalSpinSOp3_commutator_orderDensity d L N b)
    (totalSpinSOp3_commutator_heisenbergSignComm d L N b)
  have hscalar : (if b then (2 : ℂ) else (-2 : ℂ))
      = (if b then (1 : ℂ) else (-1 : ℂ)) + (if b then (1 : ℂ) else (-1 : ℂ)) := by
    cases b <;> norm_num
  rw [hscalar]
  exact h

/-- **`orderDoubleComm = [ô⁺, [Ĥ, ô⁻]]` is charge neutral**:
`[Ŝ_tot^{(3)}, orderDoubleComm] = 0`.  Charge `ε_true + ε_false = 1 + (−1) = 0`. -/
theorem totalSpinSOp3_commutator_orderDoubleComm (d L N : ℕ) [NeZero L] :
    totalSpinSOp3 (HypercubicTorus d L) N * orderDoubleComm d L N
        - orderDoubleComm d L N * totalSpinSOp3 (HypercubicTorus d L) N
      = 0 := by
  have h := commutator_bracket_smul (totalSpinSOp3_commutator_orderDensity d L N true)
    (totalSpinSOp3_commutator_heisenbergSignComm d L N false)
  rw [show ((if true then (1 : ℂ) else (-1 : ℂ)) + (if false then (1 : ℂ) else (-1 : ℂ)))
      = 0 from by norm_num, zero_smul] at h
  exact h

/-- **`orderDoubleCommMirror = [ô⁻, [Ĥ, ô⁺]]` is charge neutral**:
`[Ŝ_tot^{(3)}, orderDoubleCommMirror] = 0`.  Charge `ε_false + ε_true = (−1) + 1 = 0`. -/
theorem totalSpinSOp3_commutator_orderDoubleCommMirror (d L N : ℕ) [NeZero L] :
    totalSpinSOp3 (HypercubicTorus d L) N * orderDoubleCommMirror d L N
        - orderDoubleCommMirror d L N * totalSpinSOp3 (HypercubicTorus d L) N
      = 0 := by
  have h := commutator_bracket_smul (totalSpinSOp3_commutator_orderDensity d L N false)
    (totalSpinSOp3_commutator_heisenbergSignComm d L N true)
  rw [show ((if false then (1 : ℂ) else (-1 : ℂ)) + (if true then (1 : ℂ) else (-1 : ℂ)))
      = 0 from by norm_num, zero_smul] at h
  exact h

end LatticeSystem.Quantum
