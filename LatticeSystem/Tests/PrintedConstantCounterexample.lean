/-
**Counterexample to the printed constant of Tasaki eq. (3.4.13), as literally quantified.**

Tasaki Problem 3.4.a (statement pp. 67-68, printed solution p. 501) asserts, for a Hamiltonian
`Ĥ = Σ_x ĥ_x` and order operator `Ô = Σ_x ô_x` on the periodic lattice `Λ_L`, each local term
supported on the radius-`r` ball of its own site with `manyBodyOperatorNormS ĥ_x ≤ h₀`,
`manyBodyOperatorNormS ô_x ≤ o₀`, and a normalized ground state `Φ`, the bound
`⟨Φ|[Ô,[Ĥ,Ô]]|Φ⟩ ≤ 4 (2r+1)^d (4r+1)^d h₀ o₀² L^d`.  This module exhibits an explicit `d = 1`,
`r = 1`, `L = 5` spin-1/2 ring satisfying every hypothesis of the Problem for which the printed
constant is **false**: the model attains `500`, exceeding the printed `4·3·5·1·1·5 = 300`.  It does
satisfy the repository's own honest bound `4 (4r+1)^d (8r+1)^d h₀ o₀² L^d = 500` (attained exactly,
`RangeLocalDoubleCommutatorBound.lean`), so nothing proved elsewhere in the repository is affected;
only the printed constant's literal quantification is refuted.  Whether the printed constant holds
in the regime `L > 4r+1` is left open.

The model: the 5-site ring `Λ = Fin 5` with `ringDist 5`, `ĥ_x = −Ẑ_{x−1}X̂_xẐ_{x+1}`,
`ô_x = X̂_{x−1}Ŷ_xX̂_{x+1}`, and the (normalized) cluster/graph state `Φ_GS` of the 5-cycle, which is
the unique ground state of `Ĥ = Σ_x ĥ_x` at `E₀ = −5` by Theorem 7.8
(`Quantum/SpinS/ClusterState.lean`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §3.4, Problem 3.4.a, statement pp. 67-68, printed solution p. 501.
-/
import LatticeSystem.Quantum.SpinS.ClusterState
import LatticeSystem.Quantum.SpinS.RangeLocalDoubleCommutatorBound
import LatticeSystem.Quantum.SpinS.ExpectationNormBound
import Mathlib.Combinatorics.SimpleGraph.Circulant

namespace LatticeSystem.Tests.PrintedConstantCounterexample

open LatticeSystem.Quantum LatticeSystem.Math Matrix

/-! ## Single-site 2×2 letters -/

/-- The single-site Pauli-`X` matrix `!![0,1;1,0]`. -/
private def sX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The single-site Pauli-`Z` matrix `!![1,0;0,-1]`. -/
private def sZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The single-site Pauli-`Y` matrix `!![0,-i;i,0]`. -/
private noncomputable def sY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-! ## The model: the 5-cycle, its local Hamiltonian/order terms, and its cluster ground state -/

/-- The 5-cycle graph on `Fin 5`, the site graph of the model.  An `abbrev` (not a plain `def`) so
that `cycleGraph`'s `DecidableRel Adj` instance is found by unfolding through typeclass search. -/
private noncomputable abbrev ringG : SimpleGraph (Fin 5) := SimpleGraph.cycleGraph 5

/-- The local Hamiltonian term `ĥ_x = −Ẑ_{x−1}X̂_xẐ_{x+1}` at site `x`. -/
private noncomputable def hLoc (x : Fin 5) : ManyBodyOpS (Fin 5) 1 :=
  -(onSiteS (x - 1) sZ * onSiteS x sX * onSiteS (x + 1) sZ)

/-- The local order-operator term `ô_x = X̂_{x−1}Ŷ_xX̂_{x+1}` at site `x`. -/
private noncomputable def oLoc (x : Fin 5) : ManyBodyOpS (Fin 5) 1 :=
  onSiteS (x - 1) sX * onSiteS x sY * onSiteS (x + 1) sX

/-- The unnormalized cluster-state ray representative of the 5-cycle. -/
private noncomputable def gsVec : (Fin 5 → Fin 2) → ℂ := clusterStateVec ringG

/-- The normalized ground state `Φ_GS` used in the counterexample. -/
private noncomputable def gsState : (Fin 5 → Fin 2) → ℂ := unitNormalize gsVec

/-! ## The counterexample -/

/-- **Counterexample to the printed constant of Tasaki eq. (3.4.13), as literally quantified.**
The explicit `d = 1`, `r = 1`, `L = 5` spin-1/2 ring model of this file (`hLoc`, `oLoc`, `gsState`)
satisfies every hypothesis of Problem 3.4.a (range-1 support, unit local-term norms, normalized
ground state at `E₀ = −5`) yet has `⟨Φ_GS|[Ô,[Ĥ,Ô]]|Φ_GS⟩ = 500`, exceeding the printed constant
`4(2·1+1)^1(4·1+1)^1·1·1²·5^1 = 300` of eq. (3.4.13) as literally quantified. The repository's own
proved bound `4(4·1+1)^1(8·1+1)^1·1·1²·5^1 = 500` (`RangeLocalDoubleCommutatorBound.lean`) is
attained exactly, and is unaffected. Whether the printed constant holds when `L > 4r+1` is open. -/
theorem tasaki_problem_3_4_a_printed_constant_counterexample :
    (∀ x : Fin 5, SupportedOnS (siteBall (ringDist 5) 1 x) (hLoc x)) ∧
      (∀ x : Fin 5, SupportedOnS (siteBall (ringDist 5) 1 x) (oLoc x)) ∧
      (∀ x : Fin 5, manyBodyOperatorNormS (hLoc x) ≤ 1) ∧
      (∀ x : Fin 5, manyBodyOperatorNormS (oLoc x) ≤ 1) ∧
      star gsState ⬝ᵥ gsState = 1 ∧
      IsGroundEnergy (∑ x, hLoc x) (-5) ∧
      (∑ x, hLoc x) *ᵥ gsState = ((-5 : ℝ) : ℂ) • gsState ∧
      rayleighOnVec
          ((∑ x, oLoc x) * ((∑ b, hLoc b) * (∑ x, oLoc x) - (∑ x, oLoc x) * (∑ b, hLoc b))
            - ((∑ b, hLoc b) * (∑ x, oLoc x) - (∑ x, oLoc x) * (∑ b, hLoc b)) * (∑ x, oLoc x))
          gsState = 500 ∧
      4 * (2 * (1 : ℝ) + 1) ^ 1 * (4 * (1 : ℝ) + 1) ^ 1 * 1 * 1 ^ 2 * (5 : ℝ) ^ 1
        < rayleighOnVec
            ((∑ x, oLoc x) * ((∑ b, hLoc b) * (∑ x, oLoc x) - (∑ x, oLoc x) * (∑ b, hLoc b))
              - ((∑ b, hLoc b) * (∑ x, oLoc x) - (∑ x, oLoc x) * (∑ b, hLoc b)) * (∑ x, oLoc x))
            gsState := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hLoc_supportedOnS_siteBall
  · exact oLoc_supportedOnS_siteBall
  · exact hLoc_manyBodyOperatorNormS_le_one
  · exact oLoc_manyBodyOperatorNormS_le_one
  · exact gsState_dotProduct_self_eq_one
  · exact hLoc_sum_isGroundEnergy
  · exact hLoc_sum_mulVec_gsState_eq_smul
  · exact doubleCommutator_rayleighOnVec_gsState_eq_five_hundred
  · exact doubleCommutator_rayleighOnVec_gsState_gt_printed_constant

/-
Positive control (to be added and run after Green, then reverted — §3.3 of the design):

example : (500 : ℝ) ≠ 4 * (4 * (1 : ℝ) + 1) ^ 1 * (4 * (1 : ℝ) + 1) ^ 1 * 1 * 1 ^ 2 * (5 : ℝ) ^ 1 :=
  by norm_num

replacing the printed-constant literal `4*(2r+1)^1*(4r+1)^1*...` by the honest-bound literal
`4*(4r+1)^1*(4r+1)^1*...` (both equal 500) must turn the strict `<` conjunct into `500 < 500`,
which must fail to build; likewise substituting `499` for the exact value `500` in the eighth
conjunct must fail to build; likewise dropping the sign in any one anticommutation δ-lemma used by
the (future) proof of the eighth/ninth conjuncts must fail to build.
-/

end LatticeSystem.Tests.PrintedConstantCounterexample
