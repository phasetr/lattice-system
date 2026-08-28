import LatticeSystem.Quantum.SpinS.BasisVecSOrthonormal
import LatticeSystem.Quantum.SpinS.SaturatedCoherentWeight

/-!
# Test coverage for Tasaki Problem 2.4.b — `Φ_M`, `c_M(θ)`, expansion, nonvanishing

Signature pin for the declarations of `LatticeSystem/Quantum/SpinS/SaturatedCoherentWeight.lean`:
`saturatedWeightVector` (the normalised weight state `Φ_M` of eq. (2.4.9), printed p. 33),
`saturatedCoherentCoeff` (the coefficient `c_M(θ) := ⟪Φ_M, Ξ_{θ,0}⟫`), the expansion theorem
`saturatedCoherentState_zero_eq_sum` (the `|Φ⟩ = Ξ_{θ,0}` instance of Theorem 2.1 / eq. (2.4.10),
printed p. 34), and the nonvanishing theorem `saturatedCoherentCoeff_ne_zero`. Together these are
the two ingredients that Problem 2.4.b (statement p. 34, solution pp. 496-497) needs before its
own capstone, eq. (S.17), can be stated.

The fixtures fix the exact name, binder order, and hypothesis set of each declaration (no
hypothesis beyond what each theorem's proof actually uses — in particular no `Nonempty V` on the
two definitions, and no coefficient/expansion side hypothesis on the nonvanishing theorem beyond
`0 < θ`, `θ < π`), and pin two concrete instances (`|Λ| = 1` and `|Λ| = 2`, both at `N = 1`) that
exercise the `k ↦ M` orientation and exclude a vacuous hypothesis set.
-/

namespace LatticeSystem.Tests.Problem24bWeightExpansion

open LatticeSystem.Quantum

/-! ## Signature pins: no hypothesis beyond what each proof route actually needs -/

/-- **Expansion signature pin.** For any nonempty site set `V`, spin data `N`, and angle `θ`, the
coherent state at `φ = 0` is the sum, over every weight index `k`, of `c_k(θ) • Φ_k`. This fixture
pins `saturatedCoherentState_zero_eq_sum`'s exact name, binder order (`V N` implicit-typeclass,
`[Nonempty V]`, `θ` explicit) and hypothesis set: no side hypothesis beyond `[Nonempty V]`. -/
example {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ} [Nonempty V] (θ : ℝ) :
    saturatedCoherentState V N θ 0
      = ∑ k, saturatedCoherentCoeff V N θ k • saturatedWeightVector V N k :=
  saturatedCoherentState_zero_eq_sum θ

/-- **Nonvanishing signature pin.** For any nonempty site set `V`, spin data `N`, angle `θ` strictly
between `0` and `π`, and weight index `k`, the coefficient `c_k(θ)` is nonzero. This fixture pins
`saturatedCoherentCoeff_ne_zero`'s exact hypothesis set: `[Nonempty V]`, `0 < θ`, `θ < π`, and
`k` — no expansion hypothesis, no all-sector closed-form coefficient hypothesis. -/
example {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ} [Nonempty V] {θ : ℝ}
    (hθ₀ : 0 < θ) (hθπ : θ < Real.pi) (k : Fin (Fintype.card V * N + 1)) :
    saturatedCoherentCoeff V N θ k ≠ 0 :=
  saturatedCoherentCoeff_ne_zero hθ₀ hθπ k

/-! ## Anti-vacuity instantiation -/

/-- **Anti-vacuity.** The nonvanishing theorem's hypothesis set is satisfiable: at `|Λ| = 2`,
`N = 1`, `θ = π/2`, `k = 1`, it produces a concrete nonzero coefficient. Excludes a vacuous
hypothesis set mechanically (the defect class recorded for `Problem23a.lean`). -/
example : saturatedCoherentCoeff (Fin 2) 1 (Real.pi / 2) 1 ≠ 0 :=
  saturatedCoherentCoeff_ne_zero (by positivity)
    (by linarith [Real.pi_pos]) 1

/-! ## `|Λ| = 1`, `N = 1` fixture: the `k ↦ M` orientation -/

/-- At `|Λ| = 1`, `N = 1` the `k = 0` ladder iterate is the all-up basis vector. -/
private lemma ladderIterateUp_fin_one_zero :
    ladderIterateUp (Fin 1) 1 0 = basisVecS (fun _ => (0 : Fin 2)) := by
  rw [ladderIterateUp, show ((0 : Fin (Fintype.card (Fin 1) * 1 + 1)) : ℕ) = 0 from rfl, pow_zero,
    Matrix.one_mulVec]
  rfl

/-- At `|Λ| = 1`, `N = 1` the `k = 1` ladder iterate is the all-down basis vector: a single
lowering carries the all-up state to it with coefficient `1`. -/
private lemma ladderIterateUp_fin_one_one :
    ladderIterateUp (Fin 1) 1 1 = basisVecS (fun _ => (1 : Fin 2)) := by
  funext τ
  rw [ladderIterateUp, show ((1 : Fin (Fintype.card (Fin 1) * 1 + 1)) : ℕ) = 1 from rfl, pow_one]
  simp only [totalSpinSOpMinus, Finset.univ_unique, Finset.sum_singleton, allAlignedStateS,
    onSiteS_mulVec_basisVecS_apply, onSiteS_apply, basisVecS_apply, allAlignedConfigS]
  rw [if_pos fun k hk => absurd (Subsingleton.elim k default) hk]
  simp [spinSOpMinus, funext_iff, Fin.forall_fin_one, Fin.ext_iff, @eq_comm ℕ 1]

/-- **Weight-vector orientation at `|Λ| = 1`.** The `k = 1` weight vector (one lowering from the
all-up state) is exactly the all-down basis vector: `Φ_M` at `k = 1` is the state with `M`
minimal, not maximal. This is the check that catches a reversed `k ↦ M` index. -/
example : saturatedWeightVector (Fin 1) 1 1 = basisVecS (fun _ => (1 : Fin 2)) := by
  rw [saturatedWeightVector, saturatedLadderNorm, ladderIterateUp_fin_one_one,
    norm_toLp_basisVecS_eq_one, Complex.ofReal_one, inv_one, one_smul]

/-- **Coefficient at `k = 0` (all-up weight), `|Λ| = 1`.** `c_0(θ) = cos(θ/2)`. -/
example (θ : ℝ) : saturatedCoherentCoeff (Fin 1) 1 θ 0 = Complex.cos (θ / 2) := by
  rw [saturatedCoherentCoeff, saturatedWeightVector, saturatedLadderNorm,
    ladderIterateUp_fin_one_zero, norm_toLp_basisVecS_eq_one, Complex.ofReal_one, inv_one,
    one_smul, EuclideanSpace.inner_toLp_toLp, dotProduct_star_basisVecS,
    saturatedCoherentState_zero_apply]
  simp [saturatedCoherentAmp]

/-- **Coefficient at `k = 1` (all-down weight), `|Λ| = 1`.** `c_1(θ) = sin(θ/2)`. This, together
with the `k = 0` fixture above, pins the `k ↦ M` orientation on the coefficient side as well as on
`saturatedWeightVector`. -/
example (θ : ℝ) : saturatedCoherentCoeff (Fin 1) 1 θ 1 = Complex.sin (θ / 2) := by
  rw [saturatedCoherentCoeff, saturatedWeightVector, saturatedLadderNorm,
    ladderIterateUp_fin_one_one, norm_toLp_basisVecS_eq_one, Complex.ofReal_one, inv_one,
    one_smul, EuclideanSpace.inner_toLp_toLp, dotProduct_star_basisVecS,
    saturatedCoherentState_zero_apply]
  simp [saturatedCoherentAmp]

/-! ## `V = Fin 0` value fixture (targets only the Problem 2.4.c eq. (S.18) product form) -/

/-- **Empty product at `V = Fin 0`.** For the empty site set the coherent state at any
configuration is `1` (product over an empty index set), independent of `θ`. This targets only the
already-proved Problem 2.4.c eq. (S.18) product form `saturatedCoherentState_zero_apply`; it needs
no `Nonempty` instance and fabricates none. -/
example (N : ℕ) (θ : ℝ) (σ : Fin 0 → Fin (N + 1)) :
    saturatedCoherentState (Fin 0) N θ 0 σ = 1 := by
  rw [saturatedCoherentState_zero_apply]
  simp

end LatticeSystem.Tests.Problem24bWeightExpansion
