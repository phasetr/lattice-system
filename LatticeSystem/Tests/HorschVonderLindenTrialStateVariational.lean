import LatticeSystem.Quantum.HorschVonderLindenProblem34b
import LatticeSystem.Quantum.Pauli
import LatticeSystem.Quantum.SpinS.DoubleCommutatorVariational

/-!
# Test coverage for the §3.4 trial state and the basic variational estimate

Fixtures for the shared Horsch–von der Linden trial-state vocabulary of the module
`HorschVonderLindenTrialState.lean` and for the variational-estimate identity eq. (3.4.8) of
H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer, 2020), §3.4,
p. 66.

## What each block pins

**Trial-state block.** `HorschVonderLindenTrialState.lean` is the public §3.4 home of five
theorems about the trial state `Γ = hvlTrialState O Φ` (eq. (3.4.7)): its scaling form
(`trialState_eq_smul`), its unit-norm identity (`trialState_dotProduct_self`), and three
absorption identities that move a power of `O` across the `⟨·,·⟩` pairing onto `Φ`
(`dotProduct_mulVec_trialState`, `trialState_dotProduct_mulVec`,
`trialState_dotProduct_mulVec_trialState`). The `Ξ₊`-specific moment identities of
`HorschVonderLindenProblem34b.lean` and the states of the later §3.4 modules (the symmetric
combination `Ξ₊` of eq. (3.4.14) and its mirror `Ξ₋`) use this vocabulary independently of one
another. Each theorem is pinned below as a **signature pin**: the declaration's own statement,
discharged only by applying the identifier itself, so the pin fails exactly when the identifier
cannot be resolved from another module.

**Eq. (3.4.8) block.** `hvlTrialState_energy_sub_eq` pins the identity
`⟨Γ|Ĥ|Γ⟩ − E_GS = ⟨Φ_GS|[Ô_L,[Ĥ,Ô_L]]|Φ_GS⟩ / (2⟨Φ_GS|(Ô_L)²|Φ_GS⟩)`, for an arbitrary Hermitian
`H`/`O` pair and an arbitrary eigenvector `Φ` of `H` with eigenvalue `E₀` (not assumed to be the
ground state): the identity uses no long-range-order or odd-moment hypothesis, so none is pinned
here. The lower bound `0 ≤ ⟨Γ|Ĥ|Γ⟩ − E_GS` is the left half of eq. (3.4.12), p. 67, and is not
part of this module, so it is not pinned either. The pins reuse `Matrix.IsHermitian` for `H`/`O`,
`rayleighOnVec` for the sandwiched expectation values, and `hvlTrialState` for `Γ` from the
existing production code, rather than inventing new vocabulary in this file.

## Duplicate assessment

`double_commutator_ground_state_eq` (`DoubleCommutatorVariational.lean`) already gives the
un-normalized double-commutator identity
`⟨Φ|[A,[H,A]]|Φ⟩ = 2⟨AΦ|H|AΦ⟩ − 2E₀⟨AΦ|AΦ⟩`
for any Hermitian `H`/`A` and eigenvector `Φ` of `H`. Eq. (3.4.8) genuinely follows from it by
dividing both sides by `2⟨Φ|A²|Φ⟩ = 2⟨AΦ|AΦ⟩` and rewriting the quotient
`⟨AΦ|H|AΦ⟩ / ⟨AΦ|AΦ⟩` as `⟨Γ|H|Γ⟩ = rayleighOnVec H (hvlTrialState A Φ)` via the unit
normalization of `Γ`, so `hvlTrialState_energy_sub_eq` is genuinely new content (the division step
and the rewrite into `hvlTrialState`/`rayleighOnVec` form) rather than a restatement of
`double_commutator_ground_state_eq`, which is therefore not re-pinned here.

## Fixtures and their perturbations

The two numeric examples in the final block instantiate `H = pauliZ`, `O = pauliX` and
`Φ = e₀ = (1, 0)` on `Fin 2 → ℂ`, an eigenvector of `H` with eigenvalue `E₀ = 1` (not the ground
state, since `pauliZ`'s ground eigenvalue is `−1` — deliberately, since (3.4.8) itself needs no
ground-state hypothesis). `pauliX *ᵥ e₀ = e₁`, so `Γ = e₁` exactly (no normalization correction,
since `‖e₁‖ = 1`), giving `rayleighOnVec pauliZ Γ − 1 = −1 − 1 = −2` on the LHS of (3.4.8), and
`⟨e₀|[pauliX,[pauliZ,pauliX]]|e₀⟩ / (2·⟨e₀|pauliX²|e₀⟩) = −4 / 2 = −2` on the RHS, matching. Each
example was checked to fail by perturbation before being fixed at its stated value: replacing the
denominator's factor `2` with `4` turns the RHS example's goal into the false statement
`-1 = -2` (verified to produce an `unsolved goals ⊢ False` build error); the LHS example was
checked the same way by replacing its target `-2` with `-1`. Both examples use the production
Pauli matrices `pauliZ`/`pauliX` (`Quantum/Pauli.lean`) together with `hvlTrialState`,
`rayleighOnVec` and matrix/`dotProduct` operations, so they build (and are checked by `norm_num`)
independently of the pins above; the only definition made here is the reference vector
`e0Fixture`, which has no production counterpart. Rather than applying
`hvlTrialState_energy_sub_eq`, they evaluate its two sides separately, so that a defect in the
identity's proof cannot propagate into the numbers they check.
-/

namespace LatticeSystem.Tests.HorschVonderLindenTrialStateVariational

open LatticeSystem.Quantum
open Matrix

/-! ## Signature pins: the five shared trial-state helpers -/

/-- **Signature pin (scaling).** `Γ` written as `(√m₂)⁻¹ • (Ô_L|Φ_GS⟩)`, the defining unfolding of
`unitNormalize` used throughout the arc's downstream absorption identities. -/
example {n : Type*} [Fintype n] [DecidableEq n] {O : Matrix n n ℂ} (hO : O.IsHermitian)
    (Φ : n → ℂ) :
    hvlTrialState O Φ = ((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ)⁻¹ • (O *ᵥ Φ) :=
  trialState_eq_smul hO Φ

/-- **Signature pin (ket-side absorption).** `⟨Φ_GS, (Ô_L)^k Γ⟩ = (√m₂)⁻¹ ⟨Φ_GS, (Ô_L)^{k+1}
Φ_GS⟩`, moving a power of `O` from the ket `Γ` back onto `Φ`. -/
example {n : Type*} [Fintype n] [DecidableEq n] {O : Matrix n n ℂ} (hO : O.IsHermitian)
    (Φ : n → ℂ) (k : ℕ) :
    star Φ ⬝ᵥ ((O ^ k) *ᵥ hvlTrialState O Φ)
      = ((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ)⁻¹ * (star Φ ⬝ᵥ ((O ^ (k + 1)) *ᵥ Φ)) :=
  dotProduct_mulVec_trialState hO Φ k

/-- **Signature pin (bra-side absorption).** `⟨Γ, (Ô_L)^k Φ_GS⟩ = (√m₂)⁻¹ ⟨Φ_GS, (Ô_L)^{k+1}
Φ_GS⟩`, the adjoint-transfer companion of the ket-side pin above. -/
example {n : Type*} [Fintype n] [DecidableEq n] {O : Matrix n n ℂ} (hO : O.IsHermitian)
    (Φ : n → ℂ) (k : ℕ) :
    star (hvlTrialState O Φ) ⬝ᵥ ((O ^ k) *ᵥ Φ)
      = ((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ)⁻¹ * (star Φ ⬝ᵥ ((O ^ (k + 1)) *ᵥ Φ)) :=
  trialState_dotProduct_mulVec hO Φ k

/-- **Signature pin (diagonal absorption).** `⟨Γ, (Ô_L)^k Γ⟩ = ((√m₂)⁻¹)² ⟨Φ_GS, (Ô_L)^{k+2}
Φ_GS⟩`, absorbing a power of `O` from both the bra and the ket copy of `Γ` at once. -/
example {n : Type*} [Fintype n] [DecidableEq n] {O : Matrix n n ℂ} (hO : O.IsHermitian)
    (Φ : n → ℂ) (k : ℕ) :
    star (hvlTrialState O Φ) ⬝ᵥ ((O ^ k) *ᵥ hvlTrialState O Φ)
      = (((Real.sqrt (rayleighOnVec (O ^ 2) Φ) : ℝ) : ℂ)⁻¹) ^ 2
        * (star Φ ⬝ᵥ ((O ^ (k + 2)) *ᵥ Φ)) :=
  trialState_dotProduct_mulVec_trialState hO Φ k

/-- **Signature pin (normalization).** `Γ` is a unit vector, `⟨Γ, Γ⟩ = 1`, given `m₂ > 0`. This is
the hypothesis with which the states built on top of `Γ` are normalized. -/
example {n : Type*} [Fintype n] [DecidableEq n] {O : Matrix n n ℂ} (hO : O.IsHermitian)
    (Φ : n → ℂ) (hm2 : 0 < rayleighOnVec (O ^ 2) Φ) :
    star (hvlTrialState O Φ) ⬝ᵥ hvlTrialState O Φ = 1 :=
  trialState_dotProduct_self hO Φ hm2

/-! ## Eq. (3.4.8): the basic variational estimate -/

/-- **Signature pin (eq. (3.4.8)).** `⟨Γ|Ĥ|Γ⟩ − E_GS = ⟨Φ_GS|[Ô_L,[Ĥ,Ô_L]]|Φ_GS⟩ /
(2⟨Φ_GS|(Ô_L)²|Φ_GS⟩)`, for any Hermitian `H`/`O` pair and any eigenvector `Φ` of `H` — not assumed
to be the ground state, since the identity is the un-normalized double-commutator identity divided
by `2 m₂`. -/
example {n : Type*} [Fintype n] [DecidableEq n] {H O : Matrix n n ℂ} {Φ : n → ℂ} {E₀ : ℝ}
    (hH : H.IsHermitian) (hO : O.IsHermitian) (hΦE : H *ᵥ Φ = (E₀ : ℂ) • Φ)
    (hm2 : 0 < rayleighOnVec (O ^ 2) Φ) :
    rayleighOnVec H (hvlTrialState O Φ) - E₀
      = (star Φ ⬝ᵥ ((O * (H * O - O * H) - (H * O - O * H) * O) *ᵥ Φ)).re
          / (2 * rayleighOnVec (O ^ 2) Φ) :=
  hvlTrialState_energy_sub_eq hH hO hΦE hm2

/-! ## Numeric fixtures: `H = pauliZ`, `O = pauliX`, `Φ = e₀` on `Fin 2 → ℂ` -/

/-- The reference vector `Φ = e₀ = (1, 0)`, an eigenvector of `pauliZ` with eigenvalue `1`
(the excited, not ground, eigenvalue: (3.4.8) itself needs no ground-state hypothesis). -/
noncomputable def e0Fixture : Fin 2 → ℂ := ![1, 0]

/-- **Fixture (LHS of (3.4.8)).** `⟨Γ|Ĥ|Γ⟩ − E₀ = −2` at the concrete instance above: `Γ =
pauliX *ᵥ e0Fixture = e₁` exactly (already unit-norm), so `⟨Γ|Ĥ|Γ⟩ = −1` and `−1 − 1 = −2`.
Checked to fail by perturbation: replacing the target `-2` with `-1` (the value obtained by
dropping the `− E₀` term) makes this `norm_num` call leave `unsolved goals ⊢ False`. -/
example :
    rayleighOnVec pauliZ (hvlTrialState pauliX e0Fixture) - (1 : ℝ) = -2 := by
  unfold rayleighOnVec hvlTrialState unitNormalize vecNormSqRe pauliX pauliZ e0Fixture
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **Fixture (RHS of (3.4.8)).** `⟨Φ_GS|[Ô_L,[Ĥ,Ô_L]]|Φ_GS⟩ / (2⟨Φ_GS|(Ô_L)²|Φ_GS⟩) = −2` at the
same instance, matching the LHS fixture above and confirming (3.4.8) is not vacuous at this point.
Checked to fail by perturbation: replacing the denominator's factor `2` with `4` (a dropped-`1/2`
defect) turns the goal into the false statement `-1 = -2`, which `norm_num` cannot discharge. -/
example :
    (star e0Fixture ⬝ᵥ
        ((pauliX * (pauliZ * pauliX - pauliX * pauliZ)
            - (pauliZ * pauliX - pauliX * pauliZ) * pauliX)
          *ᵥ e0Fixture)).re
      / (2 * rayleighOnVec (pauliX ^ 2) e0Fixture) = -2 := by
  unfold rayleighOnVec pauliX pauliZ e0Fixture
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply, Matrix.sub_apply,
    pow_two]

end LatticeSystem.Tests.HorschVonderLindenTrialStateVariational
