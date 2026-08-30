import LatticeSystem.Quantum.HorschVonderLindenProblem34b
import LatticeSystem.Quantum.SpinS.DoubleCommutatorVariational

/-!
# Test coverage for PR-1 of the §3.4 arc: trial-state relocation + eq. (3.4.8)

Fixtures for the first PR of the Tasaki §3.4 backfill arc (issue #5395): the relocation of the
Horsch–von der Linden trial-state vocabulary out of `HorschVonderLindenProblem34b.lean` into a
shared module `HorschVonderLindenTrialState.lean`, and the variational-estimate identity eq.
(3.4.8) of H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, p. 66.

## What each block pins

**Relocation block.** `HorschVonderLindenProblem34b.lean` currently defines five `private`
theorems about the trial state `Γ = hvlTrialState O Φ` (eq. (3.4.7)): its scaling form
(`trialState_eq_smul`), its unit-norm identity (`trialState_dotProduct_self`), and three
absorption identities that move a power of `O` across the `⟨·,·⟩` pairing onto `Φ`
(`dotProduct_mulVec_trialState`, `trialState_dotProduct_mulVec`,
`trialState_dotProduct_mulVec_trialState`). Later PRs of the arc (the eq. (3.4.16) bound on `Ξ₊`
and the mirror state `Ξ₋`) need this vocabulary independently of the `Ξ₊`-specific moment
identities that stay in `HorschVonderLindenProblem34b.lean`, so PR-1 moves all five out of
`private`-in-that-file status into a shared, public home. Each is pinned below as a
**signature pin**: the declaration's own statement, discharged only by applying the identifier
itself, so the pin fails exactly when the identifier cannot be resolved from this file — which is
the case today, since a `private` declaration in one module is never visible from another.

**Eq. (3.4.8) block.** `hvlTrialState_energy_sub_eq` pins the identity itself,
`⟨Γ|Ĥ|Γ⟩ − E_GS = ⟨Φ_GS|[Ô_L,[Ĥ,Ô_L]]|Φ_GS⟩ / (2⟨Φ_GS|(Ô_L)²|Φ_GS⟩)`, for an arbitrary Hermitian
`H`/`O` pair and an arbitrary eigenvector `Φ` of `H` with eigenvalue `E₀` (not assumed to be the
ground state): the book derives this line "by inspection" from (3.4.1)/(3.4.2) alone, with no use
of (3.4.3)/(3.4.4), so no odd-moment or LRO hypothesis is pinned here.
`hvlTrialState_energy_sub_nonneg` pins its non-negativity side, `0 ≤ ⟨Γ|Ĥ|Γ⟩ − E_GS`: this
direction genuinely needs `E₀` to be the *ground-state* energy (the minimum of the Rayleigh
quotient over normalized vectors), which is the extra hypothesis `hGS` below — the book's running
assumption that `|Φ_GS⟩` is a normalized ground state of `Ĥ`, stated in the "Setting and
assumptions" paragraph on p. 65 and used silently at (3.4.8). Both pins reuse `Matrix.IsHermitian`
for `H`/`O`, `rayleighOnVec` for the sandwiched
expectation values, and `hvlTrialState` for `Γ` from the existing production code, rather than
inventing new vocabulary in this file.

## Duplicate assessment

`double_commutator_ground_state_eq` (`DoubleCommutatorVariational.lean`) already gives the
un-normalized double-commutator identity
`⟨Φ|[A,[H,A]]|Φ⟩ = 2⟨AΦ|H|AΦ⟩ − 2E₀⟨AΦ|AΦ⟩`
for any Hermitian `H`/`A` and eigenvector `Φ` of `H`. Eq. (3.4.8) genuinely follows from it by
dividing both sides by `2⟨Φ|A²|Φ⟩ = 2⟨AΦ|AΦ⟩` and rewriting the quotient
`⟨AΦ|H|AΦ⟩ / ⟨AΦ|AΦ⟩` as `⟨Γ|H|Γ⟩ = rayleighOnVec H (hvlTrialState A Φ)` via the unit
normalization of `Γ`, so `hvlTrialState_energy_sub_eq` is genuinely new content (the division step
and the rewrite into `hvlTrialState`/`rayleighOnVec` form) rather than a restatement of
`double_commutator_ground_state_eq`; the two are pinned together in the second block above to make
that relationship explicit for the reviewer, and `double_commutator_ground_state_eq` itself is not
re-pinned.

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
checked the same way by replacing its target `-2` with `-1`. Both fixtures reference only
`hvlTrialState`, `rayleighOnVec` and matrix/`dotProduct` operations that already exist in
production code, so they build (and are checked by `norm_num`) independently of the pins above;
they do not themselves reference `hvlTrialState_energy_sub_eq`, since that identifier does not yet
exist to apply.
-/

namespace LatticeSystem.Tests.HorschVonderLindenTrialStateRelocation

open LatticeSystem.Quantum
open Matrix

/-! ## Relocation pins: the five currently-`private` trial-state helpers -/

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
the hypothesis the eq. (3.4.8) non-negativity pin below needs to invoke the ground-state minimality
of `E₀` at the normalized vector `Γ`. -/
example {n : Type*} [Fintype n] [DecidableEq n] {O : Matrix n n ℂ} (hO : O.IsHermitian)
    (Φ : n → ℂ) (hm2 : 0 < rayleighOnVec (O ^ 2) Φ) :
    star (hvlTrialState O Φ) ⬝ᵥ hvlTrialState O Φ = 1 :=
  trialState_dotProduct_self hO Φ hm2

/-! ## Eq. (3.4.8): the variational estimate and its non-negativity side -/

/-- **Signature pin (eq. (3.4.8)).** `⟨Γ|Ĥ|Γ⟩ − E_GS = ⟨Φ_GS|[Ô_L,[Ĥ,Ô_L]]|Φ_GS⟩ /
(2⟨Φ_GS|(Ô_L)²|Φ_GS⟩)`, for any Hermitian `H`/`O` pair and any eigenvector `Φ` of `H` (not assumed
to be the ground state — the book derives this line by inspection from (3.4.1)/(3.4.2) alone). -/
example {n : Type*} [Fintype n] [DecidableEq n] {H O : Matrix n n ℂ} {Φ : n → ℂ} {E₀ : ℝ}
    (hH : H.IsHermitian) (hO : O.IsHermitian) (hΦE : H *ᵥ Φ = (E₀ : ℂ) • Φ)
    (hm2 : 0 < rayleighOnVec (O ^ 2) Φ) :
    rayleighOnVec H (hvlTrialState O Φ) - E₀
      = (star Φ ⬝ᵥ ((O * (H * O - O * H) - (H * O - O * H) * O) *ᵥ Φ)).re
          / (2 * rayleighOnVec (O ^ 2) Φ) :=
  hvlTrialState_energy_sub_eq hH hO hΦE hm2

/-- **Signature pin (eq. (3.4.8), non-negativity side).** `0 ≤ ⟨Γ|Ĥ|Γ⟩ − E_GS`, using the extra
ground-state-minimality hypothesis `hGS` (the book's running assumption that `E_GS` is the energy
of a normalized *ground* state of `Ĥ`, i.e. the minimum Rayleigh quotient over normalized
vectors), applied at the normalized trial state `Γ`. -/
example {n : Type*} [Fintype n] [DecidableEq n] {H O : Matrix n n ℂ} {Φ : n → ℂ} {E₀ : ℝ}
    (hH : H.IsHermitian) (hO : O.IsHermitian) (hΦE : H *ᵥ Φ = (E₀ : ℂ) • Φ)
    (hm2 : 0 < rayleighOnVec (O ^ 2) Φ)
    (hGS : ∀ ψ : n → ℂ, star ψ ⬝ᵥ ψ = 1 → (E₀ : ℝ) ≤ rayleighOnVec H ψ) :
    0 ≤ rayleighOnVec H (hvlTrialState O Φ) - E₀ :=
  hvlTrialState_energy_sub_nonneg hH hO hΦE hm2 hGS

/-! ## Numeric fixtures: `H = pauliZ`, `O = pauliX`, `Φ = e₀` on `Fin 2 → ℂ` -/

/-- The Pauli matrix `σ³` (`Ĥ` for the fixtures below). -/
noncomputable def pauliZFixture : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Pauli matrix `σ¹` (`Ô_L` for the fixtures below). -/
noncomputable def pauliXFixture : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The reference vector `Φ = e₀ = (1, 0)`, an eigenvector of `pauliZFixture` with eigenvalue `1`
(the excited, not ground, eigenvalue: (3.4.8) itself needs no ground-state hypothesis). -/
noncomputable def e0Fixture : Fin 2 → ℂ := ![1, 0]

/-- **Fixture (LHS of (3.4.8)).** `⟨Γ|Ĥ|Γ⟩ − E₀ = −2` at the concrete instance above: `Γ =
pauliXFixture *ᵥ e0Fixture = e₁` exactly (already unit-norm), so `⟨Γ|Ĥ|Γ⟩ = −1` and `−1 − 1 = −2`.
Checked to fail by perturbation: replacing the target `-2` with `-1` (the value obtained by
dropping the `− E₀` term) makes this `norm_num` call fail. -/
example :
    rayleighOnVec pauliZFixture (hvlTrialState pauliXFixture e0Fixture) - (1 : ℝ) = -2 := by
  unfold rayleighOnVec hvlTrialState unitNormalize vecNormSqRe pauliXFixture pauliZFixture
    e0Fixture
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **Fixture (RHS of (3.4.8)).** `⟨Φ_GS|[Ô_L,[Ĥ,Ô_L]]|Φ_GS⟩ / (2⟨Φ_GS|(Ô_L)²|Φ_GS⟩) = −2` at the
same instance, matching the LHS fixture above and confirming (3.4.8) is not vacuous at this point.
Checked to fail by perturbation: replacing the denominator's factor `2` with `4` (a dropped-`1/2`
defect) turns the goal into the false statement `-1 = -2`, which `norm_num` cannot discharge. -/
example :
    (star e0Fixture ⬝ᵥ
        ((pauliXFixture * (pauliZFixture * pauliXFixture - pauliXFixture * pauliZFixture)
            - (pauliZFixture * pauliXFixture - pauliXFixture * pauliZFixture) * pauliXFixture)
          *ᵥ e0Fixture)).re
      / (2 * rayleighOnVec (pauliXFixture ^ 2) e0Fixture) = -2 := by
  unfold rayleighOnVec pauliXFixture pauliZFixture e0Fixture
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply, Matrix.sub_apply,
    pow_two]

end LatticeSystem.Tests.HorschVonderLindenTrialStateRelocation
