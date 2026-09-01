---
layout: page
title: "Legacy catalogue: Horsch–von der Linden low-lying states (Tasaki §3.4, Theorem 3.1) (part 3 of 4)"
permalink: /formalization/legacy/16-horsch-von-der-linden-low-lying-states-tasaki-3-4-theorem--part-03/
---

# Legacy catalogue: Horsch–von der Linden low-lying states (Tasaki §3.4, Theorem 3.1) (part 3 of 4)

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Spin models, Chapters 3–7, and spectral tools](/lattice-system/formalization/legacy/#group-spin-models)

## Authoritative supplemental implementation record (§3.4 trial state, locality core, and Problem 3.4.b)

This section is maintained by hand, lies outside the migrated catalogue block, and records
declarations added after the migration baseline; it is not subject to the frozen byte-for-byte
parity of the migrated block.

### Problem 3.4.b

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, §3.4, Problem 3.4.b:
statement p. 69 eq. (3.4.18), solution p. 501 eqs. (S.42)-(S.43), with the surrounding
eqs. (3.4.3), (3.4.4), (3.4.7) and (3.4.14)-(3.4.15), pp. 65-69 (locality of `Ô_L`,
eqs. (3.4.1)-(3.4.2), is not assumed by this module).

Problem 3.4.b asks to show that vanishing of the fourth-moment combination
`⟨Φ_GS|(Ô_L/L^d)⁴|Φ_GS⟩ − (⟨Φ_GS|(Ô_L/L^d)²|Φ_GS⟩)²` as `L ↑ ∞` forces the fluctuation of
`Ô_L/L^d` in the state `Ξ₊` to vanish. The state is **constructed** here rather than assumed:
`hvlTrialState` is the Horsch-von der Linden trial state `|Γ⟩ = Ô_L|Φ_GS⟩ / ‖Ô_L|Φ_GS⟩‖`
(eq. (3.4.7)) and `hvlPlusState` is `|Ξ₊⟩ = (1/√2)(|Φ_GS⟩ + |Γ⟩)` (eq. (3.4.14)). Writing
`m₂ = ⟨Φ_GS|(Ô_L)²|Φ_GS⟩` and `m₄ = ⟨Φ_GS|(Ô_L)⁴|Φ_GS⟩`, the four finite-volume identities are
exact equalities, not approximations: the source introduces no `≃` at this point, and none is
introduced here.

Assumption (3.4.4) enters as the complex equalities `⟨Φ_GS|(Ô_L)^k|Φ_GS⟩ = 0` for `k = 1, 3`,
which for Hermitian `Ô_L` is equivalent to the vanishing of the (automatically real) odd moments.
The third moment is load-bearing: it is carried by one diagonal term of (3.4.15) and by both
cross terms of (S.42). Normalisation of `Φ_GS` is used only for `⟨Ξ₊|Ξ₊⟩ = 1`; the other three
identities do not need it, since `rayleighOnVec` carries no denominator. Every per-`L` statement
is guarded by `1 ≤ L`, because the normalisation `L^d` degenerates at `L = 0`; a concrete family
in the regression fixtures witnesses that the guarded hypothesis bundle is satisfiable.

The `L`-indexed family is typed abstractly (`n : ℕ → Type*` with a `Fintype` and a `DecidableEq`
instance per `L`), matching the fact that the solution's algebra uses no lattice, locality or
Hamiltonian structure.

**What these declarations do not assert.** The Hamiltonian never appears: neither the low-lying
energy bound of the unnumbered sentence following (3.4.14) (p. 68) nor the ground-state property of
`Φ_GS` is assumed. Locality of `Ô_L` (eqs. (3.4.1)-(3.4.2)) is not assumed, so nothing here
certifies a concrete model — in particular neither that the quantum Ising model satisfies (3.4.18)
nor that the antiferromagnetic Heisenberg model fails it, the contrast Tasaki draws on p. 69. The
informal notion of a physical "ground state" of p. 69 is not formalised; the book defers its
precise formulation to §4.3. Eq. (3.4.16) `⟨Ξ₊|Ô_L/L^d|Ξ₊⟩ ≥ √q₀` and the Schwarz remark
(3.4.17) are recorded in
[part 4](/lattice-system/formalization/legacy/16-horsch-von-der-linden-low-lying-states-tasaki-3-4-theorem--part-04/)
under "The low-lying state `Ξ₊`, eqs. (3.4.16)-(3.4.17)"; the mirror
state `Ξ₋` is outside this development. The `L ↑ ∞` statement is a limit of
finite-volume real numbers, not a statement about a state on a quasi-local C\*-algebra.

All declarations below are **PROVED**; `#print axioms` on each yields only `propext`,
`Classical.choice`, `Quot.sound`.

| Lean name | Statement | File |
|---|---|---|
| `hvlTrialState` | the Horsch-von der Linden trial state `\|Γ⟩` of eq. (3.4.7): `Ô_L\|Φ_GS⟩` unit-normalised in the `L²` pairing | `Quantum/HorschVonderLindenTrialState.lean` |
| `smul_add_dotProduct_mulVec` | the sandwiched-form expansion `⟨c(u+v)\|A\|c(u+v)⟩ = (c̄c)(⟨u\|A\|u⟩ + ⟨u\|A\|v⟩ + ⟨v\|A\|u⟩ + ⟨v\|A\|v⟩)` for any scalar `c` and matrix `A` | `Quantum/HorschVonderLindenProblem34b.lean` |
| `hvlPlusState` | the state `\|Ξ₊⟩ = (1/√2)(\|Φ_GS⟩ + \|Γ⟩)` of eq. (3.4.14) | `Quantum/HorschVonderLindenProblem34b.lean` |
| `hvlPlusState_dotProduct_self` | the remark after eq. (3.4.14): `⟨Ξ₊\|Ξ₊⟩ = 1`, from `⟨Γ\|Γ⟩ = 1` and the vanishing of `⟨Φ_GS\|Γ⟩` | `Quantum/HorschVonderLindenProblem34b.lean` |
| `hvlPlusState_order_mean` | eq. (3.4.15): `⟨Ξ₊\|Ô_L\|Ξ₊⟩ = √m₂`, under the vanishing of the first and third odd moments | `Quantum/HorschVonderLindenProblem34b.lean` |
| `hvlPlusState_order_second_moment` | eq. (S.42): `⟨Ξ₊\|(Ô_L)²\|Ξ₊⟩ = (1/2)(m₂ + m₄/m₂)`, under the vanishing of the third odd moment | `Quantum/HorschVonderLindenProblem34b.lean` |
| `hvlPlusState_order_variance` | eq. (S.43) in the volume-normalised form: the variance of `Ô_L/V` in `Ξ₊` equals `(1/2)(m₄/V⁴ − (m₂/V²)²)/(m₂/V²)`, for any `V > 0` | `Quantum/HorschVonderLindenProblem34b.lean` |
| `tasaki_problem_3_4_b_order_fluctuation` (**capstone**) | Problem 3.4.b: the four identities above at every `L ≥ 1`, plus the `L ↑ ∞` vanishing of the `Ô_L/L^d`-fluctuation in `Ξ₊` under (3.4.18), with the `L`-uniform bound `q₀ > 0` of (3.4.3) keeping the prefactor `1/m₂` bounded | `Quantum/HorschVonderLindenProblem34b.lean` |

Regression fixtures live in `LatticeSystem/Tests/Problem34bFluctuation.lean`: each of the
declarations above other than `smul_add_dotProduct_mulVec` has a signature fixture restating it in
full and discharging it by the declaration itself, together with two concrete numeric instances and
one satisfiability witness for the capstone's hypothesis bundle.

### Trial state and the basic variational estimate, eq. (3.4.8)

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, §3.4, "Setting and
assumptions" p. 65, eqs. (3.4.7)-(3.4.8), p. 66.

`Quantum/HorschVonderLindenTrialState.lean` is the shared §3.4 home of the normalised trial state
`|Γ⟩ = Ô_L|Φ_GS⟩ / ‖Ô_L|Φ_GS⟩‖` (eq. (3.4.7), the definition `hvlTrialState` catalogued in the
Problem 3.4.b record above), of the algebra that moves powers of `Ô_L` across the `L²` pairing
between `Γ` and `Φ_GS`, and of the basic variational estimate

`⟨Γ|Ĥ|Γ⟩ − E_GS = ⟨Φ_GS|[Ô_L,[Ĥ,Ô_L]]|Φ_GS⟩ / (2⟨Φ_GS|(Ô_L)²|Φ_GS⟩)` (eq. (3.4.8))

that Tasaki reads off "by inspection" on p. 66. The symmetric combination `Ξ₊` of eq. (3.4.14)
(`Quantum/HorschVonderLindenProblem34b.lean`) is built on top of `Γ` and imports this module; the
mirror state `Ξ₋` (pp. 68-69) is not formalised anywhere yet and is left to a later stage of the
§3.4 development.

Eq. (3.4.8) is the un-normalised double-commutator identity
`double_commutator_ground_state_eq` (`Quantum/SpinS/DoubleCommutatorVariational.lean`) divided by
`2 m₂` with `m₂ = ⟨Φ_GS|(Ô_L)²|Φ_GS⟩`: taking real parts turns its right-hand side into
`2⟨Ô_LΦ_GS|Ĥ|Ô_LΦ_GS⟩ − 2 E_GS m₂`, while `Γ = (√m₂)⁻¹ • Ô_L|Φ_GS⟩` makes the left-hand Rayleigh
quotient `⟨Ô_LΦ_GS|Ĥ|Ô_LΦ_GS⟩/m₂`. The identity therefore holds at **any** eigenvector `Φ_GS` of
`Ĥ` with eigenvalue `E_GS`, with no long-range-order (3.4.3) or odd-moment (3.4.4) hypothesis;
positivity of `m₂` enters only through the normalisation of `Γ`.

**What these declarations do not assert.** The lower bound `0 ≤ ⟨Γ|Ĥ|Γ⟩ − E_GS`, which is the
left half of eq. (3.4.12) (p. 67), is *not* a consequence of the identity and is not stated in this
module; it is proved in `Quantum/HorschVonderLindenEnergyBound.lean`, described below.
It needs `E_GS` to be a ground-state energy, i.e. the minimum of the Rayleigh quotient of `Ĥ` over
normalised vectors — the running assumption of the "Setting and assumptions" paragraph on p. 65.
It cannot be dropped: at `Ĥ = σ³`, `Ô_L = σ¹`, `Φ_GS = (2, 0)` the eigenvalue `E_GS = 1` is not the
ground energy and both sides of (3.4.8) equal `−2`. Locality of `Ô_L` (eqs. (3.4.1)-(3.4.2))
and any lattice structure are absent here, so nothing in this module certifies a concrete model.
The `C L^{-d}` low-lying bound (3.4.12) that (3.4.8) feeds is
`Quantum/HorschVonderLindenEnergyBound.lean`, described below. Its composition with
`horsch_vonderLinden_lowLying` (`Quantum/HorschVonderLinden.lean`, Theorem 3.1), which would
discharge that theorem's hypothesis `hvar`, is not formalised: Theorem 3.1 also demands its
orthogonality hypothesis `hortho` and `E_GS` presented as a minimal eigenvalue of `Ĥ`, and
(3.4.12) supplies neither.

All declarations below are **PROVED**; `#print axioms` on each yields only `propext`,
`Classical.choice`, `Quot.sound`.

| Lean name | Statement | File |
|---|---|---|
| `dotProduct_mulVec_trialState` | ket-side absorption: `⟨Φ_GS, (Ô_L)^k Γ⟩ = (√m₂)⁻¹ ⟨Φ_GS, (Ô_L)^{k+1} Φ_GS⟩` | `Quantum/HorschVonderLindenTrialState.lean` |
| `trialState_dotProduct_mulVec` | bra-side adjoint transfer: `⟨Γ, (Ô_L)^k Φ_GS⟩ = (√m₂)⁻¹ ⟨Φ_GS, (Ô_L)^{k+1} Φ_GS⟩` | `Quantum/HorschVonderLindenTrialState.lean` |
| `trialState_dotProduct_mulVec_trialState` | diagonal absorption: `⟨Γ, (Ô_L)^k Γ⟩ = ((√m₂)⁻¹)² ⟨Φ_GS, (Ô_L)^{k+2} Φ_GS⟩` | `Quantum/HorschVonderLindenTrialState.lean` |
| `trialState_dotProduct_self` | `⟨Γ\|Γ⟩ = 1`, the unit normalisation of the trial state, given `m₂ > 0` | `Quantum/HorschVonderLindenTrialState.lean` |
| `hvlTrialState_energy_sub_eq` | eq. (3.4.8): `⟨Γ\|Ĥ\|Γ⟩ − E_GS = ⟨Φ_GS\|[Ô_L,[Ĥ,Ô_L]]\|Φ_GS⟩ / (2 m₂)`, for Hermitian `Ĥ`, `Ô_L` and any eigenvector `Φ_GS` of `Ĥ` | `Quantum/HorschVonderLindenTrialState.lean` |

Regression fixtures live in `LatticeSystem/Tests/HorschVonderLindenTrialStateVariational.lean`:
each of the five declarations above has a signature fixture restating it in full and discharging it
by the declaration itself, so the fixture fails to elaborate if the name is not resolvable from
another module, together with numeric instances that evaluate both sides of (3.4.8) at two
concrete points. The first is `Ĥ = σ³`, `Ô_L = σ¹`, `Φ_GS = (2, 0)`, where both sides equal `−2`;
there `σ¹` is involutive and `Φ_GS` a coordinate vector, so `m₂ = 4` coincides with `‖Φ_GS‖²`,
`‖Ô_LΦ_GS‖` with `‖Φ_GS‖`, and `√m₂` with `m₂/2`. The second, `Ĥ = σ¹`, `Ô_L = 4σ¹ + σ³ + 3·1`,
`Φ_GS = (1, 1)`, separates them: `Ô_L` is Hermitian but not involutive, its square is not a
multiple of the identity, `m₂ = 100` against `‖Φ_GS‖² = 2` and `√m₂ = 10` against `m₂/2 = 50`, and
both sides equal `−1/25`. Neither reference vector is a unit vector, so the normalisation of `Γ`
is load-bearing in every number the instances check.

### Locality of the double commutator, eqs. (3.4.9)-(3.4.11)

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, §3.4, eqs. (3.4.1)-
(3.4.2) p. 65, eq. (3.4.9) p. 66, eqs. (3.4.10)-(3.4.11) p. 67; operator-norm properties
(A.2.5)/(A.2.6), p. 463.

`Quantum/SpinS/LocalDoubleCommutatorBound.lean` turns the locality of `Ĥ = Σ_{b∈B} ĥ_b` and `Ô =
Σ_{x∈Λ} ô_x` into the numerator estimate that eq. (3.4.8) consumes. Locality is expressed by
plain commutation hypotheses rather than a support predicate: `ĥ_b` commutes with every `ô_z`
seated outside a window `W b` (the Lean content of eq. (3.4.1)'s "acts nontrivially only on the
spins at `x` and `y`"), and distinct sites carry commuting order operators (eq. (3.4.2)). The
collapse carries **two** windows, an inner `W₁ b` off which `ĥ_b` commutes with the order terms
and an outer `W₂ b` off which the order terms commute with the inner commutators, with
independent cardinality bounds `m₁` and `m₂` and kernel constant `4 m₁ m₂ h₀ o₀² |B|`. The
one-window statements are the instance `W₁ = W₂`, `m₁ = m₂ = mW`, and the bond case is `mW = 2`,
`4 · 2² = 16`; the counting that produces the book's constant is therefore proved in general.
Norm hypotheses are stated as `≤` rather than the book's `=`, and `0 ≤ o₀` is an explicit
hypothesis because an empty site type makes it underivable from the per-site bounds.

The commutator norm inequality `‖[Â, B̂]‖ ≤ 2‖Â‖‖B̂‖` used twice per term is
`manyBodyOperatorNormS_comm_le`, which lives in `Quantum/SpinS/ManyBodyOperatorNorm.lean` next to
the submultiplicativity and triangle inequalities it is proved from, and the commutator/finite-sum
distribution is `Math/CommutatorSum.lean`, shared with the §4.1 staggered-order expansion.

**What these declarations do not assert.** Self-adjointness of `ĥ_b` and `ô_x` is not assumed
anywhere: the first inequality of (3.4.11) is taken on the real part of the expectation, so no
reality obligation arises. The long-range order condition (3.4.3) and the no-SSB condition
(3.4.4) are unused here. Only (3.4.3) is consumed at (3.4.12); (3.4.4) is not used in that
derivation either. `Quantum/HorschVonderLindenProblem34b.lean` takes it as a named hypothesis in
its first- and third-odd-moment forms; on
[part 4](/lattice-system/formalization/legacy/16-horsch-von-der-linden-low-lying-states-tasaki-3-4-theorem--part-04/),
`hvlPlusState_energy_eq` takes its first-moment form (`hodd1` alone), while
`hvlPlusState_order_mean_ge_sqrt` and the capstone `tasaki_eq_3_4_16_lowLyingState_ssb` each take
both its first- and third-moment forms (`hodd1` and `hodd3`).
No lattice structure is imposed:
`|B_L| = d L^d` enters only as the numeric hypothesis `|B| ≤ d L^d`, and neither `1 ≤ d` nor
`1 ≤ L` is required.

All declarations below are **PROVED**; `#print axioms` on each yields only `propext`,
`Classical.choice`, `Quot.sound`.

| Lean name | Statement | File |
|---|---|---|
| `commutator_sum_right` | `[A, Σ_{i∈s} f i] = Σ_{i∈s} [A, f i]` in any ring | `Math/CommutatorSum.lean` |
| `commutator_sum_left` | `[Σ_{i∈s} f i, A] = Σ_{i∈s} [f i, A]` in any ring | `Math/CommutatorSum.lean` |
| `commutator_sum_smul_right` | `[A, Σ_{i∈s} c i • B i] = Σ_{i∈s} c i • [A, B i]` in a `K`-algebra | `Math/CommutatorSum.lean` |
| `commutator_sum_smul_left` | `[Σ_{i∈s} c i • B i, A] = Σ_{i∈s} c i • [B i, A]` in a `K`-algebra | `Math/CommutatorSum.lean` |
| `commutator_orderSum_eq_windowSum` | eq. (3.4.9): `[Ĥ, Ô] = Σ_{b∈B} Σ_{z∈W b} [ĥ_b, ô_z]` | `Quantum/SpinS/LocalDoubleCommutatorBound.lean` |
| `doubleCommutator_orderSum_eq_twoWindowSum` | two-window form of eq. (3.4.10): `[Ô, [Ĥ, Ô]] = Σ_{b∈B} Σ_{x∈W₂ b} Σ_{z∈W₁ b} [ô_x, [ĥ_b, ô_z]]` | `Quantum/SpinS/LocalDoubleCommutatorBound.lean` |
| `manyBodyOperatorNormS_doubleCommutator_le_of_twoWindows` | two-window norm kernel: `‖[Ô, [Ĥ, Ô]]‖ ≤ 4 m₁ m₂ h₀ o₀² \|B\|` | `Quantum/SpinS/LocalDoubleCommutatorBound.lean` |
| `doubleCommutator_orderSum_eq_windowSum` | eq. (3.4.10): `[Ô, [Ĥ, Ô]] = Σ_{b∈B} Σ_{x∈W b} Σ_{z∈W b} [ô_x, [ĥ_b, ô_z]]` (the `W₁ = W₂` instance of the two-window form) | `Quantum/SpinS/LocalDoubleCommutatorBound.lean` |
| `manyBodyOperatorNormS_doubleCommutator_le_of_windows` | general-window norm kernel: `‖[Ô, [Ĥ, Ô]]‖ ≤ 4 mW² h₀ o₀² \|B\|` (the `m₁ = m₂ = mW` instance) | `Quantum/SpinS/LocalDoubleCommutatorBound.lean` |
| `doubleCommutator_bondLocal_expectation_le` | eq. (3.4.11): `⟨Φ\|[Ô,[Ĥ,Ô]]\|Φ⟩ ≤ ‖[Ô,[Ĥ,Ô]]‖ ≤ 16 d h₀ o₀² L^d` for normalised `Φ` and bond-local windows | `Quantum/SpinS/LocalDoubleCommutatorBound.lean` |

Regression fixtures live in `LatticeSystem/Tests/LocalDoubleCommutatorBound.lean`: each of the
four **one-window** §3.4 declarations has a signature fixture restating it in full and
discharging it by the declaration itself (the two-window pins for
`doubleCommutator_orderSum_eq_twoWindowSum` and
`manyBodyOperatorNormS_doubleCommutator_le_of_twoWindows` live instead in
`LatticeSystem/Tests/RangeLocalDoubleCommutatorBound.lean`), and the two collapse identities are
pinned with `W b` on **both** window index positions, so a vacuous `W b = univ` reading would not
satisfy the pin. Two numeric fixtures pin
the constants over abstract data constrained only by the hypotheses, so no arithmetic tautology can
close them: the kernel at `mW = 3`, `h₀ = 5/2`, `o₀ = 1/2`, `|B| = 7` gives `315/2`, a point away
from `mW = 2` where `4mW²`, `8mW`, `2mW³` and `mW⁴` all coincide; the capstone at `d = 3`, `L = 4`,
`h₀ = 5/2`, `o₀ = 1/2` gives `1920`, where `L^d = 64 ≠ d^L = 81` also separates the `d · L^d` shape
from a `d^L` slip.

### The two-sided energy bound, eq. (3.4.12)

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, §3.4, "Setting and
assumptions" and eq. (3.4.3) p. 65, eq. (3.4.8) p. 66, eqs. (3.4.11)-(3.4.12) p. 67.

`Quantum/HorschVonderLindenEnergyBound.lean` assembles the printed display

`0 ≤ ⟨Γ|Ĥ|Γ⟩ − E_GS ≤ C L^{-d}`, `C = 8 d h₀ o₀² / q₀`

out of the basic variational estimate (3.4.8) and the locality bound (3.4.11). The abstract upper
half is stated first, with the system size entering only as a positive real parameter `Ld` and the
long-range order (3.4.3) as the lower bound `q₀ ≤ ⟨Φ_GS|(Ô_L)²|Φ_GS⟩ / Ld²`; it applies unchanged
at `Ô_L` and at its mirror `−Ô_L`, because `(−Ô_L)² = (Ô_L)²` and
`[−Ô_L, [Ĥ, −Ô_L]] = [Ô_L, [Ĥ, Ô_L]]`. Its proof takes (3.4.8), whose right-hand side already
carries the denominator `2 m₂` with `m₂ = ⟨Φ_GS|(Ô_L)²|Φ_GS⟩`, and compares that quotient with
`K / (2 q₀ Ld²)` in two separate monotone steps, first in the numerator and then in the
denominator, so it needs only `0 ≤ K` for the numerator bound `K` — no sign information about the
double-commutator expectation, hence no ground-state property of `Φ_GS`. The capstone specialises
it at `Ld = L^d`, feeds it (3.4.11)'s `K = 16 d h₀ o₀² L^d`, and reduces `16 L^d / (2 q₀ (L^d)²)`
to `8 / (q₀ L^d)`, which is the book's constant. The left half is the variational hypothesis
applied to the unit vector `Γ`, whose normalisation is `trialState_dotProduct_self`.

**Hypothesis ledger.** The ground-state assumption of p. 65 is rendered as the three separate facts
`⟨Φ_GS|Φ_GS⟩ = 1`, `Ĥ|Φ_GS⟩ = E_GS|Φ_GS⟩` and `E_GS ≤ ⟨v|Ĥ|v⟩` for every normalised `v`. The
first two give `⟨Φ_GS|Ĥ|Φ_GS⟩ = E_GS`, so the third is *equivalent* to `E_GS` being the minimum of
the Rayleigh quotient over normalised vectors and covers exactly the same data; what the explicit
form buys is that a caller may supply the minimality directly, without routing through
`hermitianMinEigenvalue` and the `Nonempty` instance it requires. A regression fixture discharges
it from `hermitianMinEigenvalue_le_rayleighOnVec_of_unit` at a genuine ground state.
Self-adjointness of `Ĥ` and `Ô_L` is taken at the level of the sums, not per term, which is the
weaker form. `q₀ > 0` is printed in (3.4.3) itself. `1 ≤ L` is used only to make `L^d` positive.

**What these declarations do not assert.** The no-SSB condition (3.4.4), p. 65, is not used: only
(3.4.3) is consumed here. The statement is at a single `L`, an implication between hypotheses and
conclusion at that same `L`; the "for sufficiently large `L`" reading of (3.4.3)-(3.4.4) is a
statement about a family and is not formalised here. Neither the mirror `−Ô_L` instance nor the
symmetric state `Ξ₊` of eq. (3.4.14), p. 68, is treated here.

All declarations below are **PROVED**; `#print axioms` on each yields only `propext`,
`Classical.choice`, `Quot.sound`.

| Lean name | Statement | File |
|---|---|---|
| `hvlTrialState_energy_sub_le_of_lro` | abstract upper half of eq. (3.4.12): `⟨Γ\|Ĥ\|Γ⟩ − E_GS ≤ K / (2 q₀ Ld²)` from `q₀ ≤ ⟨Φ_GS\|(Ô_L)²\|Φ_GS⟩ / Ld²` and a numerator bound `K ≥ 0` | `Quantum/HorschVonderLindenEnergyBound.lean` |
| `tasaki_eq_3_4_12_trialState_energy_bound` | eq. (3.4.12): `0 ≤ ⟨Γ\|Ĥ\|Γ⟩ − E_GS ≤ 8 d h₀ o₀² / q₀ / L^d` for a bond-local `Ĥ` at a normalised ground state with long-range order | `Quantum/HorschVonderLindenEnergyBound.lean` |

Regression fixtures live in `LatticeSystem/Tests/HorschVonderLindenEnergyBound.lean`: a signature
fixture for each declaration restating it in full and discharging it by the declaration itself —
the abstract one pinning that neither the variational hypothesis nor `⟨Φ_GS|Φ_GS⟩ = 1` appears in
it, the capstone pinning both conjuncts and that no (3.4.4) hypothesis and no `1 ≤ d` is required —
a numeric fixture for each constant over abstract data constrained only by the hypotheses, and the
witness that discharges the variational hypothesis at the canonical ground-state energy. The
capstone's numeric point is `d = 3`, `L = 2`, `h₀ = 5/2`, `o₀ = 1/3`, `q₀ = 3/4`, giving `10/9`;
`o₀ = 1/3` is chosen so that the ratio `o₀ : o₀² = 3` differs from the factor `2` separating the
candidate leading constants `16` and `8`, and `q₀ = 3/4` differs from `1`, `q₀²` and `2q₀`, so a
dropped square, a dropped factor of two and a dropped `q₀` are pairwise distinguishable. Since a
numeric endpoint is one-sided and blind to a wrongly small constant, each fixture routes through an
intermediate step that spells the constant out syntactically.

### The general range-`r` bound, Problem 3.4.a (not eq. (3.4.13) as printed)

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, §2.1 p. 52 (periodic
lattice), §3.4, Problem 3.4.a, statement pp. 67-68, printed solution p. 501; operator-norm
properties (A.2.5)/(A.2.6), p. 463.

Problem 3.4.a generalizes the bond-local estimate (3.4.11) to a Hamiltonian and an order operator
that are both sums over *every* site of Tasaki's **periodic** lattice `Λ_L = Fin d → Fin L`
(p. 52), `Ĥ = Σ_{x∈Λ_L} ĥ_x` and `Ô_L = Σ_{x∈Λ_L} ô_x`, with each local term acting only on sites
within distance `r` of its own site. That premise is a statement about operator *support*, and is
taken here as one, `SupportedOnS` (`Quantum/SpinS/OperatorSupport.lean`: `A` lies in the subalgebra
`B(H_S) ⊗ I_{Λ∖S}`), on the radius-`r` torus sup-distance ball of `x` — the sup norm since Tasaki's
unqualified `|x − y| ≤ r` (p. 52 is Euclidean) is read in the weaker of the two, the Euclidean ball
sitting inside the sup-norm ball. Disjointly supported operators commute
(`commute_of_supportedOnS_disjoint`), so the commutation relations the estimate needs are *derived*
from this premise rather than assumed alongside it, and deriving them fixes both windows: a
nonzero `[ĥ_x, ô_y]` forces the two `r`-balls to meet, so `y` ranges over the `2r`-ball of `x`; the
commutator is supported in `B_r(x) ∪ B_r(y) ⊆ B_{3r}(x)`, so a non-commuting `ô_z` has `z` in the
`4r`-ball of `x`. Counting those windows on the torus
(`card_siteBall_torusSupDist_le`, `Quantum/SpinS/TorusSupDistance.lean`, which transports a torus
ball to a coordinate sup-norm ball via the injective signed cyclic displacement
`signedRingDisp`/`RingDistance.lean` and reuses `card_coordSupBall_le`) gives `m₁ ≤ (4r+1)^d` on
the `2r`-ball and `m₂ ≤ (8r+1)^d` on the `4r`-ball, giving

`⟨Φ_GS|[Ô_L,[Ĥ,Ô_L]]|Φ_GS⟩ ≤ 4 (4r+1)^d (8r+1)^d h₀ o₀² L^d`.

`Quantum/SpinS/RangeLocalDoubleCommutatorBound.lean` proves this display. The estimate is the
two-window kernel of `LocalDoubleCommutatorBound.lean` at `m₁ = (4r+1)^d`, `m₂ = (8r+1)^d` and
`|B| = |Λ_L| = L^d` — now an identity on the periodic lattice, not a bound — followed by the
operator-norm bound on the expectation in a unit vector. Book order note: Problem 3.4.a is
textually earlier than the `Ξ₊` material but is logically independent of it — Theorem 3.1's own
proof uses the concrete eq. (3.4.11), not this generalization.

**Corrigendum (index ranges).** The printed solution (Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, 1st ed., Springer 2020, Problem 3.4.a, solution p. 501) counts over
`|x − y| ≤ r` and `|x − z| ≤ 2r`. Those ranges do not follow from the range-`r` premise stated in
the Problem (pp. 67-68) — they are what a range-`r/2` premise would give. Under the printed
solution's own conditions the printed constant `4 (2r+1)^d (4r+1)^d h₀ o₀² L^d` is itself
provable: it is the two-window kernel `manyBodyOperatorNormS_doubleCommutator_le_of_twoWindows`
instantiated at `m₁ = (2r+1)^d`, `m₂ = (4r+1)^d`, so the discrepancy is a premise mismatch, not an
arithmetic slip. Whether the printed constant is nevertheless true under the range-`r` premise
itself is **open**: this repository neither proves nor refutes it; what is proved is the bound
above, at the windows the premise actually yields.

**Corrigendum (exponent typo, a separate defect).** The printed solution (p. 501) gives the
intermediate `y`-count as `(2r+1)²` while giving the `z`-count as `(4r+1)^d`. The exponent `2` is a
misprint: the target it claims to reach, eq. (3.4.13) on p. 68, carries `(2r+1)^d`, and counting
the lattice points within distance `r` of a site in `d` dimensions gives `(2r+1)^d`. No declaration
in this repository states the `(2r+1)²` form.

**What these declarations do not assert.** Self-adjointness of `ĥ_x` and `ô_x` is not assumed; the
expectation is taken on its real part. The long-range order condition (3.4.3) and the no-SSB
condition (3.4.4) are unused. No `1 ≤ d` and no `1 ≤ L` is required. The Problem's closing remark —
that Theorem 3.1 extends to this class given (3.4.3) and `⟨Φ_GS|Ô_L|Φ_GS⟩ = 0` — is not formalized
here; it is the composition of this bound with the (3.4.12) route, at a different object class.

All declarations below are **PROVED**; `#print axioms` on each yields only `propext`,
`Classical.choice`, `Quot.sound`.

| Lean name | Statement | File |
|---|---|---|
| `coordSupBall` | the coordinate sup-norm ball `{y : ∀ i, \|pos yᵢ − pos xᵢ\| ≤ r}` as a `Finset Λ` | `Math/Combinatorics/CoordinateBall.lean` |
| `mem_coordSupBall` | `y ∈ coordSupBall pos r x ↔ ∀ i, \|pos yᵢ − pos xᵢ\| ≤ r` | `Math/Combinatorics/CoordinateBall.lean` |
| `card_coordSupBall_le` | `\|B_r(x)\| ≤ (2r+1)^d` for injective coordinates; at radius `2r` it gives `(4r+1)^d` | `Math/Combinatorics/CoordinateBall.lean` |
| `SupportedOnS` | `A` lies in the subalgebra `B(H_S) ⊗ I_{Λ∖S}`: entries vanish unless row/column agree off `S`, and depend only on the restriction to `S` | `Quantum/SpinS/OperatorSupport.lean` |
| `SupportedOnS.add` | a sum of two operators supported on the same `S` is supported on `S` | `Quantum/SpinS/OperatorSupport.lean` |
| `commute_of_supportedOnS_disjoint` | operators supported on disjoint site sets commute | `Quantum/SpinS/OperatorSupport.lean` |
| `supportedOnS_onSiteS` | the single-site embedding `onSiteS i A` is supported on any `S ∋ i` | `Quantum/SpinS/OperatorSupport.lean` |
| `siteBall` | the ball `{y : dist y x ≤ r}` as a `Finset Λ`, for an abstract `ℕ`-valued distance | `Math/Combinatorics/SiteBall.lean` |
| `mem_siteBall` | `y ∈ siteBall dist r x ↔ dist y x ≤ r` | `Math/Combinatorics/SiteBall.lean` |
| `disjoint_siteBall_of_lt` | `2r < dist x y` gives disjoint `r`-balls, from symmetry and the triangle inequality | `Math/Combinatorics/SiteBall.lean` |
| `ringDist_comm` | the ring distance on `Fin L` is symmetric | `Quantum/SpinS/RingDistance.lean` |
| `ringDist_self` | the ring distance from a site to itself is `0` | `Quantum/SpinS/RingDistance.lean` |
| `ringDist_triangle` | the ring distance satisfies the triangle inequality | `Quantum/SpinS/RingDistance.lean` |
| `signedRingDisp_self` | the signed cyclic displacement of a site to itself is `0` | `Quantum/SpinS/RingDistance.lean` |
| `signedRingDisp_injective` | for fixed `x`, `y ↦ signedRingDisp L x y` is injective | `Quantum/SpinS/RingDistance.lean` |
| `torusSupDist` | the sup-norm of per-coordinate ring distances on `Fin d → Fin L` | `Quantum/SpinS/TorusSupDistance.lean` |
| `torusSupDist_le_iff` | `torusSupDist d L x y ≤ r ↔ ∀ i, ringDist L (x i) (y i) ≤ r` | `Quantum/SpinS/TorusSupDistance.lean` |
| `torusSupDist_comm` | the torus sup-distance is symmetric | `Quantum/SpinS/TorusSupDistance.lean` |
| `torusSupDist_triangle` | the torus sup-distance satisfies the triangle inequality | `Quantum/SpinS/TorusSupDistance.lean` |
| `card_siteBall_torusSupDist_le` | `\|B_r(x)\| ≤ (2r+1)^d` for the torus sup-distance ball | `Quantum/SpinS/TorusSupDistance.lean` |
| `manyBodyOperatorNormS_doubleCommutator_le_of_rangeLocal` | `‖[Ô,[Ĥ,Ô]]‖ ≤ 4 m₁ m₂ h₀ o₀² \|Λ\|` for `SupportedOnS`-local terms over an abstract distance, `m₁`/`m₂` the `2r`-/`4r`-ball counts | `Quantum/SpinS/RangeLocalDoubleCommutatorBound.lean` |
| `tasaki_problem_3_4_a_doubleCommutator_expectation_le` | Problem 3.4.a, with the constant the range-`r` premise yields (not eq. (3.4.13) as printed): `⟨Φ\|[Ô,[Ĥ,Ô]]\|Φ⟩ ≤ 4 (4r+1)^d (8r+1)^d h₀ o₀² L^d` for a normalised `Φ` and range-`r` `SupportedOnS` site-local terms on `Λ_L` | `Quantum/SpinS/RangeLocalDoubleCommutatorBound.lean` |

Regression fixtures live in `LatticeSystem/Tests/OperatorSupport.lean` (signature pins on
`SupportedOnS` and its three lemmas) and `LatticeSystem/Tests/RangeLocalDoubleCommutatorBound.lean`
(signature pins on the remaining declarations above, plus numeric fixtures): F-1, periodic
wraparound on `Fin 2 → Fin 5` (the torus sup-distance from the origin to `fun _ => 4` is the
*cyclic* arc length `1`, not the linear gap `4`); F-2 — `coordSupBall`
tightness on `Fin 2 → Fin 3`, every site lies in the radius-`1` coordinate ball, exhausting the
`(2·1+1)^2 = 9`-site bound; F-2′, ball-count tightness — the radius-`1` `siteBall`/`torusSupDist`
ball on `d = 2`, `L = 5` has exactly `9 = (2·1+1)²` sites out of `25`; F-3, the two-window kernel
constant at `m₁ = 3 ≠ 5 = m₂`, `h₀ = 5/2`, `o₀ = 1/2`, `|B| = 7`, giving `525/2`, a point where
`4m₁m₂`, `4m₁²`, `4m₂²` and `8m₁m₂` take the pairwise distinct values `262.5`, `157.5`, `437.5` and
`525`; F-4′, the capstone constant at `r = 1`, `d = 2`, `L = 5`, `h₀ = 2`, `o₀ = 1/2`, giving
`101250`, discriminated from the book-solution printed-constant form (`11250`) and from the
exponent-shape slip `L^d = 25 ≠ d^L = 32`; and F-5, a concrete witness — a `SupportedOnS`-bound
support of at most two sites (one reached by ring-wrapping) and a singleton-support order term on
`Fin 2 → Fin 5` — whose `SupportedOnS` hypotheses are *discharged by proof* rather than assumed,
giving the same `101250`
bound. Since
`4 m₁ m₂` is symmetric, a swap of the two window bounds is invisible to any numeric fixture on the
constant alone; in this `SupportedOnS`-based form the window roles are pinned by **provability**
instead — assembling the swapped windows into the kernel's outer-commutation obligation requires
deriving `2r < dist x z` from `4r < dist x b` and `dist z b ≤ 2r`, which needs the outer ball to be
the *wider* one, and with the windows swapped this derivation is not available.

---

[← Horsch–von der Linden low-lying states (Tasaki §3.4, Theorem 3.1)](/lattice-system/formalization/legacy/16-horsch-von-der-linden-low-lying-states-tasaki-3-4-theorem--part-02/) · [Catalogue](/lattice-system/formalization/legacy/) · [Horsch–von der Linden low-lying states (Tasaki §3.4, Theorem 3.1) →](/lattice-system/formalization/legacy/16-horsch-von-der-linden-low-lying-states-tasaki-3-4-theorem--part-04/)
