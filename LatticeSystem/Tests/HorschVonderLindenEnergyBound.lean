import LatticeSystem.Quantum.HorschVonderLindenEnergyBound
import LatticeSystem.Quantum.SpinS.RayleighRitzEquality

/-!
# Test coverage for eq. (3.4.12), the two-sided Horsch–von der Linden energy bound

Fixtures for `LatticeSystem/Quantum/HorschVonderLindenEnergyBound.lean`, covering H. Tasaki,
*Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer, 2020), §3.4, p. 67,
eq. (3.4.12): the abstract Layer-A upper bound `hvlTrialState_energy_sub_le_of_lro` and the
Layer-B capstone `tasaki_eq_3_4_12_trialState_energy_bound`.

## What each block pins

**Signature pins.** Both declarations are pinned as their own statement, discharged only by
applying the identifier itself, so a pin fails exactly when the identifier does not resolve.
The Layer-A pin fixes the exact denominator `2 * q₀ * Ld ^ 2` and that the hypothesis list has
**no** `hmin` and **no** `star Φ ⬝ᵥ Φ = 1` (Layer A needs no ground-state or normalisation fact,
only the abstract eq. (3.4.8) denominator positivity). The capstone pin fixes both conjuncts, the
literal constant `8 * (d : ℝ) * h₀ * o₀ ^ 2 / q₀ / (L : ℝ) ^ d`, and that **no** (3.4.4)/`hodd`
hypothesis and **no** `1 ≤ d` hypothesis appears among the named hypotheses — only eq. (3.4.3)
(via `hLRO`) and ground-stateness (via `hmin`) are consumed.

**Numeric fixtures (constant guard).** At `d := 3`, `L := 2`, `h₀ := 5/2`, `o₀ := 1/3`, `q₀ := 3/4`
the capstone's constant evaluates to `C = 8 · 3 · (5/2) · (1/3)² / (3/4) = 80/9`, and the bound
`C / L^d = (80/9)/8 = 10/9`. The chosen point avoids the degeneracy of `o₀ = 1/2` (used elsewhere
in this arc): here `o₀ = 1/3` gives ratio `o₀ : o₀² = 3`, distinct from the factor `2` between the
candidate leading constants `16` and `8`, so "`o₀` not squared" cannot be confused with "wrong
leading constant". The **discriminating mechanism is the intermediate `have`**, whose right-hand
side spells the constant out syntactically
(`8 * (3:ℝ) * (5/2:ℝ) * (1/3:ℝ)^2 / (3/4:ℝ) / (2:ℝ)^(3:ℕ)`): a capstone with a different
constant shape yields a syntactically different expression and does not close that `have` by
`exact`/application. The final numeric endpoint `≤ 10/9` alone is a strictly weaker, one-sided
check: it is blind to a wrongly-*small* constant such as `8 d h₀ o₀² / (2 q₀)` (value `5/9 < 10/9`,
from double-counting the `2` in eq. (3.4.8)'s denominator), which the endpoint would not catch but
which the syntactic `have` does, since that wrong expression could not close a `have` stated with
the `8 * … / q₀ / L^d` shape. The candidate `16 d h₀ o₀² / q₀` (dropping the eq. (3.4.8) factor of
`2`) gives `20/9 > 10/9` and is caught by the numeric endpoint as well as the `have`. The Layer-A
fixture (`K := 9`, `q₀ := 3/4`, `Ld := 3`, correct value `2/3`) is stated the same way.

**Witness (§3 discharge of `hmin`).** `hmin` is taken as an explicit hypothesis on the capstone
rather than derived from `hermitianMinEigenvalue`, on hypothesis-strength grounds (`hmin` is
implied by, but strictly weaker than, "`E₀` is *the* Rayleigh-Ritz minimum"). To close the risk
that `hmin` becomes a permanently-unproven standing assumption, the witness block below
instantiates `E₀ := hermitianMinEigenvalue hH` and discharges `hmin` from
`hermitianMinEigenvalue_le_rayleighOnVec_of_unit` (`RayleighRitzEquality.lean`). This import is
Tests-only; the library module `HorschVonderLindenEnergyBound.lean` does not import
`RayleighRitzEquality`.

## Duplicate assessment

`double_commutator_ground_state_nonneg` (`DoubleCommutatorNonneg.lean`) proves
`0 ≤ Re⟨Φ|[A,[H,A]]|Φ⟩` for `E₀ = hermitianMinEigenvalue hH` — the nearest existing neighbour of
the capstone's left (`0 ≤ …`) conjunct, but not a duplicate: different conclusion (a double
commutator expectation, not the trial-state energy gap) and a different, hypothesis-bound `E₀`.
Neither the Layer-A nor the Layer-B declaration restates it. The `0 ≤ …` half of (3.4.12) is
inlined into the capstone's own proof (one line, `sub_nonneg.mpr (hmin _ …)`), not given a separate
named declaration or pin, per the arc's decorative-declaration prohibition.
-/

namespace LatticeSystem.Tests.HorschVonderLindenEnergyBound

open LatticeSystem
open LatticeSystem.Quantum
open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Signature pin 1 — Layer A, `hvlTrialState_energy_sub_le_of_lro` -/

/-- **Signature pin (Layer A).** Pins the abstract upper bound of eq. (3.4.12): no `hmin`, no
`star Φ ⬝ᵥ Φ = 1`, denominator exactly `2 * q₀ * Ld ^ 2`. Discharged only by the identifier
itself. -/
example {n : Type*} [Fintype n] [DecidableEq n] {H O : Matrix n n ℂ} {Φ : n → ℂ}
    {E₀ q₀ Ld K : ℝ}
    (hH : H.IsHermitian) (hO : O.IsHermitian) (hΦE : H *ᵥ Φ = (E₀ : ℂ) • Φ)
    (hq₀ : 0 < q₀) (hLd : 0 < Ld) (hLRO : q₀ ≤ rayleighOnVec (O ^ 2) Φ / Ld ^ 2)
    (hK : 0 ≤ K)
    (hnum : rayleighOnVec (O * (H * O - O * H) - (H * O - O * H) * O) Φ ≤ K) :
    rayleighOnVec H (hvlTrialState O Φ) - E₀ ≤ K / (2 * q₀ * Ld ^ 2) :=
  hvlTrialState_energy_sub_le_of_lro hH hO hΦE hq₀ hLd hLRO hK hnum

/-! ## Signature pin 2 — Layer B, `tasaki_eq_3_4_12_trialState_energy_bound` -/

/-- **Signature pin (capstone).** Pins both conjuncts of eq. (3.4.12), the literal constant
`8 * (d : ℝ) * h₀ * o₀ ^ 2 / q₀ / (L : ℝ) ^ d`, and that the hypothesis list uses only eq. (3.4.3)
(`hLRO`) and ground-stateness (`hmin`, `hΦ`, `hΦE`) — no (3.4.4)/`hodd` hypothesis, no `1 ≤ d`.
Discharged only by the identifier itself. -/
example {ι : Type*} (B : Finset ι)
    (hb : ι → ManyBodyOpS Λ N) (o : Λ → ManyBodyOpS Λ N) (W : ι → Finset Λ)
    (d L : ℕ) (q₀ h₀ o₀ : ℝ) {Φ : (Λ → Fin (N + 1)) → ℂ} {E₀ : ℝ}
    (hH : (∑ b ∈ B, hb b).IsHermitian) (hO : (∑ x : Λ, o x).IsHermitian)
    (hW : ∀ b ∈ B, ∀ z ∉ W b, Commute (hb b) (o z))
    (hoo : ∀ x z : Λ, x ≠ z → Commute (o x) (o z))
    (hnh : ∀ b ∈ B, manyBodyOperatorNormS (hb b) ≤ h₀)
    (hno : ∀ x : Λ, manyBodyOperatorNormS (o x) ≤ o₀)
    (hh₀ : 0 ≤ h₀) (ho₀ : 0 ≤ o₀)
    (hbond : ∀ b ∈ B, (W b).card ≤ 2)
    (hB : (B.card : ℝ) ≤ (d : ℝ) * (L : ℝ) ^ d)
    (hΦ : star Φ ⬝ᵥ Φ = 1)
    (hΦE : (∑ b ∈ B, hb b) *ᵥ Φ = (E₀ : ℂ) • Φ)
    (hmin : ∀ v : (Λ → Fin (N + 1)) → ℂ, star v ⬝ᵥ v = 1 →
      E₀ ≤ rayleighOnVec (∑ b ∈ B, hb b) v)
    (hq₀ : 0 < q₀) (hL : 1 ≤ L)
    (hLRO : q₀ ≤ rayleighOnVec ((∑ x : Λ, o x) ^ 2) Φ / ((L : ℝ) ^ d) ^ 2) :
    0 ≤ rayleighOnVec (∑ b ∈ B, hb b) (hvlTrialState (∑ x : Λ, o x) Φ) - E₀
      ∧ rayleighOnVec (∑ b ∈ B, hb b) (hvlTrialState (∑ x : Λ, o x) Φ) - E₀
          ≤ 8 * (d : ℝ) * h₀ * o₀ ^ 2 / q₀ / (L : ℝ) ^ d :=
  tasaki_eq_3_4_12_trialState_energy_bound B hb o W d L q₀ h₀ o₀ hH hO hW hoo hnh hno hh₀ ho₀
    hbond hB hΦ hΦE hmin hq₀ hL hLRO

/-! ## Numeric fixture 1 — Layer-A constant guard -/

/-- **Fixture (Layer-A constant guard).** At `K := 9`, `q₀ := 3/4`, `Ld := 3` the correct
denominator `2 * q₀ * Ld ^ 2 = 27/2` gives bound `9 / (27/2) = 2/3`. The discriminating step is
the intermediate `have`, whose right-hand side spells the denominator out syntactically; the
numeric endpoint `≤ 2/3` additionally rules out `K/(q₀ Ld) = 4` and `K/(2 q₀² Ld²) = 8/9`, both
`> 2/3`, but is blind to any candidate giving a value `≤ 2/3`. -/
example {n : Type*} [Fintype n] [DecidableEq n] {H O : Matrix n n ℂ} {Φ : n → ℂ} {E₀ : ℝ}
    (hH : H.IsHermitian) (hO : O.IsHermitian) (hΦE : H *ᵥ Φ = (E₀ : ℂ) • Φ)
    (hLRO : (3 / 4 : ℝ) ≤ rayleighOnVec (O ^ 2) Φ / (3 : ℝ) ^ 2)
    (hnum : rayleighOnVec (O * (H * O - O * H) - (H * O - O * H) * O) Φ ≤ (9 : ℝ)) :
    rayleighOnVec H (hvlTrialState O Φ) - E₀ ≤ (2 / 3 : ℝ) := by
  have h : rayleighOnVec H (hvlTrialState O Φ) - E₀
      ≤ (9 : ℝ) / (2 * (3 / 4 : ℝ) * (3 : ℝ) ^ 2) :=
    hvlTrialState_energy_sub_le_of_lro hH hO hΦE (by norm_num) (by norm_num) hLRO (by norm_num)
      hnum
  have hc : (9 : ℝ) / (2 * (3 / 4 : ℝ) * (3 : ℝ) ^ 2) = (2 / 3 : ℝ) := by norm_num
  rwa [hc] at h

/-! ## Numeric fixture 2 — capstone constant guard -/

/-- **Fixture (capstone constant guard).** At `d := 3`, `L := 2`, `h₀ := 5/2`, `o₀ := 1/3`,
`q₀ := 3/4` the capstone's constant `C = 8·3·(5/2)·(1/3)²/(3/4) = 80/9` gives bound
`C/L^d = (80/9)/8 = 10/9`. Non-degeneracy: `d = 3 ≠ L = 2`; `o₀ : o₀² = 3`, distinct from the
factor `2` between the candidate leading constants `16` and `8`, so a dropped square on `o₀` and a
wrong leading constant cannot coincide here (unlike at `o₀ = 1/2`); `q₀ = 3/4` is not `1`, `q₀²`,
or `2q₀`, so `/q₀` is load-bearing and separates `8/q₀` from `8/(2q₀)`. The **discriminating
mechanism is the intermediate `have`**, whose right-hand side spells the constant out
syntactically; the numeric endpoint `≤ 10/9` alone is one-sided and is blind to a wrongly-*small*
constant such as `8 d h₀ o₀²/(2q₀)` (value `5/9`), which only the syntactic `have` excludes. The
candidate `16 d h₀ o₀²/q₀` (value `20/9`) is caught by both. -/
example {ι : Type*} (B : Finset ι) (hb : ι → ManyBodyOpS Λ N) (o : Λ → ManyBodyOpS Λ N)
    (W : ι → Finset Λ) {Φ : (Λ → Fin (N + 1)) → ℂ} {E₀ : ℝ}
    (hH : (∑ b ∈ B, hb b).IsHermitian) (hO : (∑ x : Λ, o x).IsHermitian)
    (hW : ∀ b ∈ B, ∀ z ∉ W b, Commute (hb b) (o z))
    (hoo : ∀ x z : Λ, x ≠ z → Commute (o x) (o z))
    (hnh : ∀ b ∈ B, manyBodyOperatorNormS (hb b) ≤ (5 / 2 : ℝ))
    (hno : ∀ x : Λ, manyBodyOperatorNormS (o x) ≤ (1 / 3 : ℝ))
    (hbond : ∀ b ∈ B, (W b).card ≤ 2)
    (hB : (B.card : ℝ) ≤ (3 : ℝ) * (2 : ℝ) ^ (3 : ℕ))
    (hΦ : star Φ ⬝ᵥ Φ = 1)
    (hΦE : (∑ b ∈ B, hb b) *ᵥ Φ = (E₀ : ℂ) • Φ)
    (hmin : ∀ v : (Λ → Fin (N + 1)) → ℂ, star v ⬝ᵥ v = 1 →
      E₀ ≤ rayleighOnVec (∑ b ∈ B, hb b) v)
    (hLRO : (3 / 4 : ℝ) ≤ rayleighOnVec ((∑ x : Λ, o x) ^ 2) Φ / ((2 : ℝ) ^ (3 : ℕ)) ^ 2) :
    rayleighOnVec (∑ b ∈ B, hb b) (hvlTrialState (∑ x : Λ, o x) Φ) - E₀ ≤ (10 / 9 : ℝ) := by
  have h : rayleighOnVec (∑ b ∈ B, hb b) (hvlTrialState (∑ x : Λ, o x) Φ) - E₀
      ≤ 8 * (3 : ℝ) * (5 / 2 : ℝ) * (1 / 3 : ℝ) ^ 2 / (3 / 4 : ℝ) / (2 : ℝ) ^ (3 : ℕ) :=
    (tasaki_eq_3_4_12_trialState_energy_bound B hb o W 3 2 (3 / 4) (5 / 2) (1 / 3)
      hH hO hW hoo hnh hno (by norm_num) (by norm_num) hbond hB hΦ hΦE hmin (by norm_num)
      (by norm_num) hLRO).2
  have hc : 8 * (3 : ℝ) * (5 / 2 : ℝ) * (1 / 3 : ℝ) ^ 2 / (3 / 4 : ℝ) / (2 : ℝ) ^ (3 : ℕ)
      = (10 / 9 : ℝ) := by norm_num
  rwa [hc] at h

/-! ## Witness — discharging `hmin` from `hermitianMinEigenvalue_le_rayleighOnVec_of_unit` -/

/-- **Discharge witness for `hmin`.** Instantiates the capstone at `E₀ := hermitianMinEigenvalue
hH`, the canonical ground-state energy, and discharges `hmin` from
`hermitianMinEigenvalue_le_rayleighOnVec_of_unit`, showing `hmin` is a dischargeable fact (not a
permanently standing assumption) and that the capstone is non-vacuous at a genuine ground state.
This import (`RayleighRitzEquality.lean`) is Tests-only; the library module does not import it
(§3 of the design). -/
example [Nonempty (Λ → Fin (N + 1))] {ι : Type*} (B : Finset ι)
    (hb : ι → ManyBodyOpS Λ N) (o : Λ → ManyBodyOpS Λ N) (W : ι → Finset Λ)
    (d L : ℕ) (q₀ h₀ o₀ : ℝ) {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hH : (∑ b ∈ B, hb b).IsHermitian) (hO : (∑ x : Λ, o x).IsHermitian)
    (hW : ∀ b ∈ B, ∀ z ∉ W b, Commute (hb b) (o z))
    (hoo : ∀ x z : Λ, x ≠ z → Commute (o x) (o z))
    (hnh : ∀ b ∈ B, manyBodyOperatorNormS (hb b) ≤ h₀)
    (hno : ∀ x : Λ, manyBodyOperatorNormS (o x) ≤ o₀)
    (hh₀ : 0 ≤ h₀) (ho₀ : 0 ≤ o₀)
    (hbond : ∀ b ∈ B, (W b).card ≤ 2)
    (hB : (B.card : ℝ) ≤ (d : ℝ) * (L : ℝ) ^ d)
    (hΦ : star Φ ⬝ᵥ Φ = 1)
    (hΦE : (∑ b ∈ B, hb b) *ᵥ Φ = ((hermitianMinEigenvalue hH : ℝ) : ℂ) • Φ)
    (hq₀ : 0 < q₀) (hL : 1 ≤ L)
    (hLRO : q₀ ≤ rayleighOnVec ((∑ x : Λ, o x) ^ 2) Φ / ((L : ℝ) ^ d) ^ 2) :
    0 ≤ rayleighOnVec (∑ b ∈ B, hb b) (hvlTrialState (∑ x : Λ, o x) Φ)
          - hermitianMinEigenvalue hH
      ∧ rayleighOnVec (∑ b ∈ B, hb b) (hvlTrialState (∑ x : Λ, o x) Φ)
          - hermitianMinEigenvalue hH
          ≤ 8 * (d : ℝ) * h₀ * o₀ ^ 2 / q₀ / (L : ℝ) ^ d :=
  tasaki_eq_3_4_12_trialState_energy_bound B hb o W d L q₀ h₀ o₀ hH hO hW hoo hnh hno hh₀ ho₀
    hbond hB hΦ hΦE
    (fun (v : (Λ → Fin (N + 1)) → ℂ) (hv : star v ⬝ᵥ v = 1) =>
      hermitianMinEigenvalue_le_rayleighOnVec_of_unit hH hv)
    hq₀ hL hLRO

end LatticeSystem.Tests.HorschVonderLindenEnergyBound
