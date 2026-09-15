import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSTheorem24
import LatticeSystem.Quantum.SpinS.DressedAxisSwappedAnisotropic
import LatticeSystem.Quantum.SpinS.SpinHalfSpecialization
import LatticeSystem.Quantum.SpinHalf

/-!
# Red fixture (#5475 / #5478): `hc_axis_strict` / `hc_strict` binder unsatisfiability

Repository-internal regression guard, **not** a Tasaki result on its own. This file pins the
acceptance criteria of Issue #5475's first PR (spin-`S` tower, 7 modules): the `∀ (lam D : ℂ)
(σ : Λ → Fin (N + 1)), … < c` shaped hypothesis binders (`hc_axis_strict` / `hc_strict`) are
**not** replaced by a function-valued or path-restricted variant — they are **deleted**, with
`c` obtained internally at each of the (measured) 10 point-wise consumption sites from a new
one-line existence lemma, the axis-swapped twin of
`exists_strict_diag_bound_dressedHeisenbergSReMatrix`
(`LatticeSystem/Quantum/SpinS/FerrimagneticLROUniversal.lean:61`).

Before the repair this file is Red in three independent ways:

1. **Identifier Red** (§1): the new supplier lemma
   `exists_strict_diag_bound_dressedAxisSwappedAnisotropicHeisenbergSReMatrix` does not exist
   yet, so applying it fails with `unknown identifier`.
2. **Binder-deletion pin** (§2): the two capstones of Tasaki Theorem 2.4
   (`anisotropicHeisenbergS_tasaki24_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_general`,
   `aHeisS_tasaki24_target_zeroMag_of_MLM_casLadder_t23_pf_gen`) currently *require* the
   `hc_axis_strict` argument positionally; applying them with every other hypothesis supplied
   abstractly but this one omitted is a genuine type mismatch (not a parse/import failure).
   After the repair the same term (with the binder dropped from both the `example`'s own
   parameter list and the application) type-checks, because the target signature no longer
   has that parameter. This simultaneously serves as the **strength control**: the endpoint
   conclusion is derived supplying *no* `c`-hypothesis at all, which cannot be written against
   the old (binder-carrying) signature.
3. **Negative control** (§3): the old `∀ (lam D : ℂ) (σ : …), … < c` form is unsatisfiable at
   the minimal instance `Λ = Unit`, `N = 1`, `J = 0`: the diagonal there is exactly `D.re / 4`
   for every `(lam, D, σ)` (the bond term vanishes since `J = 0`; the single-ion term reduces
   to `spinHalfOp2 * spinHalfOp2 = (1/4 : ℂ) • 1` at `N = 1`), so `D := ((4 * c + 1 : ℝ) : ℂ)`
   refutes any fixed `c`. This is real proof work (not a decorative `sorry`) because it is the
   fact that #5475 is diagnosing: no fixed `c` can witness the old binder.

## Differential-gate baseline (measured at `main = febc306e9d195e5f7724b8a99950764ebb1be8ff`)

This file cannot itself pin a repo-wide grep count, so the two invariants for `dev-verify` to
re-measure after the repair are recorded here as the exact commands used:

* **∀-lam-D binder lines in this PR's 7-module scope must become 0** (currently **30**):
  ```
  git grep -n '(hc_axis_strict : ∀ (lam D : ℂ)\|(hc_strict : ∀ (lam D : ℂ)' -- \
    LatticeSystem/Quantum/SpinS/AnisotropicHeisenbergSpinSDNonnegBoundary.lean \
    LatticeSystem/Quantum/SpinS/AnisotropicHeisenbergSpinSDNonnegBoundaryGlobalMin.lean \
    LatticeSystem/Quantum/SpinS/AnisotropicHeisenbergSpinSLambdaOneBoundary.lean \
    LatticeSystem/Quantum/SpinS/AnisotropicHeisenbergSpinSMLMEndpoint.lean \
    LatticeSystem/Quantum/SpinS/AnisotropicHeisenbergSpinSObligation2FromSU2Unique.lean \
    LatticeSystem/Quantum/SpinS/AnisotropicHeisenbergSpinSObligation2FromSU2UniqueCore.lean \
    LatticeSystem/Quantum/SpinS/AnisotropicHeisenbergSpinSTheorem24.lean | wc -l
  ```
* **Point-wise `(hc_strict : ∀ σ : Λ → Fin …)` binder lines repo-wide must stay unchanged**
  (measured **52**, positive control = the command itself finding 52 non-zero hits so a silent
  `0` cannot pass unnoticed):
  ```
  git grep -c '(hc_strict : ∀ σ : Λ → Fin' -- '*.lean' | awk -F: '{s+=$2} END{print s}'
  ```
  A drop below 52 after the repair means the deletion went one layer too deep into the
  irreducibility engines (whose conclusions carry `c`, e.g.
  `(shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p).IsIrreducible`), which must
  not be touched by this issue.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Tests.AxisSwapDiagBoundSatisfiable

open LatticeSystem.Quantum Module

/-! ## §1 Identifier Red: the new supplier lemma does not exist yet -/

/-- **Identifier Red.** The axis-swapped twin of
`exists_strict_diag_bound_dressedHeisenbergSReMatrix`, applied at a concrete small instance
(so this is a positive-control-style application, not merely a signature) — fails today with
`unknown identifier` because the declaration does not exist. -/
example :
    ∃ c : ℝ, ∀ σ : Fin 2 → Fin (1 + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix
        (fun x => x = 0) (fun x y => if x ≠ y then (1 : ℂ) else 0) (0 : ℂ) (0 : ℂ) 1 σ σ < c :=
  exists_strict_diag_bound_dressedAxisSwappedAnisotropicHeisenbergSReMatrix
    (fun x => x = 0) (fun x y => if x ≠ y then (1 : ℂ) else 0) (0 : ℂ) (0 : ℂ) 1

/-! ## §2 Binder-deletion pin (+ strength control): apply the Theorem 2.4 capstones with the
`∀-lam-D` hypothesis omitted entirely -/

/-- **Binder-deletion pin (finrank conjunct).** Every hypothesis of
`anisotropicHeisenbergS_tasaki24_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_general`
is supplied here as an abstract bound variable **except** `hc_axis_strict`, which is dropped
from both this `example`'s binder list and the application. Today the application is missing
a positional argument (`hA_ne` lands where `hc_axis_strict` is expected), a genuine type
mismatch — not a parse or import failure. After the binder is deleted from the target theorem,
this term type-checks unchanged, which also certifies the **strength control**: the conclusion
is reached with no `c`-hypothesis of any kind. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M : ℕ, M ∈ Finset.range (Fintype.card Λ * N + 1) → M ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M : ℂ)) ≠ 0)
    {lam D : ℝ}
    (h_region :
      (-1 < lam ∧ lam < 1 ∧ 0 ≤ D) ∨
      (lam = 1 ∧ 0 ≤ D) ∨
      (1 ≤ lam ∧ D ≤ 0)) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ)) ≤ 1 :=
  anisotropicHeisenbergS_tasaki24_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_general
    A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hA_ne hB_ne hN c_mlm c_toy hT23
    hc_heis_strict hc_toy_strict h_card_eq M_balanced h_balanced h_centered_nonzero h_region

/-- **Binder-deletion pin (zero-magnetization conjunct).** Same construction as above for
`aHeisS_tasaki24_target_zeroMag_of_MLM_casLadder_t23_pf_gen`, the second conjunct of Tasaki
Theorem 2.4. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M : ℕ, M ∈ Finset.range (Fintype.card Λ * N + 1) → M ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M : ℂ)) ≠ 0)
    {lam D : ℝ}
    (h_region :
      (-1 < lam ∧ lam < 1 ∧ 0 ≤ D) ∨
      (lam = 1 ∧ 0 ≤ D) ∨
      (1 ≤ lam ∧ D ≤ 0))
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 :=
  aHeisS_tasaki24_target_zeroMag_of_MLM_casLadder_t23_pf_gen
    A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hA_ne hB_ne hN c_mlm c_toy hT23
    hc_heis_strict hc_toy_strict h_card_eq M_balanced h_balanced h_centered_nonzero h_region
    hΦ_ne hΦ_gs

/-! ## §3 Negative control: the old binder is unsatisfiable at a minimal instance -/

/-- The Marshall-dressed axis-swapped diagonal at `Λ = Unit`, `N = 1`, `J = 0` is exactly
`D.re / 4`, for every `lam` and every configuration `σ` (the sole site's own coupling `J () ()`
is `0`, so the bond term vanishes; the single-ion term reduces to `spinHalfOp2 * spinHalfOp2
= (1/4 : ℂ) • 1` via the `N = 1` specialization). -/
theorem dressedAxisSwappedDiag_unit_zero_coupling
    (A : Unit → Bool) (lam D : ℂ) (σ : Unit → Fin (1 + 1)) :
    dressedAxisSwappedAnisotropicHeisenbergSReMatrix A (fun _ _ => (0 : ℂ)) lam D 1 σ σ
      = D.re / 4 := by
  rw [dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply,
    dressedAxisSwappedAnisotropicHeisenbergS_diag, axisSwappedAnisotropicHeisenbergS_def]
  have hbond :
      (∑ x : Unit, ∑ y : Unit,
          (0 : ℂ) • spinSDotXXZSwap x y lam 1) σ σ = 0 := by
    simp
  have honeIon :
      singleIonAnisotropyS2 (Λ := Unit) D 1 σ σ = D / 4 := by
    unfold singleIonAnisotropyS2
    rw [Finset.univ_unique, Finset.sum_singleton]
    have hself : onSiteS () (spinSOp2 1) * onSiteS () (spinSOp2 1)
        = onSiteS (Λ := Unit) () ((1 / 4 : ℂ) • (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ)) := by
      rw [onSiteS_mul_onSiteS_same, spinSOp2_one_eq_spinHalfOp2, spinHalfOp2_mul_self]
    rw [hself, onSiteS_smul, onSiteS_one]
    simp [Matrix.smul_apply, Matrix.one_apply_eq]
    ring
  rw [Matrix.add_apply, hbond, honeIon]
  simp

/-- **Negative control.** No fixed `c` bounds the diagonal for every `(lam, D)`: choosing
`D := 4 * c + 1` (real, embedded in `ℂ`) forces the diagonal to `c + 1/4 > c`, refuting the old
`hc_axis_strict`/`hc_strict` binder at the minimal instance `Λ = Unit`, `N = 1`, `J = 0`. -/
example (A : Unit → Bool) (c : ℝ) :
    ¬ ∀ (lam D : ℂ) (σ : Unit → Fin (1 + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A (fun _ _ => (0 : ℂ)) lam D 1 σ σ < c := by
  intro h
  have hval := h 0 (((4 * c + 1 : ℝ) : ℂ)) (fun _ => 0)
  rw [dressedAxisSwappedDiag_unit_zero_coupling] at hval
  have : ((((4 * c + 1 : ℝ) : ℂ)).re) = 4 * c + 1 := Complex.ofReal_re _
  rw [this] at hval
  linarith

end LatticeSystem.Tests.AxisSwapDiagBoundSatisfiable
