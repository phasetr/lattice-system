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
`c` obtained internally at each of the 6 point-wise consumption sites from a new one-line
existence lemma, the axis-swapped twin of
`exists_strict_diag_bound_dressedHeisenbergSReMatrix`
(`LatticeSystem/Quantum/SpinS/FerrimagneticLROUniversal.lean:61`).

Unit for that 6: proof-body applications of the supplier identifier *within those 7 modules*.
Repo-wide the identifier has 10 grep hits, splitting as those 6, one further proof-body
application (§1 of this file), its own declaration, and 2 prose citations (§ below and
`LatticeSystem/Tests/Theorem24ConnectedEndpoints.lean`) — so the raw hit count is not the count
of consumption sites and must not be quoted as one, and neither number may be quoted without its
unit.

This fixture is Red against any tree carrying the pre-repair signatures, in three independent
ways:

1. **Identifier Red** (§1): applying the supplier lemma
   `exists_strict_diag_bound_dressedAxisSwappedAnisotropicHeisenbergSReMatrix` fails with
   `unknown identifier` unless that declaration is present.
2. **Binder-deletion pin** (§2): the two capstones of Tasaki Theorem 2.4
   (`anisotropicHeisenbergS_tasaki24_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_general`,
   `aHeisS_tasaki24_target_zeroMag_of_MLM_casLadder_t23_pf_gen`) are applied with every
   hypothesis supplied abstractly *except* `hc_axis_strict`, which is absent from both the
   `example`'s own parameter list and the application. Such a term type-checks exactly when the
   target signature has no such parameter; against a signature that still binds it positionally
   the application is short one argument, a genuine type mismatch (not a parse/import failure).
   This simultaneously serves as the **strength control**: the endpoint
   conclusion is derived supplying *no axis-swapped diagonal-shift* hypothesis
   (`c_axis` / `hc_axis_strict`) at all, which cannot be written against the old
   (binder-carrying) signature. It is not a claim that no `c`-hypothesis of any kind is
   supplied: the MLM/toy scalars `c_mlm`, `c_toy` and their bounds `hc_heis_strict`,
   `hc_toy_strict` are still bound here and on the target signature.
3. **Negative control** (§3): the old `∀ (lam D : ℂ) (σ : …), … < c` form is unsatisfiable at
   an instance the binder-carrying theorems actually admit. Take
   `anisotropicHeisenbergS_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_D_nonneg_general`
   and the witness `Λ = Fin 2`, `A = (· = 0)`, `J = bipartiteCoupling A`, `N = 1`. The first
   `example` of §3 discharges in Lean every *explicit* hypothesis that theorem places on
   `(A, J, N)`: the seven `J` conditions standing before the deleted binder (`hJim`, `hJnn`,
   `hJpos` on `bipartiteCompleteGraphOf A`, `hJself`, `hJbip`, `hJ_star`, `hJ_sym`) together with
   `hA_ne`, `hB_ne` and `hN : 1 ≤ N`. Its three instance-implicit arguments
   (`Nonempty (parityConfigS Λ N 0)`, `Nonempty (parityConfigS Λ N 1)`,
   `Nonempty (Λ → Fin (N + 1))`) are outside that enumeration and are left to instance search.
   `Λ = Unit` is *not* such an instance — `hA_ne` and `hB_ne` cannot
   both hold at a one-point type, and all 30 binder-carrying declarations in this PR's scope
   bind both — so a witness there would show only that the binder is unsatisfiable in
   isolation, not that the theorems carrying it are vacuous, which is the claim at issue.
   On the admissible witness the diagonal splits as (bond part) `+ D.re / 2`: at `N = 1` the
   single-ion term contributes `D * |Λ| / 4 = D / 2` on every configuration, independently of
   `lam` and of `σ`. The binder places `c` *before* `lam` and `D`, so one `c` would have to
   dominate every `D`; `D := ((2 * (c - bond) + 2 : ℝ) : ℂ)` refutes any fixed `c`. This is
   real proof work (not a decorative `sorry`) because it is the fact that #5475 is diagnosing.

## Differential-gate baseline (measured at `main = febc306e9d195e5f7724b8a99950764ebb1be8ff`)

This file cannot itself pin a repo-wide grep count, so the two invariants for `dev-verify` to
re-measure after the repair are recorded here as the exact commands used:

* **∀-lam-D binder lines in this PR's 7-module scope must become 0** (**30** at that baseline):
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
  `0` cannot pass unnoticed). This file's own module doc quotes the pattern twice (this bullet
  and the command below), so re-running the grep verbatim over the whole tree double-counts
  this file's prose by 2 (54, not 52); the command below excludes this file by path to measure
  the invariant it documents rather than its own citation of it:
  ```
  git grep -c '(hc_strict : ∀ σ : Λ → Fin' -- '*.lean' \
    ':!LatticeSystem/Tests/AxisSwapDiagBoundSatisfiable.lean' | awk -F: '{s+=$2} END{print s}'
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

/-! ## §1 Identifier Red: the supplier lemma must be present and applicable -/

/-- **Identifier Red.** Pins the axis-swapped twin of
`exists_strict_diag_bound_dressedHeisenbergSReMatrix` by applying it at a concrete small instance
(so this is a positive-control-style application, not merely a signature): the term elaborates
only where that declaration exists, and fails with `unknown identifier` where it does not. -/
example :
    ∃ c : ℝ, ∀ σ : Fin 2 → Fin (1 + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix
        (fun x => x = 0) (fun x y => if x ≠ y then (1 : ℂ) else 0) (0 : ℂ) (0 : ℂ) 1 σ σ < c :=
  exists_strict_diag_bound_dressedAxisSwappedAnisotropicHeisenbergSReMatrix
    _ _ _ _ _

/-! ## §2 Binder-deletion pin (+ strength control): apply the Theorem 2.4 capstones with the
`∀-lam-D` hypothesis omitted entirely -/

/-- **Binder-deletion pin (finrank conjunct).** Every hypothesis of
`anisotropicHeisenbergS_tasaki24_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_general`
is supplied here as an abstract bound variable **except** `hc_axis_strict`, which is absent from
both this `example`'s binder list and the application. The term type-checks exactly when the
target signature carries no such parameter; against a signature that still binds it the
application is short one positional argument (`hA_ne` lands where `hc_axis_strict` is expected),
a genuine type mismatch rather than a parse or import failure. It thereby certifies the
**strength control**: the conclusion is reached with no axis-swapped diagonal-shift `c`
hypothesis (`c_axis` / `hc_axis_strict`). The MLM/toy scalars `c_mlm`, `c_toy` and their strict
bounds remain bound below. -/
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
Theorem 2.4: `hc_axis_strict` is absent from both the binder list and the application, so the
term type-checks exactly when the target signature carries no such parameter. -/
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

/-! ## §3 Negative control: the old binder is unsatisfiable at an instance the theorems admit -/

/-- The negative-control bipartition on `Fin 2`: site `0` on sublattice `A`, site `1` on `B`. -/
private def negCtrlA : Fin 2 → Bool := fun x => x = 0

/-- **Admissibility of the negative-control witness.** `Λ = Fin 2`, `A = negCtrlA`,
`J = bipartiteCoupling A`, `N = 1` discharges every *explicit* hypothesis that
`anisotropicHeisenbergS_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_D_nonneg_general`
places on `(A, J, N)`: the seven `J` conditions standing before the deleted binder, together
with `hA_ne`, `hB_ne` and `hN`. That theorem's three instance-implicit `Nonempty` arguments
(`parityConfigS Λ N 0`, `parityConfigS Λ N 1`, `Λ → Fin (N + 1)`) are outside this enumeration
and are left to instance search. The refutation below therefore concerns an instance the
binder-carrying theorems accept, not one their own standing assumptions exclude. -/
example :
    (∀ x y, (bipartiteCoupling negCtrlA x y).im = 0) ∧
    (∀ x y, 0 ≤ (bipartiteCoupling negCtrlA x y).re) ∧
    (∀ x y, (bipartiteCompleteGraphOf negCtrlA).Adj x y →
      0 < (bipartiteCoupling negCtrlA x y).re) ∧
    (∀ x, bipartiteCoupling negCtrlA x x = 0) ∧
    (∀ x y, bipartiteCoupling negCtrlA x y ≠ 0 → negCtrlA x ≠ negCtrlA y) ∧
    (∀ x y, star (bipartiteCoupling negCtrlA x y) = bipartiteCoupling negCtrlA x y) ∧
    (∀ x y, bipartiteCoupling negCtrlA x y = bipartiteCoupling negCtrlA y x) ∧
    (∃ a, negCtrlA a = true) ∧ (∃ b, negCtrlA b = false) ∧ (1 : ℕ) ≤ 1 := by
  refine ⟨fun x y => bipartiteCoupling_im _ x y, fun x y => bipartiteCoupling_nonneg _ x y,
    fun _ _ hadj =>
      bipartiteCoupling_pos_of_diff_sublattice _ (bipartiteCompleteGraphOf_adj_sublattice_ne hadj),
    fun _ => bipartiteCoupling_eq_zero_of_same_sublattice _ rfl, ?_, ?_,
    fun x y => bipartiteCoupling_symm _ x y, ⟨0, by decide⟩, ⟨1, by decide⟩, le_refl 1⟩
  · intro _ _ hne hAeq
    exact hne (bipartiteCoupling_eq_zero_of_same_sublattice _ hAeq)
  · intro x y
    unfold bipartiteCoupling
    split_ifs <;> simp

/-- At `Λ = Fin 2`, `N = 1` the Marshall-dressed axis-swapped diagonal splits as the bond part
plus `D.re / 2`: the single-ion term reduces to `spinHalfOp2 * spinHalfOp2 = (1/4 : ℂ) • 1` at
each of the two sites, so it contributes `D / 2` on every configuration, independently of `lam`
and of `σ`. The bond part never mentions `D`. -/
private theorem dressedAxisSwappedDiag_fin2_spinHalf_bond_add_D
    (A : Fin 2 → Bool) (J : Fin 2 → Fin 2 → ℂ) (lam D : ℂ) (σ : Fin 2 → Fin (1 + 1)) :
    dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ
      = ((∑ x : Fin 2, ∑ y : Fin 2, J x y • spinSDotXXZSwap x y lam 1) σ σ).re + D.re / 2 := by
  rw [dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply,
    dressedAxisSwappedAnisotropicHeisenbergS_diag, axisSwappedAnisotropicHeisenbergS_def,
    Matrix.add_apply]
  have hself : ∀ x : Fin 2,
      (onSiteS x (spinSOp2 1) * onSiteS x (spinSOp2 1) : ManyBodyOpS (Fin 2) 1)
        = (1 / 4 : ℂ) • 1 := by
    intro x
    rw [onSiteS_mul_onSiteS_same, spinSOp2_one_eq_spinHalfOp2, spinHalfOp2_mul_self,
      onSiteS_smul, onSiteS_one]
  have honeIon : singleIonAnisotropyS2 (Λ := Fin 2) D 1 σ σ = D / 2 := by
    unfold singleIonAnisotropyS2
    rw [Finset.sum_congr rfl (fun x _ => hself x), Matrix.smul_apply, Matrix.sum_apply]
    simp
    ring
  rw [honeIon, Complex.add_re]
  have hD2 : (D / 2 : ℂ).re = D.re / 2 := by simp
  rw [hD2]

/-- **Negative control.** At the admissible witness above no fixed `c` bounds the diagonal for
every `(lam, D)`. The binder quantifies `c` *before* `lam` and `D`, so a single `c` would have
to dominate the `D.re / 2` single-ion contribution for every `D`; taking `lam := 0` and
`D := ((2 * (c - bond) + 2 : ℝ) : ℂ)` at the all-`0` configuration pushes the diagonal to
`c + 1 > c`. So the deleted `hc_axis_strict` / `hc_strict` binder is unsatisfiable on an
instance that satisfies the standing assumptions of the binder-carrying signatures. -/
example (c : ℝ) :
    ¬ ∀ (lam D : ℂ) (σ : Fin 2 → Fin (1 + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix negCtrlA (bipartiteCoupling negCtrlA)
        lam D 1 σ σ < c := by
  intro h
  set b : ℝ := ((∑ x : Fin 2, ∑ y : Fin 2,
      bipartiteCoupling negCtrlA x y • spinSDotXXZSwap x y (0 : ℂ) 1)
        (fun _ => 0) (fun _ => 0)).re with hb
  have hval := h 0 (((2 * (c - b) + 2 : ℝ) : ℂ)) (fun _ => 0)
  rw [dressedAxisSwappedDiag_fin2_spinHalf_bond_add_D, Complex.ofReal_re, ← hb] at hval
  linarith

end LatticeSystem.Tests.AxisSwapDiagBoundSatisfiable
