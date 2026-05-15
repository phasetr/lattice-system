import LatticeSystem.Quantum.MarshallLiebMattis.SublatticeCasimirNeel

/-!
# Spin-`1/2` Heisenberg Hamiltonian expectations on the Néel state
and the variational gap (γ-4 steps 147–168 mirrors)

Extracted from `SublatticeCasimirNeel.lean` (build-speed refactor).
This file contains the per-pair correlation trio, the
Heisenberg-Hamiltonian apply-diagonal at the Néel configuration,
the cross-only specialisation, the Heisenberg-on-graph bipartite
expectations, and the toy-Hamiltonian variational gap.

Theorems:
- `allUp_basisVec_heisenbergToyHamiltonian_expectation`
- `allDown_basisVec_heisenbergToyHamiltonian_expectation`
- `heisenbergToyHamiltonian_variational_gap`
- `neelConfigOf_ne_allUp` / `_ne_allDown`
- `neelStateOf_totalSpinHalfOp12_sq_expectation`
- `neelStateOf_expectation_spinHalfDot_of_cross` / `_same` / `_self`
- `heisenbergHamiltonian_apply_diag_neel`
- `neelStateOf_heisenbergHamiltonian_expectation`
- `neelStateOf_totalSpinHalfOp12_sq_expectation_re_pos`
- `neelStateOf_totalSpinHalfSquared_expectation_re_gt_OpZ_sq`
- `heisenbergHamiltonian_apply_diag_neel_of_cross_only`
- `neelStateOf_heisenbergHamiltonian_expectation_of_cross_only`
- `neelStateOf_heisenbergToyHamiltonian_expectation_via_cross_only`
- `heisenbergHamiltonianOnGraph_apply_diag_neel_of_bipartite`
- `neelStateOf_heisenbergHamiltonianOnGraph_expectation_of_bipartite` / `_closed` / `_re_neg`
- `heisenbergToyHamiltonian_variational_gap_re_pos`
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- `<basisVec (fun _ => 0) | Ĥ_toy | basisVec (fun _ => 0)> = +|A|·|¬A|/2`.
Spin-`1/2` mirror of γ-4 step 147 (toy Hamiltonian expectation on the all-up
basis state). Variational signature opposite to the Néel state. -/
theorem allUp_basisVec_heisenbergToyHamiltonian_expectation (A : Λ → Bool) :
    dotProduct (star (basisVec (fun _ : Λ => (0 : Fin 2))))
        ((heisenbergToyHamiltonian A : ManyBodyOp Λ).mulVec
          (basisVec (fun _ : Λ => (0 : Fin 2)))) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) / 2) := by
  rw [basisVec_expectation_eq_diagonal]
  -- The diagonal at allZeros: use heisenbergToyHamiltonian_mulVec_basisVec_const_simplified
  -- and basisVec_expectation_eq_diagonal again, or unfold.
  have h := heisenbergToyHamiltonian_mulVec_basisVec_const_simplified A 0
  -- h: (H_toy).mulVec (basisVec (fun _ => 0)) = c • basisVec (fun _ => 0)
  -- diagonal element = ((H_toy).mulVec (basisVec ...)) at (fun _ => 0) = c
  have hdiag :
      (heisenbergToyHamiltonian A : ManyBodyOp Λ)
          (fun _ : Λ => (0 : Fin 2)) (fun _ : Λ => (0 : Fin 2)) =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) / 2 := by
    have h2 : (heisenbergToyHamiltonian A : ManyBodyOp Λ).mulVec
        (basisVec (fun _ : Λ => (0 : Fin 2))) (fun _ : Λ => (0 : Fin 2)) =
        (heisenbergToyHamiltonian A : ManyBodyOp Λ)
          (fun _ : Λ => (0 : Fin 2)) (fun _ : Λ => (0 : Fin 2)) := by
      rw [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single (fun _ : Λ => (0 : Fin 2))]
      · rw [basisVec_self, mul_one]
      · intros τ _ hτne
        rw [basisVec_of_ne hτne]
        simp
      · intro h
        exact (h (Finset.mem_univ _)).elim
    rw [h] at h2
    rw [Pi.smul_apply, basisVec_self, smul_eq_mul, mul_one] at h2
    -- h2 : c = (H_toy)(allZero, allZero), need other direction
    exact h2.symm
  rw [hdiag]

/-- `<basisVec (fun _ => 1) | Ĥ_toy | basisVec (fun _ => 1)> = +|A|·|¬A|/2`.
Spin-`1/2` mirror of γ-4 step 148 (all-down spin-S expectation). Same
positive eigenvalue as the all-up basis state by the Casimir symmetry. -/
theorem allDown_basisVec_heisenbergToyHamiltonian_expectation (A : Λ → Bool) :
    dotProduct (star (basisVec (fun _ : Λ => (1 : Fin 2))))
        ((heisenbergToyHamiltonian A : ManyBodyOp Λ).mulVec
          (basisVec (fun _ : Λ => (1 : Fin 2)))) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) / 2) := by
  rw [basisVec_expectation_eq_diagonal]
  have h := heisenbergToyHamiltonian_mulVec_basisVec_const_simplified A 1
  have hdiag :
      (heisenbergToyHamiltonian A : ManyBodyOp Λ)
          (fun _ : Λ => (1 : Fin 2)) (fun _ : Λ => (1 : Fin 2)) =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) / 2 := by
    have h2 : (heisenbergToyHamiltonian A : ManyBodyOp Λ).mulVec
        (basisVec (fun _ : Λ => (1 : Fin 2))) (fun _ : Λ => (1 : Fin 2)) =
        (heisenbergToyHamiltonian A : ManyBodyOp Λ)
          (fun _ : Λ => (1 : Fin 2)) (fun _ : Λ => (1 : Fin 2)) := by
      rw [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single (fun _ : Λ => (1 : Fin 2))]
      · rw [basisVec_self, mul_one]
      · intros τ _ hτne
        rw [basisVec_of_ne hτne]
        simp
      · intro h
        exact (h (Finset.mem_univ _)).elim
    rw [h] at h2
    rw [Pi.smul_apply, basisVec_self, smul_eq_mul, mul_one] at h2
    exact h2.symm
  rw [hdiag]

/-- **Variational spin gap** (spin-`1/2` mirror of γ-4 step 150):
`<basisVec 0|Ĥ_toy|basisVec 0> - <Φ_Néel|Ĥ_toy|Φ_Néel> = |A|·|¬A|`.

The all-up basis state has positive expectation `+|A|·|¬A|/2`, the Néel
state has negative `-|A|·|¬A|/2`. Their difference is `|A|·|¬A|`,
strictly positive when both sublattices are non-empty. -/
theorem heisenbergToyHamiltonian_variational_gap (A : Λ → Bool) :
    dotProduct (star (basisVec (fun _ : Λ => (0 : Fin 2))))
        ((heisenbergToyHamiltonian A : ManyBodyOp Λ).mulVec
          (basisVec (fun _ : Λ => (0 : Fin 2)))) -
      dotProduct (star (neelStateOf A))
        ((heisenbergToyHamiltonian A : ManyBodyOp Λ).mulVec (neelStateOf A)) =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) := by
  rw [allUp_basisVec_heisenbergToyHamiltonian_expectation,
    neelStateOf_heisenbergToyHamiltonian_expectation]
  ring

omit [Fintype Λ] [DecidableEq Λ] in
/-- Configuration-level distinctness for spin-`1/2`: `neelConfigOf A ≠
fun _ => 0` when `|¬A| > 0`. Spin-`1/2` mirror of γ-4 step 144. -/
theorem neelConfigOf_ne_allUp
    (A : Λ → Bool) (hA : ∃ x : Λ, A x = false) :
    neelConfigOf A ≠ (fun _ : Λ => (0 : Fin 2)) := by
  obtain ⟨x, hx⟩ := hA
  intro heq
  have h := congrFun heq x
  unfold neelConfigOf at h
  rw [if_neg (by rw [hx]; decide : ¬ A x = true)] at h
  exact (by decide : (1 : Fin 2) ≠ 0) h

omit [Fintype Λ] [DecidableEq Λ] in
/-- Configuration-level distinctness for spin-`1/2`: `neelConfigOf A ≠
fun _ => 1` when `|A| > 0`. Spin-`1/2` mirror of γ-4 step 152. -/
theorem neelConfigOf_ne_allDown
    (A : Λ → Bool) (hA : ∃ x : Λ, A x = true) :
    neelConfigOf A ≠ (fun _ : Λ => (1 : Fin 2)) := by
  obtain ⟨x, hx⟩ := hA
  intro heq
  have h := congrFun heq x
  unfold neelConfigOf at h
  rw [if_pos hx] at h
  exact (by decide : (0 : Fin 2) ≠ 1) h

/-- `<Φ_Néel | (Ŝ_tot^(1))² + (Ŝ_tot^(2))² | Φ_Néel> = |Λ|/2`. Spin-`1/2`
mirror of γ-4 step 156. -/
theorem neelStateOf_totalSpinHalfOp12_sq_expectation (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((totalSpinHalfOp1 Λ * totalSpinHalfOp1 Λ +
          totalSpinHalfOp2 Λ * totalSpinHalfOp2 Λ).mulVec
          (neelStateOf A)) =
      (Fintype.card Λ : ℂ) / 2 := by
  have htotal := neelStateOf_totalSpinHalfSquared_expectation_card_Lambda A
  have hSq3 := neelStateOf_totalSpinHalfOp3_sq_expectation A
  unfold totalSpinHalfSquared at htotal
  rw [Matrix.add_mulVec, Matrix.add_mulVec] at htotal
  rw [dotProduct_add, dotProduct_add] at htotal
  rw [hSq3] at htotal
  rw [Matrix.add_mulVec, dotProduct_add]
  linear_combination htotal

/-- `<Φ_Néel | Ŝ_x · Ŝ_y | Φ_Néel> = -1/4` for a cross-sublattice pair
`x ∈ A`, `y ∈ ¬A`. Spin-`1/2` mirror of γ-4 step 157: lifts the diagonal
matrix element `spinHalfDot_apply_diag_neelConfigOf_of_cross` via
`basisVec_expectation_eq_diagonal`, since `Φ_Néel = basisVec
(neelConfigOf A)`. -/
theorem neelStateOf_expectation_spinHalfDot_of_cross
    (A : Λ → Bool) {x y : Λ} (hAx : A x = true) (hAy : A y = false) :
    dotProduct (star (neelStateOf A))
        ((spinHalfDot x y : ManyBodyOp Λ).mulVec (neelStateOf A)) =
      -(1 / 4 : ℂ) := by
  unfold neelStateOf
  rw [basisVec_expectation_eq_diagonal]
  exact spinHalfDot_apply_diag_neelConfigOf_of_cross A hAx hAy

/-- `<Φ_Néel | Ŝ_x · Ŝ_y | Φ_Néel> = +1/4` for a same-sublattice pair
`x ≠ y` with `A x = A y` (both in `A` or both in `¬A`). Spin-`1/2`
mirror of γ-4 step 158: lifts the diagonal matrix element
`spinHalfDot_apply_diag_neelConfigOf_of_same` via
`basisVec_expectation_eq_diagonal`. The positive sign matches the
ferromagnetic alignment of two spins on the same sublattice in the
Néel state. -/
theorem neelStateOf_expectation_spinHalfDot_of_same
    (A : Λ → Bool) {x y : Λ} (hxy : x ≠ y) (h : A x = A y) :
    dotProduct (star (neelStateOf A))
        ((spinHalfDot x y : ManyBodyOp Λ).mulVec (neelStateOf A)) =
      (1 / 4 : ℂ) := by
  unfold neelStateOf
  rw [basisVec_expectation_eq_diagonal]
  exact spinHalfDot_apply_diag_neelConfigOf_of_same A hxy h

/-- `<Φ_Néel | Ŝ_x · Ŝ_x | Φ_Néel> = 3/4 = S(S+1)` for `S = 1/2`. Spin-`1/2`
mirror of γ-4 step 159: the same-site (diagonal) per-pair correlation
equals the universal local Casimir eigenvalue, here `1/2 · 3/2 = 3/4`.
Direct from `spinHalfDot_self` (which states `Ŝ_x · Ŝ_x = (3/4) · 1`)
combined with `neelStateOf_inner_self` (norm² = 1). -/
theorem neelStateOf_expectation_spinHalfDot_self
    (A : Λ → Bool) (x : Λ) :
    dotProduct (star (neelStateOf A))
        ((spinHalfDot x x : ManyBodyOp Λ).mulVec (neelStateOf A)) =
      (3 / 4 : ℂ) := by
  rw [spinHalfDot_self, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [dotProduct_smul, smul_eq_mul, neelStateOf_inner_self, mul_one]

/-- The spin-`1/2` Heisenberg Hamiltonian's diagonal matrix element at
the Néel configuration: synthesis of the per-pair correlation trio
(γ-4 steps 157/158/159 spin-`1/2` mirrors). Each `(x, y)` term contributes

  `J(x,y) · 3/4`     if `x = y`,
  `J(x,y) · +1/4`    if `x ≠ y` and `A x = A y`,
  `J(x,y) · -1/4`    if `x ≠ y` and `A x ≠ A y`.

Spin-`1/2` mirror of γ-4 step 160. -/
theorem heisenbergHamiltonian_apply_diag_neel
    (J : Λ → Λ → ℂ) (A : Λ → Bool) :
    (heisenbergHamiltonian J : ManyBodyOp Λ) (neelConfigOf A) (neelConfigOf A) =
      ∑ x : Λ, ∑ y : Λ,
        J x y *
          (if x = y then (3 / 4 : ℂ)
           else if A x = A y then (1 / 4 : ℂ)
           else -(1 / 4 : ℂ)) := by
  unfold heisenbergHamiltonian
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  refine Finset.sum_congr rfl (fun y _ => ?_)
  congr 1
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, spinHalfDot_self, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one]
  · rw [if_neg hxy]
    by_cases hAxy : A x = A y
    · rw [if_pos hAxy]
      exact spinHalfDot_apply_diag_neelConfigOf_of_same A hxy hAxy
    · rw [if_neg hAxy]
      by_cases hAx : A x = true
      · have hAy : A y = false := by
          cases hAyc : A y with
          | true => exact absurd (hAx.trans hAyc.symm) hAxy
          | false => rfl
        exact spinHalfDot_apply_diag_neelConfigOf_of_cross A hAx hAy
      · have hAxF : A x = false := by
          cases hAxc : A x with
          | true => exact absurd hAxc hAx
          | false => rfl
        have hAy : A y = true := by
          cases hAyc : A y with
          | true => rfl
          | false => exact absurd (hAxF.trans hAyc.symm) hAxy
        rw [show (spinHalfDot x y : ManyBodyOp Λ) = spinHalfDot y x from
              spinHalfDot_comm x y]
        exact spinHalfDot_apply_diag_neelConfigOf_of_cross A hAy hAxF

/-- State-level expectation of the spin-`1/2` Heisenberg Hamiltonian on
the Néel state: lifts `heisenbergHamiltonian_apply_diag_neel` via
`basisVec_expectation_eq_diagonal`. Spin-`1/2` mirror of γ-4 step 160. -/
theorem neelStateOf_heisenbergHamiltonian_expectation
    (J : Λ → Λ → ℂ) (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((heisenbergHamiltonian J : ManyBodyOp Λ).mulVec (neelStateOf A)) =
      ∑ x : Λ, ∑ y : Λ,
        J x y *
          (if x = y then (3 / 4 : ℂ)
           else if A x = A y then (1 / 4 : ℂ)
           else -(1 / 4 : ℂ)) := by
  unfold neelStateOf
  rw [basisVec_expectation_eq_diagonal]
  exact heisenbergHamiltonian_apply_diag_neel J A

/-- The transverse total-spin Casimir expectation on the spin-`1/2`
Néel state has strictly positive real part when `Λ` is non-empty:

  `0 < Re <Φ_Néel | (Ŝ_tot^(1))² + (Ŝ_tot^(2))² | Φ_Néel>`,

since the value equals `|Λ|/2 > 0`. Spin-`1/2` mirror of γ-4 step 161. -/
theorem neelStateOf_totalSpinHalfOp12_sq_expectation_re_pos
    [Nonempty Λ] (A : Λ → Bool) :
    0 < (dotProduct (star (neelStateOf A))
        ((totalSpinHalfOp1 Λ * totalSpinHalfOp1 Λ +
          totalSpinHalfOp2 Λ * totalSpinHalfOp2 Λ).mulVec
          (neelStateOf A))).re := by
  rw [neelStateOf_totalSpinHalfOp12_sq_expectation]
  have hreal :
      (Fintype.card Λ : ℂ) / 2 =
        (((Fintype.card Λ : ℝ) / 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [hreal, Complex.ofReal_re]
  refine div_pos ?_ two_pos
  exact_mod_cast Fintype.card_pos

/-- **Strict spread** (spin-`1/2` mirror of γ-4 step 162):
`Re <Φ_Néel | (Ŝ_tot^(3))² | Φ_Néel> < Re <Φ_Néel | (Ŝ_tot)² | Φ_Néel>`
when `Λ` is non-empty. The Néel state has strictly larger total-spin
Casimir than the squared magnetization, so it spans multiple
`S_tot`-sectors. -/
theorem neelStateOf_totalSpinHalfSquared_expectation_re_gt_OpZ_sq
    [Nonempty Λ] (A : Λ → Bool) :
    (dotProduct (star (neelStateOf A))
        ((totalSpinHalfOp3 Λ * totalSpinHalfOp3 Λ).mulVec
          (neelStateOf A))).re <
    (dotProduct (star (neelStateOf A))
        ((totalSpinHalfSquared Λ).mulVec (neelStateOf A))).re := by
  have h12pos := neelStateOf_totalSpinHalfOp12_sq_expectation_re_pos A
  rw [show (totalSpinHalfSquared Λ : ManyBodyOp Λ) =
        (totalSpinHalfOp1 Λ * totalSpinHalfOp1 Λ +
          totalSpinHalfOp2 Λ * totalSpinHalfOp2 Λ) +
          totalSpinHalfOp3 Λ * totalSpinHalfOp3 Λ from by
      unfold totalSpinHalfSquared; abel]
  rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]
  linarith

/-- **Cross-only specialization** (spin-`1/2` mirror of γ-4 step 164):
when `J(x, y) = 0` whenever `A x = A y`, the Heisenberg Néel diagonal
collapses to `-(1/4) · Σ J(x, y)`. -/
theorem heisenbergHamiltonian_apply_diag_neel_of_cross_only
    (J : Λ → Λ → ℂ) (A : Λ → Bool)
    (hJ : ∀ x y, A x = A y → J x y = 0) :
    (heisenbergHamiltonian J : ManyBodyOp Λ) (neelConfigOf A) (neelConfigOf A) =
      -(1 / 4 : ℂ) * (∑ x : Λ, ∑ y : Λ, J x y) := by
  rw [heisenbergHamiltonian_apply_diag_neel]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, hJ x x rfl]; ring
  · rw [if_neg hxy]
    by_cases hAxy : A x = A y
    · rw [if_pos hAxy, hJ x y hAxy]; ring
    · rw [if_neg hAxy]; ring

/-- State-level cross-only specialization (spin-`1/2` mirror of γ-4 step 164). -/
theorem neelStateOf_heisenbergHamiltonian_expectation_of_cross_only
    (J : Λ → Λ → ℂ) (A : Λ → Bool)
    (hJ : ∀ x y, A x = A y → J x y = 0) :
    dotProduct (star (neelStateOf A))
        ((heisenbergHamiltonian J : ManyBodyOp Λ).mulVec (neelStateOf A)) =
      -(1 / 4 : ℂ) * (∑ x : Λ, ∑ y : Λ, J x y) := by
  unfold neelStateOf
  rw [basisVec_expectation_eq_diagonal]
  exact heisenbergHamiltonian_apply_diag_neel_of_cross_only J A hJ

/-- **Toy Hamiltonian Néel expectation via cross-only synthesis** (spin-`1/2`):
`<Φ_Néel | Ĥ_toy A | Φ_Néel> = -(1/4) · Σ bipartiteCoupling A x y =
-|A|·|¬A|/2`. Spin-`1/2` mirror of γ-4 step 165: independent re-derivation
through the per-pair correlation trio. -/
theorem neelStateOf_heisenbergToyHamiltonian_expectation_via_cross_only
    (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((heisenbergToyHamiltonian A : ManyBodyOp Λ).mulVec (neelStateOf A)) =
      -(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) / 2) := by
  unfold heisenbergToyHamiltonian
  rw [neelStateOf_heisenbergHamiltonian_expectation_of_cross_only
        (bipartiteCoupling A) A
        (fun x y h => bipartiteCoupling_eq_zero_of_same_sublattice A h)]
  rw [bipartiteCoupling_sum]
  ring

/-- **Heisenberg-on-graph diagonal Néel matrix element** (spin-`1/2`)
under bipartite alignment: when every edge of `G` crosses `(A, ¬A)`,
`(heisenbergHamiltonianOnGraph G J)(neel)(neel) = -(1/4) · Σ couplingOf G J`.
Spin-`1/2` mirror of γ-4 step 166. -/
theorem heisenbergHamiltonianOnGraph_apply_diag_neel_of_bipartite
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (J : ℂ) (A : Λ → Bool)
    (hG : ∀ x y, G.Adj x y → A x ≠ A y) :
    (heisenbergHamiltonianOnGraph G J : ManyBodyOp Λ)
        (neelConfigOf A) (neelConfigOf A) =
      -(1 / 4 : ℂ) *
        (∑ x : Λ, ∑ y : Λ, LatticeSystem.Lattice.couplingOf G J x y) := by
  unfold heisenbergHamiltonianOnGraph
  refine heisenbergHamiltonian_apply_diag_neel_of_cross_only _ A ?_
  intros x y h
  unfold LatticeSystem.Lattice.couplingOf
  rw [if_neg (fun hAdj => hG x y hAdj h)]

/-- State-level spin-`1/2` Heisenberg-on-graph Néel expectation under
bipartite alignment. Spin-`1/2` mirror of γ-4 step 166. -/
theorem neelStateOf_heisenbergHamiltonianOnGraph_expectation_of_bipartite
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (J : ℂ) (A : Λ → Bool)
    (hG : ∀ x y, G.Adj x y → A x ≠ A y) :
    dotProduct (star (neelStateOf A))
        ((heisenbergHamiltonianOnGraph G J : ManyBodyOp Λ).mulVec (neelStateOf A)) =
      -(1 / 4 : ℂ) *
        (∑ x : Λ, ∑ y : Λ, LatticeSystem.Lattice.couplingOf G J x y) := by
  unfold neelStateOf
  rw [basisVec_expectation_eq_diagonal]
  exact heisenbergHamiltonianOnGraph_apply_diag_neel_of_bipartite G J A hG

/-- **Closed-form Heisenberg-on-graph Néel expectation** (spin-`1/2`)
under bipartite alignment: `<Φ_Néel | H_G | Φ_Néel> = -J · #G.edgeFinset / 2`.
Spin-`1/2` mirror of γ-4 step 167. -/
theorem neelStateOf_heisenbergHamiltonianOnGraph_expectation_of_bipartite_closed
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (J : ℂ) (A : Λ → Bool)
    (hG : ∀ x y, G.Adj x y → A x ≠ A y) :
    dotProduct (star (neelStateOf A))
        ((heisenbergHamiltonianOnGraph G J : ManyBodyOp Λ).mulVec (neelStateOf A)) =
      -(J * (G.edgeFinset.card : ℂ) / 2) := by
  rw [neelStateOf_heisenbergHamiltonianOnGraph_expectation_of_bipartite G J A hG]
  rw [LatticeSystem.Lattice.couplingOf_sum]
  ring

/-- **Strict negativity in ℝ** (spin-`1/2`) of the AFM Heisenberg-on-graph
Néel expectation: for `J = (J_re : ℂ)` with `0 < J_re`, bipartite
alignment, and `0 < #G.edgeFinset`, the real part is strictly negative.
Spin-`1/2` mirror of γ-4 step 168. -/
theorem neelStateOf_heisenbergHamiltonianOnGraph_expectation_of_bipartite_re_neg
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (A : Λ → Bool)
    {J_re : ℝ} (hJ : 0 < J_re)
    (hG : ∀ x y, G.Adj x y → A x ≠ A y)
    (hE : 0 < G.edgeFinset.card) :
    (dotProduct (star (neelStateOf A))
        ((heisenbergHamiltonianOnGraph G (J_re : ℂ) : ManyBodyOp Λ).mulVec
          (neelStateOf A))).re < 0 := by
  rw [neelStateOf_heisenbergHamiltonianOnGraph_expectation_of_bipartite_closed
        G (J_re : ℂ) A hG]
  have hreal :
      -((J_re : ℂ) * (G.edgeFinset.card : ℂ) / 2) =
        ((-(J_re * (G.edgeFinset.card : ℝ) / 2) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hreal, Complex.ofReal_re]
  refine neg_neg_iff_pos.mpr (div_pos (mul_pos hJ ?_) two_pos)
  exact_mod_cast hE

/-- **Real-valued positivity** of the spin-`1/2` toy Hamiltonian
variational gap: `0 < Re (<basisVec 0|Ĥ_toy|basisVec 0> -
<Φ_Néel|Ĥ_toy|Φ_Néel>) = |A|·|¬A|` when both sublattices are non-empty.
Spin-`1/2` mirror of γ-4 step 163. -/
theorem heisenbergToyHamiltonian_variational_gap_re_pos
    (A : Λ → Bool)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    0 < (dotProduct (star (basisVec (fun _ : Λ => (0 : Fin 2))))
        ((heisenbergToyHamiltonian A : ManyBodyOp Λ).mulVec
          (basisVec (fun _ : Λ => (0 : Fin 2)))) -
      dotProduct (star (neelStateOf A))
        ((heisenbergToyHamiltonian A : ManyBodyOp Λ).mulVec (neelStateOf A))).re := by
  rw [heisenbergToyHamiltonian_variational_gap]
  have hreal :
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) =
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) : ℝ) := by
    push_cast; ring
  rw [hreal, Complex.ofReal_re]
  refine mul_pos ?_ ?_
  · exact_mod_cast hA
  · exact_mod_cast hAc


end LatticeSystem.Quantum
