import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeel

/-!
# Heisenberg / toy-Hamiltonian expectation on the Néel state and
bipartite-graph forms (build-speed companion)

Build-speed companion to `SublatticeCasimirNeel.lean`. Hosts the
trailing block on Heisenberg / `heisenbergHamiltonianOnGraphS`
expectation values at the Néel state and bipartite-complete-graph
specialisations (originally lines 1893..2430 of the parent file).

Splitting this trailing section out drops the parent file from
~2430 lines to ~1892 lines.

No in-repo downstream consumers of the moved names — all 25
theorems were only used inside this trailing block.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body
  Systems*, Springer 2020, §2.5 Theorem 2.2 (Marshall–Lieb–Mattis),
  pp. 39–43.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]


/-- `<Φ_⊥ | Ĥ_toy_S | Φ_⊥> = +|A|·|¬A|·N²/2`. The all-down state's toy
Hamiltonian expectation. Same eigenvalue as the all-up state by the
symmetry of the toy Hamiltonian. -/
theorem allAlignedStateS_last_heisenbergToyHamiltonianS_expectation
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (allAlignedStateS Λ N (Fin.last N))) =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
        ((N : ℂ) * (N : ℂ)) / 2 := by
  rw [heisenbergToyHamiltonianS_mulVec_allAlignedStateS_last_simplified]
  rw [dotProduct_smul, allAlignedStateS_inner_self]
  rw [smul_eq_mul, mul_one]

omit [Fintype Λ] [DecidableEq Λ] in
/-- Configuration-level distinctness: the Néel config differs from the
all-up config when `|¬A| > 0` and `N > 0`. Used to conclude that Néel
and all-up states span different basis vectors. -/
theorem neelConfigOfS_ne_allAlignedConfigS
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N)
    (hA : ∃ x : Λ, A x = false) :
    neelConfigOfS A N ≠ allAlignedConfigS Λ N 0 := by
  obtain ⟨x, hx⟩ := hA
  intro heq
  have h := congrFun heq x
  unfold neelConfigOfS allAlignedConfigS at h
  rw [if_neg (by rw [hx]; decide : ¬ A x = true)] at h
  simp [Fin.last] at h
  omega

omit [Fintype Λ] [DecidableEq Λ] in
/-- Configuration-level distinctness: the Néel config differs from the
all-down config when `|A| > 0` and `N > 0`. -/
theorem neelConfigOfS_ne_allAlignedConfigS_last
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N)
    (hA : ∃ x : Λ, A x = true) :
    neelConfigOfS A N ≠ allAlignedConfigS Λ N (Fin.last N) := by
  obtain ⟨x, hx⟩ := hA
  intro heq
  have h := congrFun heq x
  unfold neelConfigOfS allAlignedConfigS at h
  rw [if_pos hx] at h
  -- h : 0 = Fin.last N (in Fin (N+1))
  have : (0 : Fin (N + 1)).val = (Fin.last N).val := by rw [h]
  simp [Fin.last] at this
  omega

/-- `<Φ_Néel | (Ŝ_tot^(1))² + (Ŝ_tot^(2))² | Φ_Néel> = |Λ|·N/2`. The
transverse-axis component of the total-spin Casimir on the Néel state.

Direct subtraction:
`<(Ŝ_tot^(1))² + (Ŝ_tot^(2))²> = <(Ŝ_tot)²> - <(Ŝ_tot^(3))²>
                                = (M² + |Λ|·N/2) - M² = |Λ|·N/2`. -/
theorem neelStateOfS_totalSpinSOp12_sq_expectation (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS A N))
        ((totalSpinSOp1 Λ N * totalSpinSOp1 Λ N +
          totalSpinSOp2 Λ N * totalSpinSOp2 Λ N).mulVec
          (neelStateOfS A N)) =
      (Fintype.card Λ : ℂ) * ((N : ℂ) / 2) := by
  have htotal := neelStateOfS_totalSpinSSquared_expectation_card_Lambda A N
  have hSq3 := neelStateOfS_totalSpinSOp3_sq_expectation A N
  rw [totalSpinSSquared_def] at htotal
  rw [Matrix.add_mulVec, Matrix.add_mulVec] at htotal
  rw [dotProduct_add, dotProduct_add] at htotal
  rw [hSq3] at htotal
  -- htotal: A + B + M² = M² + |Λ|·N/2, where A, B = <S1², S2²>(Néel)
  rw [Matrix.add_mulVec, dotProduct_add]
  -- goal: A + B = |Λ|·N/2
  have h := htotal
  linear_combination h

/-- `<Φ_Néel | Ŝ_x · Ŝ_y | Φ_Néel> = -N²/4` for a cross-sublattice pair
`x ∈ A`, `y ∈ ¬A`. The state-level expectation lifts the diagonal matrix
element `spinSDot_apply_diag_neelConfigOfS_of_cross` via
`basisVecS_expectation_eq_diagonal`, since `Φ_Néel = basisVecS
(neelConfigOfS A N)`.

This is the antiferromagnetic per-bond Néel correlation, the variational
input to Tasaki §2.5 Theorem 2.3. -/
theorem neelStateOfS_expectation_spinSDot_of_cross
    (A : Λ → Bool) (N : ℕ)
    {x y : Λ} (hAx : A x = true) (hAy : A y = false) :
    dotProduct (star (neelStateOfS A N))
        ((spinSDot x y N : ManyBodyOpS Λ N).mulVec (neelStateOfS A N)) =
      -((N : ℂ) * (N : ℂ) / 4) := by
  unfold neelStateOfS
  rw [basisVecS_expectation_eq_diagonal]
  exact spinSDot_apply_diag_neelConfigOfS_of_cross A N hAx hAy

/-- `<Φ_Néel | Ŝ_x · Ŝ_y | Φ_Néel> = +N²/4` for a same-sublattice pair
`x ≠ y` with `A x = A y` (both in `A` or both in `¬A`). The state-level
expectation lifts the diagonal matrix element
`spinSDot_apply_diag_neelConfigOfS_of_same` via
`basisVecS_expectation_eq_diagonal`. The positive sign reflects the
ferromagnetic alignment of the two sites within the same sublattice in
the Néel state. -/
theorem neelStateOfS_expectation_spinSDot_of_same
    (A : Λ → Bool) (N : ℕ)
    {x y : Λ} (hxy : x ≠ y) (h : A x = A y) :
    dotProduct (star (neelStateOfS A N))
        ((spinSDot x y N : ManyBodyOpS Λ N).mulVec (neelStateOfS A N)) =
      ((N : ℂ) * (N : ℂ) / 4) := by
  unfold neelStateOfS
  rw [basisVecS_expectation_eq_diagonal]
  exact spinSDot_apply_diag_neelConfigOfS_of_same A N hxy h

/-- `<Φ_Néel | Ŝ_x · Ŝ_x | Φ_Néel> = N(N+2)/4 = S(S+1)`. The same-site
(diagonal) per-pair correlation is the universal single-site Casimir
eigenvalue `S(S+1)` on the spin-`S` irrep, evaluated against the
normalized Néel state. Direct application of
`spinSDot_self_expectation_normalized` with `neelStateOfS_inner_self`. -/
theorem neelStateOfS_expectation_spinSDot_self
    (A : Λ → Bool) (N : ℕ) (x : Λ) :
    dotProduct (star (neelStateOfS A N))
        ((spinSDot x x N : ManyBodyOpS Λ N).mulVec (neelStateOfS A N)) =
      ((N : ℂ) * (N + 2) / 4) :=
  spinSDot_self_expectation_normalized x (neelStateOfS_inner_self A N)

/-- The Heisenberg Hamiltonian's diagonal matrix element at the spin-`S`
Néel configuration: synthesis of the per-pair correlation trio (γ-4
steps 157/158/159) over the full coupling. Each `(x, y)` term contributes
`J(x,y) · v(x,y)` where

  `v(x,y) = N(N+2)/4`     if `x = y` (local Casimir),
  `v(x,y) = +N²/4`        if `x ≠ y` and `A x = A y` (same sublattice),
  `v(x,y) = -N²/4`        if `x ≠ y` and `A x ≠ A y` (cross sublattice).

For the bipartite AFM Heisenberg (J supported only on `A`–`¬A` bonds),
the same-sublattice and self contributions vanish, recovering the
toy Hamiltonian Néel expectation. -/
theorem heisenbergHamiltonianS_apply_diag_neel
    (J : Λ → Λ → ℂ) (A : Λ → Bool) (N : ℕ) :
    (heisenbergHamiltonianS J N) (neelConfigOfS A N) (neelConfigOfS A N) =
      ∑ x : Λ, ∑ y : Λ,
        J x y *
          (if x = y then ((N : ℂ) * (N + 2) / 4)
           else if A x = A y then ((N : ℂ) * (N : ℂ) / 4)
           else -((N : ℂ) * (N : ℂ) / 4)) := by
  rw [heisenbergHamiltonianS_apply]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  refine Finset.sum_congr rfl (fun y _ => ?_)
  congr 1
  by_cases hxy : x = y
  · subst hxy; rw [if_pos rfl, spinSDot_self_apply_diag]
  · rw [if_neg hxy]
    by_cases hAxy : A x = A y
    · rw [if_pos hAxy]
      exact spinSDot_apply_diag_neelConfigOfS_of_same A N hxy hAxy
    · rw [if_neg hAxy]
      by_cases hAx : A x = true
      · have hAy : A y = false := by
          cases hAyc : A y with
          | true => exact absurd (hAx.trans hAyc.symm) hAxy
          | false => rfl
        exact spinSDot_apply_diag_neelConfigOfS_of_cross A N hAx hAy
      · have hAxF : A x = false := by
          cases hAxc : A x with
          | true => exact absurd hAxc hAx
          | false => rfl
        have hAy : A y = true := by
          cases hAyc : A y with
          | true => rfl
          | false => exact absurd (hAxF.trans hAyc.symm) hAxy
        rw [show (spinSDot x y N : ManyBodyOpS Λ N) = spinSDot y x N from
              spinSDot_comm x y N]
        exact spinSDot_apply_diag_neelConfigOfS_of_cross A N hAy hAxF

/-- State-level expectation of the spin-`S` Heisenberg Hamiltonian on
the Néel state: lifts `heisenbergHamiltonianS_apply_diag_neel` via
`basisVecS_expectation_eq_diagonal`. -/
theorem neelStateOfS_heisenbergHamiltonianS_expectation
    (J : Λ → Λ → ℂ) (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS A N))
        ((heisenbergHamiltonianS J N).mulVec (neelStateOfS A N)) =
      ∑ x : Λ, ∑ y : Λ,
        J x y *
          (if x = y then ((N : ℂ) * (N + 2) / 4)
           else if A x = A y then ((N : ℂ) * (N : ℂ) / 4)
           else -((N : ℂ) * (N : ℂ) / 4)) := by
  unfold neelStateOfS
  rw [basisVecS_expectation_eq_diagonal]
  exact heisenbergHamiltonianS_apply_diag_neel J A N

/-- The transverse total-spin Casimir expectation on the Néel state has
strictly positive real part when `Λ` is non-empty and `N ≥ 1`:

  `0 < Re <Φ_Néel | (Ŝ_tot^(1))² + (Ŝ_tot^(2))² | Φ_Néel>`,

since the value equals `|Λ|·N/2` which is a strictly positive real
number under those hypotheses. Together with `<(Ŝ_tot^(3))²>_Néel = M²`
(γ-4 step 155), this proves `<(Ŝ_tot)²>_Néel > M²` strictly: the Néel
state is spread across multiple `S_tot`-sectors, the foundational
input for Tasaki §2.5 Theorem 2.3's variational argument. -/
theorem neelStateOfS_totalSpinSOp12_sq_expectation_re_pos
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    0 < (dotProduct (star (neelStateOfS A N))
        ((totalSpinSOp1 Λ N * totalSpinSOp1 Λ N +
          totalSpinSOp2 Λ N * totalSpinSOp2 Λ N).mulVec
          (neelStateOfS A N))).re := by
  rw [neelStateOfS_totalSpinSOp12_sq_expectation]
  have hreal :
      (Fintype.card Λ : ℂ) * ((N : ℂ) / 2) =
        (((Fintype.card Λ : ℝ) * (N : ℝ) / 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [hreal, Complex.ofReal_re]
  refine div_pos (mul_pos ?_ ?_) two_pos
  · exact_mod_cast Fintype.card_pos
  · exact_mod_cast hN

/-- **Strict spread**: `Re <Φ_Néel | (Ŝ_tot^(3))² | Φ_Néel> < Re <Φ_Néel | (Ŝ_tot)² | Φ_Néel>`
when `Λ` is non-empty and `N ≥ 1`. The Néel state has a strictly larger
total-spin Casimir than its (Ŝ_tot^(3))²-eigenvalue, so it is **not**
concentrated in a single `S_tot`-sector. Combines γ-4 step 161
(transverse positivity) with the operator decomposition `(Ŝ_tot)² =
(Ŝ_tot^(1))² + (Ŝ_tot^(2))² + (Ŝ_tot^(3))²`. -/
theorem neelStateOfS_totalSpinSSquared_expectation_re_gt_OpZ_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    (dotProduct (star (neelStateOfS A N))
        ((totalSpinSOp3 Λ N * totalSpinSOp3 Λ N).mulVec
          (neelStateOfS A N))).re <
    (dotProduct (star (neelStateOfS A N))
        ((totalSpinSSquared Λ N).mulVec (neelStateOfS A N))).re := by
  have h12pos := neelStateOfS_totalSpinSOp12_sq_expectation_re_pos A N hN
  rw [show totalSpinSSquared Λ N =
        (totalSpinSOp1 Λ N * totalSpinSOp1 Λ N +
          totalSpinSOp2 Λ N * totalSpinSOp2 Λ N) +
          totalSpinSOp3 Λ N * totalSpinSOp3 Λ N from
      totalSpinSSquared_def Λ N]
  rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]
  linarith

/-- **Cross-only specialization** of the synthesis (γ-4 step 160): when
the coupling `J` vanishes on intra-sublattice pairs (`A x = A y →
J x y = 0`), the Heisenberg Néel diagonal collapses to a single closed
form, since the same-sublattice and self contributions are killed:

  `<Φ_Néel | H_J | Φ_Néel> = -(N²/4) · Σ_{x, y} J(x, y)`.

Applies to `bipartiteCoupling` via `bipartiteCoupling_eq_zero_of_same_sublattice`. -/
theorem heisenbergHamiltonianS_apply_diag_neel_of_cross_only
    (J : Λ → Λ → ℂ) (A : Λ → Bool) (N : ℕ)
    (hJ : ∀ x y, A x = A y → J x y = 0) :
    (heisenbergHamiltonianS J N) (neelConfigOfS A N) (neelConfigOfS A N) =
      -((N : ℂ) * (N : ℂ) / 4) * (∑ x : Λ, ∑ y : Λ, J x y) := by
  rw [heisenbergHamiltonianS_apply_diag_neel]
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

/-- State-level cross-only specialization (spin-S): for a coupling
vanishing on intra-sublattice pairs,
`<Φ_Néel | H_J | Φ_Néel> = -(N²/4) · Σ J(x,y)`. Lifts
`heisenbergHamiltonianS_apply_diag_neel_of_cross_only` via
`basisVecS_expectation_eq_diagonal`. -/
theorem neelStateOfS_heisenbergHamiltonianS_expectation_of_cross_only
    (J : Λ → Λ → ℂ) (A : Λ → Bool) (N : ℕ)
    (hJ : ∀ x y, A x = A y → J x y = 0) :
    dotProduct (star (neelStateOfS A N))
        ((heisenbergHamiltonianS J N).mulVec (neelStateOfS A N)) =
      -((N : ℂ) * (N : ℂ) / 4) * (∑ x : Λ, ∑ y : Λ, J x y) := by
  unfold neelStateOfS
  rw [basisVecS_expectation_eq_diagonal]
  exact heisenbergHamiltonianS_apply_diag_neel_of_cross_only J A N hJ

/-- **Toy Hamiltonian Néel expectation via cross-only synthesis** (spin-S):
`<Φ_Néel | Ĥ_toy_S A | Φ_Néel> = -(N²/4) · Σ bipartiteCoupling A x y =
-|A|·|¬A|·N²/2`. Direct application of γ-4 step 164 to
`heisenbergToyHamiltonianS = heisenbergHamiltonianS (bipartiteCoupling A)`,
combined with `bipartiteCoupling_sum = 2·|A|·|¬A|`. Reproduces
`neelStateOfS_heisenbergToyHamiltonianS_expectation` (γ-4 step 131) by an
independent route through the per-pair correlation trio. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_via_cross_only
    (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec (neelStateOfS A N)) =
      -(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          ((N : ℂ) * (N : ℂ)) / 2) := by
  unfold heisenbergToyHamiltonianS
  rw [neelStateOfS_heisenbergHamiltonianS_expectation_of_cross_only
        (bipartiteCoupling A) A N
        (fun x y h => bipartiteCoupling_eq_zero_of_same_sublattice A h)]
  rw [bipartiteCoupling_sum]
  ring

/-- **Heisenberg-on-graph diagonal Néel matrix element** under bipartite
alignment: when every edge of the SimpleGraph `G` crosses the
sublattice partition `(A, ¬A)`, the coupling `couplingOf G J` satisfies
the cross-only hypothesis, and the synthesis collapses to
`-(N²/4) · Σ couplingOf G J`. Spin-S generalization of the toy
expectation, applicable to any bipartite-aligned graph (e.g. a path
graph on a bipartite-coloured chain). -/
theorem heisenbergHamiltonianOnGraphS_apply_diag_neel_of_bipartite
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (J : ℂ) (A : Λ → Bool) (N : ℕ)
    (hG : ∀ x y, G.Adj x y → A x ≠ A y) :
    (heisenbergHamiltonianOnGraphS G J N) (neelConfigOfS A N) (neelConfigOfS A N) =
      -((N : ℂ) * (N : ℂ) / 4) *
        (∑ x : Λ, ∑ y : Λ, LatticeSystem.Lattice.couplingOf G J x y) := by
  unfold heisenbergHamiltonianOnGraphS
  refine heisenbergHamiltonianS_apply_diag_neel_of_cross_only _ A N ?_
  intros x y h
  unfold LatticeSystem.Lattice.couplingOf
  rw [if_neg (fun hAdj => hG x y hAdj h)]

/-- State-level Heisenberg-on-graph Néel expectation under bipartite
alignment: lifts `heisenbergHamiltonianOnGraphS_apply_diag_neel_of_bipartite`
via `basisVecS_expectation_eq_diagonal`. -/
theorem neelStateOfS_heisenbergHamiltonianOnGraphS_expectation_of_bipartite
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (J : ℂ) (A : Λ → Bool) (N : ℕ)
    (hG : ∀ x y, G.Adj x y → A x ≠ A y) :
    dotProduct (star (neelStateOfS A N))
        ((heisenbergHamiltonianOnGraphS G J N).mulVec (neelStateOfS A N)) =
      -((N : ℂ) * (N : ℂ) / 4) *
        (∑ x : Λ, ∑ y : Λ, LatticeSystem.Lattice.couplingOf G J x y) := by
  unfold neelStateOfS
  rw [basisVecS_expectation_eq_diagonal]
  exact heisenbergHamiltonianOnGraphS_apply_diag_neel_of_bipartite G J A N hG

/-- **Closed-form Heisenberg-on-graph Néel expectation under bipartite
alignment** (spin-S): `<Φ_Néel | H_G | Φ_Néel> = -J · #G.edgeFinset · N²/2`.
Combines γ-4 step 166 with `couplingOf_sum = J · 2 · #G.edgeFinset`
(γ-4 step 167) — the variational upper bound `E_GS ≤ -J·#edges·N²/2`
on the AFM Heisenberg ground-state energy when J > 0. -/
theorem neelStateOfS_heisenbergHamiltonianOnGraphS_expectation_of_bipartite_closed
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (J : ℂ) (A : Λ → Bool) (N : ℕ)
    (hG : ∀ x y, G.Adj x y → A x ≠ A y) :
    dotProduct (star (neelStateOfS A N))
        ((heisenbergHamiltonianOnGraphS G J N).mulVec (neelStateOfS A N)) =
      -(J * (G.edgeFinset.card : ℂ) * ((N : ℂ) * (N : ℂ)) / 2) := by
  rw [neelStateOfS_heisenbergHamiltonianOnGraphS_expectation_of_bipartite G J A N hG]
  rw [LatticeSystem.Lattice.couplingOf_sum]
  ring

/-- **Specialization to `bipartiteCompleteGraphOf A`**: the spin-S
Heisenberg-on-graph Néel expectation on the canonical complete bipartite
graph (every edge crosses sublattices, `Adj x y ↔ x ≠ y ∧ A x ≠ A y`).
Direct application of γ-4 step 166 via the existing
`bipartiteCompleteGraphOf_adj_sublattice_ne`. -/
theorem heisenbergHamiltonianOnGraphS_apply_diag_neel_bipartiteCompleteGraph
    (A : Λ → Bool) (J : ℂ) (N : ℕ) :
    (heisenbergHamiltonianOnGraphS (bipartiteCompleteGraphOf A) J N)
        (neelConfigOfS A N) (neelConfigOfS A N) =
      -((N : ℂ) * (N : ℂ) / 4) *
        (∑ x : Λ, ∑ y : Λ,
          LatticeSystem.Lattice.couplingOf (bipartiteCompleteGraphOf A) J x y) :=
  heisenbergHamiltonianOnGraphS_apply_diag_neel_of_bipartite
    (bipartiteCompleteGraphOf A) J A N
    (fun _ _ => bipartiteCompleteGraphOf_adj_sublattice_ne)

/-- State-level expectation specialization (spin-S): on the
`bipartiteCompleteGraphOf A`. -/
theorem neelStateOfS_heisenbergHamiltonianOnGraphS_expectation_bipartiteCompleteGraph
    (A : Λ → Bool) (J : ℂ) (N : ℕ) :
    dotProduct (star (neelStateOfS A N))
        ((heisenbergHamiltonianOnGraphS (bipartiteCompleteGraphOf A) J N).mulVec
          (neelStateOfS A N)) =
      -((N : ℂ) * (N : ℂ) / 4) *
        (∑ x : Λ, ∑ y : Λ,
          LatticeSystem.Lattice.couplingOf (bipartiteCompleteGraphOf A) J x y) :=
  neelStateOfS_heisenbergHamiltonianOnGraphS_expectation_of_bipartite
    (bipartiteCompleteGraphOf A) J A N
    (fun _ _ => bipartiteCompleteGraphOf_adj_sublattice_ne)

/-- **Edge count** of `bipartiteCompleteGraphOf A`: the number of edges
equals `|A| · |¬A|`. Each edge has one endpoint in `A` and one in `¬A`,
so the unordered count is the product of sublattice sizes. The proof
chains `couplingOf G 1 = bipartiteCoupling A` (pointwise),
`couplingOf_sum` (γ-4 step 167), and `bipartiteCoupling_sum`
(γ-4 step 165), giving `2 · #edges = 2 · |A| · |¬A|` in ℂ which casts
to ℕ and divides by 2 (γ-4 step 198). -/
theorem bipartiteCompleteGraphOf_edgeFinset_card (A : Λ → Bool) :
    (bipartiteCompleteGraphOf A).edgeFinset.card =
      (Finset.univ.filter (fun x : Λ => A x = true)).card *
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  classical
  have h_eq : ∀ x y : Λ,
      LatticeSystem.Lattice.couplingOf (bipartiteCompleteGraphOf A) (1 : ℂ) x y =
        bipartiteCoupling A x y := by
    intros x y
    unfold LatticeSystem.Lattice.couplingOf bipartiteCoupling
    by_cases hxy : x = y
    · subst hxy
      have h1 : ¬ (bipartiteCompleteGraphOf A).Adj x x :=
        (bipartiteCompleteGraphOf A).irrefl
      have h2 : ¬ A x ≠ A x := fun h => h rfl
      rw [if_neg h1, if_neg h2]
    · by_cases hA : A x ≠ A y
      · have hAdj : (bipartiteCompleteGraphOf A).Adj x y := ⟨hxy, hA⟩
        rw [if_pos hAdj, if_pos hA]
      · have hAeq : A x = A y := not_ne_iff.mp hA
        have hNotAdj : ¬ (bipartiteCompleteGraphOf A).Adj x y :=
          fun ⟨_, h⟩ => h hAeq
        rw [if_neg hNotAdj, if_neg (fun h => h hAeq)]
  have h_coupling :=
    LatticeSystem.Lattice.couplingOf_sum (bipartiteCompleteGraphOf A) (1 : ℂ)
  have h_sum_eq : ∑ x : Λ, ∑ y : Λ,
      LatticeSystem.Lattice.couplingOf (bipartiteCompleteGraphOf A) (1 : ℂ) x y =
      ∑ x : Λ, ∑ y : Λ, bipartiteCoupling A x y :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => h_eq x y
  rw [h_sum_eq, bipartiteCoupling_sum] at h_coupling
  have h_simp : (2 : ℂ) *
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) =
      (2 : ℂ) * ((bipartiteCompleteGraphOf A).edgeFinset.card : ℂ) := by
    linear_combination h_coupling
  have h_nat : (2 : ℕ) *
        ((Finset.univ.filter (fun x : Λ => A x = true)).card *
          (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) =
      (2 : ℕ) * (bipartiteCompleteGraphOf A).edgeFinset.card := by
    exact_mod_cast h_simp
  omega

/-- **Closed form**: Néel expectation on `bipartiteCompleteGraphOf A`
equals `-J · |A| · |¬A| · N²/2` (spin-S). Combines the
`bipartiteCompleteGraphOf` Néel expectation with the explicit edge count
`|A| · |¬A|` (γ-4 step 198) — third independent derivation of the toy
Hamiltonian Néel expectation, complementing γ-4 steps 131 and 165. -/
theorem neelStateOfS_heisenbergHamiltonianOnGraphS_expectation_bipartiteCompleteGraph_closed
    (A : Λ → Bool) (J : ℂ) (N : ℕ) :
    dotProduct (star (neelStateOfS A N))
        ((heisenbergHamiltonianOnGraphS (bipartiteCompleteGraphOf A) J N).mulVec
          (neelStateOfS A N)) =
      -(J * ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          ((N : ℂ) * (N : ℂ)) / 2) := by
  rw [neelStateOfS_heisenbergHamiltonianOnGraphS_expectation_of_bipartite_closed
        (bipartiteCompleteGraphOf A) J A N
        (fun _ _ => bipartiteCompleteGraphOf_adj_sublattice_ne)]
  rw [bipartiteCompleteGraphOf_edgeFinset_card]
  push_cast
  ring

/-- **Identification**: `heisenbergToyHamiltonianS A N =
heisenbergHamiltonianOnGraphS (bipartiteCompleteGraphOf A) 1 N`. The
toy Hamiltonian is exactly the Heisenberg Hamiltonian on the canonical
complete bipartite graph at unit coupling, since `bipartiteCoupling A x y
= couplingOf (bipartiteCompleteGraphOf A) 1 x y` pointwise (γ-4 step 199). -/
theorem heisenbergToyHamiltonianS_eq_heisenbergHamiltonianOnGraphS_bipartiteCompleteGraph
    (A : Λ → Bool) (N : ℕ) :
    heisenbergToyHamiltonianS (Λ := Λ) A N =
      heisenbergHamiltonianOnGraphS (bipartiteCompleteGraphOf A) (1 : ℂ) N := by
  unfold heisenbergToyHamiltonianS heisenbergHamiltonianOnGraphS
  congr 1
  funext x y
  unfold LatticeSystem.Lattice.couplingOf bipartiteCoupling
  by_cases hxy : x = y
  · subst hxy
    have h1 : ¬ (bipartiteCompleteGraphOf A).Adj x x :=
      (bipartiteCompleteGraphOf A).irrefl
    have h2 : ¬ A x ≠ A x := fun h => h rfl
    rw [if_neg h1, if_neg h2]
  · by_cases hA : A x ≠ A y
    · have hAdj : (bipartiteCompleteGraphOf A).Adj x y := ⟨hxy, hA⟩
      rw [if_pos hAdj, if_pos hA]
    · have hAeq : A x = A y := not_ne_iff.mp hA
      have hNotAdj : ¬ (bipartiteCompleteGraphOf A).Adj x y :=
        fun ⟨_, h⟩ => h hAeq
      rw [if_neg hNotAdj, if_neg (fun h => h hAeq)]

/-- **Strict negativity in ℝ** of the AFM Heisenberg-on-graph Néel
expectation: when `J = (J_re : ℂ)` is a strictly-positive real, every
edge of `G` crosses the bipartition, `0 < #G.edgeFinset`, and `0 < N`,
the Néel-trial expectation has strictly negative real part. Combined
with the variational principle (separately), this gives the AFM
ground-state energy upper bound `Re E_GS ≤ -J·#edges·N²/2 < 0`. -/
theorem neelStateOfS_heisenbergHamiltonianOnGraphS_expectation_of_bipartite_re_neg
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (A : Λ → Bool) (N : ℕ)
    {J_re : ℝ} (hJ : 0 < J_re)
    (hG : ∀ x y, G.Adj x y → A x ≠ A y)
    (hE : 0 < G.edgeFinset.card) (hN : 0 < N) :
    (dotProduct (star (neelStateOfS A N))
        ((heisenbergHamiltonianOnGraphS G (J_re : ℂ) N).mulVec
          (neelStateOfS A N))).re < 0 := by
  rw [neelStateOfS_heisenbergHamiltonianOnGraphS_expectation_of_bipartite_closed
        G (J_re : ℂ) A N hG]
  have hreal :
      -((J_re : ℂ) * (G.edgeFinset.card : ℂ) * ((N : ℂ) * (N : ℂ)) / 2) =
        ((-(J_re * (G.edgeFinset.card : ℝ) * ((N : ℝ) * (N : ℝ)) / 2) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hreal, Complex.ofReal_re]
  refine neg_neg_iff_pos.mpr (div_pos (mul_pos (mul_pos hJ ?_) ?_) two_pos)
  · exact_mod_cast hE
  · refine mul_pos ?_ ?_ <;> exact_mod_cast hN

/-- **Strict negativity in ℝ** of the Néel expectation on
`bipartiteCompleteGraphOf A` for real positive coupling, both
sublattices non-empty, and `0 < N`. Specializes γ-4 step 168 using
γ-4 step 198's edge count `|A|·|¬A| > 0` (γ-4 step 200). -/
theorem neelStateOfS_heisenbergHamiltonianOnGraphS_expectation_bipartiteCompleteGraph_re_neg
    (A : Λ → Bool) (N : ℕ) {J_re : ℝ} (hJ : 0 < J_re)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N) :
    (dotProduct (star (neelStateOfS A N))
        ((heisenbergHamiltonianOnGraphS (bipartiteCompleteGraphOf A)
          (J_re : ℂ) N).mulVec (neelStateOfS A N))).re < 0 := by
  refine neelStateOfS_heisenbergHamiltonianOnGraphS_expectation_of_bipartite_re_neg
    (bipartiteCompleteGraphOf A) A N hJ
    (fun _ _ => bipartiteCompleteGraphOf_adj_sublattice_ne) ?_ hN
  rw [bipartiteCompleteGraphOf_edgeFinset_card]
  exact Nat.mul_pos hA hAc

/-- **Real-valued positivity** of the toy Hamiltonian variational gap:
`0 < Re (<Φ_⊤|Ĥ_toy|Φ_⊤> - <Φ_Néel|Ĥ_toy|Φ_Néel>) = |A|·|¬A|·N²` when
both sublattices are non-empty and `N ≥ 1`. The all-up state has strictly
higher toy-Hamiltonian expectation than the Néel state, witnessing the
variational separation that underpins Tasaki §2.5 Theorem 2.3. -/
theorem heisenbergToyHamiltonianS_variational_gap_re_pos
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N) :
    0 < (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
      dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec (neelStateOfS A N))).re := by
  rw [heisenbergToyHamiltonianS_variational_gap]
  have hreal :
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          ((N : ℂ) * (N : ℂ)) =
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
          ((N : ℝ) * (N : ℝ)) : ℝ) := by
    push_cast; ring
  rw [hreal, Complex.ofReal_re]
  refine mul_pos (mul_pos ?_ ?_) (mul_pos ?_ ?_)
  · exact_mod_cast hA
  · exact_mod_cast hAc
  · exact_mod_cast hN
  · exact_mod_cast hN

end LatticeSystem.Quantum
