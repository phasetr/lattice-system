import LatticeSystem.Quantum.MarshallLiebMattis.SublatticeSpinDot
import LatticeSystem.Quantum.MarshallLiebMattis.SublatticeSpinLadderProperties
import LatticeSystem.Quantum.MarshallLiebMattis.ToyHamiltonianCasimir
import LatticeSystem.Quantum.NeelState
import LatticeSystem.Quantum.MagnetizationSubspace

/-!
# Sublattice Casimir eigenvalues on the Néel state

**Build-speed evaluation history**:
- **Refactor #45 (PR #2961, evaluate-only)**: noted 1294 lines,
  ~5.2s incremental, ~12 min from clean. Identified magnetization
  subspace section as cleanest split candidate.
- **Refactor #46 (PR #2982)**: actual split — extracted 8 magnetization
  theorems (lines 1208-1294) into companion
  `SublatticeCasimirNeelMagnetization.lean`. Parent 1308→1222 lines.
  Incremental build time 5.2s → 3.77s (**~28% speedup**).
- **Refactor #47 (PR #3002, evaluate-only)**: confirmed 3.77s
  post-#46 baseline. Next split candidate: orthogonality with basis
  vectors (lines 992-1206, ~215 lines) → potential
  `SublatticeCasimirNeelOrthogonality.lean` companion. Deferred this
  cadence to avoid coupling with the 20-PR predicted-min-energy /
  predictedSymm bridge sweep (#2962-#3001).
- **Refactor #48 (PR #3023, evaluate-only)**: post-#3022 measurement.
  File 1222 → 1223 lines (one line drift), incremental rebuild
  **3.6s wall** (1.7s user + 2.5s system, 116% CPU). Below the ~5s
  threshold; no urgent need to split. The 20-PR predicted-min-energy
  sweep (#3003-#3022) added 20 small files (each 30-90 lines) in
  `Quantum/SpinS/BipartiteToyMinEnergyPredicted*.lean` without
  touching this file. Peer measurements (incremental rebuild):
    - `SublatticeSpin.lean` (1074 lines): 3.35s.
    - `SingleClusterHamiltonian.lean` (779 lines): 12s — known
      heavy theorem, already split via refactor #25's companion
      file. No further split planned this cadence.
  Conclusion: build-speed remains healthy; deferring orthogonality
  split to a later refactor when it would yield ≥10% improvement.
- **Refactor #49 (PR #3044, evaluate-only)**: post-#3043 measurement.
  File 1236 lines, incremental rebuild **7.6s wall** (1.8s user +
  3.4s system, 68% CPU). The system-time fraction has grown; the
  wall time is approaching the ~5s evaluation threshold. The 20-PR
  orientation-sandwich sweep (#3024-#3043) added 20 small files in
  `Quantum/SpinS/BipartiteToyMinEnergyPredicted*.lean` (each 35-75
  lines) without touching this file directly. Peer measurements
  unchanged. Orthogonality section (~215 lines) remains the most
  promising future split candidate; current 7.6s is still below the
  ~10s threshold for forced action. Deferring to refactor #50.
- **Refactor #50 (PR #3065)**: actual split. Pre-split: 1246 lines,
  **13.7s wall** (8.0s user + 5.3s system, 96% CPU) — past the
  ~10s forced-split threshold (up from 7.6s at #49 due to the
  PRs #3045-#3064 sweep importing this file more often via the
  Néel bridges). Extracted 13 theorems (basisVec orthogonality +
  distinctness + inner-self) into companion
  `SublatticeCasimirNeelBasisOrthogonality.lean`. Post-split parent
  1246 → 1030 lines, **3.2s wall** — **77% speedup**. Clean cut:
  the extracted block is downstream of `heisenbergToyHamiltonian_expectation`
  (last theorem retained) with no upstream-into-parent dependencies.
- **Refactor #51 (PR #3086, evaluate-only)**: post-#3085 measurement.
  Parent 1030 lines, incremental rebuild **4.1s wall** (1.8s user +
  2.8s system, 111% CPU). Slight uptick from 3.2s at refactor #50
  due to the PRs #3066-#3085 sweep (20 PRs adding orientation-pair
  iffs + strict negativity iffs + degeneracy iffs) growing the
  import surface, but still well below the ~5s evaluation threshold
  and far below the ~10s forced-split threshold. No split needed
  this cadence; the next candidate region (Casimir cross-terms,
  lines ~535-720, ~185 lines) is structurally tightly coupled and
  would not yield a clean cut yet.
- **Refactor #52 (PR #3107, evaluate-only)**: post-#3106 measurement.
  Parent 1040 lines (10-line history additions from #51), incremental
  rebuild **8.4s wall** (2.1s user + 4.1s system, 73% CPU). Another
  uptick from 4.1s due to PRs #3087-#3106's 20-PR sweep of
  unconditional `= 0` iffs + Néel-bridge iff completions adding new
  import dependencies through this file. Approaching ~10s threshold
  but still below. Next refactor cycle should consider an actual
  split if the trajectory continues; current target remains the
  Casimir cross-term block.
- **Refactor #53 (PR #3128, evaluate-only)**: post-#3127 measurement.
  Parent 1059 lines (19 lines drift since #52), incremental rebuild
  **18.0s wall** (7.3s user + 6.6s system, 77% CPU) — **past the
  ~10s forced-split threshold**. The PRs #3108-#3127 sweep
  (unconditional Néel-bridge iffs, sublattice-swap symmetries,
  ‖biw‖-form theorems) didn't touch this file directly, but their
  import surface continued growing the transitive cost.
  Next refactor cycle MUST do an actual split. Target:
  Néel-expectation block (lines ~815-1029, ~215 lines covering
  sublattice spin operator expectations + cross-terms + total spin
  squared expectations + Heisenberg toy expectation). Deferring this
  cadence to gather more measurement data before committing to a
  specific cut.

The graph-centric Néel state `Φ_Néel(A) := basisVec (neelConfigOf A)`
on a bipartite graph `(Λ, A)` (Tasaki §2.5 eq. (2.5.2)) sets
`σ x = 0` for `A x = true` and `σ x = 1` for `A x = false` — it is
**constant on each sublattice**.

By the constant-on-`A` Casimir eigenvalue formula
(`sublatticeSpinHalfSquared_mulVec_basisVec_of_const_on`), the Néel
state is simultaneously an eigenvector of both sublattice Casimirs
`(Ŝ_A)²` and `(Ŝ_¬A)²` at their respective maximum-spin eigenvalues:

  `(Ŝ_A)² · |Φ_Néel(A)⟩ = (|A|(|A|+2)/4) · |Φ_Néel(A)⟩`,
  `(Ŝ_¬A)² · |Φ_Néel(A)⟩ = (|¬A|(|¬A|+2)/4) · |Φ_Néel(A)⟩`.

Combined with the Casimir identity
`(Ŝ_tot)² = (Ŝ_A)² + 2 (Ŝ_A · Ŝ_¬A) + (Ŝ_¬A)²` and the closed form
`Ĥ_toy = (Ŝ_tot)² − (Ŝ_A)² − (Ŝ_¬A)²`, this is a key ingredient in
Tasaki's analysis of the toy Hamiltonian's ground state in §2.5.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 eqs. (2.5.2)–(2.5.11).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- `(Ŝ_A)² · |Φ_Néel(A)⟩ = (|A|(|A|+2)/4) · |Φ_Néel(A)⟩`.
The Néel state is an eigenvector of the `A`-sublattice Casimir
with maximum-spin eigenvalue, since `neelConfigOf A` is `0` on `A`. -/
theorem sublatticeSpinHalfSquared_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfSquared A).mulVec (neelStateOf A) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => A x = true)).card + 2) / 4) •
        neelStateOf A := by
  unfold neelStateOf
  refine sublatticeSpinHalfSquared_mulVec_basisVec_of_const_on A (s := 0) ?_
  intro x hAx
  unfold neelConfigOf
  rw [if_pos hAx]

/-- `(Ŝ_¬A)² · |Φ_Néel(A)⟩ = (|¬A|(|¬A|+2)/4) · |Φ_Néel(A)⟩`.
The Néel state is an eigenvector of the `¬A`-sublattice Casimir
with maximum-spin eigenvalue, since `neelConfigOf A` is `1` on `¬A`. -/
theorem sublatticeSpinHalfSquared_complement_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfSquared (fun x => ! A x)).mulVec (neelStateOf A) =
      (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card + 2) / 4) •
        neelStateOf A := by
  unfold neelStateOf
  refine sublatticeSpinHalfSquared_mulVec_basisVec_of_const_on
    (fun x => ! A x) (s := 1) ?_
  intro x hnAx
  -- `(! A x) = true ↔ A x = false`
  have hAxF : A x = false := by
    cases h : A x
    · rfl
    · simp [h] at hnAx
  unfold neelConfigOf
  rw [if_neg (by rw [hAxF]; decide : ¬ (A x = true))]

/-! ## Toy Hamiltonian Néel diagonal -/

/-- Diagonal matrix element of the spin-`1/2` two-site dot product
`Ŝ_x · Ŝ_y` at an antiparallel configuration:
`(Ŝ_x · Ŝ_y) σ σ = -1/4` when `σ x ≠ σ y` (and `x ≠ y`).

Spin-`1/2` analog of `spinSDot_apply_diag_of_ne` (spin-`S` version
`m_x · m_y = (1/2)(-1/2) = -1/4`). Extracted from
`spinHalfDot_mulVec_basisVec_antiparallel` by evaluating both sides
at `σ`. -/
theorem spinHalfDot_apply_diag_of_ne_antiparallel
    {x y : Λ} (hxy : x ≠ y) (σ : Λ → Fin 2) (h : σ x ≠ σ y) :
    (spinHalfDot x y : ManyBodyOp Λ) σ σ = -(1 / 4 : ℂ) := by
  have hmulVec := spinHalfDot_mulVec_basisVec_antiparallel hxy σ h
  -- Evaluate both sides at σ.
  have heval := congrArg (fun v => v σ) hmulVec
  simp only at heval
  -- LHS = (spinHalfDot x y) σ σ via mulVec definition.
  have hLHS : ((spinHalfDot x y).mulVec (basisVec σ)) σ =
      (spinHalfDot x y : ManyBodyOp Λ) σ σ := by
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single σ]
    · rw [basisVec_self, mul_one]
    · intros τ _ hτ
      rw [basisVec_of_ne hτ, mul_zero]
    · intro h; exact (h (Finset.mem_univ _)).elim
  -- RHS: (1/2) basisVec (basisSwap σ x y) σ - (1/4) basisVec σ σ.
  have hRHS : ((1 / 2 : ℂ) • basisVec (basisSwap σ x y) -
      (1 / 4 : ℂ) • basisVec σ) σ = -(1 / 4 : ℂ) := by
    rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply]
    rw [basisVec_self]
    -- basisSwap σ x y ≠ σ since σ_x ≠ σ_y.
    have hswap_ne : basisSwap σ x y ≠ σ := by
      intro heq
      have hx : basisSwap σ x y x = σ x := congr_fun heq x
      unfold basisSwap at hx
      rw [Function.update_of_ne hxy] at hx
      rw [Function.update_self] at hx
      exact h hx.symm
    rw [basisVec_of_ne (Ne.symm hswap_ne)]
    simp
  rw [hLHS] at heval
  rw [heval, hRHS]

/-- Diagonal matrix element of the spin-`1/2` two-site dot product
`Ŝ_x · Ŝ_y` at a parallel configuration:
`(Ŝ_x · Ŝ_y) σ σ = +1/4` when `σ x = σ y` (and `x ≠ y`).

Parallel counterpart of `spinHalfDot_apply_diag_of_ne_antiparallel`:
the eigenvector property `spinHalfDot_mulVec_basisVec_parallel`
(`(Ŝ_x · Ŝ_y) · |σ⟩ = (1/4) · |σ⟩`) evaluated at `σ` reads off the
diagonal. -/
theorem spinHalfDot_apply_diag_of_ne_parallel
    {x y : Λ} (hxy : x ≠ y) (σ : Λ → Fin 2) (h : σ x = σ y) :
    (spinHalfDot x y : ManyBodyOp Λ) σ σ = (1 / 4 : ℂ) := by
  have hmulVec := spinHalfDot_mulVec_basisVec_parallel hxy σ h
  have heval := congrArg (fun v => v σ) hmulVec
  simp only at heval
  have hLHS : ((spinHalfDot x y).mulVec (basisVec σ)) σ =
      (spinHalfDot x y : ManyBodyOp Λ) σ σ := by
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single σ]
    · rw [basisVec_self, mul_one]
    · intros τ _ hτ
      rw [basisVec_of_ne hτ, mul_zero]
    · intro hempty; exact (hempty (Finset.mem_univ _)).elim
  have hRHS : ((1 / 4 : ℂ) • basisVec σ) σ = (1 / 4 : ℂ) := by
    rw [Pi.smul_apply, basisVec_self, smul_eq_mul, mul_one]
  rw [hLHS] at heval
  rw [heval, hRHS]

/-- Diagonal of the spin-`1/2` toy Hamiltonian on the Néel
configuration:

  `(Ĥ_toy A) (neelConfigOf A) (neelConfigOf A) = -|A|·|¬A|/2`.

Spin-`1/2` (`N=1`) specialisation of the spin-`S` formula
`-|A|·|¬A|·N²/2` (PR #1070). Negative of the all-up state eigenvalue
(PR α-6m's specialisation), demonstrating the variational separation
that underpins the AFM ground-state argument. -/
theorem heisenbergToyHamiltonian_apply_diag_neel (A : Λ → Bool) :
    (heisenbergToyHamiltonian A : ManyBodyOp Λ) (neelConfigOf A)
        (neelConfigOf A) =
      - (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) / 2) := by
  rw [heisenbergToyHamiltonian_eq_two_sublatticeSpinDot]
  rw [Matrix.smul_apply, sublatticeSpinDot_eq_sum_sum]
  rw [smul_eq_mul]
  -- Apply the bilinear sum at (neel, neel).
  rw [show (∑ x : Λ, ∑ y : Λ,
        if A x ∧ (fun z : Λ => ! A z) y = true then spinHalfDot x y else 0)
        (neelConfigOf A) (neelConfigOf A) =
      ∑ x : Λ, ∑ y : Λ,
        ((if A x ∧ (! A y) = true then spinHalfDot x y else 0)
          (neelConfigOf A) (neelConfigOf A)) from by
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.sum_apply]]
  have hterm : ∀ x y : Λ,
      ((if A x ∧ (! A y) = true then spinHalfDot x y else 0)
          (neelConfigOf A) (neelConfigOf A) : ℂ) =
      if A x ∧ (! A y) = true then -(1 / 4 : ℂ) else 0 := by
    intro x y
    by_cases hAB : A x ∧ (! A y) = true
    · obtain ⟨hAx, hAy⟩ := hAB
      rw [if_pos ⟨hAx, hAy⟩, if_pos ⟨hAx, hAy⟩]
      have hxy : x ≠ y := by
        intro heq
        subst heq
        rw [hAx] at hAy
        simp at hAy
      -- σ x ≠ σ y at the Néel config.
      have hAyF : A y = false := by
        cases h : A y
        · rfl
        · simp [h] at hAy
      have hne : neelConfigOf A x ≠ neelConfigOf A y := by
        unfold neelConfigOf
        rw [if_pos hAx, if_neg (by rw [hAyF]; decide : ¬ A y = true)]
        decide
      exact spinHalfDot_apply_diag_of_ne_antiparallel hxy _ hne
    · rw [if_neg hAB, if_neg hAB]
      rfl
  simp_rw [hterm]
  -- Sum: |A| · |¬A| · (-1/4).
  have hindicator_outer : ∀ (x : Λ) (C : ℂ),
      (∑ y : Λ, if A x ∧ (! A y) = true then C else 0) =
        if A x then ((Finset.univ.filter (fun y : Λ => (! A y) = true)).card : ℂ) * C
        else 0 := by
    intro x C
    by_cases hAx : A x = true
    · rw [if_pos hAx]
      classical
      rw [show (∑ y : Λ, if A x ∧ (! A y) = true then C else 0) =
          ∑ y : Λ, if (! A y) = true then C else 0 from by
            refine Finset.sum_congr rfl fun y _ => ?_
            by_cases hAy : (! A y) = true
            · rw [if_pos ⟨hAx, hAy⟩, if_pos hAy]
            · rw [if_neg, if_neg hAy]
              rintro ⟨_, h⟩; exact hAy h]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    · rw [if_neg hAx]
      apply Finset.sum_eq_zero
      intro y _
      rw [if_neg]
      rintro ⟨h, _⟩; exact hAx h
  simp_rw [hindicator_outer]
  classical
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

/-! ## Magnetization on the Néel state -/

/-- `magnetization Λ (neelConfigOf A) = |A| − |¬A|`: the Néel
configuration contributes `+1` on `A` (since `σ x = 0`) and `-1` on
`¬A` (since `σ x = 1`).

Spin-`1/2` specialisation of `magSumS_neelConfigOfS` (PR #1068). -/
theorem magnetization_neelConfigOf (A : Λ → Bool) :
    magnetization Λ (neelConfigOf A) =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℤ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℤ) := by
  unfold magnetization neelConfigOf
  classical
  -- Each term: spinSign(if A x then 0 else 1) = if A x then 1 else -1.
  have hterm : ∀ x : Λ,
      spinSign (if A x then (0 : Fin 2) else 1) =
        if A x = true then (1 : ℤ) else -1 := by
    intro x
    by_cases hAx : A x = true
    · rw [if_pos hAx, if_pos hAx]; simp [spinSign]
    · cases h : A x
      · rw [if_neg, if_neg]
        · simp [spinSign]
        · simp [h]
        · simp [h]
      · exact absurd h hAx
  simp_rw [hterm]
  have hsplit : ∀ x : Λ, (if A x = true then (1 : ℤ) else -1) =
      (if A x = true then (1 : ℤ) else 0) +
        (if (! A x) = true then (-1 : ℤ) else 0) := by
    intro x
    by_cases hAx : A x = true
    · rw [if_pos hAx, if_pos hAx]
      have : (! A x) = false := by simp [hAx]
      rw [if_neg]
      · ring
      · simp [this]
    · cases h : A x
      · simp
      · exact absurd h hAx
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_filter, Finset.sum_const]
  rw [← Finset.sum_filter, Finset.sum_const]
  push_cast
  ring

/-- **Sublattice-swap symmetry** of the spin-`1/2` Néel magnetization:
`magnetization Λ (neelConfigOf (¬A)) = |¬A| - |A|`. Spin-`1/2` mirror of
γ-4 step 169: the complement Néel sits in the opposite magnetization
sector. -/
theorem magnetization_neelConfigOf_complement (A : Λ → Bool) :
    magnetization Λ (neelConfigOf (fun x : Λ => ! A x)) =
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℤ) -
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℤ) := by
  rw [magnetization_neelConfigOf]
  simp [Bool.not_not]

/-- The spin-`1/2` Néel configuration `neelConfigOf A` is distinct from
its sublattice-complement `neelConfigOf (¬A)` (as functions `Λ → Fin 2`)
when `Λ` is non-empty: at any vertex `x` the swap exchanges `0 ↔ 1`,
witnessing the inequality. Spin-`1/2` mirror of γ-4 step 171's
distinctness witness. -/
theorem neelConfigOf_ne_complement [Nonempty Λ] (A : Λ → Bool) :
    neelConfigOf A ≠ neelConfigOf (fun x : Λ => ! A x) := by
  obtain ⟨x⟩ := ‹Nonempty Λ›
  intro h
  have hx := congr_fun h x
  unfold neelConfigOf at hx
  by_cases hAx : A x = true
  · rw [if_pos hAx] at hx
    have hnAxF : (! A x) = false := by simp [hAx]
    rw [if_neg (by rw [hnAxF]; decide : ¬ ((! A x) = true))] at hx
    exact (by decide : (0 : Fin 2) ≠ 1) hx
  · have hAxF : A x = false := by
      cases h' : A x with
      | true => exact absurd h' hAx
      | false => rfl
    rw [if_neg hAx] at hx
    have hnAx : (! A x) = true := by simp [hAxF]
    rw [if_pos hnAx] at hx
    exact (by decide : (1 : Fin 2) ≠ 0) hx

/-- **Néel-complement orthogonality** (spin-`1/2`):
`<Φ_Néel(A) | Φ_Néel(¬A)> = 0` when `Λ` is non-empty. Spin-`1/2`
mirror of γ-4 step 171: the two Néel basis vectors are orthogonal
because they are basis vectors of distinct configurations. -/
theorem neelStateOf_complement_orthogonal
    [Nonempty Λ] (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        (neelStateOf (fun x : Λ => ! A x)) = 0 := by
  unfold neelStateOf dotProduct
  apply Finset.sum_eq_zero
  intros τ _
  by_cases h1 : τ = neelConfigOf A
  · rw [h1]
    have hne : neelConfigOf A ≠ neelConfigOf (fun x : Λ => ! A x) :=
      neelConfigOf_ne_complement A
    simp [Pi.star_apply, basisVec_self, basisVec_of_ne hne]
  · simp [Pi.star_apply, basisVec_of_ne h1]

/-- `Ŝ_tot^(3) · |Φ_Néel⟩ = ((|A| − |¬A|)/2) · |Φ_Néel⟩`. The spin-`1/2`
Néel state is a `Ŝ_tot^(3)`-eigenvector with magnetization
`(|A| − |¬A|)/2`. For `|A| = |¬A|` the magnetization is zero (e.g.,
chain / square / cube); for `|A| ≠ |¬A|` (the Tasaki Theorem 2.3 case),
the absolute value `||A| − |¬A||/2 = ||A| − |¬A||·S` matches the
conjectured ground-state total spin.

Spin-`1/2` specialisation of `totalSpinSOp3_mulVec_neelStateOfS` (PR #1068). -/
theorem totalSpinHalfOp3_mulVec_neelStateOf (A : Λ → Bool) :
    (totalSpinHalfOp3 Λ).mulVec (neelStateOf A) =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) / 2) •
        neelStateOf A := by
  unfold neelStateOf
  rw [totalSpinHalfOp3_mulVec_basisVec_eq_magnetization]
  rw [magnetization_neelConfigOf]
  push_cast
  ring_nf

/-! ## Ladder annihilation of the Néel state -/

/-- `Ŝ_A^+ · |Φ_Néel⟩ = 0` (highest weight on A). Spin-`1/2` mirror of γ-4 step 65. -/
theorem sublatticeSpinHalfOpPlus_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfOpPlus A).mulVec (neelStateOf A) = 0 := by
  unfold neelStateOf
  refine sublatticeSpinHalfOpPlus_mulVec_basisVec_zero_on A ?_
  intro x hAx
  unfold neelConfigOf
  rw [if_pos hAx]

/-- `Ŝ_¬A^- · |Φ_Néel⟩ = 0` (lowest weight on ¬A). -/
theorem sublatticeSpinHalfOpMinus_complement_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfOpMinus (fun x => ! A x)).mulVec (neelStateOf A) = 0 := by
  unfold neelStateOf
  refine sublatticeSpinHalfOpMinus_mulVec_basisVec_one_on (fun x => ! A x) ?_
  intro x hnAx
  have hAxF : A x = false := by
    cases h : A x
    · rfl
    · simp [h] at hnAx
  unfold neelConfigOf
  rw [if_neg (by rw [hAxF]; decide : ¬ (A x = true))]

/-- On the spin-`1/2` Néel state: `Ŝ_tot^+ · |Φ_Néel⟩ = Ŝ_¬A^+ · |Φ_Néel⟩`.
Spin-`1/2` mirror of γ-4 step 67. -/
theorem totalSpinHalfOpPlus_mulVec_neelStateOf_eq_complement (A : Λ → Bool) :
    (totalSpinHalfOpPlus Λ).mulVec (neelStateOf A) =
      (sublatticeSpinHalfOpPlus (fun x => ! A x)).mulVec (neelStateOf A) := by
  rw [totalSpinHalfOpPlus_eq_sublattice_sum A]
  rw [Matrix.add_mulVec]
  rw [sublatticeSpinHalfOpPlus_mulVec_neelStateOf A]
  rw [zero_add]

/-- On the spin-`1/2` Néel state: `Ŝ_tot^- · |Φ_Néel⟩ = Ŝ_A^- · |Φ_Néel⟩`. -/
theorem totalSpinHalfOpMinus_mulVec_neelStateOf_eq_A (A : Λ → Bool) :
    (totalSpinHalfOpMinus Λ).mulVec (neelStateOf A) =
      (sublatticeSpinHalfOpMinus A).mulVec (neelStateOf A) := by
  rw [totalSpinHalfOpMinus_eq_sublattice_sum A]
  rw [Matrix.add_mulVec]
  rw [sublatticeSpinHalfOpMinus_complement_mulVec_neelStateOf A]
  rw [add_zero]

/-- `Ŝ_A^(3) · |Φ_Néel⟩ = (|A|/2) · |Φ_Néel⟩`. The sublattice z-axis acts
as `|A|/2` on the spin-`1/2` Néel state (highest weight on A:
`neelConfigOf A x = 0` for `x ∈ A`, contributing `+1/2`). Spin-`1/2`
mirror of γ-4 step 73 (`sublatticeSpinSOp3_mulVec_neelStateOfS`). -/
theorem sublatticeSpinHalfOp3_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfOp3 A).mulVec (neelStateOf A) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) / 2) •
        neelStateOf A := by
  unfold sublatticeSpinHalfOp3 neelStateOf
  rw [Matrix.sum_mulVec]
  rw [show (∑ x : Λ, (if A x then onSite x spinHalfOp3 else 0 : ManyBodyOp Λ).mulVec
        (basisVec (neelConfigOf A))) =
      ∑ x : Λ, (if A x then ((1 : ℂ) / 2) else 0) •
        basisVec (neelConfigOf A) from by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hA : A x = true
    · rw [if_pos hA, if_pos hA]
      rw [onSite_spinHalfOp3_mulVec_basisVec]
      have hσx : neelConfigOf A x = 0 := by
        unfold neelConfigOf; rw [if_pos hA]
      rw [hσx]
      rfl
    · cases h : A x
      · rw [if_neg, if_neg]
        · rw [Matrix.zero_mulVec, zero_smul]
        · simp
        · simp
      · exact absurd h hA]
  rw [← Finset.sum_smul]
  congr 1
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

/-- `Ŝ_¬A^(3) · |Φ_Néel⟩ = -(|¬A|/2) · |Φ_Néel⟩`. The complement sublattice
z-axis acts as `-|¬A|/2` on the spin-`1/2` Néel state (lowest weight on
¬A: `neelConfigOf A x = 1` for `x ∉ A`, contributing `-1/2`). Spin-`1/2`
mirror of γ-4 step 74 (`sublatticeSpinSOp3_complement_mulVec_neelStateOfS`). -/
theorem sublatticeSpinHalfOp3_complement_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfOp3 (fun x => ! A x)).mulVec (neelStateOf A) =
      (-(((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) / 2)) •
        neelStateOf A := by
  unfold sublatticeSpinHalfOp3 neelStateOf
  rw [Matrix.sum_mulVec]
  rw [show (∑ x : Λ, (if (! A x) then onSite x spinHalfOp3 else 0 : ManyBodyOp Λ).mulVec
        (basisVec (neelConfigOf A))) =
      ∑ x : Λ, (if (! A x) then -((1 : ℂ) / 2) else 0) •
        basisVec (neelConfigOf A) from by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hA : (! A x) = true
    · rw [if_pos hA, if_pos hA]
      rw [onSite_spinHalfOp3_mulVec_basisVec]
      have hAxF : A x = false := by
        cases h : A x
        · rfl
        · simp [h] at hA
      have hσx : neelConfigOf A x = 1 := by
        unfold neelConfigOf
        rw [if_neg (by rw [hAxF]; decide : ¬ A x = true)]
      rw [hσx]
      rfl
    · cases h : (! A x)
      · rw [if_neg, if_neg]
        · rw [Matrix.zero_mulVec, zero_smul]
        · simp
        · simp
      · exact absurd h hA]
  rw [← Finset.sum_smul]
  congr 1
  have hrw : ∀ x : Λ, (if (! A x) = true then -((1 : ℂ) / 2) else 0) =
      -(if (! A x) = true then ((1 : ℂ) / 2) else 0) := by
    intro x
    by_cases h : (! A x) = true
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, neg_zero]
  rw [Finset.sum_congr rfl (fun x _ => hrw x)]
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

/-- `(Ŝ_A^(3))² · |Φ_Néel⟩ = (|A|/2)² · |Φ_Néel⟩`. Square of γ-4 step 75.
Spin-`1/2` mirror of γ-4 step 77. -/
theorem sublatticeSpinHalfOp3_sq_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp3 A).mulVec (neelStateOf A) =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) / 2) ^ 2) •
        neelStateOf A := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOp3_mulVec_neelStateOf]
  rw [Matrix.mulVec_smul]
  rw [sublatticeSpinHalfOp3_mulVec_neelStateOf]
  rw [smul_smul]
  congr 1
  ring

/-- `(Ŝ_¬A^(3))² · |Φ_Néel⟩ = (|¬A|/2)² · |Φ_Néel⟩`. Square of γ-4 step 76.
Spin-`1/2` mirror of γ-4 step 77 complement. -/
theorem sublatticeSpinHalfOp3_complement_sq_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfOp3 (fun x => ! A x) *
        sublatticeSpinHalfOp3 (fun x => ! A x)).mulVec (neelStateOf A) =
      ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) / 2) ^ 2) •
        neelStateOf A := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOp3_complement_mulVec_neelStateOf]
  rw [Matrix.mulVec_smul]
  rw [sublatticeSpinHalfOp3_complement_mulVec_neelStateOf]
  rw [smul_smul]
  congr 1
  ring

/-- `Ŝ_A^(3) · Ŝ_¬A^(3) · |Φ_Néel⟩ = -|A|·|¬A|/4 · |Φ_Néel⟩`. Spin-`1/2`
mirror of γ-4 step 79: cross-sublattice z-axis product. -/
theorem sublatticeSpinHalfOp3_cross_complement_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp3 (fun x => ! A x)).mulVec
        (neelStateOf A) =
      (-(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) /
            4)) •
        neelStateOf A := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOp3_complement_mulVec_neelStateOf]
  rw [Matrix.mulVec_smul]
  rw [sublatticeSpinHalfOp3_mulVec_neelStateOf]
  rw [smul_smul]
  congr 1
  ring

/-! ## Per-pair `spinHalfDot` diagonal at the Néel configuration -/

/-- For a cross-sublattice pair `x ∈ A`, `y ∈ ¬A`, the spin-`1/2`
two-site dot product diagonal at the Néel configuration is `-1/4`:

  `(Ŝ_x · Ŝ_y) (neel) (neel) = -1/4`.

Spin-`1/2` mirror of γ-4 step 69. -/
theorem spinHalfDot_apply_diag_neelConfigOf_of_cross
    (A : Λ → Bool)
    {x y : Λ} (hAx : A x = true) (hAy : A y = false) :
    (spinHalfDot x y : ManyBodyOp Λ) (neelConfigOf A) (neelConfigOf A) =
      -(1 / 4 : ℂ) := by
  have hxy : x ≠ y := by
    intro heq
    rw [heq, hAy] at hAx
    exact Bool.noConfusion hAx
  have hne : neelConfigOf A x ≠ neelConfigOf A y := by
    unfold neelConfigOf
    rw [if_pos hAx, if_neg (by rw [hAy]; decide : ¬ A y = true)]
    decide
  exact spinHalfDot_apply_diag_of_ne_antiparallel hxy _ hne

/-- For a same-sublattice pair `x ≠ y` with `A x = A y` (both in `A`
or both in `¬A`), the spin-`1/2` two-site dot product diagonal at the
Néel configuration is `+1/4`:

  `(Ŝ_x · Ŝ_y) (neel) (neel) = +1/4`.

Spin-`1/2` mirror of the same-sublattice case: when `A x = A y`, the
Néel config gives `σ x = σ y` (both `0` if in `A`, both `1` if in
`¬A`), so the parallel diagonal lemma `spinHalfDot_apply_diag_of_ne_parallel`
applies. -/
theorem spinHalfDot_apply_diag_neelConfigOf_of_same
    (A : Λ → Bool) {x y : Λ} (hxy : x ≠ y) (h : A x = A y) :
    (spinHalfDot x y : ManyBodyOp Λ) (neelConfigOf A) (neelConfigOf A) =
      (1 / 4 : ℂ) := by
  have hpar : neelConfigOf A x = neelConfigOf A y := by
    unfold neelConfigOf; rw [h]
  exact spinHalfDot_apply_diag_of_ne_parallel hxy _ hpar

/-- `Ŝ_A^+ · Ŝ_¬A^- · |Φ_Néel⟩ = 0`. Spin-`1/2` mirror of γ-4 step 81:
the cross-ladder product annihilates the Néel state via `Ŝ_¬A^- · Néel = 0`. -/
theorem sublatticeSpinHalfOpPlus_complement_minus_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOpPlus A *
        sublatticeSpinHalfOpMinus (fun x => ! A x)).mulVec
        (neelStateOf A) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOpMinus_complement_mulVec_neelStateOf]
  rw [Matrix.mulVec_zero]

/-- `Ŝ_A^- · Ŝ_¬A^- · |Φ_Néel⟩ = 0`. Spin-`1/2` mirror of γ-4 step 83:
cross-ladder lowering annihilates Néel via `Ŝ_¬A^- · Néel = 0`. -/
theorem sublatticeSpinHalfOpMinus_complement_minus_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOpMinus A *
        sublatticeSpinHalfOpMinus (fun x => ! A x)).mulVec
        (neelStateOf A) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOpMinus_complement_mulVec_neelStateOf]
  rw [Matrix.mulVec_zero]

/-- `Ŝ_¬A^+ · Ŝ_A^+ · |Φ_Néel⟩ = 0`. Spin-`1/2` mirror of γ-4 step 85:
cross-ladder raising annihilates Néel via `Ŝ_A^+ · Néel = 0`. -/
theorem sublatticeSpinHalfOpComplementPlus_plus_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOpPlus (fun x => ! A x) *
        sublatticeSpinHalfOpPlus A).mulVec
        (neelStateOf A) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOpPlus_mulVec_neelStateOf]
  rw [Matrix.mulVec_zero]

/-- `Ŝ_A^+ · Ŝ_¬A^+ · |Φ_Néel⟩ = 0`. Spin-`1/2` mirror of γ-4 step 89: uses
cross-commute to swap factors, then `Ŝ_A^+ · Néel = 0`. -/
theorem sublatticeSpinHalfOpPlus_complement_plus_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOpPlus A *
        sublatticeSpinHalfOpPlus (fun x => ! A x)).mulVec
        (neelStateOf A) = 0 := by
  rw [(sublatticeSpinHalfOpPlus_cross_commute A).eq]
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOpPlus_mulVec_neelStateOf]
  rw [Matrix.mulVec_zero]

/-- `Ŝ_¬A^- · Ŝ_A^+ · |Φ_Néel⟩ = 0`. Spin-`1/2` mirror of γ-4 step 91:
trivial via `Ŝ_A^+ · Néel = 0`. -/
theorem sublatticeSpinHalfOpComplementMinus_plus_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOpMinus (fun x => ! A x) *
        sublatticeSpinHalfOpPlus A).mulVec
        (neelStateOf A) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOpPlus_mulVec_neelStateOf]
  rw [Matrix.mulVec_zero]

/-- `Ŝ_A^- · Ŝ_A^+ · |Φ_Néel⟩ = 0`. Spin-`1/2` mirror of γ-4 step 93. -/
theorem sublatticeSpinHalfOpMinus_plus_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOpMinus A * sublatticeSpinHalfOpPlus A).mulVec
        (neelStateOf A) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOpPlus_mulVec_neelStateOf]
  rw [Matrix.mulVec_zero]

/-- `Ŝ_¬A^+ · Ŝ_¬A^- · |Φ_Néel⟩ = 0`. Spin-`1/2` mirror of γ-4 step 93. -/
theorem sublatticeSpinHalfOpComplementPlus_minus_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOpPlus (fun x => ! A x) *
        sublatticeSpinHalfOpMinus (fun x => ! A x)).mulVec
        (neelStateOf A) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinHalfOpMinus_complement_mulVec_neelStateOf]
  rw [Matrix.mulVec_zero]

/-- `((Ŝ_A^(1))² + (Ŝ_A^(2))²) · |Φ_Néel⟩ = (|A|/2) · |Φ_Néel⟩`. Spin-`1/2`
mirror of γ-4 step 95: derived as `(Ŝ_A)² · Néel - (Ŝ_A^(3))² · Néel`,
where `(Ŝ_A)²` has eigenvalue `|A|(|A|+2)/4` and `(Ŝ_A^(3))²` has
eigenvalue `(|A|/2)² = |A|²/4`. -/
theorem sublatticeSpinHalfOp12sq_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp1 A +
        sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp2 A).mulVec
        (neelStateOf A) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) / 2) •
        neelStateOf A := by
  have hCasimir := sublatticeSpinHalfSquared_mulVec_neelStateOf A
  rw [sublatticeSpinHalfSquared_def] at hCasimir
  rw [Matrix.add_mulVec, Matrix.add_mulVec] at hCasimir
  have hSq3 := sublatticeSpinHalfOp3_sq_mulVec_neelStateOf A
  rw [hSq3] at hCasimir
  set k : ℂ := ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) / 2
  rw [Matrix.add_mulVec]
  have h := hCasimir
  have hab : (sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp1 A).mulVec
        (neelStateOf A) +
      (sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp2 A).mulVec
        (neelStateOf A) =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) + 2) / 4) -
        k ^ 2) • neelStateOf A := by
    rw [sub_smul]
    rw [eq_sub_iff_add_eq]
    exact h
  rw [hab]
  congr 1
  simp only [k]
  ring

/-- `Ŝ_A^+·Ŝ_A^- · |Φ_Néel⟩ = |A| · |Φ_Néel⟩`. Spin-`1/2` mirror of
γ-4 step 100: highest-weight Casimir formula 2s = |A| for s = |A|/2. -/
theorem sublatticeSpinHalfOpPlus_minus_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfOpPlus A * sublatticeSpinHalfOpMinus A).mulVec
        (neelStateOf A) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ)) •
        neelStateOf A := by
  rw [sublatticeSpinHalfOpPlus_mul_sublatticeSpinHalfOpMinus_eq]
  rw [Matrix.add_mulVec]
  rw [sublatticeSpinHalfOp12sq_mulVec_neelStateOf]
  rw [sublatticeSpinHalfOp3_mulVec_neelStateOf]
  rw [← add_smul]
  congr 1
  ring

/-- `((Ŝ_¬A^(1))² + (Ŝ_¬A^(2))²) · |Φ_Néel⟩ = (|¬A|/2) · |Φ_Néel⟩`.
Spin-`1/2` complement of γ-4 step 96. -/
theorem sublatticeSpinHalfOp12sq_complement_mulVec_neelStateOf (A : Λ → Bool) :
    (sublatticeSpinHalfOp1 (fun x => ! A x) *
        sublatticeSpinHalfOp1 (fun x => ! A x) +
      sublatticeSpinHalfOp2 (fun x => ! A x) *
        sublatticeSpinHalfOp2 (fun x => ! A x)).mulVec
        (neelStateOf A) =
      (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) / 2) •
        neelStateOf A := by
  have hCasimir := sublatticeSpinHalfSquared_complement_mulVec_neelStateOf A
  rw [sublatticeSpinHalfSquared_def] at hCasimir
  rw [Matrix.add_mulVec, Matrix.add_mulVec] at hCasimir
  have hSq3 := sublatticeSpinHalfOp3_complement_sq_mulVec_neelStateOf A
  rw [hSq3] at hCasimir
  set k : ℂ := ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) / 2
  rw [Matrix.add_mulVec]
  have h := hCasimir
  have hab : (sublatticeSpinHalfOp1 (fun x => ! A x) *
        sublatticeSpinHalfOp1 (fun x => ! A x)).mulVec
        (neelStateOf A) +
      (sublatticeSpinHalfOp2 (fun x => ! A x) *
        sublatticeSpinHalfOp2 (fun x => ! A x)).mulVec
        (neelStateOf A) =
      ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
        (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) + 2) / 4) -
        k ^ 2) • neelStateOf A := by
    rw [sub_smul]
    rw [eq_sub_iff_add_eq]
    exact h
  rw [hab]
  congr 1
  simp only [k]
  ring

/-- The spin-`1/2` Néel state is non-zero. Direct from `basisVec_self = 1`. -/
theorem neelStateOf_ne_zero (A : Λ → Bool) : neelStateOf A ≠ 0 := by
  intro h
  have h1 : neelStateOf A (neelConfigOf A) = 1 := by
    unfold neelStateOf
    exact basisVec_self _
  have h0 : neelStateOf A (neelConfigOf A) = 0 := by rw [h]; rfl
  rw [h1] at h0
  exact one_ne_zero h0

/-- The spin-`1/2` Néel state has norm-squared 1:
`<Φ_Néel | Φ_Néel> = 1`. Direct from `basisVec_inner` orthonormality. -/
theorem neelStateOf_inner_self (A : Λ → Bool) :
    dotProduct (star (neelStateOf A)) (neelStateOf A) = 1 := by
  unfold neelStateOf dotProduct
  rw [Finset.sum_eq_single (neelConfigOf A)]
  · rw [basisVec_self]
    simp
  · intros τ _ hτne
    rw [basisVec_of_ne hτne]
    simp
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- **State-level distinctness** of `Φ_Néel(A)` and `Φ_Néel(¬A)` (spin-`1/2`):
when `Λ` is non-empty, the two Néel states are distinct. Spin-`1/2`
mirror of γ-4 step 179: equality would force inner-self to vanish. -/
theorem neelStateOf_ne_complement
    [Nonempty Λ] (A : Λ → Bool) :
    neelStateOf A ≠ neelStateOf (fun x : Λ => ! A x) := by
  intro h
  have horth := neelStateOf_complement_orthogonal A
  rw [h] at horth
  rw [neelStateOf_inner_self] at horth
  exact one_ne_zero horth

/-- **Néel-complement linear independence** (spin-`1/2`):
`c1 • Φ_Néel(A) + c2 • Φ_Néel(¬A) = 0 → c1 = c2 = 0` when `Λ` is non-empty.
Spin-`1/2` mirror of γ-4 step 172. -/
theorem neelStateOf_complement_pair_independent
    [Nonempty Λ] (A : Λ → Bool)
    {c1 c2 : ℂ}
    (h : c1 • neelStateOf A + c2 • neelStateOf (fun x : Λ => ! A x) = 0) :
    c1 = 0 ∧ c2 = 0 := by
  have horth_AcA := neelStateOf_complement_orthogonal A
  have horth_cAA :
      dotProduct (star (neelStateOf (fun x : Λ => ! A x))) (neelStateOf A) = 0 := by
    have := neelStateOf_complement_orthogonal (fun x : Λ => ! A x)
    simpa [Bool.not_not] using this
  have hc1 : c1 = 0 := by
    have := congrArg (dotProduct (star (neelStateOf A))) h
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul,
        neelStateOf_inner_self, horth_AcA, dotProduct_zero] at this
    simp at this
    exact this
  have hc2 : c2 = 0 := by
    have := congrArg
      (dotProduct (star (neelStateOf (fun x : Λ => ! A x)))) h
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul,
        neelStateOf_inner_self, horth_cAA, dotProduct_zero] at this
    simp at this
    exact this
  exact ⟨hc1, hc2⟩

/-- `<Φ_Néel | Ŝ_A^(3)·Ŝ_¬A^(3) | Φ_Néel> = -|A|·|¬A|/4`. Spin-`1/2` mirror of
γ-4 step 116. -/
theorem neelStateOf_sublattice3_cross_complement3_expectation (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((sublatticeSpinHalfOp3 A *
            sublatticeSpinHalfOp3 (fun x => ! A x)).mulVec
          (neelStateOf A)) =
      (-(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) /
          4)) := by
  rw [sublatticeSpinHalfOp3_cross_complement_mulVec_neelStateOf]
  rw [dotProduct_smul]
  rw [neelStateOf_inner_self, smul_eq_mul, mul_one]

/-- `<Φ_Néel | Ŝ_A^+ · Ŝ_¬A^+ | Φ_Néel> = 0`. Spin-`1/2` mirror of γ-4 step 120. -/
theorem neelStateOf_sublattice_plus_complement_plus_expectation (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((sublatticeSpinHalfOpPlus A *
            sublatticeSpinHalfOpPlus (fun x => ! A x)).mulVec
          (neelStateOf A)) = 0 := by
  rw [sublatticeSpinHalfOpPlus_complement_plus_mulVec_neelStateOf]
  exact dotProduct_zero _

/-- `<Φ_Néel | Ŝ_A^- · Ŝ_¬A^- | Φ_Néel> = 0`. Spin-`1/2` mirror of γ-4 step 120. -/
theorem neelStateOf_sublattice_minus_complement_minus_expectation (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((sublatticeSpinHalfOpMinus A *
            sublatticeSpinHalfOpMinus (fun x => ! A x)).mulVec
          (neelStateOf A)) = 0 := by
  rw [sublatticeSpinHalfOpMinus_complement_minus_mulVec_neelStateOf]
  exact dotProduct_zero _

/-- `<Φ_Néel | Ŝ_A^+ · Ŝ_¬A^- | Φ_Néel> = 0`. Spin-`1/2` mirror of γ-4 step 118:
trivial via Ŝ_¬A^- annihilation. -/
theorem neelStateOf_sublattice_plus_complement_minus_expectation
    (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((sublatticeSpinHalfOpPlus A *
            sublatticeSpinHalfOpMinus (fun x => ! A x)).mulVec
          (neelStateOf A)) = 0 := by
  rw [sublatticeSpinHalfOpPlus_complement_minus_mulVec_neelStateOf]
  exact dotProduct_zero _

/-- `<Φ_Néel | Ŝ_A^- · Ŝ_¬A^+ | Φ_Néel> = 0`. Spin-`1/2` mirror of γ-4 step 114:
cross-flip expectation vanishes via Hermitian conjugate. -/
theorem neelStateOf_sublattice_minus_plus_cross_expectation (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((sublatticeSpinHalfOpMinus A *
            sublatticeSpinHalfOpPlus (fun x => ! A x)).mulVec
          (neelStateOf A)) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec]
  rw [show sublatticeSpinHalfOpMinus A =
      (sublatticeSpinHalfOpPlus A).conjTranspose from
    (sublatticeSpinHalfOpPlus_conjTranspose A).symm]
  rw [← Matrix.star_mulVec]
  rw [sublatticeSpinHalfOpPlus_mulVec_neelStateOf]
  rw [star_zero]
  exact zero_dotProduct _

/-- `<Φ_Néel | Ŝ_A · Ŝ_¬A | Φ_Néel> = -|A|·|¬A|/4`. Spin-`1/2` mirror of γ-4
step 124: cross-sublattice spin dot product expectation. Combines γ-4
steps 117 (z-axis), 123 (ladder identity), 119 + 115 (cross-flip
expectations). -/
theorem neelStateOf_sublatticeSpinHalfDot_expectation (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp1 (fun x => ! A x) +
          sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp2 (fun x => ! A x) +
          sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp3 (fun x => ! A x)).mulVec
          (neelStateOf A)) =
      (-(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) /
          4)) := by
  rw [Matrix.add_mulVec, Matrix.add_mulVec]
  rw [dotProduct_add, dotProduct_add]
  rw [neelStateOf_sublattice3_cross_complement3_expectation]
  rw [show
      dotProduct (star (neelStateOf A))
          ((sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp1 (fun x => ! A x)).mulVec
            (neelStateOf A)) +
        dotProduct (star (neelStateOf A))
          ((sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp2 (fun x => ! A x)).mulVec
            (neelStateOf A)) = 0 from ?_]
  · ring
  rw [← dotProduct_add, ← Matrix.add_mulVec]
  rw [sublatticeSpinHalfOp1_mul_op1_add_op2_mul_op2_eq_ladder]
  rw [Matrix.smul_mulVec, dotProduct_smul]
  rw [Matrix.add_mulVec, dotProduct_add]
  rw [neelStateOf_sublattice_plus_complement_minus_expectation]
  rw [neelStateOf_sublattice_minus_plus_cross_expectation]
  simp

/-- `(Ŝ_tot^(3))² · |Φ_Néel⟩ = ((|A|-|¬A|)/2)² · |Φ_Néel⟩`. Spin-`1/2` mirror of
γ-4 step 128: Néel is exact (Ŝ_tot^(3))²-eigenvector. -/
theorem totalSpinHalfOp3_sq_mulVec_neelStateOf (A : Λ → Bool) :
    (totalSpinHalfOp3 Λ * totalSpinHalfOp3 Λ).mulVec (neelStateOf A) =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) / 2) ^ 2 •
        neelStateOf A := by
  rw [← Matrix.mulVec_mulVec]
  rw [totalSpinHalfOp3_mulVec_neelStateOf]
  rw [Matrix.mulVec_smul]
  rw [totalSpinHalfOp3_mulVec_neelStateOf]
  rw [smul_smul]
  congr 1
  ring

/-- `<Φ_Néel | (Ŝ_tot^(3))² | Φ_Néel> = ((|A|-|¬A|)/2)²`. Spin-`1/2` mirror
of γ-4 step 155. -/
theorem neelStateOf_totalSpinHalfOp3_sq_expectation (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((totalSpinHalfOp3 Λ * totalSpinHalfOp3 Λ).mulVec (neelStateOf A)) =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) / 2) ^ 2 := by
  rw [totalSpinHalfOp3_sq_mulVec_neelStateOf]
  rw [dotProduct_smul, neelStateOf_inner_self, smul_eq_mul, mul_one]


/-- `<Φ_Néel | (Ŝ_tot)² | Φ_Néel> = ((|A|-|¬A|)/2)² + (|A|+|¬A|)/2`. Spin-`1/2`
mirror of γ-4 step 126. The full total-spin Casimir expectation on Néel. -/
theorem neelStateOf_totalSpinHalfSquared_expectation (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((totalSpinHalfSquared Λ).mulVec (neelStateOf A)) =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) /
          2) ^ 2 +
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) +
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) /
          2 := by
  rw [totalSpinHalfSquared_eq_sublattice_casimir A]
  rw [Matrix.add_mulVec, Matrix.add_mulVec]
  rw [dotProduct_add, dotProduct_add]
  rw [sublatticeSpinHalfSquared_mulVec_neelStateOf]
  rw [sublatticeSpinHalfSquared_complement_mulVec_neelStateOf]
  rw [Matrix.smul_mulVec]
  rw [show sublatticeSpinDot A (fun x => ! A x) =
      sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp1 (fun x => ! A x) +
        sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp2 (fun x => ! A x) +
        sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp3 (fun x => ! A x) from rfl]
  simp only [dotProduct_smul, neelStateOf_inner_self,
    neelStateOf_sublatticeSpinHalfDot_expectation,
    smul_eq_mul, mul_one]
  ring

/-- `<Φ_Néel | Ŝ_tot^(3) | Φ_Néel> = (|A| - |¬A|)/2`. Spin-`1/2` mirror of
γ-4 step 112: Néel state magnetization expectation. -/
theorem neelStateOf_totalSpinHalfOp3_expectation (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((totalSpinHalfOp3 Λ).mulVec (neelStateOf A)) =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) / 2) := by
  rw [totalSpinHalfOp3_mulVec_neelStateOf]
  rw [dotProduct_smul]
  rw [neelStateOf_inner_self, smul_eq_mul, mul_one]

/-- `Ŝ_¬A^- · Ŝ_¬A^+ · |Φ_Néel⟩ = |¬A| · |Φ_Néel⟩`. Spin-`1/2` mirror of
γ-4 step 104 via dual Cartan identity. -/
theorem sublatticeSpinHalfOpComplementMinus_complement_plus_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOpMinus (fun x => ! A x) *
        sublatticeSpinHalfOpPlus (fun x => ! A x)).mulVec
        (neelStateOf A) =
      (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) •
        neelStateOf A := by
  rw [sublatticeSpinHalfOpMinus_mul_sublatticeSpinHalfOpPlus_eq]
  rw [Matrix.sub_mulVec]
  rw [sublatticeSpinHalfOp12sq_complement_mulVec_neelStateOf]
  rw [sublatticeSpinHalfOp3_complement_mulVec_neelStateOf]
  rw [← sub_smul]
  congr 1
  ring

/-- `<Φ_Néel | (Ŝ_tot)² | Φ_Néel> = ((|A|-|¬A|)/2)² + |Λ|/2`. Spin-`1/2`
reformulation of γ-4 step 127 using `|A| + |¬A| = |Λ|`. -/
theorem neelStateOf_totalSpinHalfSquared_expectation_card_Lambda (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((totalSpinHalfSquared Λ).mulVec (neelStateOf A)) =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) / 2) ^ 2 +
        (Fintype.card Λ : ℂ) / 2 := by
  rw [neelStateOf_totalSpinHalfSquared_expectation]
  congr 1
  have h : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) +
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) =
      (Fintype.card Λ : ℂ) := by
    have h1 : (Finset.univ.filter (fun x : Λ => A x = true)).card +
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card =
        Finset.univ.card (α := Λ) := by
      have hfilter_eq : Finset.univ.filter (fun x : Λ => (! A x) = true) =
          Finset.univ.filter (fun x : Λ => ¬ (A x = true)) := by
        congr 1
        funext x
        by_cases hA : A x = true
        · simp [hA]
        · simp [hA]
      rw [hfilter_eq]
      exact Finset.card_filter_add_card_filter_not (fun x : Λ => A x = true)
    have h2 : (Finset.univ.card (α := Λ) : ℂ) = (Fintype.card Λ : ℂ) := by
      rw [Finset.card_univ]
    rw [← h2]
    exact_mod_cast h1
  rw [h]

/-- `<Φ_Néel | Ĥ_toy | Φ_Néel> = -|A|·|¬A|/2`. Spin-`1/2` mirror of γ-4
step 131. Uses the generic basis-vector expectation lemma
`basisVec_expectation_eq_diagonal` (γ-4 step 132). -/
theorem neelStateOf_heisenbergToyHamiltonian_expectation (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((heisenbergToyHamiltonian A : ManyBodyOp Λ).mulVec (neelStateOf A)) =
      - (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) / 2) := by
  unfold neelStateOf
  rw [basisVec_expectation_eq_diagonal]
  exact heisenbergToyHamiltonian_apply_diag_neel A

end LatticeSystem.Quantum
