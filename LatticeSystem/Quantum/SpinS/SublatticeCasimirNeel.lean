import LatticeSystem.Quantum.SpinS.SublatticeSpinDot
import LatticeSystem.Quantum.SpinS.Magnetization
import LatticeSystem.Quantum.SpinS.ToyHamiltonianCasimir

/-!
# Spin-`S` Néel state and sublattice Casimir eigenvalues

Spin-`S` analog of `Quantum/MarshallLiebMattis/SublatticeCasimirNeel.lean`.

The graph-centric spin-`S` Néel state on a bipartite graph `(Λ, A)` is

  `Φ_Néel(A, N) := basisVecS (neelConfigOfS A N)`,

where `neelConfigOfS A N x := 0` if `A x = true` (highest weight) and
`Fin.last N` otherwise (lowest weight). The state is **constant on
each sublattice** at the extreme spin values.

By the constant-on-`A` Casimir eigenvalue formulas (PR #1066), the
Néel state is simultaneously an eigenvector of both sublattice
Casimirs `(Ŝ_A)²` and `(Ŝ_¬A)²` at their respective maximum-spin
eigenvalues:

  `(Ŝ_A)² · |Φ_Néel⟩ = ((|A|·N/2)·(|A|·N/2+1)) · |Φ_Néel⟩`,
  `(Ŝ_¬A)² · |Φ_Néel⟩ = ((|¬A|·N/2)·(|¬A|·N/2+1)) · |Φ_Néel⟩`.

Combined with the Casimir identity (PR #1056) and the closed form of
`Ĥ_toy_S` (PR #1060), this is a key ingredient in Tasaki's analysis
of the toy Hamiltonian's ground state in §2.5 for general spin-`S`.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 eqs. (2.5.2)–(2.5.11).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Spin-`S` Néel configuration and state -/

/-- The spin-`S` Néel configuration on a bipartite graph `(Λ, A)`:
sites with `A x = true` carry `0 : Fin (N+1)` (highest weight),
sites with `A x = false` carry `Fin.last N` (lowest weight).

Generalises the spin-`1/2` `neelConfigOf` (which uses `Fin 2`,
`0 ↔ ↑`, `1 ↔ ↓`); for spin-`S`, the lowest weight is
`Fin.last N` instead of `1`. -/
def neelConfigOfS (A : Λ → Bool) (N : ℕ) : Λ → Fin (N + 1) :=
  fun x => if A x then 0 else Fin.last N

/-- The spin-`S` Néel state: the many-body basis vector at
`neelConfigOfS A N`. -/
noncomputable def neelStateOfS (A : Λ → Bool) (N : ℕ) :
    (Λ → Fin (N + 1)) → ℂ :=
  basisVecS (neelConfigOfS A N)

/-! ## Sublattice Casimir eigenvalues on the Néel state -/

/-- `(Ŝ_A)² · |Φ_Néel⟩ = ((|A|·N/2)·(|A|·N/2+1)) · |Φ_Néel⟩`. The
Néel state is an eigenvector of the `A`-sublattice Casimir at the
maximum-spin eigenvalue, since `neelConfigOfS A N` is `0` on `A`. -/
theorem sublatticeSpinSquaredS_mulVec_neelStateOfS (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSquaredS N A).mulVec (neelStateOfS A N) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((N : ℂ) / 2) *
          (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) + 1)) •
        neelStateOfS A N := by
  unfold neelStateOfS
  refine sublatticeSpinSquaredS_mulVec_basisVecS_of_const_zero_on N A ?_
  intro x hAx
  unfold neelConfigOfS
  rw [if_pos hAx]

/-- `(Ŝ_¬A)² · |Φ_Néel⟩ = ((|¬A|·N/2)·(|¬A|·N/2+1)) · |Φ_Néel⟩`. The
Néel state is an eigenvector of the `¬A`-sublattice Casimir at the
maximum-spin eigenvalue, since `neelConfigOfS A N` is `Fin.last N` on
`¬A`. -/
theorem sublatticeSpinSquaredS_complement_mulVec_neelStateOfS
    (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec (neelStateOfS A N) =
      (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2) *
          (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2) + 1)) •
        neelStateOfS A N := by
  unfold neelStateOfS
  refine sublatticeSpinSquaredS_mulVec_basisVecS_of_const_last_on N
    (fun x => ! A x) ?_
  intro x hnAx
  have hAxF : A x = false := by
    cases h : A x
    · rfl
    · simp [h] at hnAx
  unfold neelConfigOfS
  rw [if_neg (by rw [hAxF]; decide : ¬ (A x = true))]

/-! ## `Ŝ_tot^(3)` eigenvalue on the Néel state -/

/-- `magSumS (neelConfigOfS A N) = |¬A| · N`. The Néel configuration
contributes `0` on `A` and `N` (i.e., `(Fin.last N).val`) on `¬A`. -/
theorem magSumS_neelConfigOfS (A : Λ → Bool) (N : ℕ) :
    magSumS (neelConfigOfS A N) =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N := by
  unfold magSumS neelConfigOfS
  classical
  -- Convert each term: if A x then 0 else N.
  have hterm : ∀ x : Λ, (if A x then (0 : Fin (N + 1)) else Fin.last N).val =
      if (! A x) = true then N else 0 := by
    intro x
    by_cases hAx : A x = true
    · rw [if_pos hAx]
      simp [hAx]
    · cases h : A x
      · rw [if_neg]
        · simp [h, Fin.last]
        · simp [h]
      · exact absurd h hAx
  simp_rw [hterm]
  rw [← Finset.sum_filter, Finset.sum_const]
  rw [smul_eq_mul]

/-- `Ŝ_tot^(3) · |Φ_Néel⟩ = ((|A| − |¬A|)·N/2) · |Φ_Néel⟩`. The spin-`S`
Néel state is a `Ŝ_tot^(3)`-eigenvector with magnetization
`(|A| − |¬A|)·N/2`. For `|A| = |¬A|` the magnetization is zero; for
`|A| ≠ |¬A|` (the Tasaki §2.5 Theorem 2.3 case) the absolute value
`||A| − |¬A||·N/2` matches the conjectured ground-state total spin
`||A| − |¬A||·S`. -/
theorem totalSpinSOp3_mulVec_neelStateOfS (A : Λ → Bool) (N : ℕ) :
    (totalSpinSOp3 Λ N).mulVec (neelStateOfS A N) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) •
        neelStateOfS A N := by
  unfold neelStateOfS
  rw [totalSpinSOp3_mulVec_basisVecS]
  congr 1
  unfold magEigenvalueS
  rw [magSumS_neelConfigOfS]
  -- |Λ| = |A| + |¬A| as ℂ.
  have hsum : (Fintype.card Λ : ℕ) =
      (Finset.univ.filter (fun x : Λ => A x = true)).card +
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
    have hfilter : Finset.univ.filter (fun x : Λ => (! A x) = true) =
        Finset.univ.filter (fun x : Λ => ¬ (A x = true)) := by
      ext x; simp [Bool.not_eq_true]
    rw [hfilter]
    rw [← Finset.card_univ (α := Λ)]
    exact (Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun x : Λ => A x = true)).symm
  have hsumℂ : (Fintype.card Λ : ℂ) =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) +
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) := by
    have := congrArg (Nat.cast (R := ℂ)) hsum
    push_cast at this
    exact this
  rw [hsumℂ]
  push_cast
  ring

/-! ## Néel config under sublattice swap -/

/-- `neelConfigOfS (¬A) N` is the "swapped" Néel configuration: `σ x = N`
for `A x = true` (i.e., on `A`) and `σ x = 0` for `A x = false` (on `¬A`).
This is the natural sublattice-swap dual of `neelConfigOfS A N`. -/
theorem neelConfigOfS_complement (A : Λ → Bool) (N : ℕ) (x : Λ) :
    neelConfigOfS (fun y => ! A y) N x =
      if A x then Fin.last N else 0 := by
  unfold neelConfigOfS
  by_cases hA : A x = true
  · simp [hA]
  · cases h : A x
    · simp [h]
    · exact absurd h hA

/-! ## Sublattice axis-3 on the Néel state -/

/-- `Ŝ_A^(3) · |Φ_Néel⟩ = (|A|·N/2) · |Φ_Néel⟩`. The sublattice
z-axis acts as |A|·N/2 on the Néel state (highest weight on A). -/
theorem sublatticeSpinSOp3_mulVec_neelStateOfS (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSOp3 N A).mulVec (neelStateOfS A N) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) •
        neelStateOfS A N := by
  unfold sublatticeSpinSOp3 neelStateOfS
  rw [Matrix.sum_mulVec]
  rw [show (∑ x : Λ, (if A x then onSiteS x (spinSOp3 N) else 0 : ManyBodyOpS Λ N).mulVec
        (basisVecS (neelConfigOfS A N))) =
      ∑ x : Λ, (if A x then ((N : ℂ) / 2) else 0) •
        basisVecS (neelConfigOfS A N) from by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hA : A x = true
    · rw [if_pos hA, if_pos hA]
      rw [onSiteS_spinSOp3_mulVec_basisVecS]
      have hσx : (neelConfigOfS A N x).val = 0 := by
        unfold neelConfigOfS; rw [if_pos hA]; simp
      rw [hσx]
      simp
    · cases h : A x
      · rw [if_neg, if_neg]
        · rw [Matrix.zero_mulVec, zero_smul]
        · simp
        · simp
      · exact absurd h hA]
  rw [← Finset.sum_smul]
  congr 1
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]

/-- `Ŝ_¬A^(3) · |Φ_Néel⟩ = -(|¬A|·N/2) · |Φ_Néel⟩`. The complement
sublattice z-axis acts as -|¬A|·N/2 on the Néel state (lowest weight on ¬A). -/
theorem sublatticeSpinSOp3_complement_mulVec_neelStateOfS
    (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSOp3 N (fun x => ! A x)).mulVec (neelStateOfS A N) =
      (-(((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2))) •
        neelStateOfS A N := by
  unfold sublatticeSpinSOp3 neelStateOfS
  rw [Matrix.sum_mulVec]
  rw [show (∑ x : Λ, (if (! A x) then onSiteS x (spinSOp3 N) else 0 : ManyBodyOpS Λ N).mulVec
        (basisVecS (neelConfigOfS A N))) =
      ∑ x : Λ, (if (! A x) then -((N : ℂ) / 2) else 0) •
        basisVecS (neelConfigOfS A N) from by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hA : (! A x) = true
    · rw [if_pos hA, if_pos hA]
      rw [onSiteS_spinSOp3_mulVec_basisVecS]
      have hAxF : A x = false := by
        cases h : A x
        · rfl
        · simp [h] at hA
      have hσx : (neelConfigOfS A N x).val = N := by
        unfold neelConfigOfS
        rw [if_neg (by rw [hAxF]; decide : ¬ A x = true)]
        simp [Fin.last]
      rw [hσx]
      congr 1
      ring
    · cases h : (! A x)
      · rw [if_neg, if_neg]
        · rw [Matrix.zero_mulVec, zero_smul]
        · simp
        · simp
      · exact absurd h hA]
  rw [← Finset.sum_smul]
  congr 1
  have hrw : ∀ x : Λ, (if (! A x) = true then -((N : ℂ) / 2) else 0) =
      -(if (! A x) = true then ((N : ℂ) / 2) else 0) := by
    intro x
    by_cases h : (! A x) = true
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, neg_zero]
  rw [Finset.sum_congr rfl (fun x _ => hrw x)]
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- `(Ŝ_A^(3))² · |Φ_Néel⟩ = (|A|·N/2)² · |Φ_Néel⟩`. Square of γ-4 step 73:
the squared sublattice z-axis acts as `(|A|·N/2)²` on the Néel state. -/
theorem sublatticeSpinSOp3_sq_mulVec_neelStateOfS
    (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N A).mulVec (neelStateOfS A N) =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) ^ 2) •
        neelStateOfS A N := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinSOp3_mulVec_neelStateOfS]
  rw [Matrix.mulVec_smul]
  rw [sublatticeSpinSOp3_mulVec_neelStateOfS]
  rw [smul_smul]
  congr 1
  ring

/-- `(Ŝ_¬A^(3))² · |Φ_Néel⟩ = (|¬A|·N/2)² · |Φ_Néel⟩`. Square of γ-4 step 74. -/
theorem sublatticeSpinSOp3_complement_sq_mulVec_neelStateOfS
    (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSOp3 N (fun x => ! A x) *
        sublatticeSpinSOp3 N (fun x => ! A x)).mulVec (neelStateOfS A N) =
      ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) ^ 2) •
        neelStateOfS A N := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinSOp3_complement_mulVec_neelStateOfS]
  rw [Matrix.mulVec_smul]
  rw [sublatticeSpinSOp3_complement_mulVec_neelStateOfS]
  rw [smul_smul]
  congr 1
  ring

/-- `Ŝ_A^(3) · Ŝ_¬A^(3) · |Φ_Néel⟩ = -|A|·|¬A|·(N/2)² · |Φ_Néel⟩`.
Cross-sublattice product of γ-4 steps 73 and 74. -/
theorem sublatticeSpinSOp3_cross_complement_mulVec_neelStateOfS
    (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x)).mulVec
        (neelStateOfS A N) =
      (-(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2) ^ 2)) •
        neelStateOfS A N := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinSOp3_complement_mulVec_neelStateOfS]
  rw [Matrix.mulVec_smul]
  rw [sublatticeSpinSOp3_mulVec_neelStateOfS]
  rw [smul_smul]
  congr 1
  ring

/-! ## Per-pair `spinSDot` diagonal at the Néel configuration -/

/-- For a cross-sublattice pair `x ∈ A`, `y ∈ ¬A`, the two-site dot
product diagonal at the Néel configuration is `-N²/4`:

  `(Ŝ_x · Ŝ_y) (neel) (neel) = (N/2)·(-N/2) = -N²/4`.

Direct from `spinSDot_apply_diag_of_ne` with `m_x = N/2` and
`m_y = -N/2` from the Néel config values. -/
theorem spinSDot_apply_diag_neelConfigOfS_of_cross
    (A : Λ → Bool) (N : ℕ)
    {x y : Λ} (hAx : A x = true) (hAy : A y = false) :
    (spinSDot x y N : ManyBodyOpS Λ N)
        (neelConfigOfS A N) (neelConfigOfS A N) =
      -((N : ℂ) * (N : ℂ) / 4) := by
  have hxy : x ≠ y := by
    intro heq
    rw [heq, hAy] at hAx
    exact Bool.noConfusion hAx
  rw [spinSDot_apply_diag_of_ne hxy]
  -- m_x = N/2 since σ_x = 0; m_y = -N/2 since σ_y = Fin.last N.
  have hmx : ((N : ℂ) / 2 - (neelConfigOfS A N x).val) = (N : ℂ) / 2 := by
    unfold neelConfigOfS
    rw [if_pos hAx]; simp
  have hmy : ((N : ℂ) / 2 - (neelConfigOfS A N y).val) = -((N : ℂ) / 2) := by
    unfold neelConfigOfS
    rw [if_neg (by rw [hAy]; decide : ¬ (A y = true))]
    push_cast [Fin.last]; ring
  rw [hmx, hmy]
  ring

/-! ## Toy Hamiltonian diagonal matrix element on the Néel state -/

/-- The diagonal matrix element of the cross-sublattice spin dot
product `Ŝ_A · Ŝ_¬A` at the spin-`S` Néel configuration:

  `(Ŝ_A · Ŝ_¬A) (neel) (neel) = -|A|·|¬A|·N²/4`.

Each `(x ∈ A, y ∈ ¬A)` pair contributes
`(spinSDot x y) (neel) (neel) = m_x · m_y = (N/2)·(−N/2) = -N²/4`
(diagonal formula `spinSDot_apply_diag_of_ne`, since `A x ≠ A y`
implies `x ≠ y`); summing over the `|A|·|¬A|` such pairs gives the
result. -/
theorem sublatticeSpinSDot_apply_diag_neel (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSDot N A (fun x => ! A x))
        (neelConfigOfS A N) (neelConfigOfS A N) =
      -(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          ((N : ℂ) * (N : ℂ)) / 4) := by
  rw [sublatticeSpinSDot_eq_sum_sum]
  -- Apply at (neel, neel).
  rw [show (∑ x : Λ, ∑ y : Λ,
        if A x ∧ (fun z : Λ => ! A z) y = true then spinSDot x y N else 0)
        (neelConfigOfS A N) (neelConfigOfS A N) =
      ∑ x : Λ, ∑ y : Λ,
        ((if A x ∧ (! A y) = true then spinSDot x y N else 0)
          (neelConfigOfS A N) (neelConfigOfS A N)) from by
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.sum_apply]]
  have hterm : ∀ x y : Λ,
      ((if A x ∧ (! A y) = true then spinSDot x y N else 0)
          (neelConfigOfS A N) (neelConfigOfS A N) : ℂ) =
      if A x ∧ (! A y) = true then -((N : ℂ) * (N : ℂ) / 4) else 0 := by
    intro x y
    by_cases hAB : A x ∧ (! A y) = true
    · obtain ⟨hAx, hAy⟩ := hAB
      rw [if_pos ⟨hAx, hAy⟩, if_pos ⟨hAx, hAy⟩]
      have hxy : x ≠ y := by
        intro heq
        subst heq
        rw [hAx] at hAy
        simp at hAy
      rw [spinSDot_apply_diag_of_ne hxy]
      -- m_x = N/2 (since A x = true, neel x = 0).
      have hmx : ((N : ℂ) / 2 - (neelConfigOfS A N x).val) = (N : ℂ) / 2 := by
        unfold neelConfigOfS
        rw [if_pos hAx]; simp
      -- m_y = -N/2 (since A y = false, neel y = Fin.last N).
      have hAyF : A y = false := by
        cases h : A y
        · rfl
        · simp [h] at hAy
      have hmy : ((N : ℂ) / 2 - (neelConfigOfS A N y).val) = -((N : ℂ) / 2) := by
        unfold neelConfigOfS
        rw [if_neg (by rw [hAyF]; decide : ¬ (A y = true))]
        push_cast [Fin.last]; ring
      rw [hmx, hmy]
      ring
    · rw [if_neg hAB, if_neg hAB]
      rfl
  simp_rw [hterm]
  -- Sum: |A| · |¬A| · (-N²/4).
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

/-- The Néel-state expectation value of the spin-`S` toy Hamiltonian:

  `⟨Φ_Néel | Ĥ_toy_S | Φ_Néel⟩ = -|A|·|¬A|·N²/2`,

i.e., the diagonal matrix element at the Néel configuration is
`-|A|·|¬A|·N²/2`. This is the **negative** of the all-up state
eigenvalue (PR #1061), `+|A|·|¬A|·N²/2`.

The negative sign is the variational signature: the Néel state has
strictly lower toy-Hamiltonian expectation value than the all-up
state, demonstrating that the ground state has `S_tot < |Λ|·S` —
consistent with the Tasaki §2.5 Theorem 2.3 prediction
`S_tot = ||A|−|B||·S`. -/
theorem heisenbergToyHamiltonianS_apply_diag_neel (A : Λ → Bool) (N : ℕ) :
    (heisenbergToyHamiltonianS (Λ := Λ) A N) (neelConfigOfS A N)
        (neelConfigOfS A N) =
      - (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          ((N : ℂ) * (N : ℂ)) / 2) := by
  rw [heisenbergToyHamiltonianS_eq_two_sublatticeSpinSDot]
  rw [Matrix.smul_apply, sublatticeSpinSDot_apply_diag_neel]
  rw [smul_eq_mul]
  ring

/-! ## Ladder annihilation of the Néel state -/

/-- `Ŝ_A^+ · |Φ_Néel⟩ = 0`: the sublattice A raising operator annihilates
the Néel state, since the Néel state has `σ|_A = 0` (highest weight on
`A`). -/
theorem sublatticeSpinSOpPlus_mulVec_neelStateOfS (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSOpPlus N A).mulVec (neelStateOfS A N) = 0 := by
  unfold neelStateOfS
  refine sublatticeSpinSOpPlus_mulVec_basisVecS_zero_on N A ?_
  intro x hAx
  unfold neelConfigOfS
  rw [if_pos hAx]

/-- `Ŝ_¬A^- · |Φ_Néel⟩ = 0`: the sublattice ¬A lowering operator
annihilates the Néel state, since the Néel state has `σ|_¬A = Fin.last N`
(lowest weight on `¬A`). -/
theorem sublatticeSpinSOpMinus_complement_mulVec_neelStateOfS
    (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec (neelStateOfS A N) = 0 := by
  unfold neelStateOfS
  refine sublatticeSpinSOpMinus_mulVec_basisVecS_last_on N (fun x => ! A x) ?_
  intro x hnAx
  have hAxF : A x = false := by
    cases h : A x
    · rfl
    · simp [h] at hnAx
  unfold neelConfigOfS
  rw [if_neg (by rw [hAxF]; decide : ¬ (A x = true))]

/-- On the Néel state: `Ŝ_tot^+ · |Φ_Néel⟩ = Ŝ_¬A^+ · |Φ_Néel⟩`.
The total raising decomposes as `Ŝ_A^+ + Ŝ_¬A^+`, and `Ŝ_A^+` annihilates
the Néel state (PR #1111). -/
theorem totalSpinSOpPlus_mulVec_neelStateOfS_eq_complement
    (A : Λ → Bool) (N : ℕ) :
    (totalSpinSOpPlus Λ N).mulVec (neelStateOfS A N) =
      (sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec (neelStateOfS A N) := by
  rw [totalSpinSOpPlus_eq_sublattice_sum (N := N) A]
  rw [Matrix.add_mulVec]
  rw [sublatticeSpinSOpPlus_mulVec_neelStateOfS A N]
  rw [zero_add]

/-- On the Néel state: `Ŝ_tot^- · |Φ_Néel⟩ = Ŝ_A^- · |Φ_Néel⟩`.
The total lowering decomposes as `Ŝ_A^- + Ŝ_¬A^-`, and `Ŝ_¬A^-` annihilates
the Néel state. -/
theorem totalSpinSOpMinus_mulVec_neelStateOfS_eq_A
    (A : Λ → Bool) (N : ℕ) :
    (totalSpinSOpMinus Λ N).mulVec (neelStateOfS A N) =
      (sublatticeSpinSOpMinus N A).mulVec (neelStateOfS A N) := by
  rw [totalSpinSOpMinus_eq_sublattice_sum (N := N) A]
  rw [Matrix.add_mulVec]
  rw [sublatticeSpinSOpMinus_complement_mulVec_neelStateOfS A N]
  rw [add_zero]

/-- `Ŝ_A^+ · Ŝ_¬A^- · |Φ_Néel⟩ = 0`. The cross product of raising on `A` with
lowering on `¬A` annihilates the Néel state, since `Ŝ_¬A^- · |Φ_Néel⟩ = 0`.
Direct ingredient for `(Ŝ_tot)² · |Φ_Néel⟩` (one of the cross-ladder terms
in the Casimir identity vanishes). -/
theorem sublatticeSpinSOpPlus_complement_minus_mulVec_neelStateOfS
    (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSOpPlus N A *
        sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
        (neelStateOfS A N) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinSOpMinus_complement_mulVec_neelStateOfS]
  rw [Matrix.mulVec_zero]

end LatticeSystem.Quantum
