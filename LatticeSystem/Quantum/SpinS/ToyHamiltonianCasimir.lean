import LatticeSystem.Quantum.SpinS.SublatticeSpinDot
import LatticeSystem.Quantum.SpinS.ToyHamiltonian
import LatticeSystem.Quantum.SpinS.AllAlignedState

/-!
# Spin-`S` toy Hamiltonian as a cross-sublattice spin dot product

Spin-`S` analog of the leading section of
`Quantum/MarshallLiebMattis/ToyHamiltonianCasimir.lean`.
The spin-`S` MLM toy Hamiltonian (Tasaki §2.5 eq. (2.5.10), without
the `1/|Λ|` factor)

  `Ĥ_toy_S = Σ_{(x, y) bipartite} Ŝ_x · Ŝ_y`

decomposes through the cross-sublattice spin dot product as

  `Ĥ_toy_S = Ŝ_A · Ŝ_¬A + Ŝ_¬A · Ŝ_A = 2 • Ŝ_A · Ŝ_¬A`,

since the bipartite bond sum splits into the two oriented
cross-sublattice contributions. This is the bridge from the bond
sum to the operator-level Casimir form (Tasaki §2.5 (2.5.11)),
which is assembled in subsequent PRs.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 eqs. (2.5.10)–(2.5.11).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (N : ℕ)

/-- The spin-`S` cross-sublattice spin dot product is symmetric across
the bipartition: `Ŝ_A · Ŝ_¬A = Ŝ_¬A · Ŝ_A`. Each axis pair commutes by
the same-axis cross-sublattice commutativity lemmas (PR #1045). -/
theorem sublatticeSpinSDot_complement_comm (A : Λ → Bool) :
    sublatticeSpinSDot N A (fun x => ! A x) =
      sublatticeSpinSDot N (fun x => ! A x) A := by
  unfold sublatticeSpinSDot
  congr 1
  · congr 1
    · exact (sublatticeSpinSOp1_cross_commute N A).eq
    · exact (sublatticeSpinSOp2_cross_commute N A).eq
  · exact (sublatticeSpinSOp3_cross_commute N A).eq

/-- The spin-`S` MLM toy Hamiltonian decomposes as an oriented
cross-sublattice spin dot product:
`Ĥ_toy_S = Ŝ_A · Ŝ_¬A + Ŝ_¬A · Ŝ_A`. -/
theorem heisenbergToyHamiltonianS_eq_sublatticeSpinSDot_sum (A : Λ → Bool) :
    heisenbergToyHamiltonianS (Λ := Λ) A N =
      sublatticeSpinSDot N A (fun x => ! A x) +
        sublatticeSpinSDot N (fun x => ! A x) A := by
  unfold heisenbergToyHamiltonianS heisenbergHamiltonianS bipartiteCoupling
  rw [sublatticeSpinSDot_eq_sum_sum, sublatticeSpinSDot_eq_sum_sum,
      ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hAx : A x = true
  · by_cases hAy : A y = true
    · have hne : ¬ A x ≠ A y := fun h => h (hAx.trans hAy.symm)
      rw [if_neg hne, zero_smul]
      have h1 : ¬ (A x ∧ (fun z : Λ => ! A z) y) := by
        intro ⟨_, h2⟩; rw [show (fun z : Λ => ! A z) y = false from by simp [hAy]] at h2
        exact Bool.noConfusion h2
      have h2 : ¬ ((fun z : Λ => ! A z) x ∧ A y) := by
        intro ⟨h1, _⟩; rw [show (fun z : Λ => ! A z) x = false from by simp [hAx]] at h1
        exact Bool.noConfusion h1
      rw [if_neg h1, if_neg h2, add_zero]
    · have hAy' : A y = false := by
        cases h : A y
        · rfl
        · exact absurd h hAy
      have hne : A x ≠ A y := by rw [hAx, hAy']; decide
      rw [if_pos hne, one_smul]
      have h1 : A x ∧ (fun z : Λ => ! A z) y := by
        refine ⟨hAx, ?_⟩
        rw [show (fun z : Λ => ! A z) y = true from by simp [hAy']]
      have h2 : ¬ ((fun z : Λ => ! A z) x ∧ A y) := by
        intro ⟨_, h⟩; rw [hAy'] at h; exact Bool.noConfusion h
      rw [if_pos h1, if_neg h2, add_zero]
  · have hAx' : A x = false := by
      cases h : A x
      · rfl
      · exact absurd h hAx
    by_cases hAy : A y = true
    · have hne : A x ≠ A y := by rw [hAx', hAy]; decide
      rw [if_pos hne, one_smul]
      have h1 : ¬ (A x ∧ (fun z : Λ => ! A z) y) := by
        intro ⟨h, _⟩; rw [hAx'] at h; exact Bool.noConfusion h
      have h2 : (fun z : Λ => ! A z) x ∧ A y := by
        refine ⟨?_, hAy⟩
        rw [show (fun z : Λ => ! A z) x = true from by simp [hAx']]
      rw [if_neg h1, if_pos h2, zero_add]
    · have hAy' : A y = false := by
        cases h : A y
        · rfl
        · exact absurd h hAy
      have hne : ¬ A x ≠ A y := fun h => h (hAx'.trans hAy'.symm)
      rw [if_neg hne, zero_smul]
      have h1 : ¬ (A x ∧ (fun z : Λ => ! A z) y) := by
        intro ⟨h, _⟩; rw [hAx'] at h; exact Bool.noConfusion h
      have h2 : ¬ ((fun z : Λ => ! A z) x ∧ A y) := by
        intro ⟨_, h⟩; rw [hAy'] at h; exact Bool.noConfusion h
      rw [if_neg h1, if_neg h2, add_zero]

/-- The spin-`S` MLM toy Hamiltonian equals twice the cross-sublattice
spin dot product:
`Ĥ_toy_S = 2 • Ŝ_A · Ŝ_¬A`. Combines the oriented sum form
`Ĥ_toy_S = Ŝ_A · Ŝ_¬A + Ŝ_¬A · Ŝ_A` with the cross-sublattice
symmetry `_complement_comm`. -/
theorem heisenbergToyHamiltonianS_eq_two_sublatticeSpinSDot (A : Λ → Bool) :
    heisenbergToyHamiltonianS (Λ := Λ) A N =
      (2 : ℂ) • sublatticeSpinSDot N A (fun x => ! A x) := by
  rw [heisenbergToyHamiltonianS_eq_sublatticeSpinSDot_sum]
  rw [← sublatticeSpinSDot_complement_comm]
  rw [two_smul]

/-! ## Casimir identity for the total spin-`S` -/

/-- Helper: for commuting operators, `(a + b)(a + b) = a*a + 2•(a*b) + b*b`. -/
private lemma square_add_of_commuteS
    {a b : ManyBodyOpS Λ N} (h : Commute a b) :
    (a + b) * (a + b) = a * a + (2 : ℂ) • (a * b) + b * b := by
  rw [add_mul, mul_add, mul_add, h.eq, two_smul]
  abel

/-- **Casimir identity for spin-`S`** (Tasaki §2.5 (2.5.11)):
the total spin squared decomposes across the bipartition as

`(Ŝ_tot)² = (Ŝ_A)² + 2 • (Ŝ_A · Ŝ_¬A) + (Ŝ_¬A)²`.

Each axis contributes `(Ŝ_A^α + Ŝ_¬A^α)² = (Ŝ_A^α)² + 2 Ŝ_A^α Ŝ_¬A^α + (Ŝ_¬A^α)²`
by the cross-sublattice commutativity (PR #1045); summing
gives the operator identity. -/
theorem totalSpinSSquared_eq_sublattice_casimir (A : Λ → Bool) :
    totalSpinSSquared Λ N =
      sublatticeSpinSquaredS N A
      + (2 : ℂ) • sublatticeSpinSDot N A (fun x => ! A x)
      + sublatticeSpinSquaredS N (fun x => ! A x) := by
  unfold totalSpinSSquared sublatticeSpinSquaredS
  rw [sublatticeSpinSDot_def]
  rw [totalSpinSOp1_eq_sublattice_sum (N := N) A,
      totalSpinSOp2_eq_sublattice_sum (N := N) A,
      totalSpinSOp3_eq_sublattice_sum (N := N) A]
  rw [square_add_of_commuteS N (sublatticeSpinSOp1_cross_commute N A),
      square_add_of_commuteS N (sublatticeSpinSOp2_cross_commute N A),
      square_add_of_commuteS N (sublatticeSpinSOp3_cross_commute N A)]
  rw [smul_add, smul_add]
  abel

/-- **Tasaki §2.5 (2.5.11) closed form for spin-`S`** (without the
`1/|Λ|` factor): the toy Hamiltonian equals the difference of the
total Casimir and the two sublattice Casimirs:

`Ĥ_toy_S = (Ŝ_tot)² − (Ŝ_A)² − (Ŝ_¬A)²`. -/
theorem heisenbergToyHamiltonianS_eq_casimir_diff (A : Λ → Bool) :
    heisenbergToyHamiltonianS (Λ := Λ) A N =
      totalSpinSSquared Λ N
        - sublatticeSpinSquaredS N A
        - sublatticeSpinSquaredS N (fun x => ! A x) := by
  rw [totalSpinSSquared_eq_sublattice_casimir N A,
      heisenbergToyHamiltonianS_eq_two_sublatticeSpinSDot N A]
  abel

/-! ## Commutativity with the total Casimir -/

/-- The spin-`S` toy Hamiltonian commutes with the total spin Casimir:
`Commute Ĥ_toy_S (Ŝ_tot)²`. Follows from the general SU(2) invariance
of any spin-`S` Heisenberg-type Hamiltonian
(`heisenbergHamiltonianS_commute_totalSpinSSquared`).

This is the standard fact used to project the toy Hamiltonian's
ground state onto a fixed `(Ŝ_tot)²` eigenspace; combined with the
Casimir identity, it underpins the `S_tot = ||A| − |B||·S` selection
in Tasaki §2.5 Theorem 2.3. -/
theorem heisenbergToyHamiltonianS_commute_totalSpinSSquared (A : Λ → Bool) :
    Commute (heisenbergToyHamiltonianS (Λ := Λ) A N) (totalSpinSSquared Λ N) :=
  heisenbergHamiltonianS_commute_totalSpinSSquared (bipartiteCoupling A) N

/-- The spin-`S` toy Hamiltonian commutes with the `A`-sublattice
Casimir: `Commute Ĥ_toy_S (Ŝ_A)²`. Follows from the closed form
`Ĥ_toy_S = (Ŝ_tot)² − (Ŝ_A)² − (Ŝ_¬A)²` (PR #1056) and the three
pairwise commutativities of the three Casimir operators (PRs #1047,
#1052). -/
theorem heisenbergToyHamiltonianS_commute_sublatticeSpinSquaredS (A : Λ → Bool) :
    Commute (heisenbergToyHamiltonianS (Λ := Λ) A N) (sublatticeSpinSquaredS N A) := by
  rw [heisenbergToyHamiltonianS_eq_casimir_diff N A]
  refine Commute.sub_left (Commute.sub_left ?_ ?_) ?_
  · exact (sublatticeSpinSquaredS_commute_totalSpinSSquared N A).symm
  · exact Commute.refl _
  · exact (sublatticeSpinSquaredS_cross_commute N A).symm

/-- The spin-`S` toy Hamiltonian commutes with the `¬A`-sublattice
Casimir: `Commute Ĥ_toy_S (Ŝ_¬A)²`. Symmetric to the `A` case. -/
theorem heisenbergToyHamiltonianS_commute_sublatticeSpinSquaredS_complement
    (A : Λ → Bool) :
    Commute (heisenbergToyHamiltonianS (Λ := Λ) A N)
            (sublatticeSpinSquaredS N (fun x => ! A x)) := by
  rw [heisenbergToyHamiltonianS_eq_casimir_diff N A]
  refine Commute.sub_left (Commute.sub_left ?_ ?_) ?_
  · exact (sublatticeSpinSquaredS_commute_totalSpinSSquared N (fun x => ! A x)).symm
  · exact sublatticeSpinSquaredS_cross_commute N A
  · exact Commute.refl _

/-! ## Eigenvalue on the all-up state -/

/-- **Spin-`S` toy Hamiltonian eigenvalue on the all-up state**
(Tasaki §2.5 maximum-weight contribution). From the closed form
`Ĥ_toy_S = (Ŝ_tot)² − (Ŝ_A)² − (Ŝ_¬A)²` (PR #1056) and the three
Casimir eigenvalue formulas:

  `Ĥ_toy_S · |σ_⊤⟩ =
    ((|Λ|·N/2)(|Λ|·N/2+1) − (|A|·N/2)(|A|·N/2+1) − (|¬A|·N/2)(|¬A|·N/2+1)) · |σ_⊤⟩`.

This is the maximum-spin eigenvalue contribution: each Casimir
attains its maximum on the all-up state with `J = |Λ|·N/2`,
`J_A = |A|·N/2`, `J_{¬A} = |¬A|·N/2`. -/
theorem heisenbergToyHamiltonianS_mulVec_allAlignedStateS_zero
    [Nonempty Λ] (A : Λ → Bool) :
    (heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
        (allAlignedStateS Λ N (0 : Fin (N + 1))) =
      (((Fintype.card Λ : ℂ) * (N : ℂ) / 2 *
          ((Fintype.card Λ : ℂ) * (N : ℂ) / 2 + 1))
        - (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2) *
            (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                ((N : ℂ) / 2) + 1))
        - (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2) *
            (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                ((N : ℂ) / 2) + 1))) •
        allAlignedStateS Λ N (0 : Fin (N + 1)) := by
  rw [heisenbergToyHamiltonianS_eq_casimir_diff N A]
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec]
  rw [totalSpinSSquared_mulVec_allAlignedStateS_zero_eigenvalue (V := Λ),
      sublatticeSpinSquaredS_mulVec_allAlignedStateS_zero N A,
      sublatticeSpinSquaredS_mulVec_allAlignedStateS_zero N (fun x => ! A x)]
  rw [← sub_smul, ← sub_smul]

/-- Cardinality of the `A`-sublattice (number of sites with `A x = true`). -/
private noncomputable def sublatticeCardS (A : Λ → Bool) : ℕ :=
  (Finset.univ.filter (fun x : Λ => A x = true)).card

/-- Cardinality identity: `|Λ| = |A| + |¬A|` for any sublattice
indicator `A : Λ → Bool`. -/
private theorem sublatticeCardS_add_complement (A : Λ → Bool) :
    sublatticeCardS A + sublatticeCardS (fun x => ! A x) = Fintype.card Λ := by
  unfold sublatticeCardS
  have hfilter : Finset.univ.filter (fun x : Λ => (! A x) = true) =
      Finset.univ.filter (fun x : Λ => ¬ (A x = true)) := by
    ext x; simp [Bool.not_eq_true]
  rw [hfilter, Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun x : Λ => A x = true)]
  exact Finset.card_univ

/-! ## Eigenvalue on the all-down state -/

/-- **Spin-`S` toy Hamiltonian eigenvalue on the all-down state**.
Symmetric to PR #1060 for the all-up state — same eigenvalue formula
since both `|σ_⊤⟩` and `|σ_⊥⟩` sit in the maximum-spin irreps of all
three Casimirs:

  `Ĥ_toy_S · |σ_⊥⟩ =
    ((|Λ|·N/2)(|Λ|·N/2+1) − (|A|·N/2)(|A|·N/2+1) − (|¬A|·N/2)(|¬A|·N/2+1)) · |σ_⊥⟩`. -/
theorem heisenbergToyHamiltonianS_mulVec_allAlignedStateS_last
    [Nonempty Λ] (A : Λ → Bool) :
    (heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
        (allAlignedStateS Λ N (Fin.last N)) =
      (((Fintype.card Λ : ℂ) * (N : ℂ) / 2 *
          ((Fintype.card Λ : ℂ) * (N : ℂ) / 2 + 1))
        - (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2) *
            (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                ((N : ℂ) / 2) + 1))
        - (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2) *
            (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                ((N : ℂ) / 2) + 1))) •
        allAlignedStateS Λ N (Fin.last N) := by
  rw [heisenbergToyHamiltonianS_eq_casimir_diff N A]
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec]
  rw [totalSpinSSquared_mulVec_allAlignedStateS_last_eigenvalue (V := Λ),
      sublatticeSpinSquaredS_mulVec_allAlignedStateS_last N A,
      sublatticeSpinSquaredS_mulVec_allAlignedStateS_last N (fun x => ! A x)]
  rw [← sub_smul, ← sub_smul]

/-- **Simplified spin-`S` toy Hamiltonian eigenvalue on the all-down
state**: `Ĥ_toy_S · |σ_⊥⟩ = (|A|·|¬A|·N²/2) · |σ_⊥⟩`. Same simplified
form as PR #1061 for the all-up state. -/
theorem heisenbergToyHamiltonianS_mulVec_allAlignedStateS_last_simplified
    [Nonempty Λ] (A : Λ → Bool) :
    (heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
        (allAlignedStateS Λ N (Fin.last N)) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          ((N : ℂ) * (N : ℂ)) / 2) •
        allAlignedStateS Λ N (Fin.last N) := by
  rw [heisenbergToyHamiltonianS_mulVec_allAlignedStateS_last N A]
  congr 1
  have hsum := sublatticeCardS_add_complement (Λ := Λ) A
  unfold sublatticeCardS at hsum
  have hsumℂ : (Fintype.card Λ : ℂ) =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) +
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) := by
    have := congrArg (Nat.cast (R := ℂ)) hsum.symm
    push_cast at this
    exact this
  rw [hsumℂ]
  ring

/-- **Simplified `Ĥ_toy_S` eigenvalue on the all-up state**:
`Ĥ_toy_S · |σ_⊤⟩ = (|A|·|¬A|·N²/2) · |σ_⊤⟩`.

Algebraic simplification of `heisenbergToyHamiltonianS_mulVec_allAlignedStateS_zero`
(PR #1060) via `|Λ| = |A| + |¬A|`. Setting `a = |A|·N/2, b = |¬A|·N/2`:

```
  (a + b)(a + b + 1) − a(a + 1) − b(b + 1) = 2ab,
```

so the eigenvalue is `2·(|A|·N/2)·(|¬A|·N/2) = |A|·|¬A|·N²/2`.
Specialises to spin-`1/2` (`N = 1`) eigenvalue `|A|·|¬A|/2`. The
eigenvalue is non-negative for any bipartite lattice and strictly
positive when both sublattices are non-empty. -/
theorem heisenbergToyHamiltonianS_mulVec_allAlignedStateS_zero_simplified
    [Nonempty Λ] (A : Λ → Bool) :
    (heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
        (allAlignedStateS Λ N (0 : Fin (N + 1))) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          ((N : ℂ) * (N : ℂ)) / 2) •
        allAlignedStateS Λ N (0 : Fin (N + 1)) := by
  rw [heisenbergToyHamiltonianS_mulVec_allAlignedStateS_zero N A]
  congr 1
  -- Cardinality identity in ℂ: |Λ| = |A| + |¬A|.
  have hsum := sublatticeCardS_add_complement (Λ := Λ) A
  unfold sublatticeCardS at hsum
  have hsumℂ : (Fintype.card Λ : ℂ) =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) +
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) := by
    have := congrArg (Nat.cast (R := ℂ)) hsum.symm
    push_cast at this
    exact this
  rw [hsumℂ]
  ring

end LatticeSystem.Quantum
