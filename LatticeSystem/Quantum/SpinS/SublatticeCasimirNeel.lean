import LatticeSystem.Quantum.SpinS.SublatticeSpinDot
import LatticeSystem.Quantum.SpinS.Magnetization

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

end LatticeSystem.Quantum
