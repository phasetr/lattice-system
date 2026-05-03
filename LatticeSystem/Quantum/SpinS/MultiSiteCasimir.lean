import LatticeSystem.Quantum.SpinS.TotalSquared
import LatticeSystem.Quantum.SpinS.MultiSiteDot

/-!
# Multi-site spin-`S` Casimir decomposition (Tasaki §2.4 / §2.5 setup)

This file proves the **diagonal/off-diagonal decomposition** of the
total spin-`S` Casimir `(Ŝ_tot)²` on the multi-site Hilbert space:

  `(Ŝ_tot)² = Σ_x (Ŝ_x · Ŝ_x) + Σ_{x ≠ y} (Ŝ_x · Ŝ_y)
           = |Λ| · (N(N+2)/4) · 1 + Σ_{x ≠ y} (Ŝ_x · Ŝ_y)`

starting from the existing identity
`totalSpinSSquared_eq_sum_spinSDot`. Specialising to `Λ = Fin 2`
gives the **two-site Casimir-Heisenberg identity**

  `(Ŝ_tot)² = (N(N+2)/2) · 1 + 2 · (Ŝ_0 · Ŝ_1)`

which solves for `Ŝ_0 · Ŝ_1` as a polynomial in `(Ŝ_tot)²` — the
operator-level form of Tasaki Problem 2.5.a in the single-bond
(`z = 1`) case.

Tracked as part of Tasaki §2.5 spin-`S` infrastructure (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## General multi-site decomposition -/

/-- **Diagonal/off-diagonal split** of the total spin-`S` Casimir:
`(Ŝ_tot)² = Σ_x (Ŝ_x · Ŝ_x) + Σ_{x ≠ y} (Ŝ_x · Ŝ_y)`. -/
theorem totalSpinSSquared_eq_diag_plus_offdiag (N : ℕ) :
    (totalSpinSSquared Λ N : ManyBodyOpS Λ N) =
      (∑ x : Λ, spinSDot x x N) +
      (∑ x : Λ, ∑ y ∈ Finset.univ.erase x, spinSDot x y N) := by
  rw [totalSpinSSquared_eq_sum_spinSDot]
  -- Split each inner sum into y = x and y ≠ x.
  rw [show (∑ x : Λ, ∑ y : Λ, spinSDot x y N) =
        ∑ x : Λ, (spinSDot x x N + ∑ y ∈ Finset.univ.erase x, spinSDot x y N) from by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x), add_comm]]
  rw [Finset.sum_add_distrib]

/-- **Per-site Casimir substituted**: `(Ŝ_tot)² = |Λ| · (N(N+2)/4) · 1
+ Σ_{x ≠ y} (Ŝ_x · Ŝ_y)`. -/
theorem totalSpinSSquared_eq_constMul_one_plus_offdiag (N : ℕ) :
    (totalSpinSSquared Λ N : ManyBodyOpS Λ N) =
      ((Fintype.card Λ : ℂ) * ((N : ℂ) * (N + 2) / 4)) • 1 +
      (∑ x : Λ, ∑ y ∈ Finset.univ.erase x, spinSDot x y N) := by
  rw [totalSpinSSquared_eq_diag_plus_offdiag, sum_spinSDot_self]

/-! ## Two-site specialisation (`Λ = Fin 2`) -/

/-- For `Λ = Fin 2`, the off-diagonal sum collapses to `2 · (Ŝ_0 · Ŝ_1)`
by `spinSDot_comm`. -/
theorem sum_offdiag_spinSDot_fin_two (N : ℕ) :
    (∑ x : Fin 2, ∑ y ∈ Finset.univ.erase x, spinSDot x y N : ManyBodyOpS (Fin 2) N) =
      2 • (spinSDot (0 : Fin 2) 1 N) := by
  -- Expand the sum over Fin 2 as x = 0 and x = 1.
  rw [show (∑ x : Fin 2, ∑ y ∈ Finset.univ.erase x, spinSDot x y N
        : ManyBodyOpS (Fin 2) N) =
        (∑ y ∈ Finset.univ.erase (0 : Fin 2), spinSDot 0 y N) +
        (∑ y ∈ Finset.univ.erase (1 : Fin 2), spinSDot 1 y N) from by
    rw [Fin.sum_univ_two]]
  -- For x = 0, the erased set is {1}.
  rw [show (Finset.univ.erase (0 : Fin 2)) = {1} from by
    ext y
    fin_cases y <;> simp]
  rw [show (Finset.univ.erase (1 : Fin 2)) = {0} from by
    ext y
    fin_cases y <;> simp]
  rw [Finset.sum_singleton, Finset.sum_singleton]
  rw [spinSDot_comm 1 0]
  rw [show ((2 : ℕ) • spinSDot (0 : Fin 2) 1 N : ManyBodyOpS (Fin 2) N) =
        spinSDot 0 1 N + spinSDot 0 1 N from by
    rw [two_smul]]

/-- **Two-site Casimir identity** (`Λ = Fin 2`): the spin-`S` total
Casimir on two sites decomposes as

  `(Ŝ_tot)² = (N(N+2)/2) · 1 + 2 · (Ŝ_0 · Ŝ_1)`. -/
theorem totalSpinSSquared_fin_two (N : ℕ) :
    (totalSpinSSquared (Fin 2) N : ManyBodyOpS (Fin 2) N) =
      (((N : ℂ) * (N + 2) / 2)) • 1 +
      (2 : ℕ) • spinSDot (0 : Fin 2) 1 N := by
  rw [totalSpinSSquared_eq_constMul_one_plus_offdiag,
    sum_offdiag_spinSDot_fin_two]
  -- (|Fin 2| : ℂ) · (N(N+2)/4) = 2 · (N(N+2)/4) = (N(N+2)/2)
  congr 1
  rw [show ((Fintype.card (Fin 2) : ℂ) * ((N : ℂ) * (N + 2) / 4)) =
        ((N : ℂ) * (N + 2) / 2) from by
    rw [Fintype.card_fin]
    push_cast
    ring]

/-- **Solving for `Ŝ_0 · Ŝ_1`** in the two-site Casimir identity:

  `2 · (Ŝ_0 · Ŝ_1) = (Ŝ_tot)² - (N(N+2)/2) · 1`.

This is the operator-level form of Tasaki Problem 2.5.a in the
single-bond (`z = 1`) case: every eigenvalue of `Ŝ_0 · Ŝ_1` equals
`((Ŝ_tot)²-eigenvalue - N(N+2)/2) / 2`, hence the minimum eigenvalue
of `Ŝ_0 · Ŝ_1` is reached at the minimum eigenvalue of `(Ŝ_tot)²`
(the singlet, with `(Ŝ_tot)²-eigenvalue = 0`), giving GS energy
`-(N(N+2)/4) = -S(S+1)`. -/
theorem two_smul_spinSDot_fin_two (N : ℕ) :
    ((2 : ℕ) • spinSDot (0 : Fin 2) 1 N : ManyBodyOpS (Fin 2) N) =
      (totalSpinSSquared (Fin 2) N) -
      (((N : ℂ) * (N + 2) / 2)) • 1 := by
  rw [totalSpinSSquared_fin_two]
  abel

/-- **Literal scalar form** of the two-site Casimir-Heisenberg
identity (Tasaki Problem 2.5.a single-bond, `z = 1`):

  `Ŝ_0 · Ŝ_1 = (1/2) · (Ŝ_tot)² − (N(N+2)/4) · 1`.

Direct corollary of `two_smul_spinSDot_fin_two` after applying `(1/2) •`
to both sides. -/
theorem spinSDot_fin_two_eq (N : ℕ) :
    (spinSDot (0 : Fin 2) 1 N : ManyBodyOpS (Fin 2) N) =
      ((1 / 2 : ℂ)) • totalSpinSSquared (Fin 2) N -
      (((N : ℂ) * (N + 2) / 4)) • 1 := by
  -- Apply (1/2 : ℂ) • _ to both sides of `two_smul_spinSDot_fin_two`.
  have h := two_smul_spinSDot_fin_two N
  have h' : ((1 / 2 : ℂ) • ((2 : ℕ) • spinSDot (0 : Fin 2) 1 N) : ManyBodyOpS (Fin 2) N) =
      (1 / 2 : ℂ) • (totalSpinSSquared (Fin 2) N -
        (((N : ℂ) * (N + 2) / 2)) • 1) :=
    congrArg ((1 / 2 : ℂ) • ·) h
  -- Simplify LHS: (1/2) • (2 • A) = A.
  have hLHS : ((1 / 2 : ℂ) • ((2 : ℕ) • spinSDot (0 : Fin 2) 1 N) : ManyBodyOpS (Fin 2) N) =
      spinSDot (0 : Fin 2) 1 N := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      show ((1 / 2 : ℂ) * (2 : ℕ)) = 1 from by push_cast; ring, one_smul]
  -- Simplify RHS: (1/2) • ((Ŝ_tot)² - c • 1) = (1/2) • (Ŝ_tot)² - (c/2) • 1.
  have hRHS : ((1 / 2 : ℂ) • (totalSpinSSquared (Fin 2) N -
        (((N : ℂ) * (N + 2) / 2)) • 1) : ManyBodyOpS (Fin 2) N) =
      (1 / 2 : ℂ) • totalSpinSSquared (Fin 2) N -
      (((N : ℂ) * (N + 2) / 4)) • 1 := by
    rw [smul_sub, smul_smul]
    congr 2
    ring
  rw [hLHS, hRHS] at h'
  exact h'

end LatticeSystem.Quantum
