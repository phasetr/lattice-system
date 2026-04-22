/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.TotalSpin
import LatticeSystem.Quantum.SpinHalfRotation
import LatticeSystem.Quantum.SpinHalfRotation.Conjugation

/-!
# Total spin rotation operators (Tasaki §2.2 (2.2.11))

The global rotation operator
`Û^(α)_θ_tot = exp(-iθ Ŝ_tot^(α))` and its specialisations:
- π-rotation,
- general-θ rotation,
- Tasaki Problems 2.2.a / 2.2.b (cyclic axes, two-spin),
- two-spin explicit forms,
- matrix exponential identification (`_eq_exp`),
- generic operator-level SU(2) invariance (#2.2.12 → #2.2.13),
- unitarity and conjugation forms.

(Refactor Phase 2 PR 18 — first TotalSpin extraction, plan v4 §3.1.)
-/

namespace LatticeSystem.Quantum

open Matrix

variable (Λ : Type*) [Fintype Λ] [DecidableEq Λ]

/-! ## Global π-rotation operator (Tasaki eq (2.2.11) at θ = π)

Distinct-site `onSite` embeddings commute (`onSite_mul_onSite_of_ne`),
so we can form `Û^(α)_π_tot := ∏_{x ∈ Λ} Û^(α)_π_x` as a
`Finset.noncommProd`. -/

/-- Total π-rotation about axis 1: `Û^(1)_π_tot`. -/
noncomputable def totalSpinHalfRot1Pi : ManyBodyOp Λ :=
  (Finset.univ : Finset Λ).noncommProd
    (fun x => onSite x (spinHalfRot1 Real.pi))
    (fun _ _ _ _ hxy => onSite_mul_onSite_of_ne hxy _ _)

/-- Total π-rotation about axis 2: `Û^(2)_π_tot`. -/
noncomputable def totalSpinHalfRot2Pi : ManyBodyOp Λ :=
  (Finset.univ : Finset Λ).noncommProd
    (fun x => onSite x (spinHalfRot2 Real.pi))
    (fun _ _ _ _ hxy => onSite_mul_onSite_of_ne hxy _ _)

/-- Total π-rotation about axis 3: `Û^(3)_π_tot`. -/
noncomputable def totalSpinHalfRot3Pi : ManyBodyOp Λ :=
  (Finset.univ : Finset Λ).noncommProd
    (fun x => onSite x (spinHalfRot3 Real.pi))
    (fun _ _ _ _ hxy => onSite_mul_onSite_of_ne hxy _ _)

/-! ## General-θ global rotation (Tasaki eq (2.2.11)) -/

/-- Total rotation about axis 1 by angle `θ`: `Û^(1)_θ_tot := ∏_x Û^(1)_θ_x`. -/
noncomputable def totalSpinHalfRot1 (θ : ℝ) : ManyBodyOp Λ :=
  (Finset.univ : Finset Λ).noncommProd
    (fun x => onSite x (spinHalfRot1 θ))
    (fun _ _ _ _ hxy => onSite_mul_onSite_of_ne hxy _ _)

/-- Total rotation about axis 2 by angle `θ`. -/
noncomputable def totalSpinHalfRot2 (θ : ℝ) : ManyBodyOp Λ :=
  (Finset.univ : Finset Λ).noncommProd
    (fun x => onSite x (spinHalfRot2 θ))
    (fun _ _ _ _ hxy => onSite_mul_onSite_of_ne hxy _ _)

/-- Total rotation about axis 3 by angle `θ`. -/
noncomputable def totalSpinHalfRot3 (θ : ℝ) : ManyBodyOp Λ :=
  (Finset.univ : Finset Λ).noncommProd
    (fun x => onSite x (spinHalfRot3 θ))
    (fun _ _ _ _ hxy => onSite_mul_onSite_of_ne hxy _ _)

/-- `Û^(α)_π_tot` is a special case of `Û^(α)_θ_tot` at `θ = π`. -/
theorem totalSpinHalfRot1Pi_eq : totalSpinHalfRot1Pi Λ = totalSpinHalfRot1 Λ Real.pi := rfl
/-- `Û^(2)_π_tot` is a special case of `Û^(2)_θ_tot` at `θ = π`. -/
theorem totalSpinHalfRot2Pi_eq : totalSpinHalfRot2Pi Λ = totalSpinHalfRot2 Λ Real.pi := rfl
/-- `Û^(3)_π_tot` is a special case of `Û^(3)_θ_tot` at `θ = π`. -/
theorem totalSpinHalfRot3Pi_eq : totalSpinHalfRot3Pi Λ = totalSpinHalfRot3 Λ Real.pi := rfl

/-! ## Tasaki Problem 2.2.a: total π-rotation product (in cyclic axes) -/

/-- Tasaki Problem 2.2.a, axes (1,2)→3:
`Û^(1)_π_tot · Û^(2)_π_tot = Û^(3)_π_tot`. Derived from
the single-site relation `Û^(1)_π · Û^(2)_π = Û^(3)_π` (Tasaki eq.
(2.1.29)) lifted by `Finset.noncommProd_mul_distrib`. -/
theorem totalSpinHalfRot1Pi_mul_totalSpinHalfRot2Pi :
    totalSpinHalfRot1Pi Λ * totalSpinHalfRot2Pi Λ = totalSpinHalfRot3Pi Λ := by
  unfold totalSpinHalfRot1Pi totalSpinHalfRot2Pi totalSpinHalfRot3Pi
  rw [← Finset.noncommProd_mul_distrib
    (s := (Finset.univ : Finset Λ))
    (f := fun x : Λ => onSite x (spinHalfRot1 Real.pi))
    (g := fun x : Λ => onSite x (spinHalfRot2 Real.pi))
    (comm_ff := fun _ _ _ _ hxy => onSite_mul_onSite_of_ne hxy _ _)
    (comm_gg := fun _ _ _ _ hxy => onSite_mul_onSite_of_ne hxy _ _)
    (comm_gf := fun _ _ _ _ hxy => onSite_mul_onSite_of_ne hxy _ _)]
  refine Finset.noncommProd_congr rfl ?_ _
  intros x _
  change onSite x (spinHalfRot1 Real.pi) * onSite x (spinHalfRot2 Real.pi) =
       onSite x (spinHalfRot3 Real.pi)
  rw [onSite_mul_onSite_same, spinHalfRot1_pi_mul_spinHalfRot2_pi]

/-- Tasaki Problem 2.2.a, axes (2,3)→1:
`Û^(2)_π_tot · Û^(3)_π_tot = Û^(1)_π_tot`. -/
theorem totalSpinHalfRot2Pi_mul_totalSpinHalfRot3Pi :
    totalSpinHalfRot2Pi Λ * totalSpinHalfRot3Pi Λ = totalSpinHalfRot1Pi Λ := by
  unfold totalSpinHalfRot1Pi totalSpinHalfRot2Pi totalSpinHalfRot3Pi
  rw [← Finset.noncommProd_mul_distrib
    (s := (Finset.univ : Finset Λ))
    (f := fun x : Λ => onSite x (spinHalfRot2 Real.pi))
    (g := fun x : Λ => onSite x (spinHalfRot3 Real.pi))
    (comm_ff := fun _ _ _ _ hxy => onSite_mul_onSite_of_ne hxy _ _)
    (comm_gg := fun _ _ _ _ hxy => onSite_mul_onSite_of_ne hxy _ _)
    (comm_gf := fun _ _ _ _ hxy => onSite_mul_onSite_of_ne hxy _ _)]
  refine Finset.noncommProd_congr rfl ?_ _
  intros x _
  change onSite x (spinHalfRot2 Real.pi) * onSite x (spinHalfRot3 Real.pi) =
       onSite x (spinHalfRot1 Real.pi)
  rw [onSite_mul_onSite_same, spinHalfRot2_pi_mul_spinHalfRot3_pi]

/-- Tasaki Problem 2.2.a, axes (3,1)→2:
`Û^(3)_π_tot · Û^(1)_π_tot = Û^(2)_π_tot`. -/
theorem totalSpinHalfRot3Pi_mul_totalSpinHalfRot1Pi :
    totalSpinHalfRot3Pi Λ * totalSpinHalfRot1Pi Λ = totalSpinHalfRot2Pi Λ := by
  unfold totalSpinHalfRot1Pi totalSpinHalfRot2Pi totalSpinHalfRot3Pi
  rw [← Finset.noncommProd_mul_distrib
    (s := (Finset.univ : Finset Λ))
    (f := fun x : Λ => onSite x (spinHalfRot3 Real.pi))
    (g := fun x : Λ => onSite x (spinHalfRot1 Real.pi))
    (comm_ff := fun _ _ _ _ hxy => onSite_mul_onSite_of_ne hxy _ _)
    (comm_gg := fun _ _ _ _ hxy => onSite_mul_onSite_of_ne hxy _ _)
    (comm_gf := fun _ _ _ _ hxy => onSite_mul_onSite_of_ne hxy _ _)]
  refine Finset.noncommProd_congr rfl ?_ _
  intros x _
  change onSite x (spinHalfRot3 Real.pi) * onSite x (spinHalfRot1 Real.pi) =
       onSite x (spinHalfRot2 Real.pi)
  rw [onSite_mul_onSite_same, spinHalfRot3_pi_mul_spinHalfRot1_pi]

/-- `Û^(α)_0_tot = 1`: the identity rotation on the many-body space. -/
theorem totalSpinHalfRot1_zero : totalSpinHalfRot1 Λ 0 = 1 := by
  unfold totalSpinHalfRot1
  simp_rw [spinHalfRot1_zero, onSite_one]
  exact (Finset.noncommProd_eq_pow_card _ _ _ 1 (fun _ _ => rfl)).trans (one_pow _)

/-- `Û^(2)_0_tot = 1`. -/
theorem totalSpinHalfRot2_zero : totalSpinHalfRot2 Λ 0 = 1 := by
  unfold totalSpinHalfRot2
  simp_rw [spinHalfRot2_zero, onSite_one]
  exact (Finset.noncommProd_eq_pow_card _ _ _ 1 (fun _ _ => rfl)).trans (one_pow _)

/-- `Û^(3)_0_tot = 1`. -/
theorem totalSpinHalfRot3_zero : totalSpinHalfRot3 Λ 0 = 1 := by
  unfold totalSpinHalfRot3
  simp_rw [spinHalfRot3_zero, onSite_one]
  exact (Finset.noncommProd_eq_pow_card _ _ _ 1 (fun _ _ => rfl)).trans (one_pow _)

/-! ## Site embedding as a ring homomorphism

The site-embedding `onSite x` preserves all ring operations, so it
extends to a `RingHom`. -/

/-- `onSite x` as a ring homomorphism. -/
noncomputable def onSiteRingHom (x : Λ) :
    Matrix (Fin 2) (Fin 2) ℂ →+* ManyBodyOp Λ where
  toFun := fun A => onSite x A
  map_one' := onSite_one x
  map_mul' := fun A B => (onSite_mul_onSite_same x A B).symm
  map_zero' := onSite_zero x
  map_add' := fun A B => onSite_add x A B

/-- `onSite x` as a `ℂ`-linear map. -/
noncomputable def onSiteLinearMap (x : Λ) :
    Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] ManyBodyOp Λ where
  toFun := fun A => onSite x A
  map_add' := fun A B => onSite_add x A B
  map_smul' := fun c A => onSite_smul x c A

/-- `onSite x` is continuous (as a ℂ-linear map between finite-dimensional
normed spaces). -/
theorem continuous_onSite (x : Λ) : Continuous (fun A : Matrix (Fin 2) (Fin 2) ℂ =>
    (onSite x A : ManyBodyOp Λ)) :=
  (onSiteLinearMap (Λ := Λ) x).continuous_of_finiteDimensional

/-- `(onSite x A)^k = onSite x (A^k)`. Direct induction using
`onSite_one` (base) and `onSite_mul_onSite_same` (step). -/
theorem onSite_pow (x : Λ) (A : Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) :
    ((onSite x A : ManyBodyOp Λ))^k = onSite x (A^k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, onSite_one]
  | succ k ih => rw [pow_succ, pow_succ, ih, onSite_mul_onSite_same]

/-! ## Two-spin explicit total π-rotation (Tasaki Problem 2.2.b) -/

/-- For two sites, the total π-rotation about axis 1 factors as the
product over site 0 and site 1. -/
theorem totalSpinHalfRot1Pi_two_site :
    totalSpinHalfRot1Pi (Fin 2) =
      onSite (0 : Fin 2) (spinHalfRot1 Real.pi) *
        onSite (1 : Fin 2) (spinHalfRot1 Real.pi) := by
  unfold totalSpinHalfRot1Pi
  show ((Finset.univ : Finset (Fin 2)).noncommProd _ _ : ManyBodyOp (Fin 2)) = _
  simp [show (Finset.univ : Finset (Fin 2)) = insert 0 {1} from by decide,
    Finset.noncommProd_insert_of_notMem, Finset.noncommProd_singleton]

/-- For two sites, the total π-rotation about axis 2 factors as the
product over site 0 and site 1. -/
theorem totalSpinHalfRot2Pi_two_site :
    totalSpinHalfRot2Pi (Fin 2) =
      onSite (0 : Fin 2) (spinHalfRot2 Real.pi) *
        onSite (1 : Fin 2) (spinHalfRot2 Real.pi) := by
  unfold totalSpinHalfRot2Pi
  show ((Finset.univ : Finset (Fin 2)).noncommProd _ _ : ManyBodyOp (Fin 2)) = _
  simp [show (Finset.univ : Finset (Fin 2)) = insert 0 {1} from by decide,
    Finset.noncommProd_insert_of_notMem, Finset.noncommProd_singleton]

/-- For two sites, the total π-rotation about axis 3 factors as the
product over site 0 and site 1. -/
theorem totalSpinHalfRot3Pi_two_site :
    totalSpinHalfRot3Pi (Fin 2) =
      onSite (0 : Fin 2) (spinHalfRot3 Real.pi) *
        onSite (1 : Fin 2) (spinHalfRot3 Real.pi) := by
  unfold totalSpinHalfRot3Pi
  show ((Finset.univ : Finset (Fin 2)).noncommProd _ _ : ManyBodyOp (Fin 2)) = _
  simp [show (Finset.univ : Finset (Fin 2)) = insert 0 {1} from by decide,
    Finset.noncommProd_insert_of_notMem, Finset.noncommProd_singleton]

/-! ## Two-spin explicit total general-θ rotation -/

/-- For two sites, the total `θ`-rotation about axis 1 factors as the
product over site 0 and site 1. -/
theorem totalSpinHalfRot1_two_site (θ : ℝ) :
    totalSpinHalfRot1 (Fin 2) θ =
      onSite (0 : Fin 2) (spinHalfRot1 θ) *
        onSite (1 : Fin 2) (spinHalfRot1 θ) := by
  unfold totalSpinHalfRot1
  show ((Finset.univ : Finset (Fin 2)).noncommProd _ _ : ManyBodyOp (Fin 2)) = _
  simp [show (Finset.univ : Finset (Fin 2)) = insert 0 {1} from by decide,
    Finset.noncommProd_insert_of_notMem, Finset.noncommProd_singleton]

/-- For two sites, the total `θ`-rotation about axis 2 factors as the
product over site 0 and site 1. -/
theorem totalSpinHalfRot2_two_site (θ : ℝ) :
    totalSpinHalfRot2 (Fin 2) θ =
      onSite (0 : Fin 2) (spinHalfRot2 θ) *
        onSite (1 : Fin 2) (spinHalfRot2 θ) := by
  unfold totalSpinHalfRot2
  show ((Finset.univ : Finset (Fin 2)).noncommProd _ _ : ManyBodyOp (Fin 2)) = _
  simp [show (Finset.univ : Finset (Fin 2)) = insert 0 {1} from by decide,
    Finset.noncommProd_insert_of_notMem, Finset.noncommProd_singleton]

/-- For two sites, the total `θ`-rotation about axis 3 factors as the
product over site 0 and site 1. -/
theorem totalSpinHalfRot3_two_site (θ : ℝ) :
    totalSpinHalfRot3 (Fin 2) θ =
      onSite (0 : Fin 2) (spinHalfRot3 θ) *
        onSite (1 : Fin 2) (spinHalfRot3 θ) := by
  unfold totalSpinHalfRot3
  show ((Finset.univ : Finset (Fin 2)).noncommProd _ _ : ManyBodyOp (Fin 2)) = _
  simp [show (Finset.univ : Finset (Fin 2)) = insert 0 {1} from by decide,
    Finset.noncommProd_insert_of_notMem, Finset.noncommProd_singleton]

/-! ## Total rotation as matrix exponential (Tasaki §2.2 eq (2.2.11))

The defining identity
`Û^(α)_θ_tot = exp(-iθ Ŝ_tot^(α)) = ∏_x exp(-iθ Ŝ_x^(α))`
(Tasaki *Physics and Mathematics of Quantum Many-Body Systems*, p.22,
eq. (2.2.11)). The proof composes:
1. `spinHalfRot α θ = exp(-(I·θ) • spinHalfOp α)`
   (P1e'', `spinHalfRot{1,2,3}_eq_exp`).
2. `onSite x (exp B) = exp (onSite x B)` via
   `NormedSpace.map_exp` applied to `onSiteRingHom`. This requires
   bridging the canonical Pi-product matrix topology with the
   Frobenius normed-ring structure: we install Frobenius normed
   instances locally via `letI` and pull continuity from
   `LinearMap.continuous_of_finiteDimensional`.
3. `exp(Σ_x onSite x B) = ∏_x exp(onSite x B)` via
   `Matrix.exp_sum_of_commute` (which hides the norm choice
   internally). -/

/-- `onSite x` commutes with the matrix exponential:
`onSite x (exp A) = exp (onSite x A)`. The key bridge between
single-site and many-body matrix exponentials.

Bridges the canonical Pi-product matrix topology with the Frobenius
normed-ring structure: install Frobenius `NormedRing`/`NormedAlgebra`
locally via `letI`, derive `CompleteSpace` from `FiniteDimensional`,
pull continuity from `LinearMap.continuous_of_finiteDimensional`, and
finally invoke `NormedSpace.map_exp` with all instances passed
explicitly (the implicit unification fails to bridge between the
default and Frobenius topologies). -/
theorem onSite_exp_eq_exp_onSite (x : Λ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    onSite x (NormedSpace.exp A) =
      NormedSpace.exp (onSite x A : ManyBodyOp Λ) := by
  letI iAddSrc : NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) :=
    Matrix.frobeniusNormedAddCommGroup
  letI _iSpaceSrc : NormedSpace ℂ (Matrix (Fin 2) (Fin 2) ℂ) :=
    Matrix.frobeniusNormedSpace
  letI iRingSrc : NormedRing (Matrix (Fin 2) (Fin 2) ℂ) :=
    Matrix.frobeniusNormedRing
  letI iAlgSrc : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
    Matrix.frobeniusNormedAlgebra
  letI _iAddTgt : NormedAddCommGroup (ManyBodyOp Λ) :=
    Matrix.frobeniusNormedAddCommGroup
  letI _iSpaceTgt : NormedSpace ℂ (ManyBodyOp Λ) :=
    Matrix.frobeniusNormedSpace
  letI iRingTgt : NormedRing (ManyBodyOp Λ) :=
    Matrix.frobeniusNormedRing
  letI iAlgTgt : Algebra ℚ (ManyBodyOp Λ) :=
    (Matrix.frobeniusNormedAlgebra (R := ℚ)).toAlgebra
  haveI iComplSrc : CompleteSpace (Matrix (Fin 2) (Fin 2) ℂ) :=
    FiniteDimensional.complete ℂ (Matrix (Fin 2) (Fin 2) ℂ)
  have hcont : Continuous (onSiteRingHom Λ x) :=
    (onSiteLinearMap (Λ := Λ) x).continuous_of_finiteDimensional
  -- Implicit unification of the `CompleteSpace` instance fails when we just
  -- write `NormedSpace.map_exp ...`, so we pass everything explicitly.
  exact @NormedSpace.map_exp (Matrix (Fin 2) (Fin 2) ℂ) (ManyBodyOp Λ)
    iRingSrc iAlgSrc iComplSrc iRingTgt iAlgTgt _ _ _
    (onSiteRingHom Λ x) hcont A
  -- (Lemma `iAddSrc` is referenced by the `NormedRing` synth path even though
  -- it's not passed positionally, so `letI` keeps it in scope.)

/-- Generic per-axis helper for Tasaki eq. (2.2.11): when the single-site
rotation `U θ` equals the matrix exponential of `(-(I·θ)) • S` for some
spin operator `S`, then the noncommProd over sites of `onSite x (U θ)`
equals the matrix exponential of `(-(I·θ)) • Σ_x onSite x S`. -/
private theorem totalRot_eq_exp_aux
    (S : Matrix (Fin 2) (Fin 2) ℂ) (U : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hUeq : ∀ θ : ℝ, U θ = NormedSpace.exp ((-(Complex.I * (θ : ℂ))) • S))
    (θ : ℝ) :
    ((Finset.univ : Finset Λ).noncommProd (fun x => onSite x (U θ))
        (fun _ _ _ _ hxy => onSite_mul_onSite_of_ne hxy _ _) :
      ManyBodyOp Λ) =
      NormedSpace.exp ((-(Complex.I * (θ : ℂ))) •
        (∑ x : Λ, onSite x S : ManyBodyOp Λ)) := by
  rw [Finset.smul_sum]
  simp_rw [← onSite_smul]
  rw [Matrix.exp_sum_of_commute (Finset.univ : Finset Λ)
        (fun x => (onSite x ((-(Complex.I * (θ : ℂ))) • S) : ManyBodyOp Λ))
        (fun _ _ _ _ hxy => onSite_mul_onSite_of_ne hxy _ _)]
  refine Finset.noncommProd_congr rfl ?_ _
  intros x _
  rw [← onSite_exp_eq_exp_onSite Λ x ((-(Complex.I * (θ : ℂ))) • S), ← hUeq]

/-- Tasaki §2.2 eq (2.2.11), axis 1:
`Û^(1)_θ_tot = exp(-iθ Ŝ_tot^(1))`. -/
theorem totalSpinHalfRot1_eq_exp (θ : ℝ) :
    totalSpinHalfRot1 Λ θ =
      NormedSpace.exp ((-(Complex.I * (θ : ℂ))) • totalSpinHalfOp1 Λ) :=
  totalRot_eq_exp_aux Λ spinHalfOp1 spinHalfRot1 spinHalfRot1_eq_exp θ

/-- Tasaki §2.2 eq (2.2.11), axis 2. -/
theorem totalSpinHalfRot2_eq_exp (θ : ℝ) :
    totalSpinHalfRot2 Λ θ =
      NormedSpace.exp ((-(Complex.I * (θ : ℂ))) • totalSpinHalfOp2 Λ) :=
  totalRot_eq_exp_aux Λ spinHalfOp2 spinHalfRot2 spinHalfRot2_eq_exp θ

/-- Tasaki §2.2 eq (2.2.11), axis 3. -/
theorem totalSpinHalfRot3_eq_exp (θ : ℝ) :
    totalSpinHalfRot3 Λ θ =
      NormedSpace.exp ((-(Complex.I * (θ : ℂ))) • totalSpinHalfOp3 Λ) :=
  totalRot_eq_exp_aux Λ spinHalfOp3 spinHalfRot3 spinHalfRot3_eq_exp θ

/-! ## Generic operator-level SU(2) invariance (Tasaki §2.2 (2.2.12) → (2.2.13))

If an operator `A` commutes with the total spin generator
`Ŝ_tot^(α)`, then `A` also commutes with the global rotation
`Û^(α)_θ_tot = exp(-iθ Ŝ_tot^(α))` (and therefore is invariant under
its conjugation).

The Heisenberg-type case (`A = Σ J(x,y) Ŝ_x · Ŝ_y`) was already
handled by `heisenbergHamiltonian_commutator_*` in `SpinDot.lean`;
here we provide the fully generic statement. -/

/-- If `A` commutes with `S` then `A` commutes with `exp(c • S)` for any scalar `c`. -/
private lemma totalSpinHalfRot_commute_aux (S : ManyBodyOp Λ) (θ : ℝ)
    (A : ManyBodyOp Λ) (h : Commute A S) :
    Commute A (NormedSpace.exp ((-(Complex.I * (θ : ℂ))) • S)) :=
  (h.smul_right _).exp_right

/-- Tasaki §2.2 (2.2.12) → (2.2.13), axis 1: any operator commuting
with `Ŝ_tot^(1)` also commutes with `Û^(1)_θ_tot`. -/
theorem totalSpinHalfRot1_commute_of_commute (θ : ℝ) (A : ManyBodyOp Λ)
    (h : Commute A (totalSpinHalfOp1 Λ)) :
    Commute A (totalSpinHalfRot1 Λ θ) := by
  rw [totalSpinHalfRot1_eq_exp]
  exact totalSpinHalfRot_commute_aux Λ _ θ A h

/-- Tasaki §2.2 (2.2.12) → (2.2.13), axis 2. -/
theorem totalSpinHalfRot2_commute_of_commute (θ : ℝ) (A : ManyBodyOp Λ)
    (h : Commute A (totalSpinHalfOp2 Λ)) :
    Commute A (totalSpinHalfRot2 Λ θ) := by
  rw [totalSpinHalfRot2_eq_exp]
  exact totalSpinHalfRot_commute_aux Λ _ θ A h

/-- Tasaki §2.2 (2.2.12) → (2.2.13), axis 3. -/
theorem totalSpinHalfRot3_commute_of_commute (θ : ℝ) (A : ManyBodyOp Λ)
    (h : Commute A (totalSpinHalfOp3 Λ)) :
    Commute A (totalSpinHalfRot3 Λ θ) := by
  rw [totalSpinHalfRot3_eq_exp]
  exact totalSpinHalfRot_commute_aux Λ _ θ A h

/-- Tasaki §2.2 (2.2.12) → (2.2.13), ladder version: `A` commuting
with `Ŝ^+_tot` also commutes with `exp(c • Ŝ^+_tot)` for any `c ∈ ℂ`
(direct application of `Commute.exp_right`; useful for U(1) symmetry
arguments together with the analogous `Ŝ^-_tot` statement). -/
theorem totalSpinHalfOpPlus_exp_commute_of_commute (c : ℂ) (A : ManyBodyOp Λ)
    (h : Commute A (totalSpinHalfOpPlus Λ)) :
    Commute A (NormedSpace.exp (c • totalSpinHalfOpPlus Λ)) :=
  (h.smul_right c).exp_right

/-- Same for the lowering operator. -/
theorem totalSpinHalfOpMinus_exp_commute_of_commute (c : ℂ) (A : ManyBodyOp Λ)
    (h : Commute A (totalSpinHalfOpMinus Λ)) :
    Commute A (NormedSpace.exp (c • totalSpinHalfOpMinus Λ)) :=
  (h.smul_right c).exp_right

/-! ## Unitarity and conjugation form of the global rotation

`Û^(α)_θ_tot = exp(-iθ Ŝ_tot^(α))` is unitary because `-iθ Ŝ_tot^(α)`
is skew-adjoint (Ŝ_tot^(α) is Hermitian, multiplied by an imaginary
scalar). From unitarity plus the commutativity established above, the
finite SU(2) invariance `(Û)† Â Û = Â` (Tasaki eq. (2.2.13))
follows directly. -/

omit [Fintype Λ] [DecidableEq Λ] in
/-- `(-(I·θ)) • S` is skew-adjoint when `S` is Hermitian. -/
private lemma neg_I_mul_real_smul_isHermitian_mem_skewAdjoint (θ : ℝ)
    {S : ManyBodyOp Λ} (hS : S.IsHermitian) :
    ((-(Complex.I * (θ : ℂ))) • S) ∈ skewAdjoint (ManyBodyOp Λ) := by
  rw [skewAdjoint.mem_iff, star_smul]
  have hSstar : (star S : ManyBodyOp Λ) = S := hS
  rw [hSstar]
  have hcoeff : star (-(Complex.I * (θ : ℂ))) = -(-(Complex.I * (θ : ℂ))) := by
    rw [star_neg, RCLike.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal,
      neg_mul]
  rw [hcoeff, neg_smul]

/-- Generic helper: the matrix exponential of `c • S` (with `S`
Hermitian and `c` purely imaginary, `c̄ = -c`) is unitary, in the
form `(exp ((-(I·θ)) • S))ᴴ * exp ((-(I·θ)) • S) = 1`. Pushes the
Frobenius topology bridge through `exp_mem_unitary_of_mem_skewAdjoint`
with the same `letI` + `@`-notation pattern as `onSite_exp_eq_exp_onSite`. -/
private theorem manyBody_exp_neg_I_smul_unitary {S : ManyBodyOp Λ}
    (hS : S.IsHermitian) (θ : ℝ) :
    Matrix.conjTranspose
        (NormedSpace.exp ((-(Complex.I * (θ : ℂ))) • S)) *
      NormedSpace.exp ((-(Complex.I * (θ : ℂ))) • S) = 1 := by
  letI _iAddTgt : NormedAddCommGroup (ManyBodyOp Λ) :=
    Matrix.frobeniusNormedAddCommGroup
  letI _iSpaceTgt : NormedSpace ℂ (ManyBodyOp Λ) :=
    Matrix.frobeniusNormedSpace
  letI iRingTgt : NormedRing (ManyBodyOp Λ) :=
    Matrix.frobeniusNormedRing
  letI iAlgTgt : NormedAlgebra ℚ (ManyBodyOp Λ) :=
    Matrix.frobeniusNormedAlgebra
  haveI iComplTgt : CompleteSpace (ManyBodyOp Λ) :=
    FiniteDimensional.complete ℂ (ManyBodyOp Λ)
  have hskew := neg_I_mul_real_smul_isHermitian_mem_skewAdjoint (Λ := Λ) θ hS
  have hunit : NormedSpace.exp ((-(Complex.I * (θ : ℂ))) • S) ∈
      unitary (ManyBodyOp Λ) :=
    @NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
      (ManyBodyOp Λ) iRingTgt iAlgTgt iComplTgt _ _ _ hskew
  exact hunit.1

/-- `Û^(1)_θ_tot` is unitary: its conjugate transpose is its inverse. -/
theorem totalSpinHalfRot1_conjTranspose_mul_self (θ : ℝ) :
    Matrix.conjTranspose (totalSpinHalfRot1 Λ θ) * totalSpinHalfRot1 Λ θ = 1 := by
  rw [totalSpinHalfRot1_eq_exp]
  exact manyBody_exp_neg_I_smul_unitary Λ (totalSpinHalfOp1_isHermitian Λ) θ

/-- `Û^(2)_θ_tot` is unitary. -/
theorem totalSpinHalfRot2_conjTranspose_mul_self (θ : ℝ) :
    Matrix.conjTranspose (totalSpinHalfRot2 Λ θ) * totalSpinHalfRot2 Λ θ = 1 := by
  rw [totalSpinHalfRot2_eq_exp]
  exact manyBody_exp_neg_I_smul_unitary Λ (totalSpinHalfOp2_isHermitian Λ) θ

/-- `Û^(3)_θ_tot` is unitary. -/
theorem totalSpinHalfRot3_conjTranspose_mul_self (θ : ℝ) :
    Matrix.conjTranspose (totalSpinHalfRot3 Λ θ) * totalSpinHalfRot3 Λ θ = 1 := by
  rw [totalSpinHalfRot3_eq_exp]
  exact manyBody_exp_neg_I_smul_unitary Λ (totalSpinHalfOp3_isHermitian Λ) θ

/-- Generic helper: from unitarity `Uᴴ * U = 1` and commutativity
`A * U = U * A` derive the conjugation form `Uᴴ * A * U = A`. -/
private theorem conj_eq_self_of_commute_of_unitary
    {U : ManyBodyOp Λ} (hU : Matrix.conjTranspose U * U = 1)
    (A : ManyBodyOp Λ) (hcomm : A * U = U * A) :
    Matrix.conjTranspose U * A * U = A := by
  -- (Uᴴ * A) * U = Uᴴ * (A * U) = Uᴴ * (U * A) = (Uᴴ * U) * A = 1 * A = A
  rw [mul_assoc, hcomm, ← mul_assoc, hU, one_mul]

/-- Tasaki §2.2 eq (2.2.13), axis 1: `(Û^(1)_θ_tot)ᴴ * Â * Û^(1)_θ_tot = Â`
when `Â` commutes with `Ŝ_tot^(1)`. The full finite-form SU(2)
invariance for axis 1. -/
theorem totalSpinHalfRot1_conj_eq_self_of_commute (θ : ℝ) (A : ManyBodyOp Λ)
    (h : Commute A (totalSpinHalfOp1 Λ)) :
    Matrix.conjTranspose (totalSpinHalfRot1 Λ θ) * A * totalSpinHalfRot1 Λ θ = A :=
  conj_eq_self_of_commute_of_unitary Λ
    (totalSpinHalfRot1_conjTranspose_mul_self Λ θ) A
    (totalSpinHalfRot1_commute_of_commute Λ θ A h)

/-- Tasaki §2.2 eq (2.2.13), axis 2. -/
theorem totalSpinHalfRot2_conj_eq_self_of_commute (θ : ℝ) (A : ManyBodyOp Λ)
    (h : Commute A (totalSpinHalfOp2 Λ)) :
    Matrix.conjTranspose (totalSpinHalfRot2 Λ θ) * A * totalSpinHalfRot2 Λ θ = A :=
  conj_eq_self_of_commute_of_unitary Λ
    (totalSpinHalfRot2_conjTranspose_mul_self Λ θ) A
    (totalSpinHalfRot2_commute_of_commute Λ θ A h)

/-- Tasaki §2.2 eq (2.2.13), axis 3. -/
theorem totalSpinHalfRot3_conj_eq_self_of_commute (θ : ℝ) (A : ManyBodyOp Λ)
    (h : Commute A (totalSpinHalfOp3 Λ)) :
    Matrix.conjTranspose (totalSpinHalfRot3 Λ θ) * A * totalSpinHalfRot3 Λ θ = A :=
  conj_eq_self_of_commute_of_unitary Λ
    (totalSpinHalfRot3_conjTranspose_mul_self Λ θ) A
    (totalSpinHalfRot3_commute_of_commute Λ θ A h)


end LatticeSystem.Quantum
