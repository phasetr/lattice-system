import LatticeSystem.Fermion.JordanWigner.Hubbard.TJModel
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJHermitian
import LatticeSystem.Fermion.JordanWigner.Hubbard.EffectiveHamiltonianSpinSymmetry

/-!
# Tasaki 11.5: the t-J Hamiltonian preserves the hard-core subspace (Prop 11.24 PR-E1b-hardcore)

`Ĥ_tJ` maps the no-double-occupancy (hard-core) subspace into itself. This is the operator-side
input to the sector closure: a hard-core sector state `|Φ_s⟩` stays hard-core under `Ĥ_tJ`, so the
expansion `Ĥ_tJ|Φ_s⟩ = Σ_{s'} M_{s',s}|Φ_{s'}⟩` is well-defined.

The route mirrors `fermionTotalSpinMinus_mulVec_mem_hardcore` (NagaokaConnectivity): we prove
`Commute Ĥ_tJ P̂hc` and then `P̂hc(Ĥ_tJ v) = Ĥ_tJ(P̂hc v) = Ĥ_tJ v` for `v` in the subspace.
Each piece of `Ĥ_tJ` commutes with `P̂hc`:

* the kinetic sandwich `P̂hc K P̂hc` commutes with `P̂hc` by idempotency `P̂hc² = P̂hc`;
* the per-site spin/number operators `Ŝ^±_x, Ŝ³_x, n̂_x` commute with every same-site
  double-occupancy `n̂_{i↑}n̂_{i↓}` — hence with every hard-core factor `1 - n̂_{i↑}n̂_{i↓}` and
  with their non-commutative product `P̂hc` — so the density product `n̂_x n̂_y` and the spin dot
  `Ŝ_x·Ŝ_y` commute with `P̂hc`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph

variable {N : ℕ}

/-! ## Per-site spin and number operators commute with the double-occupancy operator -/

/-- `Ŝ⁺_x = ĉ†_{x↑}ĉ_{x↓}` commutes with the same-site double occupancy `n̂_{i↑}n̂_{i↓}`
(definitionally the interaction-term commutator already established for the Hubbard symmetry). -/
theorem fermionSiteSpinPlus_commute_hubbardDoubleOccupancy (x i : Fin (N + 1)) :
    Commute (fermionSiteSpinPlus N x) (hubbardDoubleOccupancy N i) :=
  fermionSpinPlusTerm_commute_interactionTerm N x i

/-- `Ŝ⁻_x` commutes with the same-site double occupancy (adjoint of the `Ŝ⁺_x` version, using
`(Ŝ⁺_x)ᴴ = Ŝ⁻_x` and the Hermiticity of `n̂_{i↑}n̂_{i↓}`). -/
theorem fermionSiteSpinMinus_commute_hubbardDoubleOccupancy (x i : Fin (N + 1)) :
    Commute (fermionSiteSpinMinus N x) (hubbardDoubleOccupancy N i) := by
  have h := (fermionSiteSpinPlus_commute_hubbardDoubleOccupancy x i).eq
  have hd := hubbardDoubleOccupancy_isHermitian N i
  have hadj := congrArg Matrix.conjTranspose h
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hd.eq,
    fermionSiteSpinPlus_conjTranspose] at hadj
  exact hadj.symm

/-- `Ŝ³_x` commutes with the same-site double occupancy: both are diagonal in the occupation
basis (products of number operators). -/
theorem fermionSiteSpinZ_commute_hubbardDoubleOccupancy (x i : Fin (N + 1)) :
    Commute (fermionSiteSpinZ N x) (hubbardDoubleOccupancy N i) := by
  unfold fermionSiteSpinZ fermionUpCreation fermionUpAnnihilation fermionDownCreation
    fermionDownAnnihilation hubbardDoubleOccupancy fermionUpNumber fermionDownNumber
  refine Commute.smul_left (Commute.sub_left ?_ ?_) _ <;>
    exact (fermionMultiNumber_commute (2 * N + 1) _ (spinfulIndex N i 0)).mul_right
      (fermionMultiNumber_commute (2 * N + 1) _ (spinfulIndex N i 1))

/-- `n̂_x = n̂_{x↑} + n̂_{x↓}` commutes with the same-site double occupancy (all number operators
commute pairwise). -/
theorem fermionSiteNumber_commute_hubbardDoubleOccupancy (x i : Fin (N + 1)) :
    Commute (fermionSiteNumber N x) (hubbardDoubleOccupancy N i) := by
  unfold fermionSiteNumber fermionUpNumber fermionDownNumber hubbardDoubleOccupancy
    fermionUpNumber fermionDownNumber
  refine Commute.add_left ?_ ?_ <;>
    exact (fermionMultiNumber_commute (2 * N + 1) _ (spinfulIndex N i 0)).mul_right
      (fermionMultiNumber_commute (2 * N + 1) _ (spinfulIndex N i 1))

/-! ## Per-site operators commute with the hard-core projection -/

/-- A per-site operator commuting with every double occupancy commutes with every hard-core
factor `1 - n̂_{i↑}n̂_{i↓}`. -/
private theorem commute_hardcoreFactor_of_commute_dblOcc
    {O : ManyBodyOp (Fin (2 * N + 2))}
    (h : ∀ i, Commute O (hubbardDoubleOccupancy N i)) (i : Fin (N + 1)) :
    Commute O (hubbardHardcoreFactor N i) := by
  unfold hubbardHardcoreFactor
  exact (Commute.one_right _).sub_right (h i)

/-- A per-site operator commuting with every hard-core factor commutes with the hard-core
projection `P̂hc = ∏_i (1 - n̂_{i↑}n̂_{i↓})`. -/
private theorem commute_hardcoreProjection_of_commute_dblOcc
    {O : ManyBodyOp (Fin (2 * N + 2))}
    (h : ∀ i, Commute O (hubbardDoubleOccupancy N i)) :
    Commute O (hubbardHardcoreProjection N) := by
  unfold hubbardHardcoreProjection
  exact Finset.noncommProd_commute _ _ _ _
    (fun i _ => commute_hardcoreFactor_of_commute_dblOcc h i)

/-- `Ŝ⁺_x` commutes with the hard-core projection. -/
theorem fermionSiteSpinPlus_commute_hubbardHardcoreProjection (x : Fin (N + 1)) :
    Commute (fermionSiteSpinPlus N x) (hubbardHardcoreProjection N) :=
  commute_hardcoreProjection_of_commute_dblOcc
    (fun i => fermionSiteSpinPlus_commute_hubbardDoubleOccupancy x i)

/-- `Ŝ⁻_x` commutes with the hard-core projection. -/
theorem fermionSiteSpinMinus_commute_hubbardHardcoreProjection (x : Fin (N + 1)) :
    Commute (fermionSiteSpinMinus N x) (hubbardHardcoreProjection N) :=
  commute_hardcoreProjection_of_commute_dblOcc
    (fun i => fermionSiteSpinMinus_commute_hubbardDoubleOccupancy x i)

/-- `Ŝ³_x` commutes with the hard-core projection. -/
theorem fermionSiteSpinZ_commute_hubbardHardcoreProjection (x : Fin (N + 1)) :
    Commute (fermionSiteSpinZ N x) (hubbardHardcoreProjection N) :=
  commute_hardcoreProjection_of_commute_dblOcc
    (fun i => fermionSiteSpinZ_commute_hubbardDoubleOccupancy x i)

/-- `n̂_x` commutes with the hard-core projection. -/
theorem fermionSiteNumber_commute_hubbardHardcoreProjection (x : Fin (N + 1)) :
    Commute (fermionSiteNumber N x) (hubbardHardcoreProjection N) :=
  commute_hardcoreProjection_of_commute_dblOcc
    (fun i => fermionSiteNumber_commute_hubbardDoubleOccupancy x i)

/-! ## The t-J Hamiltonian pieces commute with the hard-core projection -/

/-- The per-site spin dot `Ŝ_x · Ŝ_y` commutes with the hard-core projection. -/
theorem fermionSpinDot_commute_hubbardHardcoreProjection (x y : Fin (N + 1)) :
    Commute (fermionSpinDot N x y) (hubbardHardcoreProjection N) := by
  unfold fermionSpinDot
  refine Commute.add_left (Commute.smul_left (Commute.add_left ?_ ?_) _) ?_
  · exact (fermionSiteSpinPlus_commute_hubbardHardcoreProjection x).mul_left
      (fermionSiteSpinMinus_commute_hubbardHardcoreProjection y)
  · exact (fermionSiteSpinMinus_commute_hubbardHardcoreProjection x).mul_left
      (fermionSiteSpinPlus_commute_hubbardHardcoreProjection y)
  · exact (fermionSiteSpinZ_commute_hubbardHardcoreProjection x).mul_left
      (fermionSiteSpinZ_commute_hubbardHardcoreProjection y)

/-- The density product `n̂_x n̂_y` commutes with the hard-core projection. -/
theorem fermionSiteNumber_mul_commute_hubbardHardcoreProjection (x y : Fin (N + 1)) :
    Commute (fermionSiteNumber N x * fermionSiteNumber N y) (hubbardHardcoreProjection N) :=
  (fermionSiteNumber_commute_hubbardHardcoreProjection x).mul_left
    (fermionSiteNumber_commute_hubbardHardcoreProjection y)

/-- The kinetic sandwich `P̂hc K P̂hc` commutes with the hard-core projection, by idempotency
`P̂hc² = P̂hc`: both products collapse to `P̂hc K P̂hc`. -/
theorem tJKinetic_commute_hubbardHardcoreProjection
    (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj] :
    Commute
      (hubbardHardcoreProjection N * hubbardKineticOnGraph N G 1 * hubbardHardcoreProjection N)
      (hubbardHardcoreProjection N) := by
  have h := hubbardHardcoreProjection_mul_self N
  show hubbardHardcoreProjection N * hubbardKineticOnGraph N G 1 * hubbardHardcoreProjection N *
      hubbardHardcoreProjection N =
    hubbardHardcoreProjection N *
      (hubbardHardcoreProjection N * hubbardKineticOnGraph N G 1 * hubbardHardcoreProjection N)
  rw [Matrix.mul_assoc (hubbardHardcoreProjection N * hubbardKineticOnGraph N G 1)
      (hubbardHardcoreProjection N) (hubbardHardcoreProjection N), h,
    ← Matrix.mul_assoc (hubbardHardcoreProjection N)
      (hubbardHardcoreProjection N * hubbardKineticOnGraph N G 1) (hubbardHardcoreProjection N),
    ← Matrix.mul_assoc (hubbardHardcoreProjection N) (hubbardHardcoreProjection N)
      (hubbardKineticOnGraph N G 1), h]

/-- **`Ĥ_tJ` commutes with the hard-core projection `P̂hc`.** Each piece — the kinetic sandwich,
the diagonal density products, and the per-site spin dots — commutes with `P̂hc`. -/
theorem tJHamiltonian_commute_hubbardHardcoreProjection
    (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj] (τ J : ℝ) :
    Commute (tJHamiltonian N G τ J) (hubbardHardcoreProjection N) := by
  unfold tJHamiltonian
  refine (Commute.smul_left ?_ _).add_left (Commute.smul_left ?_ _)
  · exact tJKinetic_commute_hubbardHardcoreProjection G
  · refine Commute.sum_left _ _ _ (fun x _ => Commute.sum_left _ _ _ (fun y _ => ?_))
    by_cases h : G.Adj x y
    · simp only [h, if_true]
      exact (Commute.smul_left
        (fermionSiteNumber_mul_commute_hubbardHardcoreProjection x y) _).sub_left
        (fermionSpinDot_commute_hubbardHardcoreProjection x y)
    · simp only [h, if_false, Commute.zero_left]

/-! ## The t-J Hamiltonian preserves the hard-core subspace -/

/-- **`Ĥ_tJ` maps the hard-core subspace into itself.** For `v` with no double occupancy,
`P̂hc(Ĥ_tJ v) = Ĥ_tJ(P̂hc v) = Ĥ_tJ v`, so `Ĥ_tJ v` is again hard-core. -/
theorem tJHamiltonian_mulVec_mem_hardcore
    (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj] (τ J : ℝ)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ} (hv : v ∈ hubbardHardcoreSubspace N) :
    (tJHamiltonian N G τ J).mulVec v ∈ hubbardHardcoreSubspace N := by
  have hself : (hubbardHardcoreProjection N).mulVec ((tJHamiltonian N G τ J).mulVec v)
      = (tJHamiltonian N G τ J).mulVec v := by
    rw [Matrix.mulVec_mulVec,
      (tJHamiltonian_commute_hubbardHardcoreProjection G τ J).symm.eq,
      ← Matrix.mulVec_mulVec, hubbardHardcoreProjection_mulVec_eq_self_of_mem N hv]
  rw [← hself]
  exact hubbardHardcoreProjection_mulVec_mem N _

end LatticeSystem.Fermion
