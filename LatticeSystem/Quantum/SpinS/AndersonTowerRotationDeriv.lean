import LatticeSystem.Quantum.SpinS.AndersonTowerMasterWard
import LatticeSystem.Quantum.SpinS.AndersonTowerSphereMoment
import LatticeSystem.Quantum.SpinS.AndersonTowerCartWord
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Tasaki §4.2.2 Proposition 4.10: rotation-path derivative vanishing of the directional moment

For a total-spin singlet `Φ`, the master Ward identity `cartWord_ward_singlet`
(`AndersonTowerMasterWard`) says the Levi-Civita-weighted single-letter rotation sum of the
Cartesian order-word expectation vanishes.  This module reads that algebraic identity as the
statement that the **directional moment**

`g(n) = ⟨Φ, (Ô_L^n)^{2M} Φ⟩`   (`directionMoment`)

is annihilated by the so(3) rotation generators, i.e. its derivative along any axis-`γ` rotation
path `R_γ(θ) n₀` (`rotationPath`) vanishes for all `θ` (sub-step L4b-ii of the arc PR-3.2b).

The route is purely scalar (no operator-power differentiation).  Expanding the operator power into
the polynomial `directionMoment A Φ M n = Σ_f (∏_j n_{f j}) · T_f` with axis-word coefficients
`T_f = ⟨Φ, ô^{ofFn f} Φ⟩` constant in `θ` (`directionMoment_eq_sum`), the derivative is the
commutative product derivative `HasDerivAt.finset_prod` of the coordinate monomials.  Each
coordinate derivative is the generator ODE `d/dθ (R_γ(θ) n₀)_δ = Σ_β ε_{γβδ} (R_γ(θ) n₀)_β`
(`rotationPath_coord_hasDerivAt`).  Regrouping the resulting monomials by an involution on
`(f, β) ↦ (update f k β, f k)` (`updateSwapEquiv`) collapses the inner sum into the master Ward
identity, giving `d/dθ g(R_γ(θ) n₀) = 0`
(`directionMoment_rotationPath_hasDerivAt_zero`).  Only the vanishing derivative is established
here; its global-constancy consequence is the next step (L4b-iii).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, eqs. (4.2.57)–(4.2.59), p.108–109; cf. Tasaki, arXiv:1807.05847.
-/

namespace LatticeSystem.Quantum

open Matrix LatticeSystem.Math

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ### The directional moment and its axis-word polynomial expansion -/

/-- The **directional moment** `g(n) = ⟨Φ, (Ô_L^n)^{2M} Φ⟩`: the sesquilinear expectation of the
`(2M)`-th power of the direction order operator `Ô_L^n` (`directionStaggeredOp`) on the tower vector
`Φ`.  As a function of the direction `n` it is a homogeneous degree-`2M` polynomial in the
coordinates of `n` (`directionMoment_eq_sum`); Proposition 4.10 studies its isotropy. -/
noncomputable def directionMoment (A : Λ → Bool) (Φ : (Λ → Fin (N + 1)) → ℂ) (M : ℕ)
    (n : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  star Φ ⬝ᵥ ((directionStaggeredOp n A N) ^ (2 * M)).mulVec Φ

/-- **Axis-word polynomial expansion of the directional moment.**  The directional moment
`g(n) = ⟨Φ, (Ô_L^n)^{2M} Φ⟩` expands into a finite sum over axis tuples `f : Fin (2M) → Fin 3`, each
weighted by the coordinate monomial `∏_j n_{f j}` and multiplied by the constant Cartesian
order-word expectation `T_f = ⟨Φ, ô^{ofFn f} Φ⟩` (`cartWord`).  Obtained from the operator expansion
`pow_sum_smul_eq_sum_smul_prod` of `directionStaggeredOp_eq_sum` by distributing `star Φ ⬝ᵥ ·` and
`·.mulVec Φ` through the sum and scalars. -/
theorem directionMoment_eq_sum (A : Λ → Bool) (Φ : (Λ → Fin (N + 1)) → ℂ) (M : ℕ)
    (n : EuclideanSpace ℝ (Fin 3)) :
    directionMoment A Φ M n
      = ∑ f : Fin (2 * M) → Fin 3,
          (∏ j, ((n (f j) : ℝ) : ℂ)) •
            (star Φ ⬝ᵥ (cartWord A N (List.ofFn f)).mulVec Φ) := by
  rw [directionMoment, directionStaggeredOp_eq_sum, pow_sum_smul_eq_sum_smul_prod,
    Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [smul_mulVec, dotProduct_smul, cartWord_ofFn]

/-! ### The axis-`γ` rotation path and its generator ODE -/

/-- The underlying coordinates of the axis-`γ` rotation path acting on `n`: for axis `γ` the two
perpendicular coordinates rotate by angle `θ` while the `γ`-coordinate is fixed.  Wrapped into
`EuclideanSpace` by `rotationPath`; the sign conventions are fixed so that the coordinate derivative
is the Levi-Civita generator ODE (`rotationPath_coord_hasDerivAt`). -/
noncomputable def rotationCoords (γ : Fin 3) (n : EuclideanSpace ℝ (Fin 3)) (θ : ℝ) : Fin 3 → ℝ :=
  ![![n 0, n 1 * Real.cos θ + -(n 2) * Real.sin θ, n 2 * Real.cos θ + n 1 * Real.sin θ],
    ![n 0 * Real.cos θ + n 2 * Real.sin θ, n 1, n 2 * Real.cos θ + -(n 0) * Real.sin θ],
    ![n 0 * Real.cos θ + -(n 1) * Real.sin θ, n 1 * Real.cos θ + n 0 * Real.sin θ, n 2]] γ

/-- The **axis-`γ` rotation path** `θ ↦ R_γ(θ) n`: the image of `n ∈ S² ⊂ ℝ³` under the rotation of
angle `θ` about the coordinate axis `γ`, built explicitly from `Real.cos`/`Real.sin`
(`rotationCoords`) since Mathlib has no ready SO(3) rotation matrix.  Its generator is the
Levi-Civita symbol `ε_γ` (`rotationPath_coord_hasDerivAt`). -/
noncomputable def rotationPath (γ : Fin 3) (n : EuclideanSpace ℝ (Fin 3)) (θ : ℝ) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (rotationCoords γ n θ)

/-- Coordinate access for the rotation path: `(R_γ(θ) n)_δ` is the underlying coordinate
`rotationCoords γ n θ δ`. -/
theorem rotationPath_apply (γ : Fin 3) (n : EuclideanSpace ℝ (Fin 3)) (θ : ℝ) (δ : Fin 3) :
    rotationPath γ n θ δ = rotationCoords γ n θ δ := rfl

/-- Real derivative of the coordinate combination `t ↦ a cos t + b sin t`. -/
private theorem hasDerivAt_realCosSin (a b θ : ℝ) :
    HasDerivAt (fun t : ℝ => a * Real.cos t + b * Real.sin t)
      (-(a * Real.sin θ) + b * Real.cos θ) θ := by
  have h1 : HasDerivAt (fun t : ℝ => a * Real.cos t) (a * -Real.sin θ) θ :=
    (Real.hasDerivAt_cos θ).const_mul a
  have h2 : HasDerivAt (fun t : ℝ => b * Real.sin t) (b * Real.cos θ) θ :=
    (Real.hasDerivAt_sin θ).const_mul b
  convert h1.add h2 using 1
  ring

/-- **Generator ODE of the rotation path** (Tasaki eq. (4.2.57)).  The `δ`-coordinate of the
axis-`γ` rotation path satisfies the Levi-Civita generator equation
`d/dθ (R_γ(θ) n)_δ = Σ_β ε_{γβδ} (R_γ(θ) n)_β`, viewed as a `ℝ → ℂ` map.  Proved by the axis case
split `fin_cases γ`, `fin_cases δ` with the elementary `cos`/`sin` derivatives cast to `ℂ`. -/
theorem rotationPath_coord_hasDerivAt (γ : Fin 3) (n : EuclideanSpace ℝ (Fin 3)) (δ : Fin 3)
    (θ : ℝ) :
    HasDerivAt (fun t : ℝ => ((rotationPath γ n t δ : ℝ) : ℂ))
      (∑ β : Fin 3, leviCivita3 γ β δ * ((rotationPath γ n θ β : ℝ) : ℂ)) θ := by
  fin_cases γ <;> fin_cases δ <;>
    simp only [rotationPath_apply, rotationCoords, Fin.sum_univ_three, leviCivita3]
  · simpa using hasDerivAt_const θ ((n 0 : ℝ) : ℂ)
  · convert (hasDerivAt_realCosSin (n 1) (-(n 2)) θ).ofReal_comp using 1
    push_cast; ring
  · convert (hasDerivAt_realCosSin (n 2) (n 1) θ).ofReal_comp using 1
    push_cast; ring
  · convert (hasDerivAt_realCosSin (n 0) (n 2) θ).ofReal_comp using 1
    push_cast; ring
  · simpa using hasDerivAt_const θ ((n 1 : ℝ) : ℂ)
  · convert (hasDerivAt_realCosSin (n 2) (-(n 0)) θ).ofReal_comp using 1
    push_cast; ring
  · convert (hasDerivAt_realCosSin (n 0) (-(n 1)) θ).ofReal_comp using 1
    push_cast; ring
  · convert (hasDerivAt_realCosSin (n 1) (n 0) θ).ofReal_comp using 1
    push_cast; ring
  · simpa using hasDerivAt_const θ ((n 2 : ℝ) : ℂ)

/-! ### Index bridges: `ofFn`/`set`/`update` and the reindexed master Ward -/

/-- Bridge between `List.set` on an `ofFn` list and `Function.update`:
`(ofFn g).set k a = ofFn (update g k a)`.  Both lists agree entrywise by `List.getElem_set` /
`List.getElem_ofFn`. -/
theorem ofFn_set_eq_ofFn_update {α : Type*} {n : ℕ} (g : Fin n → α) (k : Fin n) (a : α) :
    (List.ofFn g).set (k : ℕ) a = List.ofFn (Function.update g k a) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_set, List.getElem_ofFn, List.getElem_ofFn, Function.update_apply]
    rcases eq_or_ne (k : ℕ) i with hik | hik
    · rw [if_pos hik, if_pos (Fin.ext hik.symm)]
    · rw [if_neg hik, if_neg (fun h => hik (Fin.ext_iff.mp h).symm)]

/-- **Reindexed master Ward identity.**  The master Ward identity `cartWord_ward_singlet` rewritten
over the finite index `Fin (2M)` and phrased with `Function.update`:
`Σ_k Σ_α ε_{γ (g k) α} ⟨Φ, ô^{ofFn (update g k α)} Φ⟩ = 0` for every tuple `g : Fin (2M) → Fin 3`
and total-spin singlet `Φ`.  Obtained from `cartWord_ward_singlet A γ (ofFn g)` by reindexing the
position sum along `finCongr (length_ofFn)` and applying `List.get_ofFn` and
`ofFn_set_eq_ofFn_update`. -/
theorem cartWord_ward_singlet_ofFn (A : Λ → Bool) (γ : Fin 3) {M : ℕ}
    (g : Fin (2 * M) → Fin 3) (Φ : (Λ → Fin (N + 1)) → ℂ)
    (h3 : (totalSpinSOp3 Λ N).mulVec Φ = 0) (h1 : (totalSpinSOp1 Λ N).mulVec Φ = 0) :
    ∑ k : Fin (2 * M), ∑ α : Fin 3,
        leviCivita3 γ (g k) α *
          (star Φ ⬝ᵥ (cartWord A N (List.ofFn (Function.update g k α))).mulVec Φ) = 0 := by
  have hlen : (List.ofFn g).length = 2 * M := List.length_ofFn
  have hward := cartWord_ward_singlet A γ (List.ofFn g) Φ h3 h1
  rw [← hward]
  refine Fintype.sum_equiv (finCongr hlen).symm _ _ (fun k => ?_)
  refine Finset.sum_congr rfl fun α _ => ?_
  have hget : (List.ofFn g).get ((finCongr hlen).symm k) = g k := by
    simp
  have hidx : ((finCongr hlen).symm k : ℕ) = (k : ℕ) := by simp
  rw [hget, hidx, ofFn_set_eq_ofFn_update]

/-! ### The monomial-regrouping involution -/

/-- The **monomial-regrouping involution** `(f, β) ↦ (update f k β, f k)` on
`(Fin n → Fin 3) × Fin 3`, used to fold the differentiated coordinate monomials at position `k` back
into the master Ward sum.  It is its own inverse: reapplying it restores `f` at position `k` via
`Function.update_idem` / `Function.update_eq_self`. -/
def updateSwapEquiv {n : ℕ} (k : Fin n) :
    ((Fin n → Fin 3) × Fin 3) ≃ ((Fin n → Fin 3) × Fin 3) where
  toFun p := (Function.update p.1 k p.2, p.1 k)
  invFun p := (Function.update p.1 k p.2, p.1 k)
  left_inv := fun ⟨f, β⟩ => by
    simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
  right_inv := fun ⟨f, β⟩ => by
    simp only [Function.update_self, Function.update_idem, Function.update_eq_self]

/-! ### Vanishing of the rotation derivative -/

/-- **Rotation-derivative vanishing of the directional moment** (Prop 4.10 arc PR-3.2b sub-step
L4b-ii).  For a total-spin singlet `Φ`, the directional moment `g(n) = ⟨Φ, (Ô_L^n)^{2M} Φ⟩` has
vanishing derivative along the axis-`γ` rotation path `θ ↦ R_γ(θ) n₀`:
`d/dθ g(R_γ(θ) n₀) = 0` for every `θ`.  The polynomial expansion `directionMoment_eq_sum` makes the
`θ`-dependence purely the coordinate monomials, whose derivative is the commutative product
derivative `HasDerivAt.finset_prod` fed by the generator ODE `rotationPath_coord_hasDerivAt`;
regrouping the monomials by `updateSwapEquiv` collapses the inner sum into the reindexed master Ward
identity `cartWord_ward_singlet_ofFn`, which vanishes.  Downstream (L4b-iii) this supplies both the
differentiability and the zero derivative to `is_const_of_deriv_eq_zero`. -/
theorem directionMoment_rotationPath_hasDerivAt_zero (A : Λ → Bool) (γ : Fin 3)
    (n₀ : EuclideanSpace ℝ (Fin 3)) (M : ℕ) (Φ : (Λ → Fin (N + 1)) → ℂ)
    (h3 : (totalSpinSOp3 Λ N).mulVec Φ = 0) (h1 : (totalSpinSOp1 Λ N).mulVec Φ = 0) (θ : ℝ) :
    HasDerivAt (fun t => directionMoment A Φ M (rotationPath γ n₀ t)) 0 θ := by
  -- Rewrite the map as the axis-word polynomial in the rotating coordinates.
  have hfun : (fun t => directionMoment A Φ M (rotationPath γ n₀ t))
      = fun t => ∑ f : Fin (2 * M) → Fin 3,
          (∏ j, ((rotationPath γ n₀ t (f j) : ℝ) : ℂ)) *
            (star Φ ⬝ᵥ (cartWord A N (List.ofFn f)).mulVec Φ) := by
    funext t; rw [directionMoment_eq_sum]; simp only [smul_eq_mul]
  rw [hfun]
  -- Per tuple `f`, differentiate the coordinate monomial by the commutative product rule.
  have hpf : ∀ f : Fin (2 * M) → Fin 3,
      HasDerivAt (fun t => (∏ j, ((rotationPath γ n₀ t (f j) : ℝ) : ℂ)) *
          (star Φ ⬝ᵥ (cartWord A N (List.ofFn f)).mulVec Φ))
        ((∑ k : Fin (2 * M),
            (∏ j ∈ Finset.univ.erase k, ((rotationPath γ n₀ θ (f j) : ℝ) : ℂ)) •
              (∑ β : Fin 3, leviCivita3 γ β (f k) * ((rotationPath γ n₀ θ β : ℝ) : ℂ))) *
          (star Φ ⬝ᵥ (cartWord A N (List.ofFn f)).mulVec Φ)) θ := by
    intro f
    refine HasDerivAt.mul_const ?_ _
    exact HasDerivAt.fun_finset_prod fun k _ => rotationPath_coord_hasDerivAt γ n₀ (f k) θ
  -- Sum the per-tuple derivatives.
  have hsum := HasDerivAt.sum (fun f (_ : f ∈ Finset.univ) => hpf f)
  -- The summed derivative vanishes by regrouping into the master Ward identity.
  have hzero : (∑ f : Fin (2 * M) → Fin 3,
      (∑ k : Fin (2 * M),
          (∏ j ∈ Finset.univ.erase k, ((rotationPath γ n₀ θ (f j) : ℝ) : ℂ)) •
            (∑ β : Fin 3, leviCivita3 γ β (f k) * ((rotationPath γ n₀ θ β : ℝ) : ℂ))) *
        (star Φ ⬝ᵥ (cartWord A N (List.ofFn f)).mulVec Φ)) = 0 := by
    -- Regroup each `(∏_{j≠k}) · nᵦ` into `∏_j n_{(update f k β) j}`.
    have hprodupd : ∀ (f : Fin (2 * M) → Fin 3) (k : Fin (2 * M)) (β : Fin 3),
        (∏ j, ((rotationPath γ n₀ θ ((Function.update f k β) j) : ℝ) : ℂ))
          = ((rotationPath γ n₀ θ β : ℝ) : ℂ) *
              ∏ j ∈ Finset.univ.erase k, ((rotationPath γ n₀ θ (f j) : ℝ) : ℂ) := by
      intro f k β
      rw [← Finset.mul_prod_erase Finset.univ
        (fun j => ((rotationPath γ n₀ θ ((Function.update f k β) j) : ℝ) : ℂ)) (Finset.mem_univ k)]
      congr 1
      · simp only [Function.update_self]
      · refine Finset.prod_congr rfl fun j hj => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    -- Flatten each summand into a monomial triple sum.
    have hflat : ∀ f : Fin (2 * M) → Fin 3,
        (∑ k : Fin (2 * M),
            (∏ j ∈ Finset.univ.erase k, ((rotationPath γ n₀ θ (f j) : ℝ) : ℂ)) •
              (∑ β : Fin 3, leviCivita3 γ β (f k) * ((rotationPath γ n₀ θ β : ℝ) : ℂ))) *
          (star Φ ⬝ᵥ (cartWord A N (List.ofFn f)).mulVec Φ)
          = ∑ k : Fin (2 * M), ∑ β : Fin 3,
              leviCivita3 γ β (f k) *
                (∏ j, ((rotationPath γ n₀ θ ((Function.update f k β) j) : ℝ) : ℂ)) *
                (star Φ ⬝ᵥ (cartWord A N (List.ofFn f)).mulVec Φ) := by
      intro f
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [hprodupd f k β]; ring
    -- Per position `k`, reindex `(f, β)` by the regrouping involution.
    have hk : ∀ k : Fin (2 * M),
        (∑ f : Fin (2 * M) → Fin 3, ∑ β : Fin 3,
            leviCivita3 γ β (f k) *
              (∏ j, ((rotationPath γ n₀ θ ((Function.update f k β) j) : ℝ) : ℂ)) *
              (star Φ ⬝ᵥ (cartWord A N (List.ofFn f)).mulVec Φ))
          = ∑ g : Fin (2 * M) → Fin 3,
              (∏ j, ((rotationPath γ n₀ θ (g j) : ℝ) : ℂ)) *
                ∑ α : Fin 3, leviCivita3 γ (g k) α *
                  (star Φ ⬝ᵥ (cartWord A N (List.ofFn (Function.update g k α))).mulVec Φ) := by
      intro k
      rw [← Fintype.sum_prod_type' (f := fun (f : Fin (2 * M) → Fin 3) (β : Fin 3) =>
        leviCivita3 γ β (f k) *
          (∏ j, ((rotationPath γ n₀ θ ((Function.update f k β) j) : ℝ) : ℂ)) *
          (star Φ ⬝ᵥ (cartWord A N (List.ofFn f)).mulVec Φ))]
      rw [Fintype.sum_equiv (updateSwapEquiv k)
        (fun p : (Fin (2 * M) → Fin 3) × Fin 3 =>
          leviCivita3 γ p.2 (p.1 k) *
            (∏ j, ((rotationPath γ n₀ θ ((Function.update p.1 k p.2) j) : ℝ) : ℂ)) *
            (star Φ ⬝ᵥ (cartWord A N (List.ofFn p.1)).mulVec Φ))
        (fun p : (Fin (2 * M) → Fin 3) × Fin 3 =>
          (∏ j, ((rotationPath γ n₀ θ (p.1 j) : ℝ) : ℂ)) *
            (leviCivita3 γ (p.1 k) p.2 *
              (star Φ ⬝ᵥ (cartWord A N (List.ofFn (Function.update p.1 k p.2))).mulVec Φ)))
        (fun p => by
          simp only [updateSwapEquiv, Equiv.coe_fn_mk, Function.update_self, Function.update_idem,
            Function.update_eq_self]
          ring)]
      rw [Fintype.sum_prod_type' (f := fun (g : Fin (2 * M) → Fin 3) (α : Fin 3) =>
        (∏ j, ((rotationPath γ n₀ θ (g j) : ℝ) : ℂ)) *
          (leviCivita3 γ (g k) α *
            (star Φ ⬝ᵥ (cartWord A N (List.ofFn (Function.update g k α))).mulVec Φ)))]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Finset.mul_sum]
    -- Assemble: flatten, swap sums, reindex, factor, and apply the reindexed master Ward.
    rw [Finset.sum_congr rfl fun f (_ : f ∈ Finset.univ) => hflat f, Finset.sum_comm]
    rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => hk k, Finset.sum_comm]
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [← Finset.mul_sum, cartWord_ward_singlet_ofFn A γ g Φ h3 h1, mul_zero]
  rw [← hzero, show (fun t => ∑ f : Fin (2 * M) → Fin 3,
        (∏ j, ((rotationPath γ n₀ t (f j) : ℝ) : ℂ)) *
          (star Φ ⬝ᵥ (cartWord A N (List.ofFn f)).mulVec Φ))
      = ∑ f : Fin (2 * M) → Fin 3, fun t =>
          (∏ j, ((rotationPath γ n₀ t (f j) : ℝ) : ℂ)) *
            (star Φ ⬝ᵥ (cartWord A N (List.ofFn f)).mulVec Φ)
      from by funext t; rw [Finset.sum_apply]]
  exact hsum

end LatticeSystem.Quantum
