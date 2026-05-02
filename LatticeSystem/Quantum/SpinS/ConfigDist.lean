import LatticeSystem.Quantum.SpinS.RaiseLower
import Mathlib.Data.Nat.Dist

/-!
# Spin-`S` configuration distance
(Tasaki §2.5 Phase B-γ γ-3 connectivity prep)

The configuration distance `configDistS σ σ' := ∑_x |σ x − σ' x|`
(natural-number absolute difference) measures how far apart two
spin-`S` configurations are. It is the spin-`S` generalisation of the
Hamming distance used in the spin-`1/2` connectivity argument
(`LatticeSystem/Quantum/MarshallLiebMattis/EqMagnetizationReachable.lean`).

Key properties:
- `configDistS_eq_zero_iff`: distance zero iff configurations are equal.
- `configDistS_comm`: symmetry.

These are stepping stones for the irreducibility argument: starting
from two equal-magnetization configurations of positive distance, find
sites `x, y` where `σ x > σ' x` and `σ y < σ' y`, transport one unit
to reduce the distance, and iterate.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The configuration distance: sum of natural-number absolute
differences of `σ x` and `σ' x` over all sites. -/
def configDistS (σ σ' : V → Fin (N + 1)) : ℕ :=
  ∑ x : V, Nat.dist (σ x).val (σ' x).val

omit [DecidableEq V] in
/-- Definitional unfolding of `configDistS`. -/
theorem configDistS_def (σ σ' : V → Fin (N + 1)) :
    configDistS σ σ' = ∑ x : V, Nat.dist (σ x).val (σ' x).val := rfl

omit [DecidableEq V] in
/-- Configuration distance is zero iff the two configurations agree
everywhere. -/
theorem configDistS_eq_zero_iff (σ σ' : V → Fin (N + 1)) :
    configDistS σ σ' = 0 ↔ σ = σ' := by
  unfold configDistS
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h
    funext x
    have hx := h x (Finset.mem_univ x)
    apply Fin.ext
    exact Nat.eq_of_dist_eq_zero hx
  · intro h x _
    rw [h]
    exact Nat.dist_self _

omit [DecidableEq V] in
/-- `configDistS` is symmetric. -/
theorem configDistS_comm (σ σ' : V → Fin (N + 1)) :
    configDistS σ σ' = configDistS σ' σ := by
  unfold configDistS
  refine Finset.sum_congr rfl (fun x _ => ?_)
  exact Nat.dist_comm _ _

omit [DecidableEq V] in
/-- Configuration distance with itself is zero. -/
@[simp]
theorem configDistS_self (σ : V → Fin (N + 1)) : configDistS σ σ = 0 := by
  rw [configDistS_eq_zero_iff]

omit [DecidableEq V] in
/-- Two configurations differ iff their `configDistS` is positive. -/
theorem configDistS_pos_iff (σ σ' : V → Fin (N + 1)) :
    0 < configDistS σ σ' ↔ σ ≠ σ' := by
  rw [Nat.pos_iff_ne_zero, ne_eq, configDistS_eq_zero_iff]

end LatticeSystem.Quantum
