import LatticeSystem.Quantum.SpinS.BoxLocalTranslation
import LatticeSystem.Quantum.SpinS.HypercubicBoxModel
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Tasaki §4.3.1: the box-local energy density of the abstract partial Hamiltonian

Continuing the constructive infinite-volume layer (after the local-support
interface, the finite-box Hamiltonian, and its translation covariance), this
module connects the abstract box partial Hamiltonian `boxLocalHamiltonian S n` to
Tasaki's **per-bond ground-state energy density** `ε_GS` (Definition 4.17 /
eq. (4.3.4)).

The key point is purely algebraic: in *any* infinite-volume ground state `ω`
(Definition 4.17, where every bond carries the energy density,
`ω(Ŝ_x·Ŝ_y) = ε_GS`), the expectation of the `½`-scaled ordered bond sum
collapses to `|B_n| · ε_GS`, where `|B_n|` is the bond count of the box `Λ_n`.
Hence the normalized box-local energy density `ω(Ĥ_{Λ_n}) / |B_n|` equals `ε_GS`
exactly (for boxes with at least one bond) and so converges to `ε_GS`.

This adds **no analytic content** and **no new axiom**: the genuine existence of
the energy density and of infinite-volume ground states already lives in the
documented axioms `boxGroundEnergyDensityS_tendsto`,
`afmThermodynamicLimit_energyDensity`, and `theorem_4_20_omega0 / omegaN`.  Here
everything is proved **axiom-free** from the ground-state bond condition and a
finite graph-counting fact (ordered adjacent pairs are two orientations of each
edge).

## References

* Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
  (1st ed., Springer, 2020), §4.3.1, Definition 4.17, eqs. (4.3.1)–(4.3.4), pp.
  112–113.
-/

namespace LatticeSystem.Quantum

open LatticeSystem.Lattice
open scoped Topology

variable {d : ℕ} {A : Type*} [CStarAlgebra A]

/-- **Counting ordered adjacent pairs**: in a finite simple graph the ordered
adjacent vertex pairs `(x, y)` are the two orientations of each undirected edge,
so there are `2 · |E|` of them. -/
private theorem orderedAdjPairs_card_eq_two_mul_edgeFinset_card
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Finset.univ.filter fun p : V × V => G.Adj p.1 p.2).card = 2 * G.edgeFinset.card := by
  have e : G.Dart ≃ {p : V × V // G.Adj p.1 p.2} :=
    { toFun := fun dt => ⟨dt.toProd, dt.adj⟩
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← G.dart_card_eq_twice_card_edges, ← Fintype.card_subtype]
  exact (Fintype.card_congr e).symm

/-- The number of **ordered** nearest-neighbor bond pairs of the box `Λ_n` is
twice the bond count `|B_n|`. -/
theorem boxOrderedBondPairs_card_eq_two_mul_boxBondCount (d n : ℕ) :
    (boxOrderedBondPairs d n).card = 2 * boxBondCount d n :=
  orderedAdjPairs_card_eq_two_mul_edgeFinset_card (hypercubicBoxGraph d n)

/-- The **box-local energy density** `ω(Ĥ_{Λ_n}) / |B_n|` of a state `ω`: the
per-bond expectation of the abstract box partial Hamiltonian. -/
noncomputable def boxLocalHamiltonianEnergyDensity
    (S : InfiniteSpinSystem d A) (ω : WeakDual ℂ A) (n : ℕ) : ℝ :=
  (ω (boxLocalHamiltonian S n)).re / (boxBondCount d n : ℝ)

/-- **`ω` has box-local energy density `ε`**: the per-bond box energy density
converges to `ε` in the infinite-volume limit (using `n + 1` to avoid the empty
`n = 0` box).  A named convergence property; existence is not asserted. -/
def HasBoxLocalHamiltonianEnergyDensity
    (S : InfiniteSpinSystem d A) (ω : WeakDual ℂ A) (ε : ℝ) : Prop :=
  Filter.Tendsto (fun n : ℕ => boxLocalHamiltonianEnergyDensity S ω (n + 1))
    Filter.atTop (nhds ε)

namespace InfiniteSpinSystem.IsInfiniteVolumeGroundState

variable {S : InfiniteSpinSystem d A} {εGS : ℝ} {ω : WeakDual ℂ A}

/-- **The box partial Hamiltonian expectation in a ground state**: in any
infinite-volume ground state `ω` every bond carries the energy density, so the
`½`-scaled ordered bond sum collapses to `|B_n| · ε_GS`:
`ω(Ĥ_{Λ_n}) = |B_n| · ε_GS`. -/
theorem boxLocalHamiltonian_apply
    (hω : InfiniteSpinSystem.IsInfiniteVolumeGroundState S εGS ω) (n : ℕ) :
    ω (boxLocalHamiltonian S n) = (boxBondCount d n : ℂ) * (εGS : ℂ) := by
  have hbond : ∀ p ∈ boxOrderedBondPairs d n,
      ω (InfiniteSpinSystem.spinDot S (p.1 : Fin d → ℤ) (p.2 : Fin d → ℤ)) = (εGS : ℂ) := by
    intro p hp
    have hadj : (hypercubicBoxGraph d n).Adj p.1 p.2 := mem_boxOrderedBondPairs.mp hp
    have hbnd : InfiniteSpinSystem.bond (p.1 : Fin d → ℤ) (p.2 : Fin d → ℤ) :=
      InfiniteSpinSystem.bond_iff_adj.mpr (hypercubicBoxGraph_adj.mp hadj)
    exact hω.2.2 _ _ hbnd
  have hsmul : ω (boxLocalHamiltonian S n)
      = (1 / 2 : ℂ) * ω (∑ p ∈ boxOrderedBondPairs d n,
        InfiniteSpinSystem.spinDot S (p.1 : Fin d → ℤ) (p.2 : Fin d → ℤ)) := by
    show ω ((1 / 2 : ℂ) • ∑ p ∈ boxOrderedBondPairs d n,
        InfiniteSpinSystem.spinDot S (p.1 : Fin d → ℤ) (p.2 : Fin d → ℤ))
      = (1 / 2 : ℂ) * ω (∑ p ∈ boxOrderedBondPairs d n,
        InfiniteSpinSystem.spinDot S (p.1 : Fin d → ℤ) (p.2 : Fin d → ℤ))
    have h := map_smulₛₗ ω (1 / 2 : ℂ)
      (∑ p ∈ boxOrderedBondPairs d n,
        InfiniteSpinSystem.spinDot S (p.1 : Fin d → ℤ) (p.2 : Fin d → ℤ))
    rw [RingHom.id_apply, smul_eq_mul] at h
    exact h
  rw [hsmul, map_sum, Finset.sum_congr rfl hbond, Finset.sum_const,
    boxOrderedBondPairs_card_eq_two_mul_boxBondCount]
  simp only [nsmul_eq_mul]
  push_cast
  ring

/-- **The box-local energy density equals `ε_GS` in a ground state** (for boxes
with at least one bond): `ω(Ĥ_{Λ_n}) / |B_n| = ε_GS`. -/
theorem boxLocalHamiltonianEnergyDensity_eq
    (hω : InfiniteSpinSystem.IsInfiniteVolumeGroundState S εGS ω)
    {n : ℕ} (hB : 0 < boxBondCount d n) :
    boxLocalHamiltonianEnergyDensity S ω n = εGS := by
  have hbne : (boxBondCount d n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hB.ne'
  unfold boxLocalHamiltonianEnergyDensity
  rw [hω.boxLocalHamiltonian_apply n]
  have hb : (boxBondCount d n : ℂ) = ((boxBondCount d n : ℝ) : ℂ) := by push_cast; ring
  rw [hb, ← Complex.ofReal_mul, Complex.ofReal_re]
  field_simp

/-- **The infinite-volume ground state has box-local energy density `ε_GS`**: the
normalized box energy density converges to `ε_GS` (it is in fact constantly equal
to `ε_GS` along the tail of nonempty boxes). -/
theorem hasBoxLocalHamiltonianEnergyDensity (hd : 0 < d)
    (hω : InfiniteSpinSystem.IsInfiniteVolumeGroundState S εGS ω) :
    HasBoxLocalHamiltonianEnergyDensity S ω εGS := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards with n
  exact (hω.boxLocalHamiltonianEnergyDensity_eq
    (boxBondCount_pos d (n + 1) hd (Nat.succ_le_succ (Nat.zero_le n)))).symm

end InfiniteSpinSystem.IsInfiniteVolumeGroundState

end LatticeSystem.Quantum
