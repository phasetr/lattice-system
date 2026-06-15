import LatticeSystem.Quantum.SpinS.HypercubicBoxModel
import LatticeSystem.Quantum.SpinS.InfiniteVolumeGroundState

/-!
# Thermodynamic-limit bridge: the box AFM model → the §4.3 infinite-volume system

This is the capstone of the thermodynamic-limit thread (Issue #4564): it connects
the **concrete** finite-volume antiferromagnetic Heisenberg model on the boxes
`Λ_n ⊂ ℤᵈ` (`boxAFMHeisenbergHamiltonianS`, matrices) to the **abstract** §4.3
infinite-volume system (`InfiniteSpinSystem` over a quasi-local C*-algebra).

The two formalizations are deliberately **not identified** — there is no
canonical map from the finite matrix algebras to the abstract C*-algebra `A`.
Instead the bridge is a *documented conditional predicate*
`IsAFMThermodynamicLimit S N` ("`S` is the `L↑∞` limit of the spin-`N/2` box AFM
model on `ℤᵈ`"), kept uninterpreted (like `IsGroundStateEnergyDensity`), together
with a faithful documented axiom relating the abstract energy density of such an
`S` to the concrete finite-box limit `boxGroundEnergyDensitySLimit d N` (the value
whose existence is the PR2 axiom `boxGroundEnergyDensityS_tendsto`).  From this and
the existing `theorem_4_20_omega0`, the existence of an infinite-volume ground
state *for the box AFM model's thermodynamic limit* is then a **proved theorem**.

This records the §4.3 thermodynamic-limit connection at the axiom level
(the deep operator-algebraic content) without asserting the existence of the limit
system itself (the quasi-local C*-algebra inductive-limit construction, a heavier
statement deferred to a future thread).

## References

* Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
  (1st ed., Springer, 2020), §4.3 (eqs. (4.3.4), (4.3.7)).
-/

namespace LatticeSystem.Quantum

open scoped Topology

/-- The **thermodynamic-limit ground-state energy density** of the spin-`N/2` box
AFM Heisenberg model on `ℤᵈ`, named from the finite-box convergence axiom
`boxGroundEnergyDensityS_tendsto` (the limit is unique by the Hausdorff property of
`ℝ`).  For invalid parameters (`d = 0` or `N = 0`) it is set to `0`; all
mathematical use is under `0 < d` and `0 < N`. -/
noncomputable def boxGroundEnergyDensitySLimit (d N : ℕ) : ℝ :=
  if h : 0 < d ∧ 0 < N then
    Classical.choose (boxGroundEnergyDensityS_tendsto d N h.1 h.2)
  else 0

/-- The named limit `boxGroundEnergyDensitySLimit d N` is indeed the limit of the
concrete finite-box energy densities `boxGroundEnergyDensityS d n N` as `n → ∞`. -/
theorem boxGroundEnergyDensityS_tendsto_limit (d N : ℕ) (hd : 0 < d) (hN : 0 < N) :
    Filter.Tendsto (fun n : ℕ => boxGroundEnergyDensityS d n N)
      Filter.atTop (nhds (boxGroundEnergyDensitySLimit d N)) := by
  classical
  rw [boxGroundEnergyDensitySLimit, dif_pos ⟨hd, hN⟩]
  exact Classical.choose_spec (boxGroundEnergyDensityS_tendsto d N hd hN)

namespace InfiniteSpinSystem

/-- **`S` is the infinite-volume thermodynamic limit of the box AFM model**
(documented relating predicate): the abstract `InfiniteSpinSystem d A` is the
`L↑∞` limit of the spin-`N/2` antiferromagnetic Heisenberg model on the hypercubic
boxes `Λ_n ⊂ ℤᵈ`.  Kept uninterpreted — it is neither a construction nor an
identification of the finite matrix algebras with the abstract quasi-local
C*-algebra; it makes the bridge genuinely conditional (it does not assert that
such an `S` exists). -/
axiom IsAFMThermodynamicLimit
    {d : ℕ} {A : Type*} [CStarAlgebra A] [NormedSpace ℂ A] [StarModule ℂ A]
    (S : InfiniteSpinSystem d A) (N : ℕ) : Prop

/-- **Thermodynamic-limit energy-density bridge (documented axiom).**  If `S` is the
thermodynamic limit of the concrete box AFM model (`IsAFMThermodynamicLimit S N`),
then its abstract ground-state energy density (§4.3) is the concrete finite-box
limit `boxGroundEnergyDensitySLimit d N` (Tasaki eq. (4.3.4)).  Faithful and
conditional: it supplies `IsGroundStateEnergyDensity` only for genuine
thermodynamic-limit systems, with the value pinned to the concrete box limit. -/
axiom afmThermodynamicLimit_energyDensity
    {d : ℕ} {A : Type*} [CStarAlgebra A] [NormedSpace ℂ A] [StarModule ℂ A]
    (S : InfiniteSpinSystem d A) (N : ℕ) (hd : 0 < d) (hN : 0 < N)
    (hS : IsAFMThermodynamicLimit S N) :
    IsGroundStateEnergyDensity S (boxGroundEnergyDensitySLimit d N)

/-- **The symmetric infinite-volume ground state exists for the box AFM model's
thermodynamic limit** (proved from the energy-density bridge + Theorem 4.20).  For
any abstract `S` known to be the `L↑∞` limit of the concrete box AFM model, there
is a translation-invariant infinite-volume ground state `ω_0` at the concrete
energy density, with vanishing single-site magnetization (eqs. (4.3.7), (4.3.9)). -/
theorem afmThermodynamicLimit_exists_omega0
    {d : ℕ} {A : Type*} [CStarAlgebra A] [NormedSpace ℂ A] [StarModule ℂ A]
    (S : InfiniteSpinSystem d A) (N : ℕ) (hd : 0 < d) (hN : 0 < N)
    (hS : IsAFMThermodynamicLimit S N) :
    ∃ ω0 : WeakDual ℂ A,
      IsInfiniteVolumeGroundState S (boxGroundEnergyDensitySLimit d N) ω0 ∧
        ∀ (x : Fin d → ℤ) (α : Fin 3), ω0 (S.spin x α) = 0 :=
  theorem_4_20_omega0 S (boxGroundEnergyDensitySLimit d N)
    (afmThermodynamicLimit_energyDensity S N hd hN hS)

/-- **The symmetry-breaking infinite-volume ground states exist for the box AFM
model's thermodynamic limit** (proved from the energy-density bridge +
Theorem 4.20).  Assuming `S` is the `L↑∞` limit of the concrete box AFM model and
the model has staggered long-range order with order parameter `m∗ > 0`
(`HasStaggeredLRO`), then for every unit direction `n ∈ ℝ³` there is a
translation-invariant infinite-volume ground state `ω_n` at the concrete energy
density, with Néel magnetization `ω_n(Ŝ_x^{(α)}) = (−1)^x m∗ n_α` (eqs. (4.3.8),
(4.3.10)) — full spontaneous symmetry breaking.  Vacuous in one dimension, where
there is no long-range order (`HasStaggeredLRO` is unavailable, cf. Corollary 4.3). -/
theorem afmThermodynamicLimit_exists_omegaN
    {d : ℕ} {A : Type*} [CStarAlgebra A] [NormedSpace ℂ A] [StarModule ℂ A]
    (S : InfiniteSpinSystem d A) (N : ℕ) (hd : 0 < d) (hN : 0 < N)
    (hS : IsAFMThermodynamicLimit S N)
    (mStar : ℝ) (hm : 0 < mStar) (hLRO : HasStaggeredLRO S mStar)
    (n : Fin 3 → ℝ) (hn : IsUnitVector n) :
    ∃ ωn : WeakDual ℂ A,
      IsInfiniteVolumeGroundState S (boxGroundEnergyDensitySLimit d N) ωn ∧
        ∀ (x : Fin d → ℤ) (α : Fin 3),
          ωn (S.spin x α) = ((staggeredSign x : ℝ) : ℂ) * (mStar : ℂ) * (n α : ℂ) :=
  theorem_4_20_omegaN S (boxGroundEnergyDensitySLimit d N)
    (afmThermodynamicLimit_energyDensity S N hd hN hS) mStar hm hLRO n hn

end InfiniteSpinSystem

end LatticeSystem.Quantum
