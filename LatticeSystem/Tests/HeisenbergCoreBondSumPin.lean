import LatticeSystem.Quantum.SpinS.HeisenbergCore
import LatticeSystem.Quantum.SpinS.AndersonTower

/-!
# Signature pin: the ordered-pair bond sum at the hypercubic-torus coupling

Repository-internal regression guard, **not** a Tasaki result on its own.  The spin-`S`
Heisenberg-type Hamiltonian `Ĥ_J = Σ_{x, y ∈ Λ} J(x, y) Ŝ_x · Ŝ_y` at the nearest-neighbour
coupling `torusNNCoupling d L` of the `d`-dimensional torus `(ℤ/L)^d`, presented as a single sum
over ordered pairs.  This is the general reindexing along `Fintype.sum_prod_type`
(`LatticeSystem/Tests/HeisenbergCoreBondSumGeneralPin.lean`) at one coupling, not a separate fact.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.4, eq. (2.4.1), p. 32.
-/

namespace LatticeSystem.Tests.HeisenbergCoreBondSumPin

open LatticeSystem.Quantum

/-- **Signature pin.** The `torusNNCoupling` specialization is the general lemma applied. -/
example (d L N : ℕ) [NeZero L] :
    heisenbergHamiltonianS (torusNNCoupling d L) N
      = ∑ p : HypercubicTorus d L × HypercubicTorus d L,
          torusNNCoupling d L p.1 p.2 • spinSDot p.1 p.2 N :=
  (sum_prod_smul_spinSDot (torusNNCoupling d L) N).symm

end LatticeSystem.Tests.HeisenbergCoreBondSumPin
