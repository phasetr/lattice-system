import LatticeSystem.Quantum.SpinS.DysonLiebSimon
import LatticeSystem.Quantum.SpinS.Heisenberg

/-!
# Tasaki §4.1: absence of symmetry breaking in one dimension (Theorem 4.2, Shastry)

For the one-dimensional spin-`S` antiferromagnetic Heisenberg model on a ring of `L` sites under a
staggered magnetic field (eq. (4.1.9)),
`Ĥ_h = Σ_x Ŝ_x · Ŝ_{x+1} − h Σ_x (−1)^x Ŝ_x^{(3)}` (periodic, `Ŝ_{L+1} = Ŝ_1`),
Shastry's theorem (Theorem 4.2) asserts that the staggered order parameter vanishes in the iterated
thermodynamic-then-zero-field limit (eq. (4.1.10)):
`lim_{h↓0} lim_{L↑∞} ⟨Φ_GS,h| Ô_L^{(3)}/L |Φ_GS,h⟩ = 0`,
so the model never exhibits spontaneous symmetry breaking even though the staggered field is
designed to enhance the staggered moment.

Tasaki does **not** prove Theorem 4.2 (footnote 3, p. 76: the original argument of Shastry [58] is
not stated as a mathematical theorem; a rigorous formulation is in [63]).

This file carries only the *model*: the ring nearest-neighbor coupling, the staggered-field chain
Hamiltonian of eq. (4.1.9), and its Hermiticity.  Theorem 4.2 itself, the variational reduction of
it to a scalar energy-gain condition, and the documented axiom carrying that condition, live in
`ShastryNoSSBReduction.lean`, which needs the minimum-eigenvalue machinery this file deliberately
does not import.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, Theorem 4.2, eqs. (4.1.9)–(4.1.10), pp. 76–77 (Shastry [58]; cf. [63]).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {N : ℕ}

/-- The **directed nearest-neighbor coupling on the ring** `Fin L`: `J x y = 1` exactly when `y` is
the cyclic successor `x + 1 (mod L)` of `x`, and `0` otherwise.  Summed against `Ŝ_x · Ŝ_y` this
reproduces the periodic chain interaction `Σ_x Ŝ_x · Ŝ_{x+1}` (with `Ŝ_{L+1} = Ŝ_1`). -/
def ringCoupling (L : ℕ) (x y : Fin L) : ℂ :=
  if y.val = (x.val + 1) % L then 1 else 0

/-- The **staggered sublattice sign** on the ring `Fin L`: `A x = true` on even sites and `false` on
odd sites, so the associated sublattice sign is `ε_x = (−1)^x`.  Used with `staggeredOrderOpS` it
gives the staggered order operator `Ô_L^{(3)} = Σ_x (−1)^x Ŝ_x^{(3)}`. -/
def ringStaggeredSublattice (L : ℕ) (x : Fin L) : Bool := x.val % 2 = 0

/-- The ring nearest-neighbor coupling is real-valued (`0`/`1`), hence self-conjugate. -/
theorem ringCoupling_self_star (L : ℕ) (x y : Fin L) :
    star (ringCoupling L x y) = ringCoupling L x y := by
  unfold ringCoupling; split <;> simp

/-- The **one-dimensional staggered-field antiferromagnetic Heisenberg Hamiltonian** on a ring of
`L` sites (eq. (4.1.9)): `Ĥ_h = Σ_x Ŝ_x · Ŝ_{x+1} − h · Ô_L^{(3)}`, with `Ô_L^{(3)}` the staggered
order operator.  The staggered field `−h (−1)^x Ŝ_x^{(3)}` is designed to trigger possible symmetry
breaking. -/
noncomputable def staggeredFieldChainHamiltonianS (L : ℕ) (h : ℝ) (N : ℕ) :
    ManyBodyOpS (Fin L) N :=
  heisenbergHamiltonianS (ringCoupling L) N
    - (h : ℂ) • staggeredOrderOpS (ringStaggeredSublattice L) N

/-- **The staggered-field chain Hamiltonian is Hermitian** (eq. (4.1.9), p. 76).  `Ĥ_h` is the
difference of the Hermitian ring Heisenberg Hamiltonian
(`heisenbergHamiltonianS_isHermitian_of_real` at the real `0`/`1` coupling `ringCoupling_self_star`)
and the real scalar multiple `h · Ô_L^{(3)}` of the Hermitian staggered order operator
(`staggeredOrderOpS_isHermitian`), hence Hermitian for every ring size `L`, every real field `h` and
every spin `N`.  No parity or positivity restriction on `L` is used: the statement holds verbatim at
`L = 0` (one-dimensional Hilbert space, both summands empty) and at `L = 1` (where `ringCoupling 1`
degenerates to the self-loop `J 0 0 = 1`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, eq. (4.1.9), p. 76. -/
theorem staggeredFieldChainHamiltonianS_isHermitian (L : ℕ) (h : ℝ) (N : ℕ) :
    (staggeredFieldChainHamiltonianS L h N).IsHermitian := by
  unfold staggeredFieldChainHamiltonianS
  refine (heisenbergHamiltonianS_isHermitian_of_real (ringCoupling_self_star L) N).sub
    ((staggeredOrderOpS_isHermitian (ringStaggeredSublattice L) N).smul ?_)
  rw [isSelfAdjoint_iff]
  exact Complex.conj_ofReal h

end LatticeSystem.Quantum
