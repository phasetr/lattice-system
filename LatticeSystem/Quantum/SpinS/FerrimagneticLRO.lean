import LatticeSystem.Quantum.SpinS.Heisenberg
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Tasaki §4.1: ferrimagnetic long-range order on an asymmetric bipartite lattice (Theorem 4.4)

For the spin-`S` antiferromagnetic Heisenberg model on a *connected* bipartite lattice
`Λ = A ∪ B` (the same setting as Theorem 2.3 / the Lieb–Mattis theorem), Shen, Qiu, and Tian proved
that the ground states exhibit **ferrimagnetic long-range order** whenever the two sublattices are
imbalanced, `|A| ≠ |B|` (Theorem 4.4, eq. (4.1.13)):
`⟨Φ_GS| (Ô_Λ)² |Φ_GS⟩ ≥ S² (|A| − |B|)²`,
for *any* ground state `|Φ_GS⟩`, where `(Ô_Λ)² = Σ_α (Ô_Λ^{(α)})² = Σ_{x,y} (−1)^x (−1)^y Ŝ_x · Ŝ_y`
(eq. (4.1.12)) is the `SU(2)`-invariant squared staggered order operator.  When `|A| − |B| = a|Λ|`
with `a > 0` (e.g. the Lieb lattice, `a = 1/3`), eq. (4.1.13) gives
`⟨Φ_GS| (Ô_Λ)²/|Λ| |Φ_GS⟩ ≥ (aS)²` (eq. (4.1.14)) — genuine long-range order.

Unlike the existence theorems 4.1–4.3, Theorem 4.4 has a complete *finite-volume* proof in Tasaki
(the chain (4.1.16): the cross-term positivity (4.1.15) from Problem 2.5.d, the Lieb–Mattis total
spin `S_tot = (|A| − |B|) S` from Theorem 2.3, and `⟨(Ŝ_tot)²⟩ = S_tot(S_tot + 1) ≥ S_tot²`).  It is
therefore fully **discharged**: this file defines only the `SU(2)`-invariant squared staggered
order operator `staggeredCasimirOpS`, while Theorem 4.4 itself is proved sorry-free as the theorem
`shenQiuTian_ferrimagnetic_lro` in `FerrimagneticLROUniversalFinal.lean` (the universal form over
*every* normalized ground state, via the magnetization-sector decomposition of `(Ô_Λ)²`, the
connected Marshall–Lieb–Mattis ground-state data, strict outside-sector energy separation, and the
`SU(2)` ladder constancy of the staggered-order Rayleigh ratio across the spin-`S_tot` multiplet).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, Theorem 4.4, eqs. (4.1.12)–(4.1.16), pp. 77–78 (Shen, Qiu, and Tian [59]).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The **`SU(2)`-invariant squared staggered order operator**
`(Ô_Λ)² = Σ_{x,y} ε_x ε_y Ŝ_x · Ŝ_y` (eq. (4.1.12)), for a sublattice assignment `A : Λ → Bool`
(`ε_x = +1` on the `A`-sublattice, `−1` on the other).  Summing the three squared components
`Σ_α (Ô_Λ^{(α)})²` collapses to this single bilinear in the spin–spin dot products `Ŝ_x · Ŝ_y`, so
the operator is manifestly `SU(2)` invariant and its ground-state expectation is independent of the
choice of a (possibly degenerate) ground state. -/
noncomputable def staggeredCasimirOpS (A : Λ → Bool) (N : ℕ) : ManyBodyOpS Λ N :=
  ∑ x : Λ, ∑ y : Λ,
    ((if A x then (1 : ℂ) else (-1 : ℂ)) * (if A y then (1 : ℂ) else (-1 : ℂ))) • spinSDot x y N

end LatticeSystem.Quantum
