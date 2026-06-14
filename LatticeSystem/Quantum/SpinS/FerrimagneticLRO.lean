import LatticeSystem.Quantum.SpinS.Heisenberg

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
therefore a **discharge candidate**; here we record it as a faithful, sound documented axiom over the
concrete connected bipartite antiferromagnetic family (same hypotheses as Theorem 2.3), to be
discharged once the §2.5 Theorem 2.3 total-spin API and the (4.1.15) cross-term inequality are
assembled.

This file defines the `SU(2)`-invariant squared staggered order operator `staggeredCasimirOpS` and
states Theorem 4.4.

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

/-- **Tasaki Theorem 4.4 (Shen–Qiu–Tian ferrimagnetic long-range order), AXIOM.**  Consider the
spin-`S` (`S = N/2`) antiferromagnetic Heisenberg model on a *connected* bipartite lattice with
sublattice assignment `A`, under the same hypotheses as Theorem 2.3: the coupling `J` is real
(`hreal`) and symmetric (`hsym`), vanishes within a sublattice (`hbip`), and is strictly
antiferromagnetic across the bipartition (`hcross`: every cross-sublattice pair is coupled with
positive strength — this is the connectivity that makes the Lieb–Mattis theorem apply), with both
sublattices nonempty (`hA`, `hB`).  Then for *any* normalized ground state `Φ` of
`heisenbergHamiltonianS J N`, the squared staggered order parameter is bounded below by
`S² (|A| − |B|)²` (eq. (4.1.13)):
`(N/2)² (|A| − |B|)² ≤ ⟨Φ, (Ô_Λ)² Φ⟩.re`.

The left-hand side is independent of the choice of ground state because `(Ô_Λ)²` is `SU(2)`
invariant.  Tasaki gives a finite-volume proof (chain (4.1.16)); we record Theorem 4.4 as a faithful
documented axiom (a discharge candidate) over the concrete connected bipartite antiferromagnetic
family. -/
axiom shenQiuTian_ferrimagnetic_lro (A : Λ → Bool) (J : Λ → Λ → ℂ) (N : ℕ)
    (hreal : ∀ x y, (J x y).im = 0) (hsym : ∀ x y, J x y = J y x)
    (hbip : ∀ x y, A x = A y → J x y = 0)
    (hcross : ∀ x y, A x ≠ A y → 0 < (J x y).re)
    (hA : 1 ≤ (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hB : 1 ≤ (Finset.univ.filter (fun x : Λ => A x = false)).card)
    (Φ : (Λ → Fin (N + 1)) → ℂ) (hnorm : star Φ ⬝ᵥ Φ = 1)
    (hgs : ∃ E₀ : ℂ, (heisenbergHamiltonianS J N).mulVec Φ = E₀ • Φ ∧
      (∀ E : ℂ, ∀ Ψ : (Λ → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
        (heisenbergHamiltonianS J N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) ∧ Φ ≠ 0) :
    ((N : ℝ) / 2) ^ 2 *
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℤ) -
          ((Finset.univ.filter (fun x : Λ => A x = false)).card : ℤ) : ℝ) ^ 2 ≤
      (star Φ ⬝ᵥ (staggeredCasimirOpS A N).mulVec Φ).re

end LatticeSystem.Quantum
