import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Real.Basic

/-!
# The spin-space reflection-positivity eigenvalue rearrangement (Tasaki §10.2.4)

Twenty-ninth layer (PR29) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model), in the **corrected Hermitian-`W` endgame** (design doc at
`.self-local/docs/lieb-10-2-endgame-hermitian-W-design.md`).

The mathematical heart of Lieb's spin-space reflection-positivity inequality
`E(W) ≥ E(|W|)` (Tasaki eq. (10.2.41)→(10.2.43)) is an **elementary eigenvalue
rearrangement**. Writing a Hermitian coefficient matrix in its spectral form
`W = Σ_j λ_j v_j v_j†` (λ_j ∈ ℝ) and `|W| = Σ_j |λ_j| v_j v_j†`, the kinetic part of
the energy `Σ_j λ_j² (v_j†Tv_j)` is invariant under `λ_j ↦ |λ_j|` (`λ_j² = |λ_j|²`),
while the attractive interaction part `−Σ_x U_x Σ_{j,k} λ_j λ_k |v_j†I^(x)v_k|²`
(with `U_x > 0`) does not increase, because the nonnegative weights
`a_{j,k} = |v_j†I^(x)v_k|² ≥ 0` satisfy

  `Σ_{j,k} λ_j λ_k a_{j,k} ≤ Σ_{j,k} |λ_j| |λ_k| a_{j,k}`

termwise (`λ_j λ_k ≤ |λ_j λ_k| = |λ_j| |λ_k|`). This file isolates that elementary
inequality; assembling it into the full energy functional `E(W) ≥ E(|W|)` (on the
sectorized Hermitian coefficient matrix) is a subsequent layer.

## Main results

* `lieb_srp_rearrangement` — `Σ_{j,k} λ_j λ_k a_{j,k} ≤ Σ_{j,k} |λ_j| |λ_k| a_{j,k}`
  for real `λ` and nonnegative weights `a`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4, eq. (10.2.41)–(10.2.43); E. H. Lieb,
*Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open scoped BigOperators

/-- **The spin-space reflection-positivity eigenvalue rearrangement.** For real
eigenvalues `λ_j` and nonnegative weights `a_{j,k} ≥ 0`, replacing each `λ_j` by its
absolute value never decreases the double sum `Σ_{j,k} λ_j λ_k a_{j,k}`. This is the
elementary core of Lieb's inequality `E(W) ≥ E(|W|)`: the attractive interaction
energy `−Σ U_x Σ_{j,k} λ_j λ_k a_{j,k}` (with `U_x > 0`) does not increase under
`λ_j ↦ |λ_j|`. -/
theorem lieb_srp_rearrangement {ι : Type*} [Fintype ι] (lam : ι → ℝ)
    (a : ι → ι → ℝ) (ha : ∀ j k, 0 ≤ a j k) :
    ∑ j : ι, ∑ k : ι, lam j * lam k * a j k
      ≤ ∑ j : ι, ∑ k : ι, |lam j| * |lam k| * a j k := by
  refine Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => ?_))
  refine mul_le_mul_of_nonneg_right ?_ (ha j k)
  calc lam j * lam k ≤ |lam j * lam k| := le_abs_self _
    _ = |lam j| * |lam k| := abs_mul _ _

end LatticeSystem.Fermion
