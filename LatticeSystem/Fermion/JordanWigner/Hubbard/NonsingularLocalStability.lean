import LatticeSystem.Fermion.JordanWigner.Hubbard.NonsingularHubbardModel
import LatticeSystem.Fermion.JordanWigner.Hubbard.SectorMinEnergy

/-!
# Tasaki §11.4: local stability of ferromagnetism (Theorem 11.18)

Tasaki's first non-singular Hubbard theorem (Theorem 11.18) is the *local stability* of
the ferromagnetic ground states: under a small perturbation (controlled by parameters
`ν, ζ, U`), the maximal-spin sector lies strictly below the once-flipped sector,
`E_min(S_max) < E_min(S_max − 1)`.  This is ferromagnetic stability against a single spin
flip — necessary but not sufficient for global ferromagnetism (Theorem 11.20).

The result is proved by Tasaki via an elementary but rigorous perturbation theory; it is
recorded here as a documented `axiom` (Issue #4189, matching the Theorem 11.8 / 11.13 /
11.15 policy), to be discharged in later work.

The maximal total spin is `S_max = N/2 = |E|/2 = (K+1)/2`, so in the `twoS = 2S` indexing of
`sectorMinEnergy` the maximal-spin sector is `twoS = K+1` and the once-flipped sector is
`twoS = K−1`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.4, Theorem 11.18, eqs. (11.4.24)–(11.4.29) (pp. 422–423).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- **Regularity of the non-singular perturbation hopping** (Tasaki eqs. (11.4.24)–(11.4.25)):
the perturbation `tPert` is translation invariant (`t_{x+z,y+z} = t_{x,y}`, with the periodic
boundary conditions encoded by cyclic `Fin` addition) and summable with range `R`
(`Σ_y |t_{x,y}| ≤ t` and `Σ_y |x−y| |t_{x,y}| ≤ t R`). -/
def IsNonsingularHopping (K : ℕ) (tPert : Fin (2 * K + 2) → Fin (2 * K + 2) → ℂ)
    (t R : ℝ) : Prop :=
  (∀ x y z : Fin (2 * K + 2), tPert (x + z) (y + z) = tPert x y) ∧
    (∀ x : Fin (2 * K + 2), (∑ y, ‖tPert x y‖) ≤ t) ∧
    (∀ x : Fin (2 * K + 2),
      (∑ y, |(x.val : ℝ) - (y.val : ℝ)| * ‖tPert x y‖) ≤ t * R)

/-- **Tasaki Theorem 11.18 (local stability of ferromagnetic ground states), AXIOM.**
There are constants `ν₀, η₀, ξ₀ > 0` (depending only on the dimension `d = 1` and the
hopping range `R`, uniformly in the system size `K`) such that, for the non-singular
Hubbard model with parameters satisfying `0 < ν ≤ ν₀`, `|ζ| ≤ ν³ η₀`, and `U ≥ ξ₀ t |ζ| / ν²`
(eqs. (11.4.27)–(11.4.28)), the maximal-spin sector lies strictly below the once-flipped
sector (eq. (11.4.29)):
`E_min(S_max) < E_min(S_max − 1)`,
i.e. the ferromagnetic ground states are stable against a single spin flip.  Tasaki's
perturbation-theory proof is deferred; this is a documented axiom. -/
axiom nonsingular_theorem_11_18 (R : ℝ) (hR : 0 < R) :
    ∃ ν0 η0 ξ0 : ℝ, 0 < ν0 ∧ 0 < η0 ∧ 0 < ξ0 ∧
      ∀ (K : ℕ) (ν t ζ U : ℝ) (tPert : Fin (2 * K + 2) → Fin (2 * K + 2) → ℂ),
        0 < t → 0 < ν → ν ≤ ν0 → |ζ| ≤ ν ^ 3 * η0 → ξ0 * t * |ζ| / ν ^ 2 ≤ U →
        IsNonsingularHopping K tPert t R →
        sectorMinEnergy (nonsingularHubbardHamiltonian K ν t ζ tPert U) (K + 1) (K + 1)
          < sectorMinEnergy (nonsingularHubbardHamiltonian K ν t ζ tPert U) (K + 1) (K - 1)

end LatticeSystem.Fermion
