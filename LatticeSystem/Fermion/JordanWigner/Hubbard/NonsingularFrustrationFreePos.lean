import LatticeSystem.Fermion.JordanWigner.Hubbard.NonsingularFrustrationFree
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandPosSemidef
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Tasaki §11.4.3: frustration-free positivity `Ĥ + const ≥ 0` (towards Lemma 11.21)

From the decomposition eq. (11.4.46), `Ĥ + (K+1)(1+2ν²)s·1 = (Σ_i ĥ_p i) + lam·(Σ_u N̂^β_u + Σ_x n↑n↓_x)`.
When every `ĥ_p ≥ 0` and `lam ≥ 0`, the right side is a sum of positive-semidefinite operators, so:

* `nonsingularRemainder_eq_flatBand` — the remainder `Σ_u N̂^β_u + Σ_x n↑n↓_x` is `flatBandHamiltonian K ν 1 1`;
* `tasakiNonsingular_add_const_posSemidef` — `(Ĥ + (K+1)(1+2ν²)s·1).PosSemidef`.

So the ground energy is `≥ −(K+1)(1+2ν²)s`; the max-spin tower (which annihilates the remainder and
every `ĥ_p`) achieves it.  This is the operator-positivity half of Lemma 11.21.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.4.3, eqs. (11.4.46)–(11.4.50), Lemma 11.21 (pp. 429–435).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators ComplexOrder

variable {K : ℕ} {ν : ℝ}

/-- The `lam`-remainder of the decomposition is the flat-band Hamiltonian at `t = U = 1`. -/
theorem nonsingularRemainder_eq_flatBand (K : ℕ) (ν : ℝ) :
    (∑ u, flatBandBNumber K ν u) + (∑ x, hubbardDoubleOccupancy (2 * K + 1) x)
      = flatBandHamiltonian K ν 1 1 := by
  rw [flatBandHamiltonian]
  simp only [flatBandBNumber, Complex.ofReal_one, one_smul]

/-- **Frustration-free positivity `Ĥ + const ≥ 0`.**  If every local Hamiltonian `ĥ_p` is
positive-semidefinite and `lam ≥ 0`, then `Ĥ + (K+1)(1+2ν²)s·1` is positive-semidefinite (a sum of
the `ĥ_p` and the positive `lam`-remainder, by the decomposition eq. (11.4.46)).  Hence the ground
energy is at least `−(K+1)(1+2ν²)s`. -/
theorem tasakiNonsingular_add_const_posSemidef (K : ℕ) (ν s t U lam κ : ℝ) (hlam : 0 ≤ lam)
    (hpos : ∀ i : Fin (K + 1), (nonsingularLocalHamiltonian K ν s t U lam κ i).PosSemidef) :
    (tasakiNonsingularHamiltonian K ν t s U
      + ((K + 1 : ℂ) * ((1 + 2 * ν ^ 2) * s)) •
        (1 : ManyBodyOp (Fin (2 * (2 * K + 1) + 2)))).PosSemidef := by
  have hsum : (∑ i, nonsingularLocalHamiltonian K ν s t U lam κ i).PosSemidef := by
    refine Finset.sum_induction _ _ (fun a b ha hb => ha.add hb) Matrix.PosSemidef.zero ?_
    intro i _; exact hpos i
  have hP : (flatBandHamiltonian K ν 1 1).PosSemidef :=
    flatBandHamiltonian_posSemidef K ν 1 1 (by norm_num) (by norm_num)
  have hlamP : ((lam : ℂ) • flatBandHamiltonian K ν 1 1).PosSemidef :=
    hP.smul (by rw [Complex.le_def]; simp [hlam])
  have heq : tasakiNonsingularHamiltonian K ν t s U
      + ((K + 1 : ℂ) * ((1 + 2 * ν ^ 2) * s)) • (1 : ManyBodyOp _)
      = (∑ i, nonsingularLocalHamiltonian K ν s t U lam κ i)
        + (lam : ℂ) • flatBandHamiltonian K ν 1 1 := by
    rw [tasakiNonsingular_eq_sum_localHamiltonian K ν s t U lam κ, nonsingularRemainder_eq_flatBand]
    abel
  rw [heq]
  exact hsum.add hlamP

end LatticeSystem.Fermion
