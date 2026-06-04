import LatticeSystem.Fermion.JordanWigner.Hubbard.NonsingularHubbardModel

/-!
# Tasaki §11.4.1: the Wannier-state-perturbation example model (eq. (11.4.1))

Section 11.4.1 ("Wannier State Perturbation Theory") is a *heuristic, non-rigorous*
motivation for the non-singular Hubbard theory; it contains no numbered theorems.  Its
one concrete, formalisable object is the **illustrative example model** (eq. (11.4.1)):
the one-dimensional Tasaki flat-band model (§11.3.1) with the on-site potential on the
*internal* sites shifted by `γ`,
`t_{x,y} = ν t` (`|x−y|=1/2`), `ν² t` (external, `|x−y|=1`), `(1+γ) t` (internal on-site),
`2ν² t` (external on-site), `0` otherwise.

Tasaki notes (11.4.1) reduces to the flat-band hopping (11.3.22) when `γ = 0`.  Indeed the
only `γ`-dependence is the internal on-site term `(1+γ) t` vs `t`, i.e. an added internal
on-site potential `γ t Σ_{u∈I} n̂_u`.  We therefore realise this example as an instance of
the general non-singular model (`nonsingularHubbardHamiltonian`, eq. (11.4.23)) whose
perturbation hopping is the internal-site number operator (`ζ = γ t`).  This explicitly
covers §11.4.1's formalisable content and shows it is subsumed by §11.4.2's general model.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.4.1, eq. (11.4.1) (pp. 415–416).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- The §11.4.1 perturbation hopping: the diagonal indicator of the **internal** sites
(odd physical indices `2u+1` in the interleaved decorated chain).  Combined with the
coefficient `ζ = γ t` in `nonsingularHubbardHamiltonian`, this realises the on-site
potential shift `γ t Σ_{u∈I} n̂_u` of eq. (11.4.1). -/
def wannierExamplePerturbation (K : ℕ) :
    Fin (2 * K + 2) → Fin (2 * K + 2) → ℂ :=
  fun x y => if x = y ∧ Odd x.val then 1 else 0

/-- **The Wannier-perturbation example model** (Tasaki §11.4.1, eq. (11.4.1)): the
one-dimensional flat-band model with the internal on-site potential shifted by `γ`,
realised as the non-singular Hubbard model whose perturbation is `γ t` times the
internal-site number operator. -/
noncomputable def wannierExampleModel (K : ℕ) (ν t γ U : ℝ) :
    ManyBodyOp (Fin (2 * (2 * K + 1) + 2)) :=
  nonsingularHubbardHamiltonian K ν t (γ * t) (wannierExamplePerturbation K) U

/-- The §11.4.1 perturbation hopping is Hermitian (it is a real diagonal indicator). -/
theorem wannierExamplePerturbation_isHermitian (K : ℕ) :
    ∀ i j, star (wannierExamplePerturbation K i j) = wannierExamplePerturbation K j i := by
  intro i j
  unfold wannierExamplePerturbation
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (by tauto), if_neg (by tauto)]; simp

/-- The Wannier example model is Hermitian (for real parameters). -/
theorem wannierExampleModel_isHermitian (K : ℕ) (ν t γ U : ℝ) :
    (wannierExampleModel K ν t γ U).IsHermitian :=
  nonsingularHubbardHamiltonian_isHermitian K ν t (γ * t)
    (wannierExamplePerturbation_isHermitian K) U

/-- **`γ = 0` reduces to the flat-band model** (Tasaki: eq. (11.4.1) reduces to (11.3.22)
when `γ = 0`): with no on-site shift the Wannier example model is exactly the §11.3.1
flat-band Hamiltonian. -/
theorem wannierExampleModel_gamma_zero (K : ℕ) (ν t U : ℝ) :
    wannierExampleModel K ν t 0 U = flatBandHamiltonian K ν t U := by
  unfold wannierExampleModel nonsingularHubbardHamiltonian
  simp

end LatticeSystem.Fermion
