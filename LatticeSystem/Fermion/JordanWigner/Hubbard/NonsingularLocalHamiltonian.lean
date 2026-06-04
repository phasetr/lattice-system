import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiNonsingularFerro
import LatticeSystem.Fermion.JordanWigner.Hubbard.SectorMinEnergy
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Tasaki §11.4.3: the frustration-free local Hamiltonian `ĥ_p` and Lemmas 11.21–11.23

Tasaki proves Theorem 11.20 (`tasaki_theorem_11_20`) by writing the Hamiltonian as a
*frustration-free* sum of local Hamiltonians `ĥ_p` (eq. (11.4.46))
`Ĥ = −Lᵈ(1+2dν²)s·1 + lam Ĥ_flat + Σ_{p∈E} ĥ_p`,
where each `ĥ_p` (eq. (11.4.48)) acts on the site `p` and its `4d` neighbours, and proving
that `ĥ_p ≥ 0` in a parameter range.  This file (`d = 1`) defines `ĥ_p` and records the
three proof-internal numbered results — **Lemma 11.21** (`ĥ_p ≥ 0 ⇒` ferromagnetism, via
Theorem 11.11), **Lemma 11.22** (parameter conditions `⇒ ĥ_p ≥ 0`), and **Lemma 11.23**
(the `t,U↑∞` limit characterisation underlying 11.22) — as documented axioms (Theorem 11.20
itself remains the axiom whose proof these discharge).

`ĥ_p` (eq. (11.4.48), `d = 1`, `p` = external site `i`, with parameters
`0 < lam < min{t,U}`, `0 ≤ κ < 1`):
`ĥ_p = (1+2ν²)s·1 − s Σ_σ â†_{p,σ}â_{p,σ}
       + ((t−lam)/2) Σ_{u∈{i−1,i},σ} b̂†_{u,σ}b̂_{u,σ}
       + (1−κ)(U−lam) n̂_{p↑}n̂_{p↓} + ((U−lam)/2) Σ_{u∈{i−1,i}} n̂_{u↑}n̂_{u↓}
       + (κ/2)(U−lam) Σ_{q∈{i−1,i+1}} n̂_{q↑}n̂_{q↓}`,
where (project `d = 1` decorated chain) external `i`'s incident internal sites are `i−1, i`
and its external neighbours are `i−1, i+1` (cyclic in `Fin (K+1)`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.4.3, eqs. (11.4.46)–(11.4.50), Lemmas 11.21–11.23 (pp. 429–435).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped ComplexOrder

/-- The number operator `Σ_σ â†_{p,σ} â_{p,σ}` for the `α`-state at external site `p`. -/
noncomputable def flatBandANumber (K : ℕ) (ν : ℝ) (p : Fin (K + 1)) :
    ManyBodyOp (Fin (2 * (2 * K + 1) + 2)) :=
  ∑ σ : Fin 2, flatBandACreation K ν p σ * flatBandAAnnihilation K ν p σ

/-- The number operator `Σ_σ b̂†_{u,σ} b̂_{u,σ}` for the `β`-state at internal site `u`. -/
noncomputable def flatBandBNumber (K : ℕ) (ν : ℝ) (u : Fin (K + 1)) :
    ManyBodyOp (Fin (2 * (2 * K + 1) + 2)) :=
  ∑ σ : Fin 2, flatBandBCreation K ν u σ * flatBandBAnnihilation K ν u σ

/-- **The frustration-free local Hamiltonian `ĥ_p`** (Tasaki §11.4.3, eq. (11.4.48), `d = 1`)
for the external site `p = i`, with parameters `s, t, U, lam, κ`.  Acts nontrivially on `p`
and its four neighbours (the internal sites `i−1, i` and the external sites `i−1, i+1`). -/
noncomputable def nonsingularLocalHamiltonian (K : ℕ) (ν s t U lam κ : ℝ) (i : Fin (K + 1)) :
    ManyBodyOp (Fin (2 * (2 * K + 1) + 2)) :=
  ((1 + 2 * ν ^ 2) * s : ℂ) • (1 : ManyBodyOp _)
    - (s : ℂ) • flatBandANumber K ν i
    + (((t - lam) / 2 : ℝ) : ℂ) • (flatBandBNumber K ν (i - 1) + flatBandBNumber K ν i)
    + (((1 - κ) * (U - lam) : ℝ) : ℂ) • hubbardDoubleOccupancy (2 * K + 1) (deltaExternalSite K i)
    + (((U - lam) / 2 : ℝ) : ℂ) •
        (hubbardDoubleOccupancy (2 * K + 1) (deltaInternalSite K (i - 1)) +
          hubbardDoubleOccupancy (2 * K + 1) (deltaInternalSite K i))
    + ((κ / 2 * (U - lam) : ℝ) : ℂ) •
        (hubbardDoubleOccupancy (2 * K + 1) (deltaExternalSite K (i - 1)) +
          hubbardDoubleOccupancy (2 * K + 1) (deltaExternalSite K (i + 1)))

/-- **Tasaki Lemma 11.21 (frustration-free ⇒ ferromagnetism), AXIOM.**  If the local
Hamiltonian `ĥ_p` is positive semidefinite for every external site `p`, then the
non-singular Hubbard model is saturated-ferromagnetic (`E_min(S_max) < E_min(S)` for all
`S ≠ S_max = N/2`).  Tasaki's proof reduces to Theorem 11.11 via the frustration-free
decomposition (eq. (11.4.46)); recorded as a documented axiom (proof of Theorem 11.20). -/
axiom nonsingular_lemma_11_21 (K : ℕ) (ν s t U lam κ : ℝ) (hs : 0 < s)
    (hpos : ∀ i : Fin (K + 1),
      (nonsingularLocalHamiltonian K ν s t U lam κ i).PosSemidef) :
    exhibitsFerromagnetism (tasakiNonsingularHamiltonian K ν t s U) (K + 1)

/-- **Tasaki Lemma 11.22 (positivity of the local Hamiltonian), AXIOM.**  For `ν > 0`
(`d = 1`; for `d ≥ 2` one needs `0 < ν < ν_c(d)`) there are thresholds such that, once
`t/s` and `U/s` are large enough (with `lam, κ` taken proportional to `s`), the local
Hamiltonian `ĥ_p` is positive semidefinite for every `p`.  This is the analytic core of the
Theorem 11.20 proof; recorded as a documented axiom. -/
axiom nonsingular_lemma_11_22 (ν : ℝ) (hν : 0 < ν) :
    ∃ T V clam cκ : ℝ, 0 < T ∧ 0 < V ∧ 0 < clam ∧ 0 ≤ cκ ∧
      ∀ (K : ℕ) (s t U : ℝ), 0 < s → 0 < t → 0 < U → T ≤ t / s → V ≤ U / s →
        ∀ i : Fin (K + 1),
          (nonsingularLocalHamiltonian K ν s t U (clam * s) (cκ) i).PosSemidef

/-- **Tasaki Lemma 11.23 (zero-modes in the `t,U↑∞` limit), AXIOM.**  Underlying Lemma
11.22: for `ν` satisfying the Lemma 11.22 condition, any normalised state with
`S_tot < S_max` has strictly positive energy of the (system-size-independent) local
Hamiltonian in the `t,U↑∞` limit, so by continuity the nonzero eigenvalues are strictly
positive for large `t/s, U/s`.  Recorded as a documented axiom (the limiting statement is
phrased via the sector-minimum energy of `ĥ_p` being strictly positive below `S_max`). -/
axiom nonsingular_lemma_11_23 (ν : ℝ) (hν : 0 < ν) :
    ∃ T V clam cκ : ℝ, 0 < T ∧ 0 < V ∧ 0 < clam ∧ 0 ≤ cκ ∧
      ∀ (K : ℕ) (s t U : ℝ), 0 < s → 0 < t → 0 < U → T ≤ t / s → V ≤ U / s →
        ∀ (i : Fin (K + 1)) (twoS : ℕ), twoS < K + 1 →
          0 < sectorMinEnergy (nonsingularLocalHamiltonian K ν s t U (clam * s) cκ i) twoS

end LatticeSystem.Fermion
