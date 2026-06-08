import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiNonsingularFerro
import LatticeSystem.Fermion.JordanWigner.Hubbard.SectorMinEnergy
import LatticeSystem.Fermion.JordanWigner.Hubbard.NonsingularAllUpAnnihilation
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Tasaki §11.4.3: the frustration-free local Hamiltonian `ĥ_p` and Lemmas 11.21–11.23

Tasaki proves Theorem 11.20 (`tasaki_theorem_11_20`) by writing the Hamiltonian as a
*frustration-free* sum of local Hamiltonians `ĥ_p` (eq. (11.4.46))
`Ĥ = −Lᵈ(1+2dν²)s·1 + lam Ĥ_flat + Σ_{p∈E} ĥ_p`,
where each `ĥ_p` (eq. (11.4.48)) acts on the site `p` and its `4d` neighbours, and proving
that `ĥ_p ≥ 0` in a parameter range.  This file (`d = 1`) defines `ĥ_p` and records the
two analytic proof-internal numbered results — **Lemma 11.22** (parameter conditions
`⇒ ĥ_p ≥ 0`) and **Lemma 11.23** (the `t,U↑∞` limit characterisation underlying 11.22) — as
documented axioms (these genuinely need eigenvalue-continuity perturbation theory mathlib
lacks).  **Lemma 11.21** (`ĥ_p ≥ 0 ⇒` ferromagnetism, via Theorem 11.11) is *proved* as
`nonsingular_exhibitsFerromagnetism`, and **Theorem 11.20** is assembled as
`tasaki_theorem_11_20`, both in `NonsingularFerromagnetism.lean`.

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

/-! ## The local Hamiltonian annihilates the all-up state (`ĥ_p |Φα,all↑⟩ = 0`)

Tasaki p. 430: the all-up flat-band state is a zero-mode of every `ĥ_p`.  The α-number gives
`(1+2ν²)` (cancelling the constant `(1+2ν²)s`), while the β-number and the Coulomb terms vanish. -/

/-- `(Σ_σ â†_{p,σ} â_{p,σ}) |Φα,all↑⟩ = (1+2ν²) |Φα,all↑⟩` (genuine chain `p − 1 ≠ p`).  The
up-channel `â†_↑ â_↑ = (1+2ν²)·1 − â_↑ â†_↑` with `â†_↑|Φ↑⟩=0`; the down-channel `â_↓|Φ↑⟩=0`. -/
theorem flatBandANumber_mulVec_alphaAllUpState (K : ℕ) (ν : ℝ) (p : Fin (K + 1))
    (hp : p - 1 ≠ p) :
    (flatBandANumber K ν p).mulVec (flatBandAlphaAllUpState K ν) =
      ((1 + 2 * ν ^ 2 : ℝ) : ℂ) • flatBandAlphaAllUpState K ν := by
  unfold flatBandANumber
  rw [Matrix.sum_mulVec, Fin.sum_univ_two]
  have hup : (flatBandACreation K ν p 0 * flatBandAAnnihilation K ν p 0).mulVec
      (flatBandAlphaAllUpState K ν) = ((1 + 2 * ν ^ 2 : ℝ) : ℂ) • flatBandAlphaAllUpState K ν := by
    have hcr : flatBandACreation K ν p 0 * flatBandAAnnihilation K ν p 0
        = ((1 + 2 * ν ^ 2 : ℝ) : ℂ) • (1 : ManyBodyOp (Fin (2 * (2 * K + 1) + 2)))
          - flatBandAAnnihilation K ν p 0 * flatBandACreation K ν p 0 := by
      rw [eq_sub_iff_add_eq]
      exact (add_comm _ _).trans (flatBandAAnnihilation_ACreation_anticomm_self K ν p 0 hp)
    have hkill : (flatBandAAnnihilation K ν p 0 * flatBandACreation K ν p 0).mulVec
        (flatBandAlphaAllUpState K ν) = 0 := by
      rw [show (flatBandAAnnihilation K ν p 0 * flatBandACreation K ν p 0).mulVec
            (flatBandAlphaAllUpState K ν)
          = (flatBandAAnnihilation K ν p 0).mulVec
            ((flatBandACreation K ν p 0).mulVec (flatBandAlphaAllUpState K ν))
          from (Matrix.mulVec_mulVec _ _ _).symm,
        flatBandACreation_up_mulVec_alphaAllUpState, Matrix.mulVec_zero]
    rw [hcr, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hkill, sub_zero]
  have hdown : (flatBandACreation K ν p 1 * flatBandAAnnihilation K ν p 1).mulVec
      (flatBandAlphaAllUpState K ν) = 0 := by
    rw [← Matrix.mulVec_mulVec, flatBandAAnnihilation_down_mulVec_alphaAllUpState,
      Matrix.mulVec_zero]
  rw [hup, hdown, add_zero]

/-- `(Σ_σ b̂†_{u,σ} b̂_{u,σ}) |Φα,all↑⟩ = 0`: each `b̂_{u,σ}` annihilates the all-up state. -/
theorem flatBandBNumber_mulVec_alphaAllUpState (K : ℕ) (ν : ℝ) (u : Fin (K + 1)) :
    (flatBandBNumber K ν u).mulVec (flatBandAlphaAllUpState K ν) = 0 := by
  unfold flatBandBNumber
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun σ _ => ?_)
  rw [← Matrix.mulVec_mulVec, flatBandBAnnihilation_mulVec_alphaAllUpState, Matrix.mulVec_zero]

/-- **`ĥ_p |Φα,all↑⟩ = 0`** (Tasaki p. 430): the all-up flat-band state is a zero-mode of the
local Hamiltonian.  The constant `(1+2ν²)s` cancels against `−s` times the α-number `(1+2ν²)`,
and the β-number and Coulomb terms all annihilate the all-up state.  Requires a genuine chain
(`i − 1 ≠ i`, i.e. `K ≥ 1`). -/
theorem nonsingularLocalHamiltonian_mulVec_alphaAllUpState (K : ℕ) (ν s t U lam κ : ℝ)
    (i : Fin (K + 1)) (hi : i - 1 ≠ i) :
    (nonsingularLocalHamiltonian K ν s t U lam κ i).mulVec (flatBandAlphaAllUpState K ν) = 0 := by
  unfold nonsingularLocalHamiltonian
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    flatBandANumber_mulVec_alphaAllUpState K ν i hi, flatBandBNumber_mulVec_alphaAllUpState,
    hubbardDoubleOccupancy_mulVec_alphaAllUpState, smul_zero, add_zero]
  rw [smul_smul, ← sub_smul,
    show ((1 + 2 * ν ^ 2) * s : ℂ) - (s : ℂ) * ((1 + 2 * ν ^ 2 : ℝ) : ℂ) = 0 from by
      push_cast; ring,
    zero_smul]

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
          0 < sectorMinEnergy (nonsingularLocalHamiltonian K ν s t U (clam * s) cκ i) (K + 1) twoS

end LatticeSystem.Fermion
