import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandModel

/-!
# Tasaki §11.4.3: ferromagnetism in the non-singular Hubbard model (Theorem 11.20)

This file states Tasaki's culminating result of §11.4 — **Theorem 11.20**: a Hubbard model
on the decorated chain with a *nearly-flat* (non-flat) lowest band, obtained by perturbing
the flat-band model (§11.3.1), still exhibits saturated ferromagnetism for a suitable range
of parameters.  This is the first proof of ferromagnetism in a Hubbard model with no
singularity (finite density of states, finite `U`).

The model (eq. (11.4.38)) is `Ĥ = Ĥ_hop + Ĥ_int` with
`Ĥ_hop = t Σ_{u∈I,σ} b̂†_{u,σ} b̂_{u,σ} − s Σ_{p∈E,σ} â†_{p,σ} â_{p,σ}`  (`t, s > 0`),
i.e. the flat-band Hamiltonian (`t Σ b̂†b̂ + U Σ n̂↑n̂↓`) minus `s` times the
`α`-state number operator.  At `s = 0` it is the flat-band model.

**Theorem 11.20** (`d = 1` version): for every `ν > 0` there are thresholds (depending only
on `ν`, not on the system size) such that, once `t/s` and `U/s` are large enough, the model
exhibits ferromagnetism (`E_min(S_max) < E_min(S)` for all `S ≠ S_max = N/2`; the ground
states are the `2S_max+1 = N+1`-fold maximal-spin multiplet).  Tasaki's proof (via the
frustration-free local Hamiltonians `ĥ_p` on `4d+1` sites — Lemmas 11.21, 11.22 — reducing
to Theorem 11.11) is deep and deferred; this is a documented axiom (Theorem 11.8 / 11.13 /
11.15 / 11.18 / 11.19 policy).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.4.3, eqs. (11.4.37)/(11.4.38), Theorem 11.20, Lemmas 11.21–11.22
(pp. 425–432).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- **The Tasaki non-singular Hubbard Hamiltonian** (§11.4.3, eq. (11.4.38)): the flat-band
model (`flatBandHamiltonian`) with the additional hopping `−s Σ_{p∈E,σ} â†_{p,σ} â_{p,σ}`
(`s > 0`), giving a *nearly-flat* lowest band.  At `s = 0` it reduces to the flat-band model. -/
noncomputable def tasakiNonsingularHamiltonian (K : ℕ) (ν t s U : ℝ) :
    ManyBodyOp (Fin (2 * (2 * K + 1) + 2)) :=
  flatBandHamiltonian K ν t U -
    (s : ℂ) • ∑ p : Fin (K + 1), ∑ σ : Fin 2,
      flatBandACreation K ν p σ * flatBandAAnnihilation K ν p σ

/-- At `s = 0` the non-singular model is exactly the §11.3.1 flat-band model (eq. (11.4.38)
reduces to (11.3.5)). -/
theorem tasakiNonsingularHamiltonian_zero_s (K : ℕ) (ν t U : ℝ) :
    tasakiNonsingularHamiltonian K ν t 0 U = flatBandHamiltonian K ν t U := by
  unfold tasakiNonsingularHamiltonian
  simp

-- **Tasaki Theorem 11.20** (ferromagnetism in the non-singular Hubbard model, `d = 1`) is proved
-- as `tasaki_theorem_11_20` in `NonsingularLocalHamiltonian.lean`, downstream of the
-- frustration-free local Hamiltonians `ĥ_p` and Lemmas 11.21/11.22 it is reduced to.

end LatticeSystem.Fermion
