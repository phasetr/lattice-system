import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandBasis

/-!
# Tasaki §11.4.3 Lemma 11.21: the local Hamiltonian annihilates the all-up state

Building blocks toward discharging `nonsingular_lemma_11_21` (Issue #4189). Tasaki's proof
(p. 430) hinges on `ĥ_p |Φα,all↑⟩ = 0`, which in turn rests on
`(Σ_σ â†_{p,σ} â_{p,σ}) |Φα,all↑⟩ = (1+2ν²) |Φα,all↑⟩`.  The `1+2ν²` is the self-overlap
`⟨α_p, α_p⟩ = ‖α_p‖²` of the single-particle state `α_p = e_{ext p} − ν(e_{int p}+e_{int p−1})`,
i.e. the value of the self-anticommutator `{â_{p,σ}, â†_{p,σ}} = ‖α_p‖²·1` (eq. (11.4.42), `d=1`).

This file starts with the geometric input: `Σ_x α_p(x)² = 1 + 2ν²` on a genuine chain (`p−1 ≠ p`,
i.e. `K ≥ 1`; the single-site `K = 0` case degenerates to `1 + ν²`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed.),
§11.4.3, eqs. (11.4.42), (11.4.48)–(11.4.49), Lemma 11.21 (pp. 429–431).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- **Self-overlap of the flat-band single-particle state `α_p`**: `⟨α_p, α_p⟩ = 1 + 2ν²` on a
chain with at least two sites (`p − 1 ≠ p`).  The external site contributes `1²` and the two
distinct incident internal sites contribute `(−ν)²` each.  This is `‖α_p‖²`, the value of the
self-anticommutator `{â_{p,σ}, â†_{p,σ}}` (Tasaki eq. (11.4.42), `d = 1`). -/
theorem flatBandAlpha_dot_self (K : ℕ) (ν : ℝ) (p : Fin (K + 1)) (hp : p - 1 ≠ p) :
    ∑ x, flatBandAlpha K ν p x * flatBandAlpha K ν p x = 1 + 2 * ν ^ 2 := by
  rw [sum_deltaSite_split]
  have hext : (∑ q, flatBandAlpha K ν p (deltaExternalSite K q) *
      flatBandAlpha K ν p (deltaExternalSite K q)) = 1 := by
    rw [Finset.sum_congr rfl (fun q _ =>
      show flatBandAlpha K ν p (deltaExternalSite K q) *
          flatBandAlpha K ν p (deltaExternalSite K q) = if q = p then (1 : ℝ) else 0 from by
        rw [flatBandAlpha_deltaExternalSite]; by_cases hq : q = p <;> simp [hq])]
    rw [Finset.sum_ite_eq' Finset.univ p (fun _ => (1 : ℝ)), if_pos (Finset.mem_univ p)]
  have hint : (∑ v, flatBandAlpha K ν p (deltaInternalSite K v) *
      flatBandAlpha K ν p (deltaInternalSite K v)) = 2 * ν ^ 2 := by
    rw [Finset.sum_congr rfl (fun v _ =>
      show flatBandAlpha K ν p (deltaInternalSite K v) *
          flatBandAlpha K ν p (deltaInternalSite K v)
            = (if v = p then ν ^ 2 else 0) + (if v = p - 1 then ν ^ 2 else 0) from by
        rw [flatBandAlpha_deltaInternalSite]
        by_cases h1 : v = p
        · have h2 : ¬ v = p - 1 := fun h2 => hp (h2.symm.trans h1)
          rw [if_pos (Or.inl h1), if_pos h1, if_neg h2]; ring
        · by_cases h2 : v = p - 1
          · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2]; ring
          · rw [if_neg (not_or.mpr ⟨h1, h2⟩), if_neg h1, if_neg h2]; ring)]
    rw [Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ p (fun _ => ν ^ 2), if_pos (Finset.mem_univ p),
      Finset.sum_ite_eq' Finset.univ (p - 1) (fun _ => ν ^ 2),
      if_pos (Finset.mem_univ (p - 1))]
    ring
  rw [hext, hint]

end LatticeSystem.Fermion
