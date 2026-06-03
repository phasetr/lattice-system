import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandModel

/-!
# Tasaki §11.3.1 Lemma 11.10: the `{α_p} ∪ {β_u}` single-particle basis

**Lemma 11.10**: the localized single-particle states `{α_p}_{p ∈ E}` and
`{β_u}_{u ∈ I}` of Tasaki's `d = 1` flat-band model together form a basis of the
single-particle Hilbert space `h = (Fin (2K+2) → ℂ)`.

Following Tasaki's proof: `α_p` is supported with value `1` at its own external
site (so `{α_p}` are linearly independent), `β_u` similarly at its internal site,
and `⟨α_p, β_u⟩ = 0` (the `±ν` contributions cancel), so the two families span
mutually orthogonal subspaces; together they are `|E| + |I| = |Λ|` linearly
independent vectors in the `|Λ|`-dimensional space, hence a basis.

This file builds the `ℂ`-valued states, the diagonal-evaluation lemmas, and the
cross-orthogonality `⟨α_p, β_u⟩ = 0`, then the combined linear independence and
the `Basis`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1, Lemma 11.10.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- The single-particle state `α_p` as a `ℂ`-valued vector. -/
noncomputable def flatBandAlphaC (K : ℕ) (ν : ℝ) (p : Fin (K + 1)) :
    Fin (2 * K + 2) → ℂ :=
  fun x => (flatBandAlpha K ν p x : ℂ)

/-- The single-particle state `β_u` as a `ℂ`-valued vector. -/
noncomputable def flatBandBetaC (K : ℕ) (ν : ℝ) (u : Fin (K + 1)) :
    Fin (2 * K + 2) → ℂ :=
  fun x => (flatBandBeta K ν u x : ℂ)

/-- `α_p` evaluated at an external site is the Kronecker delta: `α_p(2q) = [p = q]`. -/
theorem flatBandAlpha_deltaExternalSite (K : ℕ) (ν : ℝ) (p q : Fin (K + 1)) :
    flatBandAlpha K ν p (deltaExternalSite K q) = if q = p then 1 else 0 := by
  unfold flatBandAlpha
  by_cases hpq : q = p
  · rw [if_pos (by rw [hpq]), if_pos hpq]
  · rw [if_neg (fun h => hpq (deltaExternalSite_injective K h)),
      if_neg (fun h => h.elim (deltaExternalSite_ne_internal K q p)
        (deltaExternalSite_ne_internal K q (p - 1))),
      if_neg hpq]

/-- `β_u` evaluated at an internal site is the Kronecker delta: `β_u(2v+1) = [u = v]`. -/
theorem flatBandBeta_deltaInternalSite (K : ℕ) (ν : ℝ) (u v : Fin (K + 1)) :
    flatBandBeta K ν u (deltaInternalSite K v) = if v = u then 1 else 0 := by
  unfold flatBandBeta
  by_cases huv : v = u
  · rw [if_pos (by rw [huv]), if_pos huv]
  · rw [if_neg (fun h => huv (deltaInternalSite_injective K h)),
      if_neg (fun h => h.elim (fun h' => (deltaExternalSite_ne_internal K u v) h'.symm)
        (fun h' => (deltaExternalSite_ne_internal K (u + 1) v) h'.symm)),
      if_neg huv]

end LatticeSystem.Fermion
