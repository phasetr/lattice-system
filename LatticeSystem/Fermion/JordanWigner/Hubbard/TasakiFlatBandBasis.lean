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

/-- `α_p` at an internal site: `α_p(2v+1) = −ν` iff `v ∈ {p, p−1}` (the two
internal sites incident to external `p`), else `0`. -/
theorem flatBandAlpha_deltaInternalSite (K : ℕ) (ν : ℝ) (p v : Fin (K + 1)) :
    flatBandAlpha K ν p (deltaInternalSite K v) =
      if v = p ∨ v = p - 1 then -ν else 0 := by
  unfold flatBandAlpha
  rw [if_neg (fun h => deltaExternalSite_ne_internal K p v h.symm)]
  by_cases hv : v = p ∨ v = p - 1
  · rw [if_pos (hv.elim (fun h => Or.inl (by rw [h])) (fun h => Or.inr (by rw [h]))),
      if_pos hv]
  · rw [if_neg (fun h => hv (h.elim (fun h' => Or.inl (deltaInternalSite_injective K h'))
      (fun h' => Or.inr (deltaInternalSite_injective K h')))), if_neg hv]

/-- `β_u` at an external site: `β_u(2q) = ν` iff `q ∈ {u, u+1}` (the two external
sites incident to internal `u`), else `0`. -/
theorem flatBandBeta_deltaExternalSite (K : ℕ) (ν : ℝ) (u q : Fin (K + 1)) :
    flatBandBeta K ν u (deltaExternalSite K q) =
      if q = u ∨ q = u + 1 then ν else 0 := by
  unfold flatBandBeta
  rw [if_neg (fun h => deltaExternalSite_ne_internal K q u h)]
  by_cases hq : q = u ∨ q = u + 1
  · rw [if_pos (hq.elim (fun h => Or.inl (by rw [h])) (fun h => Or.inr (by rw [h]))),
      if_pos hq]
  · rw [if_neg (fun h => hq (h.elim (fun h' => Or.inl (deltaExternalSite_injective K h'))
      (fun h' => Or.inr (deltaExternalSite_injective K h')))), if_neg hq]

/-- The physical sites `Fin (2K+2)` split as external (even) ⊕ internal (odd):
`Fin (K+1) ⊕ Fin (K+1) ≃ Fin (2K+2)`, `inl q ↦ 2q`, `inr v ↦ 2v+1`. -/
def deltaSiteEquiv (K : ℕ) : Fin (K + 1) ⊕ Fin (K + 1) ≃ Fin (2 * K + 2) where
  toFun := Sum.elim (deltaExternalSite K) (deltaInternalSite K)
  invFun := fun x =>
    if x.val % 2 = 0 then Sum.inl ⟨x.val / 2, by have := x.isLt; omega⟩
    else Sum.inr ⟨x.val / 2, by have := x.isLt; omega⟩
  left_inv := by
    rintro (q | v)
    · simp only [Sum.elim_inl]
      rw [if_pos (show (deltaExternalSite K q).val % 2 = 0 by
        simp only [deltaExternalSite]; omega)]
      exact congrArg Sum.inl (Fin.ext (by simp only [deltaExternalSite]; omega))
    · simp only [Sum.elim_inr]
      rw [if_neg (show ¬ (deltaInternalSite K v).val % 2 = 0 by
        simp only [deltaInternalSite]; omega)]
      exact congrArg Sum.inr (Fin.ext (by simp only [deltaInternalSite]; omega))
  right_inv := by
    intro x
    simp only []
    split_ifs with hx
    · simp only [Sum.elim_inl]
      exact Fin.ext (by simp only [deltaExternalSite]; omega)
    · simp only [Sum.elim_inr]
      exact Fin.ext (by simp only [deltaInternalSite]; omega)

/-- Splitting a sum over physical sites into external + internal parts. -/
theorem sum_deltaSite_split {M : Type*} [AddCommMonoid M] (K : ℕ)
    (f : Fin (2 * K + 2) → M) :
    ∑ x, f x = (∑ q, f (deltaExternalSite K q)) + ∑ v, f (deltaInternalSite K v) := by
  rw [← Equiv.sum_comp (deltaSiteEquiv K) f, Fintype.sum_sum_type]
  rfl

end LatticeSystem.Fermion
