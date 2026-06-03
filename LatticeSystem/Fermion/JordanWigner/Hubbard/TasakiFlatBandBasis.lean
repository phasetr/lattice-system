import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandModel
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.Defs

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

/-- The incidence relations of `α_p` and `β_u` match: `p` is an external neighbor
of internal `u` iff `u` is an internal neighbor of external `p`. -/
theorem flatBand_incidence_iff (K : ℕ) (p u : Fin (K + 1)) :
    (u = p ∨ u = p - 1) ↔ (p = u ∨ p = u + 1) := by
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr (eq_add_of_sub_eq h.symm)
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr (sub_eq_of_eq_add h).symm

/-- **Cross-orthogonality (Tasaki §11.3.1): `⟨α_p, β_u⟩ = 0`.**  The `+ν`
contribution at the shared external site and the `−ν` contribution at the shared
internal site cancel. -/
theorem flatBandAlpha_dot_beta (K : ℕ) (ν : ℝ) (p u : Fin (K + 1)) :
    ∑ x, flatBandAlpha K ν p x * flatBandBeta K ν u x = 0 := by
  rw [sum_deltaSite_split]
  have hext : (∑ q, flatBandAlpha K ν p (deltaExternalSite K q) *
      flatBandBeta K ν u (deltaExternalSite K q)) = if p = u ∨ p = u + 1 then ν else 0 := by
    rw [Finset.sum_congr rfl (fun q _ => by
      rw [flatBandAlpha_deltaExternalSite, flatBandBeta_deltaExternalSite, ite_mul, one_mul,
        zero_mul])]
    rw [Finset.sum_ite_eq' Finset.univ p (fun q => if q = u ∨ q = u + 1 then ν else 0),
      if_pos (Finset.mem_univ p)]
  have hint : (∑ v, flatBandAlpha K ν p (deltaInternalSite K v) *
      flatBandBeta K ν u (deltaInternalSite K v)) = if u = p ∨ u = p - 1 then -ν else 0 := by
    rw [Finset.sum_congr rfl (fun v _ => by
      rw [flatBandAlpha_deltaInternalSite, flatBandBeta_deltaInternalSite, mul_ite, mul_one,
        mul_zero])]
    rw [Finset.sum_ite_eq' Finset.univ u (fun v => if v = p ∨ v = p - 1 then -ν else 0),
      if_pos (Finset.mem_univ u)]
  rw [hext, hint]
  by_cases hpu : p = u ∨ p = u + 1
  · rw [if_pos hpu, if_pos ((flatBand_incidence_iff K p u).mpr hpu)]; ring
  · rw [if_neg hpu, if_neg (fun h => hpu ((flatBand_incidence_iff K p u).mp h))]; ring

/-! ## Linear independence and the basis (Lemma 11.10) -/

/-- The `α` family is linearly independent: evaluating at the external site `q`
isolates the coefficient `g_q`. -/
theorem flatBandAlphaC_linearIndependent (K : ℕ) (ν : ℝ) :
    LinearIndependent ℂ (flatBandAlphaC K ν) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  have hq := congrFun hg (deltaExternalSite K q)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, flatBandAlphaC,
    flatBandAlpha_deltaExternalSite, Pi.zero_apply, apply_ite (Complex.ofReal),
    Complex.ofReal_one, Complex.ofReal_zero, mul_ite, mul_one, mul_zero] at hq
  rwa [Finset.sum_ite_eq Finset.univ q g, if_pos (Finset.mem_univ q)] at hq

/-- The `β` family is linearly independent: evaluating at the internal site `v`
isolates the coefficient `g_v`. -/
theorem flatBandBetaC_linearIndependent (K : ℕ) (ν : ℝ) :
    LinearIndependent ℂ (flatBandBetaC K ν) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg v
  have hv := congrFun hg (deltaInternalSite K v)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, flatBandBetaC,
    flatBandBeta_deltaInternalSite, Pi.zero_apply, apply_ite (Complex.ofReal),
    Complex.ofReal_one, Complex.ofReal_zero, mul_ite, mul_one, mul_zero] at hv
  rwa [Finset.sum_ite_eq Finset.univ v g, if_pos (Finset.mem_univ v)] at hv

/-- The complex cross-orthogonality `⟨α_p, β_u⟩ = 0` (the `ℝ` version cast). -/
theorem flatBandAlphaC_dotProduct_betaC (K : ℕ) (ν : ℝ) (p u : Fin (K + 1)) :
    star (flatBandAlphaC K ν p) ⬝ᵥ flatBandBetaC K ν u = 0 := by
  rw [dotProduct]
  simp only [Pi.star_apply, flatBandAlphaC, flatBandBetaC, Complex.star_def, Complex.conj_ofReal]
  rw [show (∑ x, (flatBandAlpha K ν p x : ℂ) * (flatBandBeta K ν u x : ℂ))
      = (((∑ x, flatBandAlpha K ν p x * flatBandBeta K ν u x : ℝ)) : ℂ) from by push_cast; rfl]
  rw [flatBandAlpha_dot_beta]; simp

/-- A complex vector with `star v ⬝ᵥ v = 0` is zero (`∑ ‖v_i‖² = 0`). -/
theorem complexVec_eq_zero_of_star_dotProduct {n : Type*} [Fintype n] {v : n → ℂ}
    (h : star v ⬝ᵥ v = 0) : v = 0 := by
  have hsum : ∑ j, (Complex.normSq (v j) : ℝ) = 0 := by
    have hc : (∑ j, (Complex.normSq (v j) : ℂ)) = 0 := by
      rw [← h, dotProduct]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]
    exact_mod_cast hc
  funext j
  have hj : Complex.normSq (v j) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg _)).mp hsum j
      (Finset.mem_univ j)
  exact Complex.normSq_eq_zero.mp hj

/-- The `α` and `β` spans are disjoint (they are orthogonal). -/
theorem flatBand_span_disjoint (K : ℕ) (ν : ℝ) :
    Disjoint (Submodule.span ℂ (Set.range (flatBandAlphaC K ν)))
      (Submodule.span ℂ (Set.range (flatBandBetaC K ν))) := by
  rw [Submodule.disjoint_def]
  intro x hxA hxB
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hxA
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hxB
  refine complexVec_eq_zero_of_star_dotProduct ?_
  nth_rewrite 2 [← hc]
  rw [← hd, star_sum, sum_dotProduct]
  refine Finset.sum_eq_zero (fun p _ => ?_)
  rw [star_smul, smul_dotProduct, dotProduct_sum]
  rw [Finset.sum_eq_zero (fun u _ => ?_), smul_zero]
  rw [dotProduct_smul, flatBandAlphaC_dotProduct_betaC, smul_zero]

/-- **Tasaki Lemma 11.10**: `{α_p}_{p∈E} ∪ {β_u}_{u∈I}` is linearly independent. -/
theorem flatBand_linearIndependent (K : ℕ) (ν : ℝ) :
    LinearIndependent ℂ (Sum.elim (flatBandAlphaC K ν) (flatBandBetaC K ν)) := by
  rw [linearIndependent_sum]
  refine ⟨?_, ?_, ?_⟩
  · simpa using flatBandAlphaC_linearIndependent K ν
  · simpa using flatBandBetaC_linearIndependent K ν
  · simpa using flatBand_span_disjoint K ν

/-- **Tasaki Lemma 11.10 (basis form)**: `{α_p} ∪ {β_u}` is a basis of the
single-particle Hilbert space `Fin (2K+2) → ℂ`. -/
noncomputable def flatBandBasis (K : ℕ) (ν : ℝ) :
    Module.Basis (Fin (K + 1) ⊕ Fin (K + 1)) ℂ (Fin (2 * K + 2) → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank (flatBand_linearIndependent K ν) (by
    rw [Fintype.card_sum, Fintype.card_fin, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin]
    omega)

end LatticeSystem.Fermion
