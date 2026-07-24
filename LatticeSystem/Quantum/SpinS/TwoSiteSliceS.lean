import LatticeSystem.Quantum.SpinS.AKLTKnabe.SiteBlockEmbeddingD5b

/-!
# Two-site slices of finite spin configurations

This module restricts a many-body coefficient vector to the fibre obtained by
fixing every spectator site.  It also proves that a two-site block embedding
acts independently on every such fibre.
-/

namespace LatticeSystem.Quantum

open Matrix
open AKLTExactCertificateSector234Sequential

variable {Λ : Type*} [DecidableEq Λ]

/-- Replace the values at two distinct sites by a prescribed two-site
configuration, leaving every spectator value unchanged. -/
def glueTwoSitesS {N : ℕ} (x y : Λ)
    (a : Fin 2 → Fin (N + 1)) (τ : Λ → Fin (N + 1)) :
    Λ → Fin (N + 1) :=
  fun k => if k = x then a 0 else if k = y then a 1 else τ k

/-- The two-site coefficient slice obtained by fixing the spectator
configuration `τ`. -/
def twoSiteSliceS {N : ℕ} (x y : Λ)
    (Φ : (Λ → Fin (N + 1)) → ℂ) (τ : Λ → Fin (N + 1)) :
    (Fin 2 → Fin (N + 1)) → ℂ :=
  fun a => Φ (glueTwoSitesS x y a τ)

/-- Two-site gluing agrees with the fibre inverse used by `onEmbS`. -/
private theorem glueTwoSitesS_eq_extend {N : ℕ} {x y : Λ}
    (hxy : x ≠ y) (a : Fin 2 → Fin (N + 1))
    (τ : Λ → Fin (N + 1)) :
    glueTwoSitesS x y a τ = Function.extend ![x, y] a τ := by
  have hι := AKLTExactCertificateSector234Sequential.injective_bondEmb hxy
  funext k
  by_cases hkx : k = x
  · subst k
    rw [glueTwoSitesS, if_pos rfl]
    change a 0 = Function.extend ![x, y] a τ (![x, y] 0)
    rw [hι.extend_apply]
  · by_cases hky : k = y
    · subst k
      rw [glueTwoSitesS, if_neg hkx, if_pos rfl]
      change a 1 = Function.extend ![x, y] a τ (![x, y] 1)
      rw [hι.extend_apply]
    · rw [glueTwoSitesS, if_neg hkx, if_neg hky]
      rw [Function.extend_apply']
      rintro ⟨i, hi⟩
      fin_cases i <;> simp_all

variable [Fintype Λ]

/-- A block-embedded two-site matrix acts fibrewise on two-site slices. -/
theorem twoSiteSliceS_onEmbS_mulVec {N : ℕ} {x y : Λ}
    (hxy : x ≠ y)
    (A : Matrix (Fin 2 → Fin (N + 1)) (Fin 2 → Fin (N + 1)) ℂ)
    (Φ : (Λ → Fin (N + 1)) → ℂ) (τ : Λ → Fin (N + 1)) :
    twoSiteSliceS x y ((onEmbS ![x, y] A).mulVec Φ) τ =
      A.mulVec (twoSiteSliceS x y Φ τ) := by
  let ι : Fin 2 → Λ := ![x, y]
  have hι : Function.Injective ι := injective_bondEmb hxy
  funext a
  change ((onEmbS ![x, y] A).mulVec Φ)
      (glueTwoSitesS x y a τ) =
    A.mulVec (fun b => Φ (glueTwoSitesS x y b τ)) a
  simp_rw [glueTwoSitesS_eq_extend (hxy := hxy)]
  rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
  change (∑ σ : Λ → Fin (N + 1),
      onEmbS ι A (Function.extend ι a τ) σ * Φ σ) =
    ∑ b : Fin 2 → Fin (N + 1),
      A a b * Φ (Function.extend ι b τ)
  have hfib : ∀ σ ∈ (Finset.univ : Finset (Λ → Fin (N + 1))),
      σ ∉ Finset.univ.filter
          (fun σ : Λ → Fin (N + 1) =>
            ∀ k, (∀ i, ι i ≠ k) → σ k = τ k) →
        onEmbS ι A (Function.extend ι a τ) σ * Φ σ = 0 := by
    intro σ _ hσ
    have hnot : ¬ ∀ k, (∀ i, ι i ≠ k) → σ k = τ k := fun h =>
      hσ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    have hguard : ¬ ∀ k, (∀ i, ι i ≠ k) →
        Function.extend ι a τ k = σ k := by
      intro h
      apply hnot
      intro k hk
      rw [← h k hk, Function.extend_apply' a τ k]
      rintro ⟨i, hi⟩
      exact hk i hi
    simp only [onEmbS_apply]
    rw [if_neg hguard, zero_mul]
  refine Eq.trans (Finset.sum_subset (Finset.subset_univ _) hfib).symm ?_
  refine Finset.sum_nbij' (fun σ => σ ∘ ι)
    (fun b => Function.extend ι b τ) (fun σ _ => Finset.mem_univ _) ?_ ?_ ?_ ?_
  · intro b _
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun k hk => ?_⟩
    exact Function.extend_apply' b τ k
      (by rintro ⟨i, hi⟩; exact hk i hi)
  · intro σ hσ
    rw [Finset.mem_filter] at hσ
    funext k
    change Function.extend ι (σ ∘ ι) τ k = σ k
    by_cases hk : ∃ i, ι i = k
    · obtain ⟨i, rfl⟩ := hk
      rw [hι.extend_apply]
      rfl
    · rw [Function.extend_apply' _ _ _ hk]
      exact (hσ.2 k fun i hi => hk ⟨i, hi⟩).symm
  · intro b _
    exact Function.extend_comp hι b τ
  · intro σ hσ
    rw [Finset.mem_filter] at hσ
    have hguard : ∀ k, (∀ i, ι i ≠ k) →
        Function.extend ι a τ k = σ k := by
      intro k hk
      rw [Function.extend_apply' a τ k
        (by rintro ⟨i, hi⟩; exact hk i hi)]
      exact (hσ.2 k hk).symm
    have hext : Function.extend ι (σ ∘ ι) τ = σ := by
      funext k
      by_cases hk : ∃ i, ι i = k
      · obtain ⟨i, rfl⟩ := hk
        rw [hι.extend_apply]
        rfl
      · rw [Function.extend_apply' _ _ _ hk]
        exact (hσ.2 k fun i hi => hk ⟨i, hi⟩).symm
    simp only [onEmbS_apply]
    rw [if_pos hguard, Function.extend_comp hι, hext]

/-- A block-embedded two-site matrix annihilates a many-body vector exactly
when its local matrix annihilates every spectator slice. -/
theorem onEmbS_mulVec_eq_zero_iff_twoSiteSlices {N : ℕ} {x y : Λ}
    (hxy : x ≠ y)
    (A : Matrix (Fin 2 → Fin (N + 1)) (Fin 2 → Fin (N + 1)) ℂ)
    (Φ : (Λ → Fin (N + 1)) → ℂ) :
    (onEmbS ![x, y] A).mulVec Φ = 0 ↔
      ∀ τ : Λ → Fin (N + 1),
        A.mulVec (twoSiteSliceS x y Φ τ) = 0 := by
  constructor
  · intro hΦ τ
    rw [← twoSiteSliceS_onEmbS_mulVec hxy A Φ τ, hΦ]
    rfl
  · intro hslice
    funext q
    let ι : Fin 2 → Λ := ![x, y]
    let a : Fin 2 → Fin (N + 1) := q ∘ ι
    have hι : Function.Injective ι := injective_bondEmb hxy
    have hglue : glueTwoSitesS x y a q = q := by
      rw [glueTwoSitesS_eq_extend (hxy := hxy)]
      funext k
      by_cases hk : ∃ i, ι i = k
      · obtain ⟨i, rfl⟩ := hk
        rw [hι.extend_apply]
        rfl
      · rw [Function.extend_apply' _ _ _ hk]
    have haction :=
      congrFun (twoSiteSliceS_onEmbS_mulVec hxy A Φ q) a
    rw [hslice q] at haction
    simpa only [twoSiteSliceS, hglue, Pi.zero_apply] using haction

end LatticeSystem.Quantum
