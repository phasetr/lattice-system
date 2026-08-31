/-
Site support of a many-body spin-`S` operator, and commutation of disjointly supported operators.

Tasaki phrases the locality premise of Problem 3.4.a as "`ĥ_x` and `ô_x` act only on sites within
distance `r` of `x`".  Read literally that is a statement about *support*, not about commutators:
`SupportedOnS S A` says that `A` lies in the subalgebra `B(H_S) ⊗ I_{Λ∖S}`, and the commutation of
operators with disjoint supports is then a theorem rather than a hypothesis.  This is what lets the
range-`r` double-commutator bound be derived from the book's premise instead of from commutation
conditions assumed alongside it.

The predicate has the same two-clause shape as the half-ring predicate `SupportedOnLeftS` of
`Quantum/SpinS/RingReflectionPositivity.lean`, with the half-ring site condition `n ≤ i` replaced by
membership in an arbitrary `S : Finset Λ`: the entries vanish off the support, and inside the
support they depend only on the restricted configurations.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §3.4, Problem 3.4.a, statement pp. 67-68.
-/
import LatticeSystem.Quantum.SpinS.MultiSiteCore

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} {N : ℕ}

/-- An operator on the spin-`S` many-body space is **supported on the site set `S`** — i.e. it lies
in the subalgebra `B(H_S) ⊗ I_{Λ∖S}` — when (1) its matrix entries vanish unless the row/column
configurations agree at every site outside `S` (it preserves the complement), and (2) the entry
depends only on the restrictions of the configurations to `S`, not on their common value outside it
(it acts as the identity on the complement).  The two conditions together characterize the
subalgebra of operators acting only on the sites of `S`. -/
def SupportedOnS (S : Finset Λ) (A : ManyBodyOpS Λ N) : Prop :=
  (∀ σ τ : Λ → Fin (N + 1), A σ τ ≠ 0 → ∀ i ∉ S, σ i = τ i) ∧
    (∀ σ τ σ' τ' : Λ → Fin (N + 1),
      (∀ i ∉ S, σ i = τ i) → (∀ i ∉ S, σ' i = τ' i) →
      (∀ i ∈ S, σ i = σ' i) → (∀ i ∈ S, τ i = τ' i) → A σ τ = A σ' τ')

/-- A sum of operators supported on the same site set is supported on that site set: the support
subalgebra is closed under addition.  Needed to give a local term a support larger than one site
(for instance a bond term, or a range-`r` term assembled from single-site pieces). -/
theorem SupportedOnS.add {S : Finset Λ} {A B : ManyBodyOpS Λ N}
    (hA : SupportedOnS S A) (hB : SupportedOnS S B) : SupportedOnS S (A + B) := by
  constructor
  · intro σ τ hne k hk
    by_contra hcon
    have h1 : A σ τ = 0 := by by_contra h0; exact hcon (hA.1 σ τ h0 k hk)
    have h2 : B σ τ = 0 := by by_contra h0; exact hcon (hB.1 σ τ h0 k hk)
    rw [Matrix.add_apply, h1, h2, add_zero] at hne
    exact hne rfl
  · intro σ τ σ' τ' h1 h2 h3 h4
    rw [Matrix.add_apply, Matrix.add_apply, hA.2 σ τ σ' τ' h1 h2 h3 h4,
      hB.2 σ τ σ' τ' h1 h2 h3 h4]

variable [Fintype Λ] [DecidableEq Λ]

/-- **Disjointly supported operators commute.**  This is the content behind Tasaki's informal
"acts only on sites within distance `r`" premise: with the supports of `A` and `B` disjoint, both
`(A * B) u v` and `(B * A) u v` collapse to a single term of the intermediate sum, at the pivot
configurations `S.piecewise v u` and `T.piecewise v u` respectively, and the two surviving products
agree factor by factor. -/
theorem commute_of_supportedOnS_disjoint {S T : Finset Λ} {A B : ManyBodyOpS Λ N}
    (hA : SupportedOnS S A) (hB : SupportedOnS T B) (hST : Disjoint S T) :
    Commute A B := by
  have hTS : ∀ i ∈ T, i ∉ S := fun i hi hiS => (Finset.disjoint_left.mp hST hiS) hi
  have hSTn : ∀ i ∈ S, i ∉ T := fun i hi => Finset.disjoint_left.mp hST hi
  change A * B = B * A
  ext u v
  set pAB : Λ → Fin (N + 1) := S.piecewise v u with hpAB
  set pBA : Λ → Fin (N + 1) := T.piecewise v u with hpBA
  have hpAB_mem : ∀ i ∈ S, pAB i = v i := fun i hi => Finset.piecewise_eq_of_mem _ _ _ hi
  have hpAB_not : ∀ i ∉ S, pAB i = u i := fun i hi => Finset.piecewise_eq_of_notMem _ _ _ hi
  have hpBA_mem : ∀ i ∈ T, pBA i = v i := fun i hi => Finset.piecewise_eq_of_mem _ _ _ hi
  have hpBA_not : ∀ i ∉ T, pBA i = u i := fun i hi => Finset.piecewise_eq_of_notMem _ _ _ hi
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rw [Fintype.sum_eq_single pAB, Fintype.sum_eq_single pBA]
  · by_cases hoff : ∀ k, k ∉ S → k ∉ T → u k = v k
    · have hA' : A u pAB = A pBA v := by
        refine hA.2 u pAB pBA v (fun i hi => (hpAB_not i hi).symm) (fun i hi => ?_)
          (fun i hi => (hpBA_not i (hSTn i hi)).symm) (fun i hi => hpAB_mem i hi)
        by_cases hiT : i ∈ T
        · exact hpBA_mem i hiT
        · rw [hpBA_not i hiT]; exact hoff i hi hiT
      have hB' : B pAB v = B u pBA := by
        refine hB.2 pAB v u pBA (fun i hi => ?_) (fun i hi => (hpBA_not i hi).symm)
          (fun i hi => hpAB_not i (hTS i hi)) (fun i hi => (hpBA_mem i hi).symm)
        by_cases hiS : i ∈ S
        · exact hpAB_mem i hiS
        · rw [hpAB_not i hiS]; exact hoff i hiS hi
      rw [hA', hB', mul_comm]
    · push Not at hoff
      obtain ⟨k, hkS, hkT, hkne⟩ := hoff
      have h1 : B pAB v = 0 := by
        by_contra hne
        exact hkne ((hpAB_not k hkS).symm.trans (hB.1 pAB v hne k hkT))
      have h2 : A pBA v = 0 := by
        by_contra hne
        exact hkne ((hpBA_not k hkT).symm.trans (hA.1 pBA v hne k hkS))
      rw [h1, h2, mul_zero, mul_zero]
  · intro w hw
    have hex : ∃ k, w k ≠ pBA k := by
      by_contra hall
      push Not at hall
      exact hw (funext hall)
    obtain ⟨k, hk⟩ := hex
    by_cases hkT : k ∈ T
    · have hz : A w v = 0 := by
        by_contra hne
        exact hk (((hA.1 w v hne k (hTS k hkT))).trans (hpBA_mem k hkT).symm)
      rw [hz, mul_zero]
    · have hz : B u w = 0 := by
        by_contra hne
        exact hk ((hB.1 u w hne k hkT).symm.trans (hpBA_not k hkT).symm)
      rw [hz, zero_mul]
  · intro w hw
    have hex : ∃ k, w k ≠ pAB k := by
      by_contra hall
      push Not at hall
      exact hw (funext hall)
    obtain ⟨k, hk⟩ := hex
    by_cases hkS : k ∈ S
    · have hz : B w v = 0 := by
        by_contra hne
        exact hk (((hB.1 w v hne k (hSTn k hkS))).trans (hpAB_mem k hkS).symm)
      rw [hz, mul_zero]
    · have hz : A u w = 0 := by
        by_contra hne
        exact hk ((hA.1 u w hne k hkS).symm.trans (hpAB_not k hkS).symm)
      rw [hz, zero_mul]

/-- A single-site operator `onSiteS i A` is supported on every site set containing `i`.  The
entry-vanishing clause is the off-site agreement built into `onSiteS`, and the restriction clause
holds because the surviving entry `A (σ i) (τ i)` reads the configurations only at `i ∈ S`, while
the guard `∀ k ≠ i, σ k = τ k` is unchanged by replacing the configurations by ones agreeing with
them on `S` and off `S` separately. -/
theorem supportedOnS_onSiteS {S : Finset Λ} {i : Λ} (hi : i ∈ S)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    SupportedOnS S (onSiteS i A : ManyBodyOpS Λ N) := by
  constructor
  · intro σ τ hne k hk
    rw [onSiteS_apply] at hne
    by_cases hcond : ∀ j, j ≠ i → σ j = τ j
    · exact hcond k (by rintro rfl; exact hk hi)
    · rw [if_neg hcond] at hne; exact absurd rfl hne
  · intro σ τ σ' τ' h1 h2 h3 h4
    rw [onSiteS_apply, onSiteS_apply, h3 i hi, h4 i hi]
    congr 1
    apply propext
    constructor
    · intro hc k hk
      by_cases hkS : k ∈ S
      · rw [← h3 k hkS, ← h4 k hkS]; exact hc k hk
      · rw [← h2 k hkS]
    · intro hc k hk
      by_cases hkS : k ∈ S
      · rw [h3 k hkS, h4 k hkS]; exact hc k hk
      · rw [← h1 k hkS]

end LatticeSystem.Quantum
