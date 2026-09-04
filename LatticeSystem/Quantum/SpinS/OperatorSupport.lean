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

`LatticeSystem.Quantum.SupportedOn` (`Quantum/SpinS/AndersonTowerLocalDecay.lean`) is another
encoding of the same "acts only on `S`" concept, phrased in commutant form: `G` is supported on `S`
when it commutes with every on-site factor located off `S`. Further encodings exist elsewhere in
the library, e.g. `IsLocalRangeR` (`Quantum/SpinS/LiebSchultzMattisGeneral.lean`), which phrases
the same idea for a fixed centre and radius on a ring (its own doc comment notes it is equivalent,
by the factor double-commutant theorem, to a support condition, and that the commutant phrasing is
deliberate: it is shared with the §7.1.3 Theorem 7.3 axiom hypothesis), and `IsLocalWindowS`
(`Quantum/SpinS/KennedyTasakiProp84.lean`), the open-chain window analogue of `IsLocalRangeR`. This
family of "acts only on a subset of sites" encodings is larger than this module and has not been
enumerated exhaustively; new encodings should not be assumed absent just because a comment does not
mention them. Unifying the family into one predicate is tracked work, not done here.

`SupportedOn` and `SupportedOnS` are a particular hazard: both have signature
`Finset Λ → ManyBodyOpS Λ N → Prop`, both live in namespace `LatticeSystem.Quantum`, and they
differ by one character. Picking the wrong one therefore still type-checks. Being both "commutes
with every off-support on-site factor" versus "vanishes off support, depends only on support", the
two are expected to be logically equivalent for `ManyBodyOpS`, but no bridge lemma between them (or
between either of them and `IsLocalRangeR`) is proved in either direction anywhere in the repo, so
this equivalence is not formalised here. A caller holding a hypothesis phrased in one of these
predicates cannot currently invoke a capstone stated in another; closing that gap is tracked work
alongside the unification above.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §3.4, Problem 3.4.a, statement pp. 67-68.
-/
import LatticeSystem.Quantum.SpinS.MultiSiteCore
import Mathlib.Data.Matrix.Basis

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

/-- **Matrix-unit entry identity.**  Suppose `A` commutes with every on-site operator placed at the
site `z`.  Testing that commutation against the matrix unit `Matrix.single a b 1` and reading off
the `(σ, τ)` entry of `A * onSiteS z B = onSiteS z B * A` collapses both intermediate sums to a
single pivot configuration — `Function.update τ z a` on the left, `Function.update σ z b` on the
right — leaving the two indicator factors of `Matrix.single_apply`.  Those indicators are kept in
the literal orientation `b = τ z` / `a = σ z` supplied by `Matrix.single_apply`; the identity holds
uniformly in `a`, `b`, `σ`, `τ` with no case distinction on them, because each indicator survives
as a factor of the pivot term. -/
private theorem entry_swap_of_commute_onSiteS {z : Λ} {A : ManyBodyOpS Λ N}
    (h : ∀ B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ, Commute A (onSiteS z B))
    (a b : Fin (N + 1)) (σ τ : Λ → Fin (N + 1)) :
    (if b = τ z then A σ (Function.update τ z a) else 0) =
      if a = σ z then A (Function.update σ z b) τ else 0 := by
  have hzeroL : ∀ ρ : Λ → Fin (N + 1), ρ ≠ Function.update τ z a →
      A σ ρ * onSiteS z (Matrix.single a b (1 : ℂ)) ρ τ = 0 := by
    intro ρ hρ
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hρ
    by_cases hkz : k = z
    · rw [hkz, Function.update_self] at hk
      rw [onSiteS_apply, Matrix.single_apply_of_row_ne (Ne.symm hk), ite_self, mul_zero]
    · rw [Function.update_of_ne hkz] at hk
      rw [onSiteS_apply_eq_zero_of_off_site_diff _ _ fun hc => hk (hc k hkz), mul_zero]
  have hzeroR : ∀ ρ : Λ → Fin (N + 1), ρ ≠ Function.update σ z b →
      onSiteS z (Matrix.single a b (1 : ℂ)) σ ρ * A ρ τ = 0 := by
    intro ρ hρ
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hρ
    by_cases hkz : k = z
    · rw [hkz, Function.update_self] at hk
      rw [onSiteS_apply, Matrix.single_apply_of_col_ne _ _ (Ne.symm hk), ite_self, zero_mul]
    · rw [Function.update_of_ne hkz] at hk
      rw [onSiteS_apply_eq_zero_of_off_site_diff _ _ fun hc => hk (hc k hkz).symm, zero_mul]
  have hguardL : ∀ k, k ≠ z → Function.update τ z a k = τ k :=
    fun _ hk => Function.update_of_ne hk _ _
  have hguardR : ∀ k, k ≠ z → σ k = Function.update σ z b k :=
    fun _ hk => (Function.update_of_ne hk _ _).symm
  have hL : (A * onSiteS z (Matrix.single a b (1 : ℂ))) σ τ =
      if b = τ z then A σ (Function.update τ z a) else 0 := by
    rw [Matrix.mul_apply, Fintype.sum_eq_single (Function.update τ z a) hzeroL, onSiteS_apply,
      if_pos hguardL, Function.update_self]
    simp only [Matrix.single_apply, true_and, mul_ite, mul_one, mul_zero]
  have hR : (onSiteS z (Matrix.single a b (1 : ℂ)) * A) σ τ =
      if a = σ z then A (Function.update σ z b) τ else 0 := by
    rw [Matrix.mul_apply, Fintype.sum_eq_single (Function.update σ z b) hzeroR, onSiteS_apply,
      if_pos hguardR, Function.update_self]
    simp only [Matrix.single_apply, and_true, ite_mul, one_mul, zero_mul]
  rw [← hL, ← hR, (h (Matrix.single a b (1 : ℂ))).eq]

/-- **Off-support entries vanish.**  An operator commuting with every on-site operator at the site
`z` cannot connect two configurations differing at `z`: instantiating the entry identity at
`a = b = τ z` makes the left indicator true and the right one false. -/
theorem apply_eq_zero_of_commute_onSiteS {z : Λ} {A : ManyBodyOpS Λ N}
    (h : ∀ B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ, Commute A (onSiteS z B))
    {σ τ : Λ → Fin (N + 1)} (hne : σ z ≠ τ z) : A σ τ = 0 := by
  have hkey := entry_swap_of_commute_onSiteS h (τ z) (τ z) σ τ
  rw [if_pos rfl, Function.update_eq_self, if_neg (Ne.symm hne)] at hkey
  exact hkey

/-- **On-support entries are transported along the complement.**  If `A` commutes with every on-site
operator at `z` and the two configurations already agree at `z`, then changing that common value to
any `c` leaves the entry unchanged.  The hypothesis `σ z = τ z` is essential: the identity operator
commutes with everything, yet its off-diagonal entries are `0` while its diagonal entries are
`1`. -/
theorem apply_update_eq_of_commute_onSiteS {z : Λ} {A : ManyBodyOpS Λ N}
    (h : ∀ B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ, Commute A (onSiteS z B))
    {σ τ : Λ → Fin (N + 1)} (hz : σ z = τ z) (c : Fin (N + 1)) :
    A (Function.update σ z c) (Function.update τ z c) = A σ τ := by
  have hkey := entry_swap_of_commute_onSiteS h c (σ z) (Function.update σ z c) τ
  rw [if_pos hz, Function.update_self, if_pos rfl, Function.update_idem,
    Function.update_eq_self] at hkey
  exact hkey

/-- **Transport along a whole set of off-support sites.**  Iterating the one-site transport over a
finite set `T` of sites outside `S` replaces the row and column configurations by `σ'` and `τ'` on
all of `T` at once.  The side hypothesis `∀ z ∈ T, z ∉ S` is carried inside the induction motive:
the insert step must hand the shrunken hypothesis to the induction hypothesis. -/
private theorem apply_piecewise_eq_of_commute_onSiteS {S : Finset Λ} {A : ManyBodyOpS Λ N}
    (h : ∀ z ∉ S, ∀ B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ, Commute A (onSiteS z B))
    {σ τ σ' τ' : Λ → Fin (N + 1)} (hστ : ∀ i ∉ S, σ i = τ i) (hσ'τ' : ∀ i ∉ S, σ' i = τ' i)
    (T : Finset Λ) (hT : ∀ z ∈ T, z ∉ S) :
    A (T.piecewise σ' σ) (T.piecewise τ' τ) = A σ τ := by
  revert hT
  induction T using Finset.induction_on with
  | empty => intro _; rw [Finset.piecewise_empty, Finset.piecewise_empty]
  | @insert z T hzT ih =>
    intro hins
    have hzS : z ∉ S := hins z (Finset.mem_insert_self z T)
    have hTS : ∀ w ∈ T, w ∉ S := fun w hw => hins w (Finset.mem_insert_of_mem hw)
    have hpre : T.piecewise σ' σ z = T.piecewise τ' τ z := by
      rw [Finset.piecewise_eq_of_notMem _ _ _ hzT, Finset.piecewise_eq_of_notMem _ _ _ hzT]
      exact hστ z hzS
    rw [Finset.piecewise_insert, Finset.piecewise_insert, hσ'τ' z hzS,
      apply_update_eq_of_commute_onSiteS (h z hzS) hpre (τ' z)]
    exact ih hTS

/-- **Support = commutant of the off-support on-site algebra.**  An operator on the spin-`S`
many-body space is supported on the site set `S` — in the two-clause sense of `SupportedOnS`,
i.e. it lies in `B(H_S) ⊗ I_{Λ∖S}` — exactly when it commutes with every single-site operator
placed at a site outside `S`.  The right-hand side is the commutant reading of "acts only on `S`"
used elsewhere in the library (`SupportedOn` of `Quantum/SpinS/AndersonTowerLocalDecay.lean`,
`IsLocalRangeR` of `Quantum/SpinS/LiebSchultzMattisGeneral.lean`); it is spelled out here because
those modules are strictly downstream of this one.

Mathematically this is the finite-dimensional commutation theorem for tensor products,
`(1 ⊗ M_m)' = M_n ⊗ 1`, proved directly from matrix entries.  It is a repository-internal lemma
with **no textbook source**: it is not a Tasaki result and carries no book citation.

Forward it is the disjoint-support commutation theorem at the singleton `{z}`.  Backward, testing
against matrix units gives an entry identity from which the vanishing clause follows at once, and
the restriction clause follows by transporting the configurations one off-support site at a time. -/
theorem supportedOnS_iff_commute_onSiteS {S : Finset Λ} {A : ManyBodyOpS Λ N} :
    SupportedOnS S A ↔
      ∀ z ∉ S, ∀ B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ, Commute A (onSiteS z B) := by
  constructor
  · intro hA z hz B
    exact commute_of_supportedOnS_disjoint hA
      (supportedOnS_onSiteS (Finset.mem_singleton_self z) B)
      (Finset.disjoint_singleton_right.mpr hz)
  · intro h
    refine ⟨fun σ τ hne i hi => ?_, fun σ τ σ' τ' h1 h2 h3 h4 => ?_⟩
    · by_contra hcon
      exact hne (apply_eq_zero_of_commute_onSiteS (h i hi) hcon)
    · have hkey := apply_piecewise_eq_of_commute_onSiteS h h1 h2 (Finset.univ \ S)
        fun z hz => (Finset.mem_sdiff.mp hz).2
      have hσ : (Finset.univ \ S).piecewise σ' σ = σ' := by
        funext i
        by_cases hiS : i ∈ S
        · rw [Finset.piecewise_eq_of_notMem _ _ _ fun hc => (Finset.mem_sdiff.mp hc).2 hiS]
          exact h3 i hiS
        · exact Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiS⟩)
      have hτ : (Finset.univ \ S).piecewise τ' τ = τ' := by
        funext i
        by_cases hiS : i ∈ S
        · rw [Finset.piecewise_eq_of_notMem _ _ _ fun hc => (Finset.mem_sdiff.mp hc).2 hiS]
          exact h4 i hiS
        · exact Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiS⟩)
      rw [hσ, hτ] at hkey
      exact hkey.symm

end LatticeSystem.Quantum
