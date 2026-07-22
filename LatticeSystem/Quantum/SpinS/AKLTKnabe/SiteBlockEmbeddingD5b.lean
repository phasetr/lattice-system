import LatticeSystem.Quantum.SpinS.AKLTKnabe.P2OperatorBridgeD5b

/-!
# Gate D5b Stage 3: the multi-site block embedding `onEmbS` and the four-site AKLT window

This module (Issue #5094; Tasaki §7.1.4, Knabe) provides the one genuinely new abstraction of the
bridge: the embedding of an `m`-site operator into an `Λ`-site many-body operator,

  `onEmbS ι A σ' σ = if (σ' and σ agree off the range of ι) then A (σ' ∘ ι) (σ ∘ ι) else 0`,

together with its **multiplicativity** `onEmbS ι A * onEmbS ι B = onEmbS ι (A * B)` for injective
`ι`.  Multiplicativity is what lets the two-site Stage-2 bridge
`bondSpin2ProjectionS_fin2_apply_eq_sector2P2Entry` be transported to an arbitrary bond `{x, y}`
of a chain, because `bondSpin2ProjectionS` is a *polynomial* `½ D + ⅙ D² + ⅓` in the bond
Heisenberg operator and the squaring has to be performed after the embedding.

The `τ`-sum in the product is over the whole configuration type `Λ → Fin (N + 1)`; it is collapsed
onto the `m`-site fibre by `Finset.sum_subset` (the off-fibre terms vanish) followed by
`Finset.sum_nbij'` with the mutually inverse maps `τ ↦ τ ∘ ι` and `a ↦ Function.extend ι a σ`.
For `Λ = Fin 4`, `m = 4` a literal enumeration of the `81` configurations would be unaffordable, so
the bijection is essential and no sum is ever enumerated here.

The capstone is the **open three-bond window** of Tasaki eq. (7.1.30) with `ℓ = 3`,

  `akltWindow3H = P̂₀₁ + P̂₁₂ + P̂₂₃`  on `Fin 4`,

proved entrywise equal to the cast of the frozen rational model `physicalHEntry`.  Note that the
window is **open**: it is written with the three explicit pairs and never through
`akltHamiltonianS`, whose `ringCoupling` would add the periodic fourth bond `{3, 0}` because
`ringSucc 3 = 0` on `Fin 4` (design risk R3).  The spectator sites of the middle bond are `0`
and `3`, which are *not* contiguous (design risk R6); the three guard lemmas below record each
spectator pair separately.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.1.4, eq. (7.1.30), p. 189.
-/

namespace LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential

open Matrix

/-! ## The block embedding -/

section Embedding

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N m : ℕ}

/-- The **block-embedded operator** `onEmbS ι A`: it acts as the `m`-site operator `A` on the
sites listed by `ι : Fin m → Λ` and as the identity on every other site.  Its matrix element is
`A (σ' ∘ ι) (σ ∘ ι)` when the two configurations agree at every site outside the range of `ι`,
and `0` otherwise.  For `m = 1` this is `onSiteS`. -/
def onEmbS (ι : Fin m → Λ)
    (A : Matrix (Fin m → Fin (N + 1)) (Fin m → Fin (N + 1)) ℂ) : ManyBodyOpS Λ N :=
  fun σ' σ => if (∀ k, (∀ i, ι i ≠ k) → σ' k = σ k) then A (σ' ∘ ι) (σ ∘ ι) else 0

/-- Unfolding the matrix element of `onEmbS ι A`. -/
theorem onEmbS_apply (ι : Fin m → Λ)
    (A : Matrix (Fin m → Fin (N + 1)) (Fin m → Fin (N + 1)) ℂ)
    (σ' σ : Λ → Fin (N + 1)) :
    onEmbS ι A σ' σ =
      if (∀ k, (∀ i, ι i ≠ k) → σ' k = σ k) then A (σ' ∘ ι) (σ ∘ ι) else 0 := rfl

/-- The block embedding of the `m`-site identity is the many-body identity. -/
theorem onEmbS_one (ι : Fin m → Λ) :
    (onEmbS ι (1 : Matrix (Fin m → Fin (N + 1)) (Fin m → Fin (N + 1)) ℂ) :
        ManyBodyOpS Λ N) = 1 := by
  ext σ' σ
  rw [onEmbS_apply ι 1 σ' σ]
  by_cases hg : ∀ k, (∀ i, ι i ≠ k) → σ' k = σ k
  · rw [if_pos hg, Matrix.one_apply, Matrix.one_apply]
    by_cases he : σ' = σ
    · rw [if_pos he, if_pos]
      rw [he]
    · rw [if_neg he, if_neg]
      intro hc
      refine he (funext fun k => ?_)
      by_cases hk : ∃ i, ι i = k
      · obtain ⟨i, rfl⟩ := hk
        exact congrFun hc i
      · exact hg k fun i hi => hk ⟨i, hi⟩
  · rw [if_neg hg, Matrix.one_apply, if_neg]
    intro he
    exact hg fun k _ => congrFun he k

/-- The block embedding is additive in the embedded operator. -/
theorem onEmbS_add (ι : Fin m → Λ)
    (A B : Matrix (Fin m → Fin (N + 1)) (Fin m → Fin (N + 1)) ℂ) :
    (onEmbS ι (A + B) : ManyBodyOpS Λ N) = onEmbS ι A + onEmbS ι B := by
  ext σ' σ
  simp only [onEmbS_apply, Matrix.add_apply]
  split_ifs with h
  · rfl
  · rw [add_zero]

/-- The block embedding commutes with scalar multiplication. -/
theorem onEmbS_smul (ι : Fin m → Λ) (c : ℂ)
    (A : Matrix (Fin m → Fin (N + 1)) (Fin m → Fin (N + 1)) ℂ) :
    (onEmbS ι (c • A) : ManyBodyOpS Λ N) = c • onEmbS ι A := by
  ext σ' σ
  simp only [onEmbS_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs with h
  · rfl
  · rw [mul_zero]

/-- **Multiplicativity of the block embedding** (design item B5c).  For an injective site list
`ι`, embedding is a ring homomorphism on products: the `τ`-sum over all configurations of `Λ`
collapses onto the `m`-site fibre through `τ ↦ τ ∘ ι`, whose inverse on the fibre is
`a ↦ Function.extend ι a σ`.  This is the step that makes the polynomial
`½ D + ⅙ D² + ⅓` defining `bondSpin2ProjectionS` transport along the embedding. -/
theorem onEmbS_mul {ι : Fin m → Λ} (hι : Function.Injective ι)
    (A B : Matrix (Fin m → Fin (N + 1)) (Fin m → Fin (N + 1)) ℂ) :
    (onEmbS ι A * onEmbS ι B : ManyBodyOpS Λ N) = onEmbS ι (A * B) := by
  ext σ' σ
  rw [Matrix.mul_apply, onEmbS_apply ι (A * B) σ' σ]
  by_cases hg : ∀ k, (∀ i, ι i ≠ k) → σ' k = σ k
  · rw [if_pos hg, Matrix.mul_apply]
    have hfib : ∀ τ ∈ (Finset.univ : Finset (Λ → Fin (N + 1))),
        τ ∉ Finset.univ.filter
            (fun τ : Λ → Fin (N + 1) => ∀ k, (∀ i, ι i ≠ k) → τ k = σ k) →
          onEmbS ι A σ' τ * onEmbS ι B τ σ = 0 := by
      intro τ _ hτ
      have hnot : ¬ ∀ k, (∀ i, ι i ≠ k) → τ k = σ k := fun h =>
        hτ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      simp only [onEmbS_apply]
      rw [if_neg hnot, mul_zero]
    refine Eq.trans (Finset.sum_subset (Finset.subset_univ _) hfib).symm ?_
    refine Finset.sum_nbij' (fun τ => τ ∘ ι) (fun a => Function.extend ι a σ)
      (fun τ _ => Finset.mem_univ _) ?_ ?_ ?_ ?_
    · intro a _
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun k hk => ?_⟩
      exact Function.extend_apply' a σ k (by rintro ⟨i, hi⟩; exact hk i hi)
    · intro τ hτ
      rw [Finset.mem_filter] at hτ
      funext k
      change Function.extend ι (τ ∘ ι) σ k = τ k
      by_cases hk : ∃ i, ι i = k
      · obtain ⟨i, rfl⟩ := hk
        rw [hι.extend_apply]
        rfl
      · rw [Function.extend_apply' _ _ _ hk]
        exact (hτ.2 k fun i hi => hk ⟨i, hi⟩).symm
    · intro a _
      exact Function.extend_comp hι a σ
    · intro τ hτ
      rw [Finset.mem_filter] at hτ
      have hA : ∀ k, (∀ i, ι i ≠ k) → σ' k = τ k := fun k hk =>
        (hg k hk).trans (hτ.2 k hk).symm
      simp only [onEmbS_apply]
      rw [if_pos hA, if_pos hτ.2]
  · rw [if_neg hg]
    refine Finset.sum_eq_zero fun τ _ => ?_
    by_cases h1 : ∀ k, (∀ i, ι i ≠ k) → σ' k = τ k
    · have h2 : ¬ ∀ k, (∀ i, ι i ≠ k) → τ k = σ k := fun hh =>
        hg fun k hk => (h1 k hk).trans (hh k hk)
      simp only [onEmbS_apply]
      rw [if_neg h2, mul_zero]
    · simp only [onEmbS_apply]
      rw [if_neg h1, zero_mul]

/-! ## The two-site block: bonds -/

omit [Fintype Λ] [DecidableEq Λ] in
/-- The two-site list `![x, y]` is injective whenever the two sites are distinct.  Not `private`:
`onEmbS_mul` is applied to bond embeddings in the Gate D6b modules as well, and a second copy of
this lemma there would be a duplicate declaration. -/
theorem injective_bondEmb {x y : Λ} (hxy : x ≠ y) :
    Function.Injective (![x, y] : Fin 2 → Λ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

omit [Fintype Λ] [DecidableEq Λ] in
/-- The `onEmbS` spectator guard for the two-site list `![x, y]` is exactly the off-bond
agreement condition `∀ k ∉ {x, y}, σ' k = σ k` used by the production `spinSDot` lemmas. -/
private theorem emb_two_guard_iff {x y : Λ} (σ' σ : Λ → Fin (N + 1)) :
    (∀ k, (∀ i, (![x, y] : Fin 2 → Λ) i ≠ k) → σ' k = σ k)
      ↔ (∀ k, k ≠ x → k ≠ y → σ' k = σ k) := by
  have h0 : (![x, y] : Fin 2 → Λ) 0 = x := Matrix.cons_val_zero _ _
  have h1 : (![x, y] : Fin 2 → Λ) 1 = y := by
    rw [Matrix.cons_val_one, Matrix.cons_val_zero]
  constructor
  · intro h k hkx hky
    refine h k (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · rw [h0]; exact hkx.symm
    · rw [h1]; exact hky.symm
  · intro h k hk
    refine h k ?_ ?_
    · rw [← h0]; exact (hk 0).symm
    · rw [← h1]; exact (hk 1).symm

/-- **The bond Heisenberg operator is a two-site block embedding** (design item B5d).  For
distinct sites `x ≠ y`, `Ŝ_x · Ŝ_y` on `Λ` is the embedding along `![x, y]` of the two-site
`Ŝ₀ · Ŝ₁` on `Fin 2`. -/
theorem spinSDot_eq_onEmbS {x y : Λ} (hxy : x ≠ y) (N : ℕ) :
    (spinSDot x y N : ManyBodyOpS Λ N) = onEmbS ![x, y] (spinSDot (0 : Fin 2) 1 N) := by
  ext σ' σ
  rw [onEmbS_apply]
  by_cases hg : ∀ k, (∀ i, (![x, y] : Fin 2 → Λ) i ≠ k) → σ' k = σ k
  · rw [if_pos hg]
    rw [spinSDot_apply_of_off_two_site_agree hxy N ((emb_two_guard_iff σ' σ).mp hg)]
    have hne : (0 : Fin 2) ≠ 1 := by decide
    have hvac : ∀ k : Fin 2, k ≠ 0 → k ≠ 1 →
        (σ' ∘ (![x, y] : Fin 2 → Λ)) k = (σ ∘ (![x, y] : Fin 2 → Λ)) k := by
      intro k h0 h1
      fin_cases k
      · exact absurd rfl h0
      · exact absurd rfl h1
    rw [spinSDot_apply_of_off_two_site_agree hne N hvac]
    simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  · rw [if_neg hg]
    exact spinSDot_apply_eq_zero_of_off_two_site_diff hxy N
      fun hc => hg ((emb_two_guard_iff σ' σ).mpr hc)

end Embedding

/-! ## Transport of the two-site bridge to an arbitrary bond of a chain -/

section Chain

variable {L : ℕ}

/-- **The bond spin-two projection is a two-site block embedding** (design item B5e).  For
distinct sites `x ≠ y` of the chain `Fin L`, `P̂₂[Ŝ_x + Ŝ_y]` is the embedding along `![x, y]` of
the two-site projection on `Fin 2`.  The squaring inside the defining polynomial
`½ D + ⅙ D² + ⅓` is transported by `onEmbS_mul`. -/
theorem bondSpin2ProjectionS_eq_onEmbS {x y : Fin L} (hxy : x ≠ y) :
    (bondSpin2ProjectionS x y : ManyBodyOpS (Fin L) 2)
      = onEmbS ![x, y] (bondSpin2ProjectionS (0 : Fin 2) 1) := by
  simp only [bondSpin2ProjectionS, onEmbS_add, onEmbS_smul,
    onEmbS_mul (injective_bondEmb hxy), onEmbS_one, spinSDot_eq_onEmbS hxy 2]

/-- **The entries of an arbitrary chain bond, in the frozen rational model.**  For `x ≠ y` the
matrix element of `P̂₂[Ŝ_x + Ŝ_y]` is the cast of `sector2P2Entry` read off the two bond sites,
guarded by agreement of the two configurations at every spectator site. -/
theorem bondSpin2ProjectionS_apply_eq_sector2P2Entry {x y : Fin L} (hxy : x ≠ y)
    (σ' σ : Fin L → Fin 3) :
    bondSpin2ProjectionS x y σ' σ =
      if (∀ k, k ≠ x → k ≠ y → σ' k = σ k) then
        ((sector2P2Entry (σ' x) (σ' y) (σ x) (σ y) : ℚ) : ℂ)
      else 0 := by
  rw [bondSpin2ProjectionS_eq_onEmbS hxy, onEmbS_apply]
  by_cases hg : ∀ k, (∀ i, (![x, y] : Fin 2 → Fin L) i ≠ k) → σ' k = σ k
  · rw [if_pos hg, if_pos ((emb_two_guard_iff σ' σ).mp hg),
      bondSpin2ProjectionS_fin2_apply_eq_sector2P2Entry]
    simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  · rw [if_neg hg, if_neg fun hc => hg ((emb_two_guard_iff σ' σ).mpr hc)]

end Chain

/-! ## The open three-bond window on four sites (Tasaki eq. (7.1.30), `ℓ = 3`) -/

/-- The **open three-bond AKLT window** `ĥ = P̂₀₁ + P̂₁₂ + P̂₂₃` on four sites, Tasaki
eq. (7.1.30) with `ℓ = 3`.  Written with the three explicit bond pairs, so the periodic fourth
bond `{3, 0}` that `akltHamiltonianS 4` would contribute (`ringSucc 3 = 0` on `Fin 4`) is
excluded by construction. -/
noncomputable def akltWindow3H : ManyBodyOpS (Fin 4) 2 :=
  bondSpin2ProjectionS (0 : Fin 4) 1 + bondSpin2ProjectionS (1 : Fin 4) 2
    + bondSpin2ProjectionS (2 : Fin 4) 3

/-- Spectators of the window bond `{0, 1}`: the sites `2` and `3`. -/
private theorem window_guard01 (σ' σ : SpinConfig) :
    (∀ k : Fin 4, k ≠ 0 → k ≠ 1 → σ' k = σ k) ↔ (σ' 2 = σ 2 ∧ σ' 3 = σ 3) := by
  constructor
  · intro h
    exact ⟨h 2 (by decide) (by decide), h 3 (by decide) (by decide)⟩
  · rintro ⟨h2, h3⟩ k hk0 hk1
    fin_cases k
    · exact absurd rfl hk0
    · exact absurd rfl hk1
    · exact h2
    · exact h3

/-- Spectators of the window bond `{1, 2}`: the sites `0` and `3`, which are **not**
contiguous. -/
private theorem window_guard12 (σ' σ : SpinConfig) :
    (∀ k : Fin 4, k ≠ 1 → k ≠ 2 → σ' k = σ k) ↔ (σ' 0 = σ 0 ∧ σ' 3 = σ 3) := by
  constructor
  · intro h
    exact ⟨h 0 (by decide) (by decide), h 3 (by decide) (by decide)⟩
  · rintro ⟨h0, h3⟩ k hk1 hk2
    fin_cases k
    · exact h0
    · exact absurd rfl hk1
    · exact absurd rfl hk2
    · exact h3

/-- Spectators of the window bond `{2, 3}`: the sites `0` and `1`. -/
private theorem window_guard23 (σ' σ : SpinConfig) :
    (∀ k : Fin 4, k ≠ 2 → k ≠ 3 → σ' k = σ k) ↔ (σ' 0 = σ 0 ∧ σ' 1 = σ 1) := by
  constructor
  · intro h
    exact ⟨h 0 (by decide) (by decide), h 1 (by decide) (by decide)⟩
  · rintro ⟨h0, h1⟩ k hk2 hk3
    fin_cases k
    · exact h0
    · exact h1
    · exact absurd rfl hk2
    · exact absurd rfl hk3

/-- **The Stage-3 capstone: the four-site AKLT window has the frozen rational entries.**  Every
matrix element of the genuine operator `ĥ = P̂₀₁ + P̂₁₂ + P̂₂₃` (Tasaki eq. (7.1.30), `ℓ = 3`),
built from the production `bondSpin2ProjectionS`, is the cast of the corresponding entry of the
frozen rational model `physicalHEntry` on which the Gate C/D5a Knabe certificate was verified.
This is what Stage 4 consumes to turn `RatPosSemidef qRat` into positive semidefiniteness of
`ĥ² − (2/5) ĥ`. -/
theorem akltWindow3H_apply_eq_physicalHEntry (σ' σ : SpinConfig) :
    akltWindow3H σ' σ = ((physicalHEntry σ' σ : ℚ) : ℂ) := by
  simp only [akltWindow3H, Matrix.add_apply,
    bondSpin2ProjectionS_apply_eq_sector2P2Entry (by decide : (0 : Fin 4) ≠ 1),
    bondSpin2ProjectionS_apply_eq_sector2P2Entry (by decide : (1 : Fin 4) ≠ 2),
    bondSpin2ProjectionS_apply_eq_sector2P2Entry (by decide : (2 : Fin 4) ≠ 3),
    window_guard01, window_guard12, window_guard23,
    physicalHEntry, bond01Entry, bond12Entry, bond23Entry]
  split_ifs <;> push_cast <;> ring

end LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential
