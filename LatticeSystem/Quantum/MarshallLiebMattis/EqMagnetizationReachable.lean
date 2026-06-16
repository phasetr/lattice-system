import LatticeSystem.Quantum.MarshallLiebMattis.EqMagnetization

set_option linter.unusedSectionVars false

/-!
# Equal-magnetisation reachability (Tasaki §2.5 p. 42 Proposition)

This module formalises Tasaki's "Proposition" on p. 42:

  **Proposition.** Let the lattice `(Λ, B)` be connected. Then any
  spin configurations `σ` and `σ'` with `σ̄ = σ̄'` are connected,
  i.e., there is a sequence of single-edge bond swaps converting
  `σ` to `σ'`.

This is the iterative consequence of PR α-4's
`swapReachable_of_preconnected_of_ne` (single-step swap reachability
between any pair `(x, y)` with `σ x ≠ σ y`) combined with PR α-5b's
`magnetization_basisSwap` (swap preserves magnetisation).

Strategy: strong induction on the **disagreement count**
`Δ(σ, σ') := #{x : σ x ≠ σ' x}`. For `σ ≠ σ'` with equal
magnetisation, find sites `x` with `(σ x, σ' x) = (0, 1)` and `y`
with `(σ y, σ' y) = (1, 0)`; then `basisSwap σ x y` reduces `Δ` by
at least 2 (it newly agrees with `σ'` at both `x` and `y`), and
preserves the magnetisation.

References:

- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5, p. 42 (Proposition in "Proof of Property (iii)").
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Disagreement set and count -/

/-- The set of sites where `σ` and `σ'` disagree. -/
def disagreementSet (σ σ' : Λ → Fin 2) : Finset Λ :=
  Finset.univ.filter (fun x => σ x ≠ σ' x)

/-- Configuration distance is the size of the disagreement set. -/
def configDist (σ σ' : Λ → Fin 2) : ℕ := (disagreementSet σ σ').card

omit [DecidableEq Λ] in
@[simp] theorem mem_disagreementSet {σ σ' : Λ → Fin 2} {x : Λ} :
    x ∈ disagreementSet σ σ' ↔ σ x ≠ σ' x := by
  simp [disagreementSet]

omit [DecidableEq Λ] in
theorem configDist_eq_zero_iff (σ σ' : Λ → Fin 2) :
    configDist σ σ' = 0 ↔ σ = σ' := by
  unfold configDist disagreementSet
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  refine ⟨fun h => funext fun x => ?_, fun h x _ hne => hne (h ▸ rfl)⟩
  by_contra hne
  exact h (Finset.mem_univ x) hne

/-! ## Existence of `(0, 1)` and `(1, 0)` sites for distinct
configurations of equal magnetisation -/

omit [DecidableEq Λ] in
/-- For `σ ≠ σ'` with equal magnetisation, there exist sites
`x, y` with `σ x = 0`, `σ' x = 1`, `σ y = 1`, `σ' y = 0`.

The pigeonhole-style argument: the disagreement set partitions into
`{σ_x = 0, σ'_x = 1}` and `{σ_x = 1, σ'_x = 0}`; magnetisation
equality forces these subsets to have equal cardinality, and
non-emptiness of the disagreement set forces both to be non-empty. -/
theorem exists_swap_pair_of_eq_magnetization
    {σ σ' : Λ → Fin 2} (hne : σ ≠ σ')
    (hmag : magnetization Λ σ = magnetization Λ σ') :
    ∃ x y : Λ, σ x = 0 ∧ σ' x = 1 ∧ σ y = 1 ∧ σ' y = 0 := by
  classical
  -- The difference of magnetisations decomposes as
  --   2 · (#D01 - #D10), where D01 = {σ=0, σ'=1}, D10 = {σ=1, σ'=0}.
  -- Equality forces #D01 = #D10. Non-emptiness of disagreement set
  -- forces both to be non-empty.
  -- Show D01 nonempty (equivalently D10 nonempty by symmetry).
  set D01 : Finset Λ := Finset.univ.filter (fun x => σ x = 0 ∧ σ' x = 1) with hD01_def
  set D10 : Finset Λ := Finset.univ.filter (fun x => σ x = 1 ∧ σ' x = 0) with hD10_def
  -- Cardinality argument: D01.card = D10.card from magnetisation equality.
  have hcard : D01.card = D10.card := by
    -- magnetization σ - magnetization σ' = 2 (D01.card - D10.card) (as integers).
    -- This is 0 by hmag, so D01.card = D10.card.
    have hsub_zero : (∑ x : Λ, (spinSign (σ x) - spinSign (σ' x))) = 0 := by
      rw [Finset.sum_sub_distrib]
      change magnetization Λ σ - magnetization Λ σ' = 0
      rw [hmag, sub_self]
    have hexpand :
        (∑ x : Λ, (spinSign (σ x) - spinSign (σ' x))) =
        2 * (D01.card : ℤ) - 2 * (D10.card : ℤ) := by
      have hpoint : ∀ x : Λ,
          spinSign (σ x) - spinSign (σ' x) =
          (if x ∈ D01 then (2 : ℤ)
           else if x ∈ D10 then (-2 : ℤ) else 0) := by
        intro x
        simp only [hD01_def, hD10_def, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases h_σx : σ x with ⟨kx, _⟩
        rcases h_σ'x : σ' x with ⟨k'x, _⟩
        interval_cases kx <;> interval_cases k'x <;> simp [spinSign]
      have hpoint_pair : ∀ x : Λ,
          spinSign (σ x) - spinSign (σ' x) =
          (if x ∈ D01 then (2 : ℤ) else 0) +
          (if x ∈ D10 then (-2 : ℤ) else 0) := by
        intro x
        rw [hpoint x]
        by_cases hxD01 : x ∈ D01
        · have hxD10 : x ∉ D10 := by
            simp only [hD01_def, hD10_def, Finset.mem_filter, Finset.mem_univ, true_and] at hxD01 ⊢
            intro h
            rw [hxD01.1] at h
            exact zero_ne_one h.1
          simp [hxD01, hxD10]
        · by_cases hxD10 : x ∈ D10
          · simp [hxD01, hxD10]
          · simp [hxD01, hxD10]
      calc (∑ x : Λ, (spinSign (σ x) - spinSign (σ' x)))
          = ∑ x : Λ, ((if x ∈ D01 then (2 : ℤ) else 0) +
                       (if x ∈ D10 then (-2 : ℤ) else 0)) :=
            Finset.sum_congr rfl fun x _ => hpoint_pair x
        _ = (∑ x : Λ, (if x ∈ D01 then (2 : ℤ) else 0)) +
            (∑ x : Λ, (if x ∈ D10 then (-2 : ℤ) else 0)) :=
            Finset.sum_add_distrib
        _ = 2 * (D01.card : ℤ) - 2 * (D10.card : ℤ) := by
            rw [← Finset.sum_filter, ← Finset.sum_filter,
                Finset.sum_const, Finset.sum_const]
            -- The filter of "x ∈ D01" over univ equals D01.
            have h_filter_D01 :
                Finset.univ.filter (fun x => x ∈ D01) = D01 := by
              ext x; simp
            have h_filter_D10 :
                Finset.univ.filter (fun x => x ∈ D10) = D10 := by
              ext x; simp
            rw [h_filter_D01, h_filter_D10]
            ring
    rw [hexpand] at hsub_zero
    omega
  -- Show D01 nonempty.
  have hdis_nonempty : (disagreementSet σ σ').Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    apply hne
    funext x
    by_contra hne
    have : x ∈ disagreementSet σ σ' := mem_disagreementSet.mpr hne
    rw [hempty] at this
    exact Finset.notMem_empty _ this
  obtain ⟨z, hz⟩ := hdis_nonempty
  -- z is in D01 or D10.
  have hin : z ∈ D01 ∨ z ∈ D10 := by
    simp only [hD01_def, hD10_def, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mem_disagreementSet] at hz
    by_cases hsσz : σ z = 0
    · -- σ z = 0; since σ z ≠ σ' z, σ' z = 1.
      have hs'σz : σ' z = 1 := by
        have h0 : σ' z ≠ 0 := fun h => hz (hsσz.trans h.symm)
        rcases hv : σ' z with ⟨k, hk⟩
        interval_cases k
        · exact absurd hv h0
        · rfl
      left; exact ⟨hsσz, hs'σz⟩
    · -- σ z = 1.
      have hsσz1 : σ z = 1 := by
        rcases hv : σ z with ⟨k, hk⟩
        interval_cases k
        · exact absurd hv hsσz
        · rfl
      have hs'σz0 : σ' z = 0 := by
        have h1 : σ' z ≠ 1 := fun h => hz (hsσz1.trans h.symm)
        rcases hv : σ' z with ⟨k, hk⟩
        interval_cases k
        · rfl
        · exact absurd hv h1
      right; exact ⟨hsσz1, hs'σz0⟩
  rcases hin with hzD01 | hzD10
  · -- z ∈ D01, so |D01| ≥ 1. By hcard, |D10| ≥ 1, so D10 nonempty.
    have hD10_pos : 0 < D10.card := by
      rw [← hcard]
      exact Finset.card_pos.mpr ⟨z, hzD01⟩
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hD10_pos
    simp only [hD01_def, hD10_def, Finset.mem_filter, Finset.mem_univ, true_and] at hzD01 hy
    exact ⟨z, y, hzD01.1, hzD01.2, hy.1, hy.2⟩
  · -- z ∈ D10, similarly D01 nonempty.
    have hD01_pos : 0 < D01.card := by
      rw [hcard]
      exact Finset.card_pos.mpr ⟨z, hzD10⟩
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hD01_pos
    simp only [hD01_def, hD10_def, Finset.mem_filter, Finset.mem_univ, true_and] at hzD10 hx
    exact ⟨x, z, hx.1, hx.2, hzD10.1, hzD10.2⟩

/-! ## `basisSwap` reduces `configDist` to `σ'` -/

/-- For sites `x, y` with `σ x = 0, σ' x = 1, σ y = 1, σ' y = 0`,
swapping at `(x, y)` strictly decreases the configuration distance
to `σ'`. -/
theorem configDist_basisSwap_lt
    {σ σ' : Λ → Fin 2} {x y : Λ}
    (hx0 : σ x = 0) (hx1 : σ' x = 1) (hy1 : σ y = 1) (hy0 : σ' y = 0) :
    configDist (basisSwap σ x y) σ' < configDist σ σ' := by
  -- x ≠ y from σ x = 0 ≠ 1 = σ y.
  have hxy : x ≠ y := by
    intro heq; subst heq
    rw [hx0] at hy1; exact zero_ne_one hy1
  -- After basisSwap: at x, value is σ y = 1 = σ' x; at y, value is σ x = 0 = σ' y.
  -- Both newly agree with σ', so disagreement strictly shrinks.
  refine Finset.card_lt_card ?_
  refine ⟨?_, ?_⟩
  · -- ⊆: disagreementSet (basisSwap σ x y) σ' ⊆ disagreementSet σ σ'.
    intro z hz
    rw [mem_disagreementSet] at hz ⊢
    by_cases hzx : z = x
    · -- z = x: (basisSwap) x = σ y = 1 = σ' x. Contradicts hz.
      exfalso
      apply hz
      subst hzx
      unfold basisSwap
      rw [Function.update_of_ne hxy, Function.update_self, hy1, hx1]
    · by_cases hzy : z = y
      · -- z = y: (basisSwap) y = σ x = 0 = σ' y. Contradicts hz.
        exfalso
        apply hz
        subst hzy
        unfold basisSwap
        rw [Function.update_self, hx0, hy0]
      · -- z ∉ {x, y}: (basisSwap) z = σ z, so disagreement is the same.
        have : basisSwap σ x y z = σ z := by
          unfold basisSwap
          rw [Function.update_of_ne hzy, Function.update_of_ne hzx]
        rw [this] at hz
        exact hz
  · -- ⊊ (strict): x ∈ disagreementSet σ σ' but x ∉ disagreementSet (basisSwap) σ'.
    intro hsubset
    have hx_in_orig : x ∈ disagreementSet σ σ' := by
      rw [mem_disagreementSet, hx0, hx1]
      decide
    have hx_in_swap : x ∈ disagreementSet (basisSwap σ x y) σ' := hsubset hx_in_orig
    rw [mem_disagreementSet] at hx_in_swap
    apply hx_in_swap
    unfold basisSwap
    rw [Function.update_of_ne hxy, Function.update_self, hy1, hx1]

/-! ## Tasaki Proposition: equal-magnetisation reachability -/

/-- **Tasaki §2.5 p. 42 Proposition.** For a connected graph `G`,
any two configurations `σ` and `σ'` with the same total
magnetisation are connected by a sequence of single-edge bond swaps.

Proof: strong induction on `configDist σ σ'`. If `σ = σ'`, refl.
Otherwise, find sites `x ∈ D01` and `y ∈ D10` (existence from
`exists_swap_pair_of_eq_magnetization`); apply
`swapReachable_of_preconnected_of_ne` to get
`SwapReachable G σ (basisSwap σ x y)`; the IH applies to
`basisSwap σ x y` and `σ'` since the configDist strictly
decreased and the magnetisation is preserved
(`magnetization_basisSwap`). -/
theorem swapReachable_of_eq_magnetization
    {G : SimpleGraph Λ} (hG : G.Preconnected) :
    ∀ (σ σ' : Λ → Fin 2),
      magnetization Λ σ = magnetization Λ σ' →
      SwapReachable G σ σ' := by
  intro σ
  -- Strong induction on configDist σ σ'.
  -- We prove: ∀ σ', configDist σ σ' ≤ n → mag eq → reachable.
  have aux : ∀ (n : ℕ) (σ σ' : Λ → Fin 2),
      configDist σ σ' ≤ n →
      magnetization Λ σ = magnetization Λ σ' →
      SwapReachable G σ σ' := by
    intro n
    induction n with
    | zero =>
      intro σ σ' hd hmag
      have : configDist σ σ' = 0 := Nat.le_zero.mp hd
      rw [(configDist_eq_zero_iff σ σ').mp this]
      exact SwapReachable.refl G σ'
    | succ k ih =>
      intro σ σ' hd hmag
      by_cases hd0 : configDist σ σ' = 0
      · rw [(configDist_eq_zero_iff σ σ').mp hd0]
        exact SwapReachable.refl G σ'
      · -- σ ≠ σ' with same magnetisation.
        have hne : σ ≠ σ' := fun heq =>
          hd0 ((configDist_eq_zero_iff σ σ').mpr heq)
        -- Find x, y.
        obtain ⟨x, y, hx0, hx1, hy1, hy0⟩ :=
          exists_swap_pair_of_eq_magnetization hne hmag
        have hσxy : σ x ≠ σ y := by rw [hx0, hy1]; decide
        -- Step 1: σ → basisSwap σ x y (single PF Property (iii) step).
        have hreach1 : SwapReachable G σ (basisSwap σ x y) :=
          swapReachable_of_preconnected_of_ne hG x y hσxy
        -- Step 2: configDist (basisSwap σ x y) σ' < configDist σ σ' ≤ k+1.
        have hlt : configDist (basisSwap σ x y) σ' < configDist σ σ' :=
          configDist_basisSwap_lt hx0 hx1 hy1 hy0
        have hle : configDist (basisSwap σ x y) σ' ≤ k :=
          Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hlt hd)
        -- Step 3: magnetization preserved.
        have hmag' : magnetization Λ (basisSwap σ x y) = magnetization Λ σ' := by
          rw [magnetization_basisSwap]; exact hmag
        -- Step 4: IH on basisSwap σ x y.
        have hreach2 : SwapReachable G (basisSwap σ x y) σ' :=
          ih (basisSwap σ x y) σ' hle hmag'
        exact hreach1.trans hreach2
  intro σ' hmag
  exact aux (configDist σ σ') σ σ' (le_refl _) hmag

end LatticeSystem.Quantum
