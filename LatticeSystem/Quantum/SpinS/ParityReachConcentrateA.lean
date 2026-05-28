import LatticeSystem.Quantum.SpinS.ParityReachConcentrate

/-!
# A-side magnetization concentration at a target A-site

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Specialising `parityReachableS_drainSetInto` (#3803) with `S = {a ∈ Finset.univ | A a ∧ a ≠ a₀}`
gives an "A-side concentration" lemma: from `σ`, the config that drains every A-site `a ≠ a₀`
into `a₀` (so `σ' a₀ = ∑_{a∈A} σ a`, `σ' a = 0` for `a ∈ A \ {a₀}`, `σ' k = σ k` for `k ∉ A`) is
`ParityReachableS`-reachable.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The Finset of A-sites distinct from `a₀`. -/
noncomputable def aSitesExcept (A : V → Bool) (a₀ : V) [DecidableEq V] : Finset V :=
  Finset.univ.filter (fun v => A v = true ∧ v ≠ a₀)

omit [Fintype V] [DecidableEq V] in
/-- Membership in `aSitesExcept`. -/
theorem mem_aSitesExcept {A : V → Bool} {a₀ v : V} [Fintype V] [DecidableEq V] :
    v ∈ aSitesExcept A a₀ ↔ A v = true ∧ v ≠ a₀ := by
  simp [aSitesExcept]

/-- **A-side concentration at `a₀`**: starting from `σ`, the config that drains every A-site
`a ≠ a₀` into `a₀` is `ParityReachableS`-reachable.  Requires the target room
`(σ a₀).val + ∑_{a ∈ aSitesExcept} (σ a).val ≤ N`, B-site `b` (not in A) with `(σ b).val + 1 ≤ N`,
and `a₀ ∈ A`. -/
theorem parityReachableS_concentrate_A_at_a0
    (A : V → Bool) {a₀ b : V} (ha₀ : A a₀ = true) (hb : A b = false)
    {σ : V → Fin (N + 1)}
    (hbound : (σ a₀).val + ∑ s ∈ aSitesExcept A a₀, (σ s).val ≤ N)
    (hkb : (σ b).val + 1 ≤ N) :
    ParityReachableS (bipartiteCompleteGraphOf A) σ
      (drainSetInto σ a₀ (aSitesExcept A a₀) hbound
        (by intro h; exact (mem_aSitesExcept.mp h).2 rfl)) := by
  have ha₀b : (bipartiteCompleteGraphOf A).Adj a₀ b := by
    rw [bipartiteCompleteGraphOf_adj_iff]
    refine ⟨?_, ?_⟩
    · intro h; rw [h] at ha₀; exact absurd (ha₀.symm.trans hb) (by decide)
    · rw [ha₀, hb]; decide
  have hS_adj : ∀ s ∈ aSitesExcept A a₀, (bipartiteCompleteGraphOf A).Adj s b := by
    intro s hs
    obtain ⟨hAs, hs_ne⟩ := mem_aSitesExcept.mp hs
    rw [bipartiteCompleteGraphOf_adj_iff]
    refine ⟨?_, ?_⟩
    · intro h; rw [h] at hAs; exact absurd (hAs.symm.trans hb) (by decide)
    · rw [hAs, hb]; decide
  have hS_ne_a₀ : ∀ s ∈ aSitesExcept A a₀, s ≠ a₀ :=
    fun s hs => (mem_aSitesExcept.mp hs).2
  exact parityReachableS_drainSetInto A ha₀b (aSitesExcept A a₀) hS_adj hS_ne_a₀ hbound hkb

end LatticeSystem.Quantum
