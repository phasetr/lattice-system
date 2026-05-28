import LatticeSystem.Quantum.SpinS.ParityReachConcentrateA

/-!
# B-side magnetization concentration at a target B-site

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Symmetric to `parityReachableS_concentrate_A_at_a0` (#3804): the bipartiteCompleteGraphOf treats
A and B symmetrically (it's a complete bipartite graph), so the same concentration argument
applies to B-sites with the A-side as the temporary store.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The Finset of B-sites (`A x = false`) distinct from `b₀`. -/
noncomputable def bSitesExcept (A : V → Bool) (b₀ : V) [DecidableEq V] : Finset V :=
  Finset.univ.filter (fun v => A v = false ∧ v ≠ b₀)

omit [Fintype V] [DecidableEq V] in
/-- Membership in `bSitesExcept`. -/
theorem mem_bSitesExcept {A : V → Bool} {b₀ v : V} [Fintype V] [DecidableEq V] :
    v ∈ bSitesExcept A b₀ ↔ A v = false ∧ v ≠ b₀ := by
  simp [bSitesExcept]

/-- **B-side concentration at `b₀`**: starting from `σ`, the config that drains every B-site
`b ≠ b₀` into `b₀` is `ParityReachableS`-reachable.  Requires the target room
`(σ b₀).val + ∑_{b ∈ bSitesExcept} (σ b).val ≤ N`, A-site `a` (in A) with `(σ a).val + 1 ≤ N`,
and `b₀ ∉ A`. -/
theorem parityReachableS_concentrate_B_at_b0
    (A : V → Bool) {b₀ a : V} (hb₀ : A b₀ = false) (ha : A a = true)
    {σ : V → Fin (N + 1)}
    (hbound : (σ b₀).val + ∑ s ∈ bSitesExcept A b₀, (σ s).val ≤ N)
    (hka : (σ a).val + 1 ≤ N) :
    ParityReachableS (bipartiteCompleteGraphOf A) σ
      (drainSetInto σ b₀ (bSitesExcept A b₀) hbound
        (by intro h; exact (mem_bSitesExcept.mp h).2 rfl)) := by
  have hb₀a : (bipartiteCompleteGraphOf A).Adj b₀ a := by
    rw [bipartiteCompleteGraphOf_adj_iff]
    refine ⟨?_, ?_⟩
    · intro h; rw [h] at hb₀; exact absurd (hb₀.symm.trans ha) (by decide)
    · rw [hb₀, ha]; decide
  have hS_adj : ∀ s ∈ bSitesExcept A b₀, (bipartiteCompleteGraphOf A).Adj s a := by
    intro s hs
    obtain ⟨hAs, hs_ne⟩ := mem_bSitesExcept.mp hs
    rw [bipartiteCompleteGraphOf_adj_iff]
    refine ⟨?_, ?_⟩
    · intro h; rw [h] at hAs; exact absurd (hAs.symm.trans ha) (by decide)
    · rw [hAs, ha]; decide
  have hS_ne_b₀ : ∀ s ∈ bSitesExcept A b₀, s ≠ b₀ :=
    fun s hs => (mem_bSitesExcept.mp hs).2
  exact parityReachableS_drainSetInto A hb₀a (bSitesExcept A b₀) hS_adj hS_ne_b₀ hbound hka

end LatticeSystem.Quantum
