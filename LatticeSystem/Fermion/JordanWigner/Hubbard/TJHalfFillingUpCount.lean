import LatticeSystem.Fermion.JordanWigner.Hubbard.TJHalfFillingAmplitude
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSwapReachable

/-!
# Tasaki 11.5.3: half-filling ground amplitudes depend only on the up-count (Theorem 11.26 PR3i-3b)

The per-bond spin-swap invariance (`tJ_ground_amplitude_swap_invariant`, PR3i-3a) propagates
along the connected chain: any two half-filling configs with the same number of up-spins are
connected
by adjacent value-swaps (`adjacentSwapReachable_of_same_counts`, from the Prop 11.24 route), each of
which is an adjacent bond swap.  Hence:

* `tJ_ground_amplitude_eq_of_same_upCount` — for a ground state `v` and sector configs `t, t'`
  with the same up-count, `v (tJConfigOf t) = v (tJConfigOf t')`.

So the ground amplitudes are constant on each up-count class — the last combinatorial input
before the degeneracy upper bound `finrank ≤ N+2` (there are `N+2` up-counts).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.3, Theorem 11.26 (pp. 445–447).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph
open scoped BigOperators

variable {N : ℕ}

/-- A configuration with no empty site (`∀ k, s k ≠ 0`) has full up+down count `= N+1`. -/
theorem tJ_upDownCount_of_full (s : Fin (N + 1) → Fin 3) (hfull : ∀ k, s k ≠ 0) :
    (Finset.univ.filter (fun k => s k = 1)).card
      + (Finset.univ.filter (fun k => s k = 2)).card = N + 1 := by
  classical
  have hdisj : Disjoint (Finset.univ.filter (fun k => s k = 1))
      (Finset.univ.filter (fun k => s k = 2)) := by
    rw [Finset.disjoint_left]; intro a h1 h2
    rw [Finset.mem_filter] at h1 h2; rw [h1.2] at h2; exact absurd h2.2 (by decide)
  have hunion : Finset.univ.filter (fun k => s k = 1) ∪
      Finset.univ.filter (fun k => s k = 2) = Finset.univ := by
    have h3 : ∀ a : Fin 3, a ≠ 0 → a = 1 ∨ a = 2 := by decide
    apply Finset.eq_univ_of_forall; intro k
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases h3 (s k) (hfull k) with h | h
    · exact Or.inl ⟨Finset.mem_univ k, h⟩
    · exact Or.inr ⟨Finset.mem_univ k, h⟩
  rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]

/-- **A single adjacent value-swap preserves the ground amplitude.**  If `s` is full and `s'` is the
adjacent value-swap of `s`, then `v (tJConfigOf s) = v (tJConfigOf s')`. -/
theorem tJ_ground_amplitude_eq_of_adjacentSwapStep (τ J : ℝ) (hJ : 0 < J)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hv : v ∈ groundSubmoduleAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) (N + 1))
    {s s' : Fin (N + 1) → Fin 3} (hfull : ∀ k, s k ≠ 0) (hstep : AdjacentSwapStep N s s') :
    v (tJConfigOf N s) = v (tJConfigOf N s') := by
  obtain ⟨a, b, hadj, _, hs'⟩ := hstep
  have hsec : (Finset.univ.filter (fun k => s k = 1)).card
      + (Finset.univ.filter (fun k => s k = 2)).card = N + 1 := tJ_upDownCount_of_full s hfull
  have := tJ_ground_amplitude_swap_invariant τ J hJ hv a b hadj ⟨s, hsec⟩
  rw [this, hs', tJSpinSwap_eq_comp_swap]

/-- **Reachable configurations share the ground amplitude.**  If `s` is full and `s'` is
adjacent-swap reachable from `s`, then `v (tJConfigOf s) = v (tJConfigOf s')`. -/
theorem tJ_ground_amplitude_eq_of_reachable (τ J : ℝ) (hJ : 0 < J)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hv : v ∈ groundSubmoduleAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) (N + 1))
    {s s' : Fin (N + 1) → Fin 3} (hfull : ∀ k, s k ≠ 0) (hreach : AdjacentSwapReachable N s s') :
    v (tJConfigOf N s) = v (tJConfigOf N s') := by
  induction hreach with
  | refl => rfl
  | @tail b c hr hst ih =>
    -- `b` is reachable from the full `s`, so `b` is full (the empty-count is preserved)
    have hbfull : ∀ k, b k ≠ 0 := by
      intro k hk
      have hc0 := adjacentSwapReachable_count s b hr 0
      have : (Finset.univ.filter (fun j => b j = 0)).card = 0 := by
        rw [hc0]; exact Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr
          (fun j _ => hfull j))
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at this
      exact this (Finset.mem_univ k) hk
    exact ih.trans (tJ_ground_amplitude_eq_of_adjacentSwapStep τ J hJ hv hbfull hst)

/-- **Adjacent-swap reachability from equal value-counts, for all `N`.**  The `N = 0` case (a single
site) is degenerate: equal value-counts force the configs to be equal, so reachability is
reflexive. -/
theorem adjacentSwapReachable_of_same_counts_general (s s' : Fin (N + 1) → Fin 3)
    (hcount : ∀ v, (Finset.univ.filter (fun k => s k = v)).card
        = (Finset.univ.filter (fun k => s' k = v)).card) :
    AdjacentSwapReachable N s s' := by
  classical
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hss' : s = s' := by
      funext k
      have hc := hcount (s k)
      have hfull : (Finset.univ.filter (fun j => s j = s k)) = Finset.univ := by
        apply Finset.eq_univ_of_forall; intro j
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ j, by rw [Fin.ext (show j.val = k.val by omega)]⟩
      rw [hfull, Finset.card_univ, Fintype.card_fin] at hc
      have h1 : (Finset.univ.filter (fun j => s' j = s k)) = Finset.univ :=
        Finset.eq_univ_of_card _ (by rw [← hc, Fintype.card_fin])
      have hmem : k ∈ Finset.univ.filter (fun j => s' j = s k) := by
        rw [h1]; exact Finset.mem_univ _
      rw [Finset.mem_filter] at hmem
      exact hmem.2.symm
    rw [hss']
    exact Relation.ReflTransGen.refl
  · exact adjacentSwapReachable_of_same_counts hN s s' hcount

/-- **Half-filling ground amplitudes depend only on the up-count.**  For sector configs `t, t'`
with the same number of up-spins, `v (tJConfigOf t) = v (tJConfigOf t')`. -/
theorem tJ_ground_amplitude_eq_of_same_upCount (τ J : ℝ) (hJ : 0 < J)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hv : v ∈ groundSubmoduleAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) (N + 1))
    (t t' : TJFillingSector N (N + 1))
    (hup : (Finset.univ.filter (fun k => t.val k = 1)).card
        = (Finset.univ.filter (fun k => t'.val k = 1)).card) :
    v (tJConfigOf N t.val) = v (tJConfigOf N t'.val) := by
  classical
  have htfull := tJFillingSector_full t
  have ht'full := tJFillingSector_full t'
  -- equal value-counts for all three values `0, 1, 2`
  have h3' : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
  have hcount : ∀ w, (Finset.univ.filter (fun k => t.val k = w)).card
      = (Finset.univ.filter (fun k => t'.val k = w)).card := by
    intro w
    rcases h3' w with rfl | rfl | rfl
    · rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr (fun j _ => htfull j)),
        Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr (fun j _ => ht'full j))]
    · exact hup
    · have h1 := t.2
      have h2 := t'.2
      omega
  exact tJ_ground_amplitude_eq_of_reachable τ J hJ hv htfull
    (adjacentSwapReachable_of_same_counts_general t.val t'.val hcount)

end LatticeSystem.Fermion
