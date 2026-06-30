import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveKineticEntry
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveKineticHermitian
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractive
import LatticeSystem.Quantum.MarshallLiebMattis.EqMagnetizationReachable

/-!
# Connectivity of the fixed-count kinetic support graph (Tasaki §10.2.4)

Layer PR40d toward discharging `theorem_10_2_lieb_attractive_unique_singlet`. The Lieb
spin-reflection-positivity dichotomy (`posDef_or_eq_zero_of_connected_support`, the abstract
Lemma 10.10) needs a **connected** support graph for the up-kinetic matrix
`A = hubbardBlockKineticUpFixedMatrix`. Because `A` conserves the up-particle count, its support
graph on the full configuration space is disconnected; the relevant block lives on the fixed-count
sector `{u // Σ_x u_x = k}`.

This module builds, for a connected hopping graph `hoppingSupportGraph T` (Tasaki's "`Λ` connected
through nonvanishing `t_{x,y}`"), the **sector kinetic graph** and proves it is `Preconnected`.
Connectivity is inherited from the configuration-swap connectivity
`swapReachable_of_eq_magnetization`: two equal-count configurations have equal magnetization, hence
are linked by single-hop swaps along hopping edges, and PR40c
(`hubbardBlockKineticUpFixedMatrix_apply_hop_ne`) turns each swap into a nonzero kinetic entry.

## Main results

* `hubbardKineticSectorGraph` — the sector support graph (both off-diagonal entries nonzero).
* `hubbardKineticSectorGraph_preconnected` — it is preconnected when the hopping graph is.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4 (Lemma 10.10), pp. 363–367.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-! ## The fixed up-count sector -/

/-- The fixed up-particle-count sector of Hubbard up-configurations: configurations carrying
exactly `k` up electrons (`Σ_x u_x = k`). -/
abbrev hubbardSpinCountSector (N : ℕ) (k : ℕ) : Type :=
  {u : hubbardSpinConfig N // (∑ x : Fin (N + 1), (u x).val) = k}

/-- The integer magnetization in terms of the up-count: `|u| = |Λ| − 2·Σ_x u_x`. -/
theorem magnetization_eq_card_sub_two_mul (u : hubbardSpinConfig N) :
    magnetization (Fin (N + 1)) u
      = (N + 1 : ℤ) - 2 * ∑ x : Fin (N + 1), ((u x).val : ℤ) := by
  have hsign : ∀ s : Fin 2, (spinSign s : ℤ) = 1 - 2 * (s.val : ℤ) := by
    decide
  unfold magnetization
  simp_rw [hsign]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Finset.mul_sum]
  ring

/-- Two equal-count configurations have equal magnetization. -/
theorem magnetization_eq_of_sumVal_eq {u v : hubbardSpinConfig N}
    (h : (∑ x : Fin (N + 1), (u x).val) = ∑ x : Fin (N + 1), (v x).val) :
    magnetization (Fin (N + 1)) u = magnetization (Fin (N + 1)) v := by
  rw [magnetization_eq_card_sub_two_mul, magnetization_eq_card_sub_two_mul]
  have : (∑ x : Fin (N + 1), ((u x).val : ℤ)) = ∑ x : Fin (N + 1), ((v x).val : ℤ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum, h]
  rw [this]

/-- A `basisSwap` preserves the up-count (the swap permutes occupation values). -/
theorem sumVal_basisSwap (σ : hubbardSpinConfig N) (x y : Fin (N + 1)) :
    (∑ z : Fin (N + 1), (basisSwap σ x y z).val) = ∑ z : Fin (N + 1), (σ z).val := by
  have h := magnetization_basisSwap σ x y
  rw [magnetization_eq_card_sub_two_mul, magnetization_eq_card_sub_two_mul] at h
  have h2 : (∑ z : Fin (N + 1), ((basisSwap σ x y z).val : ℤ))
      = ∑ z : Fin (N + 1), ((σ z).val : ℤ) := by linarith
  exact_mod_cast h2

/-! ## The sector kinetic support graph -/

/-- The kinetic support graph on the fixed up-count sector `k`: two sector configurations are
adjacent when **both** off-diagonal kinetic matrix entries between them are nonzero. The symmetric
two-sided definition makes the graph directly usable as the connected support hypothesis of the
abstract Lemma 10.10 (`posDef_or_eq_zero_of_connected_support`). -/
def hubbardKineticSectorGraph (N : ℕ) (T : Fin (N + 1) → Fin (N + 1) → ℂ) (k : ℕ) :
    SimpleGraph (hubbardSpinCountSector N k) where
  Adj p q := hubbardBlockKineticUpFixedMatrix N T p.val q.val ≠ 0 ∧
      hubbardBlockKineticUpFixedMatrix N T q.val p.val ≠ 0 ∧ p ≠ q
  symm := fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩
  loopless := ⟨fun _ h => h.2.2 rfl⟩

/-- Every sector-graph edge witnesses a nonzero kinetic entry — the `hGadj` input of the abstract
Lemma 10.10. -/
theorem hubbardKineticSectorGraph_adj_entry_ne {T : Fin (N + 1) → Fin (N + 1) → ℂ} {k : ℕ}
    {p q : hubbardSpinCountSector N k} (h : (hubbardKineticSectorGraph N T k).Adj p q) :
    hubbardBlockKineticUpFixedMatrix N T p.val q.val ≠ 0 := h.1

/-- `basisSwap` is symmetric in its two sites. -/
private theorem basisSwap_comm (σ : hubbardSpinConfig N) (x y : Fin (N + 1)) :
    basisSwap σ x y = basisSwap σ y x := by
  by_cases hxy : x = y
  · rw [hxy]
  · unfold basisSwap
    exact Function.update_comm hxy (σ y) (σ x) σ

/-- A single hopping-edge swap with the source occupied (`σ x = 1`, `σ y = 0`) gives a sector-graph
edge. Both kinetic entries are nonzero: the forward one by PR40c
(`hubbardBlockKineticUpFixedMatrix_apply_hop_ne`), the reverse one by Hermiticity. -/
private theorem sectorGraph_adj_of_hop {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hT_symm : ∀ x y, T x y = T y x) {k : ℕ} {σ : hubbardSpinConfig N} {x y : Fin (N + 1)}
    (hxy : x ≠ y) (hTxy : T x y ≠ 0) (hx1 : σ x = 1) (hy0 : σ y = 0)
    (hσ : (∑ z : Fin (N + 1), (σ z).val) = k)
    (hswap : (∑ z : Fin (N + 1), (basisSwap σ x y z).val) = k) :
    (hubbardKineticSectorGraph N (fun a b => (T a b : ℂ)) k).Adj
      ⟨σ, hσ⟩ ⟨basisSwap σ x y, hswap⟩ := by
  set Tℂ : Fin (N + 1) → Fin (N + 1) → ℂ := fun a b => (T a b : ℂ) with hTℂ
  set A := hubbardBlockKineticUpFixedMatrix N Tℂ with hAdef
  -- `basisSwap σ x y` is the hop `x → y` (empty the source `x`, fill the target `y`).
  have hhop : basisSwap σ x y = hubbardSpinHopConfig N σ x y := by
    unfold basisSwap hubbardSpinHopConfig
    rw [hy0, hx1]
  -- forward entry `A (hop) σ ≠ 0` by PR40c (source `x` occupied, target `y` empty).
  have hfwd : A (basisSwap σ x y) σ ≠ 0 := by
    rw [hhop]
    have hTℂyx : Tℂ y x ≠ 0 := by simp only [hTℂ]; exact_mod_cast (hT_symm x y ▸ hTxy)
    exact hubbardBlockKineticUpFixedMatrix_apply_hop_ne (T := Tℂ) σ y x hx1 hy0 hxy.symm hTℂyx
  -- Hermiticity of `A` (`Tℂ` is real-symmetric).
  have hA : A.IsHermitian := by
    refine hubbardBlockKineticUpFixedMatrix_isHermitian N (fun a b => ?_)
    simp only [hTℂ, ← starRingEnd_apply, Complex.conj_ofReal]
    exact_mod_cast hT_symm a b
  -- reverse entry `A σ (hop) ≠ 0` from Hermiticity.
  have hrev : A σ (basisSwap σ x y) ≠ 0 := by
    rw [← hA.apply σ (basisSwap σ x y)]
    exact star_ne_zero.mpr hfwd
  -- the two configurations differ (the swap changes the value at `x`).
  have hne : (⟨σ, hσ⟩ : hubbardSpinCountSector N k) ≠ ⟨basisSwap σ x y, hswap⟩ := by
    intro hEq
    have hval : σ x = basisSwap σ x y x := congrArg (fun w => w.val x) hEq
    simp only [basisSwap, Function.update_of_ne hxy, Function.update_self] at hval
    rw [hx1, hy0] at hval
    exact absurd hval (by decide)
  exact ⟨hrev, hfwd, hne⟩

/-- Lift a full-configuration `SwapReachable` chain along the connected hopping graph to a
`Reachable` chain inside the fixed up-count sector graph. -/
theorem hubbardKineticSectorGraph_reachable_of_swapReachable
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hT_symm : ∀ x y, T x y = T y x) {k : ℕ}
    (p : hubbardSpinCountSector N k) {ξ : hubbardSpinConfig N}
    (hreach : SwapReachable (hoppingSupportGraph T) p.val ξ) :
    ∃ hξ : (∑ x : Fin (N + 1), (ξ x).val) = k,
      (hubbardKineticSectorGraph N (fun a b => (T a b : ℂ)) k).Reachable p ⟨ξ, hξ⟩ := by
  induction hreach with
  | refl => exact ⟨p.property, SimpleGraph.Reachable.refl _⟩
  | @tail ξmid ξcurr _ hstep ih =>
    obtain ⟨hmid, hreach_mid⟩ := ih
    obtain ⟨x, y, hadj, hxyval, hξcurr⟩ := hstep
    have hxy : x ≠ y := (hoppingSupportGraph T).ne_of_adj hadj
    -- The hopping edge gives a nonzero (symmetric) coupling.
    have hTedge : T x y ≠ 0 ∨ T y x ≠ 0 := ((SimpleGraph.fromRel_adj _ x y).mp hadj).2
    have hcurr : (∑ z : Fin (N + 1), (ξcurr z).val) = k := by
      rw [hξcurr, sumVal_basisSwap]; exact hmid
    subst hξcurr
    refine ⟨hcurr, hreach_mid.trans (SimpleGraph.Adj.reachable ?_)⟩
    -- Orient the swap so the source carries an up electron.
    have key : (ξmid x = 0 ∧ ξmid y = 1) ∨ (ξmid x = 1 ∧ ξmid y = 0) := by
      have h0 : ∀ s : Fin 2, s = 0 ∨ s = 1 := by decide
      rcases h0 (ξmid x) with hx | hx <;> rcases h0 (ξmid y) with hy | hy
      · exact absurd (hx.trans hy.symm) hxyval
      · exact Or.inl ⟨hx, hy⟩
      · exact Or.inr ⟨hx, hy⟩
      · exact absurd (hx.trans hy.symm) hxyval
    rcases key with ⟨hx0, hy1⟩ | ⟨hx1, hy0⟩
    · -- source at `y` (occupied), target at `x`: orient via `(y, x)`.
      have hTyx : T y x ≠ 0 := by
        rcases hTedge with h | h
        · exact hT_symm x y ▸ h
        · exact h
      have hcomm : basisSwap ξmid x y = basisSwap ξmid y x := basisSwap_comm ξmid x y
      have hcurr' : (∑ z : Fin (N + 1), (basisSwap ξmid y x z).val) = k := by
        rw [← hcomm]; exact hcurr
      have hedge := sectorGraph_adj_of_hop hT_symm (Ne.symm hxy) hTyx hy1 hx0 hmid hcurr'
      have hsub : (⟨basisSwap ξmid x y, hcurr⟩ : hubbardSpinCountSector N k)
          = ⟨basisSwap ξmid y x, hcurr'⟩ := Subtype.ext hcomm
      rw [hsub]; exact hedge
    · -- source at `x` (occupied), target at `y`: direct orientation.
      have hTxy : T x y ≠ 0 := by
        rcases hTedge with h | h
        · exact h
        · exact hT_symm x y ▸ h
      exact sectorGraph_adj_of_hop hT_symm hxy hTxy hx1 hy0 hmid hcurr

/-- **The fixed up-count kinetic support graph is preconnected** whenever the hopping graph is.
Two equal-count configurations have equal magnetization, so they are linked by configuration swaps
along hopping edges (`swapReachable_of_eq_magnetization`); each swap is a sector-graph edge by
`sectorGraph_adj_of_hop`. This supplies the connected-support hypothesis of the abstract
Lemma 10.10 (`posDef_or_eq_zero_of_connected_support`). -/
theorem hubbardKineticSectorGraph_preconnected
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hT_symm : ∀ x y, T x y = T y x) {k : ℕ}
    (hT_conn : (hoppingSupportGraph T).Preconnected) :
    (hubbardKineticSectorGraph N (fun a b => (T a b : ℂ)) k).Preconnected := by
  intro p q
  have hmag : magnetization (Fin (N + 1)) p.val = magnetization (Fin (N + 1)) q.val :=
    magnetization_eq_of_sumVal_eq (p.property.trans q.property.symm)
  have hreach : SwapReachable (hoppingSupportGraph T) p.val q.val :=
    swapReachable_of_eq_magnetization hT_conn p.val q.val hmag
  obtain ⟨hξ, hR⟩ := hubbardKineticSectorGraph_reachable_of_swapReachable hT_symm p hreach
  have hq : (⟨q.val, hξ⟩ : hubbardSpinCountSector N k) = q := Subtype.ext rfl
  rwa [hq] at hR

end LatticeSystem.Fermion
