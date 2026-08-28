import LatticeSystem.Quantum.IsingChainMatrixElements

/-!
# The `2L`-dimensional low-energy basis of Tasaki Problem 3.3.a

Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Problem 3.3.a (statement p. 59,
solution pp. 498-501) studies the spin-`1/2` transverse-field Ising chain of eq. (3.3.1), p. 56,
`Ĥ = -Σ_x Ŝ_x^(3) Ŝ_{x+1}^(3) - λ Σ_x Ŝ_x^(1)`, on `L = N + 1` sites. With the convention
`σ̂^α = 2 Ŝ^α` of §2.1, eqs. (2.1.7)-(2.1.8), p. 15, that Hamiltonian is
`quantumIsingHamiltonian N (1/4) (λ/2)`, whose chain is **open**.

For small `λ` the problem describes the low-lying states inside the `2L`-dimensional space
spanned by the fully aligned configurations `|Φ↑⟩`, `|Φ↓⟩` and the single-domain-wall
configurations `|Φ_j^↑↓⟩`, `|Φ_j^↓↑⟩` (`j = 1, …, L - 1`). This module builds that basis and the
compression of `Ĥ` to it:

* `lowEnergyConfig` enumerates the `2L` configurations by a label in `ZMod (2 * (N + 1))`, and
  `lowEnergyConfig_natCast_le` / `lowEnergyConfig_natCast_add` identify the label ranges
  `0, …, L` and `L, …, 2L` with the book's two families;
* `lowEnergyConfig_injective` records that the `2L` labels really give `2L` distinct
  configurations, i.e. the dimension named in the problem statement;
* `lowEnergyConfig_succ_eq_siteFlipAt` and `lowEnergyConfig_ne_of_not_adjacent` describe how the
  labels sit with respect to the single-site flip `siteFlipAt` that `Ĥ` implements;
* `lowEnergyMatrix` is the `2L × 2L` array of matrix elements `⟨Φ_a|Ĥ|Φ_b⟩`, and
  `lowEnergyMatrix_eq_add_tightBindingRing` evaluates all of them at once: Tasaki eqs.
  (S.24)-(S.27) together with the sentence "all other matrix elements are vanishing" (p. 499).

**The ring is a ring of basis labels, not of lattice sites.** Advancing the label by one moves the
domain wall by one site, and after `2L` steps one returns to the starting configuration; that is
why the label type is `ZMod (2 * (N + 1))` and why (S.30) carries periodic boundary conditions.
The lattice itself stays open: its site type is `Fin (N + 1)`, the bond sum of
`quantumIsingHamiltonian` runs over `Fin N`, and the periodic `isingCycleHamiltonian` is a
different operator that never appears here. The two index types are never identified.

`lowEnergyMatrix` is the compression of `Ĥ` to the span of these `2L` configurations, and `Ĥ`
does not preserve that span, so its entries are matrix elements and nothing more: no entry, and
no eigenvalue of `lowEnergyMatrix`, is asserted to be an energy of `Ĥ`. Tasaki himself notes on
p. 59 that the perturbative analysis of this problem is not mathematically rigorous.

Two index conventions of the source are worth recording. Eq. (S.30) is printed "for any
`j = 1, …, 2L - 1`", but p. 500 derives (S.33) from it "with `j = 0` or `L`"; the honest reading,
used here, is the eigenvector equation of the `2L × 2L` matrix, i.e. all `j : ZMod (2 * (N + 1))`.
Likewise (S.25) is printed for `j = 1, …, L - 1` and (S.26) for `j = 1, …, L - 2`, while
`lowEnergyMatrix_eq_add_tightBindingRing` states every entry at once and so subsumes them.
-/

namespace LatticeSystem.Quantum

open Matrix

/-! ### Arithmetic of the `2L` label ring -/

/-- Two `if`-expressions with the same pair of distinct branches are equal exactly when their
conditions are equivalent. Used to compare two `lowEnergyConfig` values site by site. -/
private theorem ite_eq_ite_iff {α : Type*} {c d : α} (hcd : c ≠ d) {P Q : Prop}
    [Decidable P] [Decidable Q] :
    ((if P then c else d) = if Q then c else d) ↔ (P ↔ Q) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ, hcd, hcd.symm]

/-- A label equals the cast of a natural number below the ring order exactly when its `ZMod.val`
is that number. -/
private theorem labelRing_eq_iff_val (N : ℕ) (a : ZMod (2 * (N + 1))) (k : ℕ)
    (hk : k < 2 * (N + 1)) : a = (k : ZMod (2 * (N + 1))) ↔ a.val = k := by
  constructor
  · intro h; rw [h, ZMod.val_cast_of_lt hk]
  · intro h; rw [← ZMod.natCast_zmod_val a, h]

/-- The label ring has order `2L ≥ 2`, so the `ZMod.val` of its unit is `1`. -/
private theorem labelRing_val_one (N : ℕ) : (1 : ZMod (2 * (N + 1))).val = 1 := by
  have h : ((1 : ℕ) : ZMod (2 * (N + 1))) = 1 := Nat.cast_one
  rw [← h]
  exact ZMod.val_cast_of_lt (by omega)

/-- The half-turn label `L = N + 1` of the `2L` ring has `ZMod.val` equal to `N + 1`. -/
private theorem labelRing_val_half (N : ℕ) :
    ((N + 1 : ℕ) : ZMod (2 * (N + 1))).val = N + 1 :=
  ZMod.val_cast_of_lt (by omega)

/-- The half-turn label expressed through the ring's own numerals, so that ring normalisation can
combine it with the cast of `N`. -/
private theorem labelRing_natCast_half (N : ℕ) :
    ((N + 1 : ℕ) : ZMod (2 * (N + 1))) = ((N : ℕ) : ZMod (2 * (N + 1))) + 1 := by
  push_cast
  ring

/-- A label whose `ZMod.val` vanishes is the zero label. -/
private theorem labelRing_eq_zero_of_val (N : ℕ) {s : ZMod (2 * (N + 1))} (h : s.val = 0) :
    s = 0 := by
  rw [← ZMod.natCast_zmod_val s, h, Nat.cast_zero]

/-- A label lying in the second half of the ring, detected by a small positive shift that sends
it to zero: if `t + c = 0` with `0 < c ≤ L`, then `t.val` exceeds `N`. -/
private theorem labelRing_val_gt (N : ℕ) {t : ZMod (2 * (N + 1))} {c : ℕ} (hc0 : 0 < c)
    (hcN : c ≤ N + 1) (h : t + (c : ZMod (2 * (N + 1))) = 0) : ¬ t.val ≤ N := by
  intro hle
  have hcv : ((c : ℕ) : ZMod (2 * (N + 1))).val = c := ZMod.val_cast_of_lt (by omega)
  have hlt : t.val + ((c : ℕ) : ZMod (2 * (N + 1))).val < 2 * (N + 1) := by rw [hcv]; omega
  have h2 := ZMod.val_add_of_lt hlt
  rw [h, ZMod.val_zero, hcv] at h2
  omega

/-- Stepping a nonzero label back by one decrements its `ZMod.val`. -/
private theorem labelRing_val_sub_one (N : ℕ) {s : ZMod (2 * (N + 1))} (hs : s ≠ 0) :
    (s - 1).val + 1 = s.val := by
  have hsum : (s - 1) + 1 = s := by ring
  have hval := ZMod.val_add (s - 1) (1 : ZMod (2 * (N + 1)))
  rw [hsum, labelRing_val_one] at hval
  have hlt : (s - 1).val < 2 * (N + 1) := ZMod.val_lt _
  rcases Nat.lt_or_ge ((s - 1).val + 1) (2 * (N + 1)) with h | h
  · rw [Nat.mod_eq_of_lt h] at hval; omega
  · have he : (s - 1).val + 1 = 2 * (N + 1) := by omega
    rw [he, Nat.mod_self] at hval
    exact absurd (labelRing_eq_zero_of_val N hval) hs

/-- The half-turn `r ↦ r + L` of the label ring swaps its two halves: exactly one of `r` and
`r + L` has `ZMod.val` at most `N`. This is the antipodal symmetry behind the `↑↓`/`↓↑` mirror
pair of families. -/
private theorem labelRing_val_add_half_le (N : ℕ) (r : ZMod (2 * (N + 1))) :
    ((r + ((N + 1 : ℕ) : ZMod (2 * (N + 1)))).val ≤ N) ↔ ¬ r.val ≤ N := by
  have hv := ZMod.val_add r ((N + 1 : ℕ) : ZMod (2 * (N + 1)))
  rw [labelRing_val_half] at hv
  have hr : r.val < 2 * (N + 1) := ZMod.val_lt _
  rcases Nat.lt_or_ge r.val (N + 1) with h | h
  · rw [Nat.mod_eq_of_lt (by omega)] at hv; omega
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
    have hsplit : r.val + (N + 1) = 2 * (N + 1) + k := by omega
    rw [hsplit, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hv
    omega

/-! ### The `2L` low-energy configurations -/

/-- The `2L` low-energy configurations of Tasaki Problem 3.3.a, indexed by a label in the ring
`ZMod (2 * (N + 1))`: site `x` of `lowEnergyConfig N j` is up (`Fin 2` value `0`) exactly when the
label `j` lies in the arc `x + 1, …, x + L`.

Following the label around the ring sweeps the domain wall once across the chain in each of the
two orientations, so the labels `0, …, L` give `|Φ↓⟩`, `|Φ_1^↑↓⟩`, …, `|Φ_{L-1}^↑↓⟩`, `|Φ↑⟩` and
the labels `L, …, 2L` give the mirror family `|Φ↑⟩`, `|Φ_1^↓↑⟩`, …, `|Φ_{L-1}^↓↑⟩`, `|Φ↓⟩`
(`lowEnergyConfig_natCast_le`, `lowEnergyConfig_natCast_add`). The ring indexes labels; the chain
of sites `Fin (N + 1)` stays open. -/
def lowEnergyConfig (N : ℕ) : ZMod (2 * (N + 1)) → (Fin (N + 1) → Fin 2) :=
  fun j x => if (j - (x.val : ZMod (2 * (N + 1))) - 1).val ≤ N then 0 else 1

/-- The unique site at which `lowEnergyConfig N a` and `lowEnergyConfig N (a + 1)` differ: the
domain wall of the label `a`, obtained by folding the label ring onto the chain of sites. -/
def wallSite (N : ℕ) (a : ZMod (2 * (N + 1))) : Fin (N + 1) :=
  ⟨a.val % (N + 1), Nat.mod_lt _ (Nat.succ_pos N)⟩

/-- Folding the label ring onto the sites: `a` differs from the cast of `wallSite N a` by either
`0` or the half-turn `L`. -/
private theorem sub_wallSite (N : ℕ) (a : ZMod (2 * (N + 1))) :
    a - ((wallSite N a).val : ZMod (2 * (N + 1))) = 0
      ∨ a - ((wallSite N a).val : ZMod (2 * (N + 1)))
          = ((N + 1 : ℕ) : ZMod (2 * (N + 1))) := by
  have hlt : a.val < 2 * (N + 1) := ZMod.val_lt _
  rcases Nat.lt_or_ge a.val (N + 1) with h | h
  · left
    have hval : ((wallSite N a).val : ℕ) = a.val := Nat.mod_eq_of_lt h
    rw [hval, ZMod.natCast_zmod_val, sub_self]
  · right
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
    have hval : ((wallSite N a).val : ℕ) = k := by
      change a.val % (N + 1) = k
      rw [hk, Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (by omega)
    have ha : a = ((N + 1 + k : ℕ) : ZMod (2 * (N + 1))) :=
      (labelRing_eq_iff_val N a (N + 1 + k) (by omega)).mpr (by omega)
    rw [hval, ha]
    push_cast
    ring

/-- Uniqueness of the fold: any site whose cast differs from `a` by `0` or by the half-turn `L`
is `wallSite N a`. -/
private theorem eq_wallSite (N : ℕ) (a : ZMod (2 * (N + 1))) (x : Fin (N + 1))
    (h : a - (x.val : ZMod (2 * (N + 1))) = 0
      ∨ a - (x.val : ZMod (2 * (N + 1))) = ((N + 1 : ℕ) : ZMod (2 * (N + 1)))) :
    x = wallSite N a := by
  have hx : x.val < N + 1 := x.is_lt
  refine Fin.ext ?_
  change x.val = a.val % (N + 1)
  rcases h with h | h
  · rw [sub_eq_zero] at h
    rw [h, ZMod.val_cast_of_lt (by omega : x.val < 2 * (N + 1)), Nat.mod_eq_of_lt hx]
  · have ha : a = ((N + 1 + x.val : ℕ) : ZMod (2 * (N + 1))) := by
      push_cast at h ⊢
      linear_combination h
    rw [ha, ZMod.val_cast_of_lt (by omega : N + 1 + x.val < 2 * (N + 1)), Nat.add_mod_left,
      Nat.mod_eq_of_lt hx]

/-- **(B3)** Book form of the first family, Tasaki's `|Φ↓⟩`, `|Φ_j^↑↓⟩` and `|Φ↑⟩`: at the label
`j ≤ L` cast from `ℕ`, site `x` is up exactly when `x.val < j`. The label `0` gives the all-down
`|Φ↓⟩`, the label `L` the all-up `|Φ↑⟩`, and `0 < j < L` the domain-wall state `|Φ_j^↑↓⟩`. -/
theorem lowEnergyConfig_natCast_le (N j : ℕ) (hj : j ≤ N + 1) :
    lowEnergyConfig N (j : ZMod (2 * (N + 1)))
      = fun x => if x.val < j then (0 : Fin 2) else 1 := by
  funext x
  have hx : x.val < N + 1 := x.is_lt
  simp only [lowEnergyConfig]
  by_cases h : x.val < j
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h
    have hcast : (j : ZMod (2 * (N + 1))) - (x.val : ZMod (2 * (N + 1))) - 1
        = ((k : ℕ) : ZMod (2 * (N + 1))) := by rw [hk]; push_cast; ring
    have hv : (((k : ℕ) : ZMod (2 * (N + 1)))).val = k := ZMod.val_cast_of_lt (by omega)
    rw [hcast, if_pos (by rw [hv]; omega), if_pos h]
  · have h' : j ≤ x.val := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h'
    have hz : ((j : ZMod (2 * (N + 1))) - (x.val : ZMod (2 * (N + 1))) - 1)
        + ((k + 1 : ℕ) : ZMod (2 * (N + 1))) = 0 := by rw [hk]; push_cast; ring
    rw [if_neg (labelRing_val_gt N (c := k + 1) (by omega) (by omega) hz), if_neg h]

/-- **(B4)** Book form of the second family, Tasaki's mirror states `|Φ_m^↓↑⟩`: at the label
`L + m` (`0 ≤ m ≤ L`) cast from `ℕ`, site `x` is down exactly when `x.val < m`. Parametrizing by
`m` rather than by `j - L` keeps `ℕ`-subtraction out of the statement. -/
theorem lowEnergyConfig_natCast_add (N m : ℕ) (hm : m ≤ N + 1) :
    lowEnergyConfig N (((N + 1) + m : ℕ) : ZMod (2 * (N + 1)))
      = fun x => if x.val < m then (1 : Fin 2) else 0 := by
  funext x
  have hx : x.val < N + 1 := x.is_lt
  simp only [lowEnergyConfig]
  by_cases h : x.val < m
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h
    have hcast : (((N + 1) + m : ℕ) : ZMod (2 * (N + 1)))
        - (x.val : ZMod (2 * (N + 1))) - 1 = ((N + 1 + k : ℕ) : ZMod (2 * (N + 1))) := by
      rw [hk]; push_cast; ring
    have hv : (((N + 1 + k : ℕ) : ZMod (2 * (N + 1)))).val = N + 1 + k :=
      ZMod.val_cast_of_lt (by omega)
    rw [hcast, if_neg (by rw [hv]; omega), if_pos h]
  · have h' : m ≤ x.val := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h'
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le (by omega : k ≤ N)
    have hNc : ((N : ℕ) : ZMod (2 * (N + 1))) = ((k : ℕ) : ZMod (2 * (N + 1)))
        + ((n : ℕ) : ZMod (2 * (N + 1))) := by
      rw [← Nat.cast_add]
      exact congrArg _ hn
    have hcast : (((N + 1) + m : ℕ) : ZMod (2 * (N + 1)))
        - (x.val : ZMod (2 * (N + 1))) - 1 = ((n : ℕ) : ZMod (2 * (N + 1))) := by
      rw [hk]; push_cast; linear_combination hNc
    have hv : (((n : ℕ) : ZMod (2 * (N + 1)))).val = n := ZMod.val_cast_of_lt (by omega)
    rw [hcast, if_pos (by rw [hv]; omega), if_neg h]

/-- **(B5)** The `2L` labels give `2L` pairwise distinct configurations, so the low-energy space
of Tasaki Problem 3.3.a really has the dimension `2L` named in the statement.

Equality of two configurations forces the indicator of the first half of the label ring to be
invariant under the shift by `b - a`; testing that invariance at the labels `0` and `L - 1`
forces the shift to vanish. -/
theorem lowEnergyConfig_injective (N : ℕ) : Function.Injective (lowEnergyConfig N) := by
  intro a b hab
  have hstep : ∀ x : Fin (N + 1),
      ((a - (x.val : ZMod (2 * (N + 1))) - 1).val ≤ N
        ↔ (b - (x.val : ZMod (2 * (N + 1))) - 1).val ≤ N) := by
    intro x
    have h := congrFun hab x
    simp only [lowEnergyConfig] at h
    exact (ite_eq_ite_iff (by decide : (0 : Fin 2) ≠ 1)).mp h
  have hper : ∀ t : ZMod (2 * (N + 1)), (t.val ≤ N ↔ (t + (b - a)).val ≤ N) := by
    intro t
    obtain ⟨x, hx⟩ : ∃ x : Fin (N + 1), x = wallSite N (a - 1 - t) := ⟨_, rfl⟩
    have hw := sub_wallSite N (a - 1 - t)
    rw [← hx] at hw
    have hs := hstep x
    rcases hw with hw | hw
    · have h1 : a - ((x.val : ℕ) : ZMod (2 * (N + 1))) - 1 = t := by linear_combination hw
      have h2 : b - ((x.val : ℕ) : ZMod (2 * (N + 1))) - 1 = t + (b - a) := by
        linear_combination hw
      rw [h1, h2] at hs
      exact hs
    · have h1 : a - ((x.val : ℕ) : ZMod (2 * (N + 1))) - 1
          = t + ((N + 1 : ℕ) : ZMod (2 * (N + 1))) := by linear_combination hw
      have h2 : b - ((x.val : ℕ) : ZMod (2 * (N + 1))) - 1
          = (t + (b - a)) + ((N + 1 : ℕ) : ZMod (2 * (N + 1))) := by linear_combination hw
      rw [h1, h2, labelRing_val_add_half_le, labelRing_val_add_half_le] at hs
      exact not_iff_not.mp hs
  have hcastN : (((N : ℕ) : ZMod (2 * (N + 1)))).val = N := ZMod.val_cast_of_lt (by omega)
  have h0 := hper 0
  rw [ZMod.val_zero, zero_add] at h0
  have hba : (b - a).val ≤ N := h0.mp (Nat.zero_le N)
  have hN' := hper ((N : ℕ) : ZMod (2 * (N + 1)))
  have hsum : ((((N : ℕ) : ZMod (2 * (N + 1)))) + (b - a)).val = N + (b - a).val := by
    rw [ZMod.val_add_of_lt (by rw [hcastN]; omega), hcastN]
  rw [hcastN, hsum] at hN'
  have hzero : (b - a).val = 0 := by
    have := hN'.mp (le_refl N)
    omega
  have hsub := labelRing_eq_zero_of_val N hzero
  rw [sub_eq_zero] at hsub
  exact hsub.symm

end LatticeSystem.Quantum
