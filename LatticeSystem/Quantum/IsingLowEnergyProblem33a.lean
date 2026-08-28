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
  rw [hsum, ZMod.val_one'' (by omega : 2 * (N + 1) ≠ 1)] at hval
  have hlt : (s - 1).val < 2 * (N + 1) := ZMod.val_lt _
  rcases Nat.lt_or_ge ((s - 1).val + 1) (2 * (N + 1)) with h | h
  · rw [Nat.mod_eq_of_lt h] at hval; omega
  · have he : (s - 1).val + 1 = 2 * (N + 1) := by omega
    rw [he, Nat.mod_self] at hval
    exact absurd ((ZMod.val_eq_zero _).mp hval) hs

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
  have hsub := (ZMod.val_eq_zero _).mp hzero
  rw [sub_eq_zero] at hsub
  exact hsub.symm

/-- **(B6)** Advancing the label by one step is exactly a single-site flip at the domain wall
`wallSite N a`. This is what makes the neighbouring entries of `lowEnergyMatrix` readable off
`quantumIsingHamiltonian_apply_siteFlip`. It holds for every `N`, the one-site chain `L = 1`
included, where the two ring neighbours `a + 1` and `a - 1` of a label coincide. -/
theorem lowEnergyConfig_succ_eq_siteFlipAt (N : ℕ) (a : ZMod (2 * (N + 1))) :
    lowEnergyConfig N (a + 1) = siteFlipAt (lowEnergyConfig N a) (wallSite N a) := by
  funext x
  by_cases hx : x = wallSite N a
  · rw [hx, siteFlipAt_self]
    simp only [lowEnergyConfig]
    rcases sub_wallSite N a with hw | hw
    · have h1 : a + 1 - (((wallSite N a).val : ℕ) : ZMod (2 * (N + 1))) - 1 = 0 := by
        linear_combination hw
      have h2 : a - (((wallSite N a).val : ℕ) : ZMod (2 * (N + 1))) - 1 = -1 := by
        linear_combination hw
      have hneg : ((-1 : ZMod (2 * (N + 1))) + ((1 : ℕ) : ZMod (2 * (N + 1)))) = 0 := by
        push_cast; ring
      rw [h1, h2, if_pos (by rw [ZMod.val_zero]; omega),
        if_neg (labelRing_val_gt N (c := 1) (by omega) (by omega) hneg)]
      decide
    · have h1 : a + 1 - (((wallSite N a).val : ℕ) : ZMod (2 * (N + 1))) - 1
          = ((N + 1 : ℕ) : ZMod (2 * (N + 1))) := by linear_combination hw
      have h2 : a - (((wallSite N a).val : ℕ) : ZMod (2 * (N + 1))) - 1
          = ((N : ℕ) : ZMod (2 * (N + 1))) := by
        linear_combination hw + labelRing_natCast_half N
      have hvN : (((N : ℕ) : ZMod (2 * (N + 1)))).val = N := ZMod.val_cast_of_lt (by omega)
      rw [h1, h2, if_neg (by rw [labelRing_val_half]; omega), if_pos (by rw [hvN])]
      decide
  · rw [siteFlipAt_of_ne _ hx]
    simp only [lowEnergyConfig]
    refine if_congr ?_ rfl rfl
    have hne : ¬ (a - ((x.val : ℕ) : ZMod (2 * (N + 1))) = 0
        ∨ a - ((x.val : ℕ) : ZMod (2 * (N + 1))) = ((N + 1 : ℕ) : ZMod (2 * (N + 1)))) :=
      fun h => hx (eq_wallSite N a x h)
    have hne0 : a - ((x.val : ℕ) : ZMod (2 * (N + 1))) ≠ 0 := fun h => hne (Or.inl h)
    have hneL : a - ((x.val : ℕ) : ZMod (2 * (N + 1)))
        ≠ ((N + 1 : ℕ) : ZMod (2 * (N + 1))) := fun h => hne (Or.inr h)
    have hstep : a + 1 - ((x.val : ℕ) : ZMod (2 * (N + 1))) - 1
        = a - ((x.val : ℕ) : ZMod (2 * (N + 1))) := by ring
    rw [hstep]
    have hval := labelRing_val_sub_one N hne0
    have hnv : (a - ((x.val : ℕ) : ZMod (2 * (N + 1)))).val ≠ N + 1 := fun hc =>
      hneL ((labelRing_eq_iff_val N _ (N + 1) (by omega)).mpr hc)
    have hpos : 0 < (a - ((x.val : ℕ) : ZMod (2 * (N + 1)))).val := by
      rcases Nat.eq_zero_or_pos (a - ((x.val : ℕ) : ZMod (2 * (N + 1)))).val with hc | hc
      · exact absurd ((ZMod.val_eq_zero _).mp hc) hne0
      · exact hc
    omega

/-- The two domain walls attached to `a` and `a + 1` are distinct sites, which is where `1 ≤ N`
(that is, `L ≥ 2`) enters: on a two-label ring the two walls would coincide. -/
private theorem wallSite_succ_ne (N : ℕ) (hN : 1 ≤ N) (a : ZMod (2 * (N + 1))) :
    wallSite N a ≠ wallSite N (a + 1) := by
  intro hcon
  have hu : (a - (((wallSite N a).val : ℕ) : ZMod (2 * (N + 1)))).val = 0
      ∨ (a - (((wallSite N a).val : ℕ) : ZMod (2 * (N + 1)))).val = N + 1 := by
    rcases sub_wallSite N a with hw | hw
    · exact Or.inl (by rw [hw, ZMod.val_zero])
    · exact Or.inr (by rw [hw, labelRing_val_half])
  have hstep : a + 1 - (((wallSite N a).val : ℕ) : ZMod (2 * (N + 1)))
      = (a - (((wallSite N a).val : ℕ) : ZMod (2 * (N + 1)))) + 1 := by ring
  have hu1 : ((a - (((wallSite N a).val : ℕ) : ZMod (2 * (N + 1)))) + 1).val = 0
      ∨ ((a - (((wallSite N a).val : ℕ) : ZMod (2 * (N + 1)))) + 1).val = N + 1 := by
    rw [← hstep, hcon]
    rcases sub_wallSite N (a + 1) with hw | hw
    · exact Or.inl (by rw [hw, ZMod.val_zero])
    · exact Or.inr (by rw [hw, labelRing_val_half])
  have hva := ZMod.val_add (a - (((wallSite N a).val : ℕ) : ZMod (2 * (N + 1))))
    (1 : ZMod (2 * (N + 1)))
  rw [ZMod.val_one'' (by omega : 2 * (N + 1) ≠ 1)] at hva
  rcases hu with hu | hu <;> rw [hu, Nat.mod_eq_of_lt (by omega)] at hva <;>
    rcases hu1 with hu1 | hu1 <;> omega

/-- Two sites at which the configurations of two labels at ring distance between `2` and `L`
differ: the domain walls of `a` and of `a + 1`. Both ends of the distance range matter — at
distance `1` the two configurations differ at a single site only. -/
private theorem lowEnergyConfig_two_ne (N : ℕ) (hN : 1 ≤ N) {a b : ZMod (2 * (N + 1))}
    (h2 : 2 ≤ (b - a).val) (hL : (b - a).val ≤ N + 1) :
    ∃ x y : Fin (N + 1), x ≠ y
      ∧ lowEnergyConfig N b x ≠ lowEnergyConfig N a x
      ∧ lowEnergyConfig N b y ≠ lowEnergyConfig N a y := by
  have hone : b - a ≠ 0 := by
    intro h
    rw [h, ZMod.val_zero] at h2
    omega
  have hv1 : (b - a - 1).val + 1 = (b - a).val := labelRing_val_sub_one N hone
  have hone' : b - a - 1 ≠ 0 := by
    intro h
    rw [h, ZMod.val_zero] at hv1
    omega
  have hv2 : (b - a - 1 - 1).val + 1 = (b - a - 1).val := labelRing_val_sub_one N hone'
  have hvN : (((N : ℕ) : ZMod (2 * (N + 1)))).val = N := ZMod.val_cast_of_lt (by omega)
  refine ⟨wallSite N a, wallSite N (a + 1), wallSite_succ_ne N hN a, ?_, ?_⟩
  · simp only [lowEnergyConfig]
    rw [ne_eq, ite_eq_ite_iff (by decide : (0 : Fin 2) ≠ 1)]
    rcases sub_wallSite N a with hw | hw
    · have h1 : a - (((wallSite N a).val : ℕ) : ZMod (2 * (N + 1))) - 1 = -1 := by
        linear_combination hw
      have h3 : b - (((wallSite N a).val : ℕ) : ZMod (2 * (N + 1))) - 1 = b - a - 1 := by
        linear_combination hw
      have hneg : ((-1 : ZMod (2 * (N + 1))) + ((1 : ℕ) : ZMod (2 * (N + 1)))) = 0 := by
        push_cast; ring
      rw [h1, h3]
      exact fun hc => labelRing_val_gt N (c := 1) (by omega) (by omega) hneg (hc.mp (by omega))
    · have h1 : a - (((wallSite N a).val : ℕ) : ZMod (2 * (N + 1))) - 1
          = ((N : ℕ) : ZMod (2 * (N + 1))) := by
        linear_combination hw + labelRing_natCast_half N
      have h3 : b - (((wallSite N a).val : ℕ) : ZMod (2 * (N + 1))) - 1
          = (b - a - 1) + ((N + 1 : ℕ) : ZMod (2 * (N + 1))) := by linear_combination hw
      rw [h1, h3, labelRing_val_add_half_le, hvN]
      exact fun hc => (hc.mpr (le_refl N)) (by omega)
  · obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hN
    have hvn : (((n : ℕ) : ZMod (2 * (N + 1)))).val = n := ZMod.val_cast_of_lt (by omega)
    simp only [lowEnergyConfig]
    rw [ne_eq, ite_eq_ite_iff (by decide : (0 : Fin 2) ≠ 1)]
    rcases sub_wallSite N (a + 1) with hw | hw
    · have h1 : a - (((wallSite N (a + 1)).val : ℕ) : ZMod (2 * (N + 1))) - 1 = -1 - 1 := by
        linear_combination hw
      have h3 : b - (((wallSite N (a + 1)).val : ℕ) : ZMod (2 * (N + 1))) - 1
          = b - a - 1 - 1 := by linear_combination hw
      have hneg : (((-1 : ZMod (2 * (N + 1))) - 1) + ((2 : ℕ) : ZMod (2 * (N + 1)))) = 0 := by
        push_cast; ring
      rw [h1, h3]
      exact fun hc => labelRing_val_gt N (c := 2) (by omega) (by omega) hneg (hc.mp (by omega))
    · have hcast2 : ((N + 1 : ℕ) : ZMod (2 * (N + 1)))
          = ((n : ℕ) : ZMod (2 * (N + 1))) + 2 := by
        rw [show N + 1 = n + 2 by omega]
        push_cast
        ring
      have h1 : a - (((wallSite N (a + 1)).val : ℕ) : ZMod (2 * (N + 1))) - 1
          = ((n : ℕ) : ZMod (2 * (N + 1))) := by linear_combination hw + hcast2
      have h3 : b - (((wallSite N (a + 1)).val : ℕ) : ZMod (2 * (N + 1))) - 1
          = (b - a - 1 - 1) + ((N + 1 : ℕ) : ZMod (2 * (N + 1))) := by linear_combination hw
      rw [h1, h3, labelRing_val_add_half_le, hvn]
      exact fun hc => (hc.mpr (by omega)) (by omega)

/-- **(B7)** Tasaki's "all other matrix elements are vanishing" (p. 499) at the level of
configurations: labels that are neither equal nor ring-adjacent give configurations that are
neither equal nor a single-site flip of one another, because they differ at two distinct sites. -/
theorem lowEnergyConfig_ne_of_not_adjacent (N : ℕ) (hN : 1 ≤ N) {a b : ZMod (2 * (N + 1))}
    (h₀ : b ≠ a) (h₁ : b ≠ a + 1) (h₂ : b ≠ a - 1) :
    lowEnergyConfig N b ≠ lowEnergyConfig N a
      ∧ ∀ x, lowEnergyConfig N b ≠ siteFlipAt (lowEnergyConfig N a) x := by
  have hlt : (b - a).val < 2 * (N + 1) := ZMod.val_lt _
  have hd0 : (b - a).val ≠ 0 := by
    intro h
    have hz := (ZMod.val_eq_zero _).mp h
    rw [sub_eq_zero] at hz
    exact h₀ hz
  have hd1 : (b - a).val ≠ 1 := by
    intro h
    have hz : b - a = ((1 : ℕ) : ZMod (2 * (N + 1))) :=
      (labelRing_eq_iff_val N _ 1 (by omega)).mpr h
    exact h₁ (by push_cast at hz; linear_combination hz)
  have hd2 : (b - a).val ≠ 2 * N + 1 := by
    intro h
    have hz : b - a = ((2 * N + 1 : ℕ) : ZMod (2 * (N + 1))) :=
      (labelRing_eq_iff_val N _ (2 * N + 1) (by omega)).mpr h
    have hs : ((2 * (N + 1) : ℕ) : ZMod (2 * (N + 1))) = 0 := ZMod.natCast_self _
    push_cast at hz hs
    exact h₂ (by linear_combination hz + hs)
  obtain ⟨x, y, hxy, hx, hy⟩ : ∃ x y : Fin (N + 1), x ≠ y
      ∧ lowEnergyConfig N b x ≠ lowEnergyConfig N a x
      ∧ lowEnergyConfig N b y ≠ lowEnergyConfig N a y := by
    rcases Nat.lt_or_ge (b - a).val (N + 2) with h | h
    · exact lowEnergyConfig_two_ne N hN (by omega) (by omega)
    · have hswap : a - b = -(b - a) := by ring
      have hneg : (a - b).val = 2 * (N + 1) - (b - a).val := by
        rw [hswap, ZMod.neg_val, if_neg]
        intro hc
        rw [hc, ZMod.val_zero] at hd0
        exact hd0 rfl
      obtain ⟨x, y, hxy, hx, hy⟩ :=
        lowEnergyConfig_two_ne N hN (a := b) (b := a) (by omega) (by omega)
      exact ⟨x, y, hxy, hx.symm, hy.symm⟩
  refine ⟨fun heq => hx (congrFun heq x), fun z heq => ?_⟩
  rcases eq_or_ne x z with rfl | hxz
  · exact hy (by rw [congrFun heq y, siteFlipAt_of_ne _ (Ne.symm hxy)])
  · exact hx (by rw [congrFun heq x, siteFlipAt_of_ne _ hxz])

/-! ### The compressed `2L × 2L` matrix -/

/-- Signed bond sum of a prefix-shaped configuration: a configuration constant on `0, …, j - 1`
and constant with the other value on `j, …, L - 1` has exactly one broken bond unless it is
constant, so the sum of `+1` over aligned bonds and `-1` over domain walls is `N` minus twice the
number of walls. -/
private theorem bondSum_prefix (N j : ℕ) (hj : j ≤ N + 1) {c d : Fin 2} (hcd : c ≠ d) :
    (∑ i : Fin N, if (if (i.castSucc : Fin (N + 1)).val < j then c else d)
        = (if (i.succ : Fin (N + 1)).val < j then c else d) then (1 : ℂ) else -1)
      = (N : ℂ) - 2 * (if j = 0 ∨ j = N + 1 then 0 else 1) := by
  have hterm : ∀ i : Fin N,
      (if (if (i.castSucc : Fin (N + 1)).val < j then c else d)
          = (if (i.succ : Fin (N + 1)).val < j then c else d) then (1 : ℂ) else -1)
        = 1 - 2 * (if j = i.val + 1 then (1 : ℂ) else 0) := by
    intro i
    rw [Fin.val_castSucc, Fin.val_succ]
    by_cases h : j = i.val + 1
    · rw [if_pos h, if_pos (by omega : i.val < j), if_neg (by omega : ¬ i.val + 1 < j),
        if_neg hcd]
      norm_num
    · rw [if_neg h]
      by_cases h2 : i.val < j
      · rw [if_pos h2, if_pos (by omega : i.val + 1 < j), if_pos rfl]
        norm_num
      · rw [if_neg h2, if_neg (by omega : ¬ i.val + 1 < j), if_pos rfl]
        norm_num
  have hcount : (∑ i : Fin N, if j = i.val + 1 then (1 : ℂ) else 0)
      = if j = 0 ∨ j = N + 1 then 0 else 1 := by
    by_cases h : j = 0 ∨ j = N + 1
    · rw [if_pos h]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have hi := i.is_lt
      refine if_neg ?_
      rcases h with h | h <;> omega
    · rw [if_neg h]
      have hj0 : j ≠ 0 := fun hc => h (Or.inl hc)
      have hjN : j ≠ N + 1 := fun hc => h (Or.inr hc)
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hj' : j' < N := by omega
      rw [Finset.sum_eq_single (⟨j', hj'⟩ : Fin N)]
      · exact if_pos rfl
      · intro i _ hi
        have hval : (⟨j', hj'⟩ : Fin N).val = j' := rfl
        exact if_neg (fun hc => hi (Fin.ext (by omega)))
      · intro hc
        exact absurd (Finset.mem_univ _) hc
  simp only [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hcount]
  simp

/-- Bond sum of a low-energy configuration presented in book form, through `bondSum_prefix`. -/
private theorem bondSum_of_prefix (N : ℕ) (a : ZMod (2 * (N + 1))) (j : ℕ) (hj : j ≤ N + 1)
    {c d : Fin 2} (hcd : c ≠ d)
    (hform : lowEnergyConfig N a = fun x => if x.val < j then c else d)
    (hcond : (a = 0 ∨ a = ((N + 1 : ℕ) : ZMod (2 * (N + 1)))) ↔ (j = 0 ∨ j = N + 1)) :
    (∑ i : Fin N, if lowEnergyConfig N a i.castSucc = lowEnergyConfig N a i.succ
        then (1 : ℂ) else -1)
      = (N : ℂ) - 2 * (if a = 0 ∨ a = ((N + 1 : ℕ) : ZMod (2 * (N + 1))) then 0 else 1) := by
  rw [hform, if_congr hcond rfl rfl]
  exact bondSum_prefix N j hj hcd

/-- **(B8)** Signed bond sum of every low-energy configuration: `N` for the two aligned labels
`0` and `L`, and `N - 2` for the `2L - 2` labels carrying a domain wall. Multiplied by `-J`, this
is Tasaki eq. (S.24) for the aligned labels and eq. (S.25) for the others. -/
private theorem bondSum_lowEnergyConfig (N : ℕ) (a : ZMod (2 * (N + 1))) :
    (∑ i : Fin N, if lowEnergyConfig N a i.castSucc = lowEnergyConfig N a i.succ
        then (1 : ℂ) else -1)
      = (N : ℂ) - 2 * (if a = 0 ∨ a = ((N + 1 : ℕ) : ZMod (2 * (N + 1))) then 0 else 1) := by
  have hlt : a.val < 2 * (N + 1) := ZMod.val_lt _
  have hzero : (a = 0) ↔ a.val = 0 := (ZMod.val_eq_zero a).symm
  have hhalf : (a = ((N + 1 : ℕ) : ZMod (2 * (N + 1)))) ↔ a.val = N + 1 :=
    labelRing_eq_iff_val N a (N + 1) (by omega)
  rcases Nat.lt_or_ge a.val (N + 2) with h | h
  · refine bondSum_of_prefix N a a.val (by omega) (c := 0) (d := 1) (by decide) ?_ ?_
    · have hb := lowEnergyConfig_natCast_le N a.val (by omega)
      rwa [ZMod.natCast_zmod_val] at hb
    · rw [hzero, hhalf]
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (by omega : N + 1 ≤ a.val)
    refine bondSum_of_prefix N a m (by omega) (c := 1) (d := 0) (by decide) ?_ ?_
    · have hb := lowEnergyConfig_natCast_add N m (by omega)
      rwa [show (((N + 1) + m : ℕ) : ZMod (2 * (N + 1))) = a by
        rw [← hm, ZMod.natCast_zmod_val]] at hb
    · rw [hzero, hhalf]
      omega

/-- **(B9)** The `2L × 2L` array of matrix elements `⟨Φ_a|Ĥ|Φ_b⟩` of the open-chain quantum
Ising Hamiltonian `quantumIsingHamiltonian N (1/4) (λ/2)` in the low-energy configuration basis
(Tasaki Problem 3.3.a, eqs. (S.24)-(S.27)).

Entries are matrix elements of `Ĥ` between the `2L` basis configurations, read off the
configuration-basis entries as in `basisVec_expectation_eq_diagonal`. Since `Ĥ` does not preserve
the span of these configurations, no entry and no eigenvalue of this matrix is claimed to be an
energy of `Ĥ`. -/
noncomputable def lowEnergyMatrix (N : ℕ) (lam : ℝ) :
    Matrix (ZMod (2 * (N + 1))) (ZMod (2 * (N + 1))) ℂ :=
  fun a b =>
    quantumIsingHamiltonian N (1 / 4) (lam / 2) (lowEnergyConfig N a) (lowEnergyConfig N b)

/-- **(B10)** The on-site potential `v_j` of Tasaki eq. (S.30): `0` at the two aligned labels
`j = 0` and `j = L`, and `1/2` at the `2L - 2` labels carrying a domain wall. -/
noncomputable def ringPotential (N : ℕ) (j : ZMod (2 * (N + 1))) : ℂ :=
  if j = 0 ∨ j = ((N + 1 : ℕ) : ZMod (2 * (N + 1))) then 0 else 1 / 2

/-- **(B11)** The tight-binding operator on the `2L` basis labels of Tasaki eq. (S.30): hopping
`-λ/2` between ring-adjacent labels, together with the diagonal potential `ringPotential`.

The ring here is the ring of basis labels, obtained by following the domain wall once around in
both orientations; the lattice underlying `quantumIsingHamiltonian` remains an open chain. -/
noncomputable def tightBindingRing (N : ℕ) (lam : ℝ) :
    Matrix (ZMod (2 * (N + 1))) (ZMod (2 * (N + 1))) ℂ :=
  fun a b => (if b = a + 1 ∨ b = a - 1 then -(lam : ℂ) / 2 else 0)
    + (if a = b then ringPotential N a else 0)

/-- **(C2)** All `2L × 2L` matrix elements of the compressed Hamiltonian at once: Tasaki
eqs. (S.24)-(S.27) together with "all other matrix elements are vanishing" (p. 499). The
compression is the constant `E_GS^(0) = -(L-1)/4 = -N/4` on the diagonal plus a tight-binding
ring on the basis labels.

Because the statement covers every entry, it subsumes the printed index ranges of (S.25)
(`j = 1, …, L - 1`), (S.26) (`j = 1, …, L - 2`) and (S.27) (the four `|Φ↑⟩`/`|Φ↓⟩` couplings).
The hypothesis `1 ≤ N` (that is, `L ≥ 2`) is what this proof route needs, not a structural
constraint: the non-adjacent entries come from `lowEnergyConfig_ne_of_not_adjacent`, whose
two-site witness is produced by `lowEnergyConfig_two_ne` at `c := 2`. Nothing degenerates at
`L = 1`: `tightBindingRing` carries a single hopping `if` per entry, so the two coinciding ring
neighbours `a + 1` and `a - 1` of a label cannot contribute twice. -/
theorem lowEnergyMatrix_eq_add_tightBindingRing (N : ℕ) (lam : ℝ) (hN : 1 ≤ N) :
    lowEnergyMatrix N lam
      = (-(N : ℂ) / 4) • (1 : Matrix (ZMod (2 * (N + 1))) (ZMod (2 * (N + 1))) ℂ)
        + tightBindingRing N lam := by
  have hone : (1 : ZMod (2 * (N + 1))) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_one'' (by omega : 2 * (N + 1) ≠ 1), ZMod.val_zero] at hv
    omega
  ext a b
  simp only [lowEnergyMatrix, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, tightBindingRing, ringPotential]
  by_cases hba : b = a
  · rw [hba]
    have hnb : ¬ (a = a + 1 ∨ a = a - 1) := by
      rintro (h | h)
      · exact hone (by linear_combination -h)
      · exact hone (by linear_combination h)
    rw [quantumIsingHamiltonian_apply_diag, bondSum_lowEnergyConfig, if_pos rfl, if_pos rfl,
      if_neg hnb]
    by_cases hc : a = 0 ∨ a = ((N + 1 : ℕ) : ZMod (2 * (N + 1)))
    · rw [if_pos hc, if_pos hc]
      push_cast
      ring
    · rw [if_neg hc, if_neg hc]
      push_cast
      ring
  · have hab : a ≠ b := fun h => hba h.symm
    by_cases hb1 : b = a + 1
    · have hflip : lowEnergyConfig N a
          = siteFlipAt (lowEnergyConfig N b) (wallSite N a) := by
        rw [hb1, lowEnergyConfig_succ_eq_siteFlipAt N a, siteFlipAt_involutive]
      rw [hflip, quantumIsingHamiltonian_apply_siteFlip, if_neg hab, if_neg hab,
        if_pos (Or.inl hb1)]
      push_cast
      ring
    · by_cases hb2 : b = a - 1
      · have hsucc : a = b + 1 := by linear_combination -hb2
        have hflip : lowEnergyConfig N a
            = siteFlipAt (lowEnergyConfig N b) (wallSite N b) := by
          rw [hsucc, lowEnergyConfig_succ_eq_siteFlipAt N b]
        rw [hflip, quantumIsingHamiltonian_apply_siteFlip, if_neg hab, if_neg hab,
          if_pos (Or.inr hb2)]
        push_cast
        ring
      · have hne2 : a ≠ b + 1 := fun h => hb2 (by linear_combination -h)
        have hne3 : a ≠ b - 1 := fun h => hb1 (by linear_combination -h)
        obtain ⟨hne, hflip⟩ := lowEnergyConfig_ne_of_not_adjacent N hN hab hne2 hne3
        have hnb : ¬ (b = a + 1 ∨ b = a - 1) := by
          rintro (h | h)
          · exact hb1 h
          · exact hb2 h
        rw [quantumIsingHamiltonian_apply_eq_zero N (1 / 4) (lam / 2) _ _ hne hflip,
          if_neg hab, if_neg hab, if_neg hnb]
        ring

end LatticeSystem.Quantum
