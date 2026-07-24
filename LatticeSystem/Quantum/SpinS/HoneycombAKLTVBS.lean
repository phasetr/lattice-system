import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Real.Sqrt
import LatticeSystem.Lattice.HoneycombLattice

/-!
# The finite honeycomb AKLT valence-bond-solid state

This module constructs the finite-volume spin-three-half VBS amplitude on the
periodic honeycomb graph.  As a formal orientation convention, each undirected
edge is represented by its unique dart from sublattice `A` to sublattice `B`.
A virtual bit selects one of the two terms of the normalized singlet, and the
three incident virtual spins at each site are projected onto the normalized
symmetric spin-three-half basis.

The resulting formula is Tasaki's finite VBS construction in equation (7.3.6).
The edge singlets and on-site symmetric basis vectors use their normalized
coefficients, but the product of the on-site projections is not asserted to
leave the global vector unit normalized.

## Reference

* Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed.,
  Springer, 2020, §7.3.2, equation (7.3.6), p. 210; periodic bipartition in
  footnote 42, p. 211.
-/

namespace LatticeSystem.Quantum

open LatticeSystem.Lattice

variable {m : ℕ}

/-- Vertices of the `m × m` periodic honeycomb graph. -/
abbrev HoneycombVertex (m : ℕ) :=
  (ZMod m × ZMod m) × Bool

/-- Honeycomb darts using the chosen orientation from sublattice `A` to `B`. -/
def HoneycombForwardDart (m : ℕ) :=
  {d : (honeycombTorusGraph m).Dart // d.fst.2 = false}

/-- One virtual bit for each canonically oriented honeycomb edge. -/
abbrev HoneycombVirtualConfig (m : ℕ) :=
  HoneycombForwardDart m → Fin 2

/-- The endpoint colors of every honeycomb dart are opposite. -/
private theorem honeycombDart_colors
    (d : (honeycombTorusGraph m).Dart) :
    (d.fst.2 = false ∧ d.snd.2 = true) ∨
      (d.fst.2 = true ∧ d.snd.2 = false) := by
  rcases honeycombTorusGraph_adj.mp d.adj with
    ⟨hfst, hsnd, -⟩ | ⟨hfst, hsnd, -⟩
  · exact Or.inl ⟨hfst, hsnd⟩
  · exact Or.inr ⟨hfst, hsnd⟩

/-- A forward honeycomb dart ends on sublattice `B`. -/
theorem HoneycombForwardDart.snd_eq_true
    (d : HoneycombForwardDart m) :
    d.1.snd.2 = true := by
  rcases honeycombDart_colors d.1 with h | h
  · exact h.2
  · have hfalse : false = true := d.2.symm.trans h.1
    exact Bool.noConfusion hfalse

/-- Reversing a non-forward honeycomb dart gives a forward dart. -/
private theorem honeycombDart_symm_fst_eq_false
    (d : (honeycombTorusGraph m).Dart)
    (hd : d.fst.2 ≠ false) :
    d.symm.fst.2 = false := by
  rcases honeycombDart_colors d with h | h
  · exact (hd h.1).elim
  · exact h.2

/-- The finite type of forward-oriented honeycomb darts when the torus
size is nonzero. -/
instance [NeZero m] : Fintype (HoneycombForwardDart m) := by
  change Fintype
    {d : (honeycombTorusGraph m).Dart // d.fst.2 = false}
  exact Subtype.fintype _

/-- Virtual spin carried by an arbitrary oriented incidence.

The value on the reverse incidence is `Fin.rev` of the bit on the canonical
`A → B` representative, which implements the two opposite singlet spins. -/
def honeycombIncidenceSpin
    (ν : HoneycombVirtualConfig m)
    (d : (honeycombTorusGraph m).Dart) :
    Fin 2 :=
  if hd : d.fst.2 = false then
    ν ⟨d, hd⟩
  else
    Fin.rev (ν ⟨d.symm, honeycombDart_symm_fst_eq_false d hd⟩)

/-- On a forward dart, the source incidence is the stored virtual bit. -/
theorem honeycombIncidenceSpin_forward
    (ν : HoneycombVirtualConfig m) (d : HoneycombForwardDart m) :
    honeycombIncidenceSpin ν d.1 = ν d := by
  rw [honeycombIncidenceSpin, dif_pos d.2]
  apply congrArg ν
  exact Subtype.ext rfl

/-- On the reverse of a forward dart, the target incidence carries the
reversed virtual bit. -/
theorem honeycombIncidenceSpin_reverse
    (ν : HoneycombVirtualConfig m) (d : HoneycombForwardDart m) :
    honeycombIncidenceSpin ν d.1.symm = Fin.rev (ν d) := by
  have hcolor : d.1.symm.fst.2 ≠ false := by
    change d.1.snd.2 ≠ false
    rw [d.snd_eq_true]
    decide
  rw [honeycombIncidenceSpin, dif_neg hcolor]
  apply congrArg (fun e => Fin.rev (ν e))
  apply Subtype.ext
  rfl

/-- Number of down virtual incidences at a physical site. -/
def honeycombVirtualDownCount [NeZero m]
    (ν : HoneycombVirtualConfig m) (x : HoneycombVertex m) : ℕ :=
  (Finset.univ.filter fun d : (honeycombTorusGraph m).Dart =>
    d.fst = x ∧ honeycombIncidenceSpin ν d = 1).card

/-- A virtual configuration realizes a physical basis configuration when
the down counts agree site by site. -/
def HoneycombVirtualConfig.Realizes [NeZero m]
    (ν : HoneycombVirtualConfig m)
    (σ : HoneycombVertex m → Fin 4) : Prop :=
  ∀ x, honeycombVirtualDownCount ν x = (σ x).val

/-- Product of the normalized singlet coefficients, including signs. -/
noncomputable def honeycombSingletWeight [NeZero m]
    (ν : HoneycombVirtualConfig m) : ℂ := by
  classical
  exact
    ((Real.sqrt 2 : ℂ)⁻¹ ^
        Fintype.card (HoneycombForwardDart m)) *
      (-1 : ℂ) ^
        ((Finset.univ.filter fun d : HoneycombForwardDart m =>
          ν d = 1).card)

/-- Coefficient of each incidence word in the normalized on-site symmetric
spin-three-half vector. -/
noncomputable def honeycombSymmetrizerWeight [NeZero m]
    (σ : HoneycombVertex m → Fin 4) : ℂ :=
  ∏ x : HoneycombVertex m,
    (Real.sqrt (Nat.choose 3 (σ x).val) : ℂ)⁻¹

/-- Tasaki's finite honeycomb VBS amplitude from equation (7.3.6), with
normalized edge singlets and normalized on-site symmetric basis embeddings. -/
noncomputable def honeycombVBSState (m : ℕ) [NeZero m] :
    (HoneycombVertex m → Fin 4) → ℂ := by
  classical
  exact fun σ =>
    honeycombSymmetrizerWeight σ *
      ∑ ν : HoneycombVirtualConfig m,
        if HoneycombVirtualConfig.Realizes ν σ then
          honeycombSingletWeight ν
        else 0

/-- With every forward virtual bit zero, an incidence is down exactly when
its source lies on sublattice `B`. -/
private theorem honeycombIncidenceSpin_zero
    (d : (honeycombTorusGraph m).Dart) :
    honeycombIncidenceSpin (fun _ => 0) d =
      if d.fst.2 = false then 0 else 1 := by
  by_cases hd : d.fst.2 = false
  · simp [honeycombIncidenceSpin, hd]
  · simp [honeycombIncidenceSpin, hd]

/-- The all-zero virtual configuration has zero down incidences on `A` and
three down incidences on `B`. -/
private theorem honeycombVirtualDownCount_zero [NeZero m]
    (hm : 2 ≤ m) (x : HoneycombVertex m) :
    honeycombVirtualDownCount (fun _ => 0) x =
      if x.2 = false then 0 else 3 := by
  classical
  have hregular := honeycombTorusGraph_isRegularOfDegree (m := m) hm
  by_cases hx : x.2 = false
  · rw [if_pos hx]
    rw [honeycombVirtualDownCount, Finset.card_eq_zero]
    apply Finset.filter_eq_empty_iff.mpr
    intro d _
    rintro ⟨hdx, hspin⟩
    rw [honeycombIncidenceSpin_zero, hdx, hx] at hspin
    exact Fin.zero_ne_one hspin
  · rw [if_neg hx]
    rw [honeycombVirtualDownCount]
    have hfilter :
        (Finset.univ.filter fun d : (honeycombTorusGraph m).Dart =>
          d.fst = x ∧ honeycombIncidenceSpin (fun _ => 0) d = 1) =
        Finset.univ.filter fun d : (honeycombTorusGraph m).Dart =>
          d.fst = x := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact And.left
      · intro hdx
        subst x
        rw [honeycombIncidenceSpin_zero, if_neg hx]
        exact ⟨rfl, rfl⟩
    rw [hfilter, SimpleGraph.dart_fst_fiber_card_eq_degree]
    exact hregular x

/-- A virtual configuration realizes the Néel certificate precisely when
all its forward bits are zero. -/
private theorem honeycombRealizes_neel_iff [NeZero m]
    (hm : 2 ≤ m) (ν : HoneycombVirtualConfig m) :
    ν.Realizes (fun x : HoneycombVertex m =>
      if x.2 = false then 0 else 3) ↔
      ν = fun _ => 0 := by
  constructor
  · intro hrealizes
    funext d
    have hcount := hrealizes d.1.fst
    simp [d.2] at hcount
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp
        (Nat.le_pred_of_lt (ν d).isLt) with hν | hν
    · exact Fin.ext hν
    · have hν' : ν d = 1 := Fin.ext hν
      have hmem :
          d.1 ∈
            Finset.univ.filter
              (fun e : (honeycombTorusGraph m).Dart =>
                e.fst = d.1.fst ∧ honeycombIncidenceSpin ν e = 1) := by
        simp [honeycombIncidenceSpin_forward, hν']
      have hpos : 0 <
          honeycombVirtualDownCount ν d.1.fst := by
        exact Finset.card_pos.mpr ⟨d.1, hmem⟩
      omega
  · rintro rfl
    intro x
    rw [honeycombVirtualDownCount_zero hm]
    by_cases hx : x.2 = false <;> simp [hx]

/-- The Néel-basis coefficient certifies the exact positive contribution of
the unique all-zero virtual configuration. -/
private theorem honeycombVBSState_apply_neel [NeZero m]
    (hm : 2 ≤ m) :
    honeycombVBSState m
        (fun x => if x.2 = false then 0 else 3) =
      (Real.sqrt 2 : ℂ)⁻¹ ^
        Fintype.card (HoneycombForwardDart m) := by
  classical
  let σ : HoneycombVertex m → Fin 4 :=
    fun x => if x.2 = false then 0 else 3
  have hsym : honeycombSymmetrizerWeight σ = 1 := by
    rw [honeycombSymmetrizerWeight]
    apply Finset.prod_eq_one
    intro x _
    by_cases hx : x.2 = false <;> simp [σ, hx]
  have hrealizes_zero :
      HoneycombVirtualConfig.Realizes
        (fun _ : HoneycombForwardDart m => (0 : Fin 2)) σ := by
    rw [honeycombRealizes_neel_iff hm]
  rw [show (fun x : HoneycombVertex m =>
    if x.2 = false then 0 else 3) = σ by rfl]
  rw [honeycombVBSState, hsym, one_mul]
  rw [Finset.sum_eq_single (fun _ : HoneycombForwardDart m => (0 : Fin 2))]
  · rw [if_pos hrealizes_zero]
    simp [honeycombSingletWeight]
  · intro ν _ hν
    have hnot : ¬HoneycombVirtualConfig.Realizes ν σ := by
      intro hrealizes
      apply hν
      exact (honeycombRealizes_neel_iff hm ν).mp hrealizes
    simp [hnot]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

/-- The finite honeycomb VBS vector is nonzero. -/
theorem honeycombVBSState_ne_zero [NeZero m] (hm : 2 ≤ m) :
    honeycombVBSState m ≠ 0 := by
  intro hzero
  have happly := congrFun hzero
    (fun x : HoneycombVertex m =>
      if x.2 = false then 0 else 3)
  rw [honeycombVBSState_apply_neel hm] at happly
  have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  exact pow_ne_zero _ (inv_ne_zero hsqrt) happly

end LatticeSystem.Quantum
