import LatticeSystem.Quantum.SpinS.HoneycombAKLTVBS
import LatticeSystem.Quantum.SpinS.SpinThreeHalfBondEmbedding

/-!
# Bond annihilation for the finite honeycomb AKLT VBS state

For a selected forward honeycomb dart, the finite virtual-configuration sum
is split into the selected singlet bit and all remaining bits.  Every
resulting two-site coefficient fibre is a scalar multiple of one of the nine
certified local spin-three-half VBS bond generators.  The arbitrary-bond
embedding theorem then proves that the maximal-spin projector annihilates the
finite honeycomb VBS state on every forward bond.

## Reference

* Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed.,
  Springer, 2020, §7.3.2, equation (7.3.7), p. 210.
-/

namespace LatticeSystem.Quantum

open LatticeSystem.Lattice

variable {m : ℕ}

/-- Virtual-bit assignments away from one selected forward honeycomb dart. -/
private abbrev HoneycombBondRestConfig (d : HoneycombForwardDart m) :=
  {e : HoneycombForwardDart m // e ≠ d} → Fin 2

/-- Extend an off-bond virtual assignment by the selected singlet bit. -/
private noncomputable def honeycombExtendBondRest
    (d : HoneycombForwardDart m)
    (μ : HoneycombBondRestConfig d) (s : Fin 2) :
    HoneycombVirtualConfig m := by
  classical
  exact fun e => if h : e = d then s else μ ⟨e, h⟩

/-- Split a virtual configuration into its off-bond assignment and selected
singlet bit. -/
private noncomputable def honeycombVirtualConfigEquivBond
    (d : HoneycombForwardDart m) :
    HoneycombVirtualConfig m ≃ HoneycombBondRestConfig d × Fin 2 := by
  classical
  refine
    { toFun := fun ν => (fun e => ν e.1, ν d)
      invFun := fun p => honeycombExtendBondRest d p.1 p.2
      left_inv := ?_
      right_inv := ?_ }
  · intro ν
    funext e
    by_cases he : e = d
    · subst e
      simp [honeycombExtendBondRest]
    · simp [honeycombExtendBondRest, he]
  · intro p
    apply Prod.ext
    · funext e
      simp [honeycombExtendBondRest, e.2]
    · simp [honeycombExtendBondRest]

/-- Classical equality on forward darts, used to synthesize the canonical
function-space finite enumerations in the VBS definition. -/
private noncomputable instance :
    DecidableEq (HoneycombForwardDart m) :=
  Classical.decEq _

/-- The selected bit of an extended rest assignment is the supplied bit. -/
private theorem honeycombExtendBondRest_apply_self
    (d : HoneycombForwardDart m)
    (μ : HoneycombBondRestConfig d) (s : Fin 2) :
    honeycombExtendBondRest d μ s d = s := by
  classical
  simp [honeycombExtendBondRest]

/-- Every nonselected bit of an extended rest assignment is unchanged. -/
private theorem honeycombExtendBondRest_apply_of_ne
    (d e : HoneycombForwardDart m) (he : e ≠ d)
    (μ : HoneycombBondRestConfig d) (s : Fin 2) :
    honeycombExtendBondRest d μ s e = μ ⟨e, he⟩ := by
  classical
  simp [honeycombExtendBondRest, he]

/-- Reversing a dart whose source is on sublattice `B` gives a forward
honeycomb dart. -/
private theorem honeycombDart_symm_fst_eq_false_local
    (e : (honeycombTorusGraph m).Dart)
    (he : e.fst.2 ≠ false) :
    e.symm.fst.2 = false := by
  rcases honeycombTorusGraph_adj.mp e.adj with h | h
  · exact (he h.1).elim
  · exact h.2.1

/-- The complete virtual sum splits into an off-bond assignment and the
selected singlet bit without duplication. -/
private theorem sum_honeycombVirtualConfig_eq_sum_rest_bit [NeZero m]
    (d : HoneycombForwardDart m) (f : HoneycombVirtualConfig m → ℂ) :
    ∑ ν, f ν = ∑ μ : HoneycombBondRestConfig d, ∑ s : Fin 2,
      f (honeycombExtendBondRest d μ s) := by
  classical
  calc
    ∑ ν, f ν =
        ∑ p : HoneycombBondRestConfig d × Fin 2,
          f ((honeycombVirtualConfigEquivBond d).symm p) :=
      ((honeycombVirtualConfigEquivBond d).symm.sum_comp f).symm
    _ = ∑ μ : HoneycombBondRestConfig d, ∑ s : Fin 2,
          f (honeycombExtendBondRest d μ s) := by
      simpa [honeycombVirtualConfigEquivBond] using
        (Fintype.sum_prod_type
          (fun p : HoneycombBondRestConfig d × Fin 2 =>
            f ((honeycombVirtualConfigEquivBond d).symm p)))

/-- Away from the two orientations of the selected dart, changing its stored
bit does not change an incidence spin. -/
private theorem honeycombIncidenceSpin_extend_of_ne
    (d : HoneycombForwardDart m) (μ : HoneycombBondRestConfig d)
    (e : (honeycombTorusGraph m).Dart)
    (he : e ≠ d.1) (hes : e ≠ d.1.symm) (s t : Fin 2) :
    honeycombIncidenceSpin (honeycombExtendBondRest d μ s) e =
      honeycombIncidenceSpin (honeycombExtendBondRest d μ t) e := by
  by_cases hf : e.fst.2 = false
  · rw [honeycombIncidenceSpin, dif_pos hf,
      honeycombIncidenceSpin, dif_pos hf]
    have hne :
        (⟨e, hf⟩ : HoneycombForwardDart m) ≠ d := by
      intro h
      exact he (congrArg Subtype.val h)
    rw [honeycombExtendBondRest_apply_of_ne d ⟨e, hf⟩ hne,
      honeycombExtendBondRest_apply_of_ne d ⟨e, hf⟩ hne]
  · rw [honeycombIncidenceSpin, dif_neg hf,
      honeycombIncidenceSpin, dif_neg hf]
    have hne :
        (⟨e.symm, honeycombDart_symm_fst_eq_false_local e hf⟩ :
          HoneycombForwardDart m) ≠ d := by
      intro h
      have hval := congrArg Subtype.val h
      apply hes
      have := congrArg SimpleGraph.Dart.symm hval
      simpa using this
    rw [honeycombExtendBondRest_apply_of_ne d
        ⟨e.symm, honeycombDart_symm_fst_eq_false_local e hf⟩ hne,
      honeycombExtendBondRest_apply_of_ne d
        ⟨e.symm, honeycombDart_symm_fst_eq_false_local e hf⟩ hne]

/-- The set of down-spin outgoing incidences at a vertex. -/
private def honeycombDownDarts [NeZero m]
    (ν : HoneycombVirtualConfig m) (x : HoneycombVertex m) :
    Finset (honeycombTorusGraph m).Dart :=
  Finset.univ.filter fun e =>
    e.fst = x ∧ honeycombIncidenceSpin ν e = 1

/-- The virtual down count is the cardinality of the down-incidence set. -/
private theorem honeycombVirtualDownCount_eq_card [NeZero m]
    (ν : HoneycombVirtualConfig m) (x : HoneycombVertex m) :
    honeycombVirtualDownCount ν x =
      (honeycombDownDarts ν x).card :=
  rfl

/-- A virtual down count is bounded by the graph degree. -/
private theorem honeycombVirtualDownCount_le_degree [NeZero m]
    (ν : HoneycombVirtualConfig m) (x : HoneycombVertex m) :
    honeycombVirtualDownCount ν x ≤
      (honeycombTorusGraph m).degree x := by
  rw [honeycombVirtualDownCount_eq_card]
  have hsub :
      honeycombDownDarts ν x ⊆
        Finset.univ.filter
          (fun e : (honeycombTorusGraph m).Dart => e.fst = x) := by
    intro e he
    simpa [honeycombDownDarts] using And.left
      (Finset.mem_filter.mp he).2
  refine (Finset.card_le_card hsub).trans_eq ?_
  rw [SimpleGraph.dart_fst_fiber_card_eq_degree]

/-- At the source endpoint, changing the selected bit from zero to one
inserts exactly the selected forward incidence into the down set. -/
private theorem honeycombDownDarts_left_one
    [NeZero m] (d : HoneycombForwardDart m)
    (μ : HoneycombBondRestConfig d) :
    honeycombDownDarts (honeycombExtendBondRest d μ 1) d.1.fst =
      insert d.1
        (honeycombDownDarts
          (honeycombExtendBondRest d μ 0) d.1.fst) := by
  classical
  ext e
  by_cases he : e = d.1
  · subst e
    simp [honeycombDownDarts, honeycombIncidenceSpin_forward,
      honeycombExtendBondRest_apply_self]
  · by_cases hfst : e.fst = d.1.fst
    · have hes : e ≠ d.1.symm := by
        intro hes
        rw [hes] at hfst
        exact d.1.adj.ne hfst.symm
      have hinc := honeycombIncidenceSpin_extend_of_ne
        d μ e he hes 1 0
      simp only [honeycombDownDarts, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨_, hs⟩
        exact Or.inr ⟨hfst, hinc ▸ hs⟩
      · rintro (hed | ⟨_, hs⟩)
        · exact (he hed).elim
        · exact ⟨hfst, hinc.symm ▸ hs⟩
    · simp [honeycombDownDarts, he, hfst]

/-- At the target endpoint, changing the selected bit from one to zero
inserts exactly the reverse incidence into the down set. -/
private theorem honeycombDownDarts_right_zero
    [NeZero m] (d : HoneycombForwardDart m)
    (μ : HoneycombBondRestConfig d) :
    honeycombDownDarts (honeycombExtendBondRest d μ 0) d.1.snd =
      insert d.1.symm
        (honeycombDownDarts
          (honeycombExtendBondRest d μ 1) d.1.snd) := by
  classical
  ext e
  by_cases he : e = d.1.symm
  · subst e
    simp [honeycombDownDarts, honeycombIncidenceSpin_reverse,
      honeycombExtendBondRest_apply_self]
  · by_cases hfst : e.fst = d.1.snd
    · have hef : e ≠ d.1 := by
        intro hef
        rw [hef] at hfst
        exact d.1.adj.ne hfst
      have hinc := honeycombIncidenceSpin_extend_of_ne
        d μ e hef he 0 1
      simp only [honeycombDownDarts, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨_, hs⟩
        exact Or.inr ⟨hfst, hinc ▸ hs⟩
      · rintro (hed | ⟨_, hs⟩)
        · exact (he hed).elim
        · exact ⟨hfst, hinc.symm ▸ hs⟩
    · simp [honeycombDownDarts, he, hfst]

/-- The selected forward incidence is absent when its stored bit is zero. -/
private theorem honeycombForwardDart_not_mem_down_zero
    [NeZero m] (d : HoneycombForwardDart m)
    (μ : HoneycombBondRestConfig d) :
    d.1 ∉ honeycombDownDarts
      (honeycombExtendBondRest d μ 0) d.1.fst := by
  simp [honeycombDownDarts, honeycombIncidenceSpin_forward,
    honeycombExtendBondRest_apply_self]

/-- The selected reverse incidence is absent when its stored bit is one. -/
private theorem honeycombReverseDart_not_mem_down_one
    [NeZero m] (d : HoneycombForwardDart m)
    (μ : HoneycombBondRestConfig d) :
    d.1.symm ∉ honeycombDownDarts
      (honeycombExtendBondRest d μ 1) d.1.snd := by
  simp [honeycombDownDarts, honeycombIncidenceSpin_reverse,
    honeycombExtendBondRest_apply_self]

/-- Changing the selected bit from zero to one increases the source down
count by one. -/
private theorem honeycombVirtualDownCount_left_one
    [NeZero m] (d : HoneycombForwardDart m)
    (μ : HoneycombBondRestConfig d) :
    honeycombVirtualDownCount (honeycombExtendBondRest d μ 1) d.1.fst =
      honeycombVirtualDownCount
        (honeycombExtendBondRest d μ 0) d.1.fst + 1 := by
  rw [honeycombVirtualDownCount_eq_card,
    honeycombVirtualDownCount_eq_card,
    honeycombDownDarts_left_one,
    Finset.card_insert_of_notMem
      (honeycombForwardDart_not_mem_down_zero d μ)]

/-- Changing the selected bit from one to zero increases the target down
count by one. -/
private theorem honeycombVirtualDownCount_right_zero
    [NeZero m] (d : HoneycombForwardDart m)
    (μ : HoneycombBondRestConfig d) :
    honeycombVirtualDownCount (honeycombExtendBondRest d μ 0) d.1.snd =
      honeycombVirtualDownCount
        (honeycombExtendBondRest d μ 1) d.1.snd + 1 := by
  rw [honeycombVirtualDownCount_eq_card,
    honeycombVirtualDownCount_eq_card,
    honeycombDownDarts_right_zero,
    Finset.card_insert_of_notMem
      (honeycombReverseDart_not_mem_down_one d μ)]

/-- Source residual down count, excluding the selected singlet incidence. -/
private noncomputable def honeycombBondLeftResidual [NeZero m]
    (hm : 2 ≤ m) (d : HoneycombForwardDart m)
    (μ : HoneycombBondRestConfig d) : Fin 3 :=
  ⟨honeycombVirtualDownCount
      (honeycombExtendBondRest d μ 0) d.1.fst, by
    have hle := honeycombVirtualDownCount_le_degree
      (honeycombExtendBondRest d μ 1) d.1.fst
    rw [honeycombTorusGraph_isRegularOfDegree (m := m) hm,
      honeycombVirtualDownCount_left_one] at hle
    omega⟩

/-- Target residual down count, excluding the selected singlet incidence. -/
private noncomputable def honeycombBondRightResidual [NeZero m]
    (hm : 2 ≤ m) (d : HoneycombForwardDart m)
    (μ : HoneycombBondRestConfig d) : Fin 3 :=
  ⟨honeycombVirtualDownCount
      (honeycombExtendBondRest d μ 1) d.1.snd, by
    have hle := honeycombVirtualDownCount_le_degree
      (honeycombExtendBondRest d μ 0) d.1.snd
    rw [honeycombTorusGraph_isRegularOfDegree (m := m) hm,
      honeycombVirtualDownCount_right_zero] at hle
    omega⟩

/-- The source down count is the source residual plus the selected bit. -/
private theorem honeycombVirtualDownCount_left
    [NeZero m] (hm : 2 ≤ m) (d : HoneycombForwardDart m)
    (μ : HoneycombBondRestConfig d) (s : Fin 2) :
    honeycombVirtualDownCount
        (honeycombExtendBondRest d μ s) d.1.fst =
      (honeycombBondLeftResidual hm d μ).val + s.val := by
  fin_cases s
  · rfl
  · simpa [honeycombBondLeftResidual] using
      honeycombVirtualDownCount_left_one d μ

/-- The target down count is the target residual plus the reversed selected
bit. -/
private theorem honeycombVirtualDownCount_right
    [NeZero m] (hm : 2 ≤ m) (d : HoneycombForwardDart m)
    (μ : HoneycombBondRestConfig d) (s : Fin 2) :
    honeycombVirtualDownCount
        (honeycombExtendBondRest d μ s) d.1.snd =
      (honeycombBondRightResidual hm d μ).val + (1 - s.val) := by
  fin_cases s
  · simpa [honeycombBondRightResidual] using
      honeycombVirtualDownCount_right_zero d μ
  · rfl

/-- Every spectator down count is independent of the selected bit. -/
private theorem honeycombVirtualDownCount_spectator
    [NeZero m] (d : HoneycombForwardDart m)
    (μ : HoneycombBondRestConfig d) (s t : Fin 2)
    (x : HoneycombVertex m) (hx : x ≠ d.1.fst)
    (hy : x ≠ d.1.snd) :
    honeycombVirtualDownCount (honeycombExtendBondRest d μ s) x =
      honeycombVirtualDownCount (honeycombExtendBondRest d μ t) x := by
  rw [honeycombVirtualDownCount_eq_card,
    honeycombVirtualDownCount_eq_card]
  apply congrArg Finset.card
  ext e
  by_cases hfst : e.fst = x
  · have hef : e ≠ d.1 := by
      intro hef
      apply hx
      simpa [hef] using hfst.symm
    have her : e ≠ d.1.symm := by
      intro her
      apply hy
      simpa [her] using hfst.symm
    have hinc := honeycombIncidenceSpin_extend_of_ne
      d μ e hef her s t
    simp only [honeycombDownDarts, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, hs⟩
      exact ⟨hfst, hinc ▸ hs⟩
    · rintro ⟨_, hs⟩
      exact ⟨hfst, hinc.symm ▸ hs⟩
  · simp [honeycombDownDarts, hfst]

/-- Changing only the selected bit from zero to one flips the singlet sign. -/
private theorem honeycombSingletWeight_extend_one_eq_neg_zero
    [NeZero m] (d : HoneycombForwardDart m)
    (μ : HoneycombBondRestConfig d) :
    honeycombSingletWeight (honeycombExtendBondRest d μ 1) =
      -honeycombSingletWeight (honeycombExtendBondRest d μ 0) := by
  classical
  let z :=
    Finset.univ.filter fun e : HoneycombForwardDart m =>
      honeycombExtendBondRest d μ 0 e = 1
  have hdnot : d ∉ z := by
    simp [z, honeycombExtendBondRest_apply_self]
  have hfilter :
      (Finset.univ.filter fun e : HoneycombForwardDart m =>
        honeycombExtendBondRest d μ 1 e = 1) = insert d z := by
    ext e
    by_cases he : e = d
    · subst e
      simp [z, honeycombExtendBondRest_apply_self]
    · simp [z, honeycombExtendBondRest_apply_of_ne, he]
  rw [honeycombSingletWeight, honeycombSingletWeight, hfilter,
    Finset.card_insert_of_notMem hdnot, pow_succ]
  ring

/-- Spectator realization condition for a fixed off-bond assignment. -/
private def HoneycombBondSpectatorsRealize [NeZero m]
    (d : HoneycombForwardDart m)
    (τ : HoneycombVertex m → Fin 4)
    (μ : HoneycombBondRestConfig d) : Prop :=
  ∀ x, x ≠ d.1.fst → x ≠ d.1.snd →
    honeycombVirtualDownCount
        (honeycombExtendBondRest d μ 0) x =
      (τ x).val

/-- With selected bit zero, realization fixes the local physical
configuration to the up-down bond word determined by the residual counts. -/
private theorem honeycombRealizes_extend_zero_iff
    [NeZero m] (hm : 2 ≤ m) (d : HoneycombForwardDart m)
    (τ : HoneycombVertex m → Fin 4)
    (μ : HoneycombBondRestConfig d) (q : Fin 2 → Fin 4) :
    (honeycombExtendBondRest d μ 0).Realizes
        (glueTwoSitesS d.1.fst d.1.snd q τ) ↔
      HoneycombBondSpectatorsRealize d τ μ ∧
        q = ![
          Fin.castSucc (honeycombBondLeftResidual hm d μ),
          Fin.succ (honeycombBondRightResidual hm d μ)] := by
  constructor
  · intro hrealizes
    constructor
    · intro x hx hy
      rw [← honeycombVirtualDownCount_spectator d μ 0 0 x hx hy]
      have hxrealizes := hrealizes x
      simpa [glueTwoSitesS, hx, hy] using hxrealizes
    · funext i
      fin_cases i
      · apply Fin.ext
        have hx := hrealizes d.1.fst
        rw [honeycombVirtualDownCount_left hm d μ 0] at hx
        simpa [glueTwoSitesS] using hx.symm
      · apply Fin.ext
        have hy := hrealizes d.1.snd
        rw [honeycombVirtualDownCount_right hm d μ 0] at hy
        simpa [glueTwoSitesS, d.1.adj.ne] using hy.symm
  · rintro ⟨hspectators, rfl⟩ x
    by_cases hx : x = d.1.fst
    · subst x
      rw [honeycombVirtualDownCount_left hm d μ 0]
      simp [glueTwoSitesS]
    · by_cases hy : x = d.1.snd
      · subst x
        rw [honeycombVirtualDownCount_right hm d μ 0]
        simp [glueTwoSitesS]
      · simpa [glueTwoSitesS, hx, hy] using
          hspectators x hx hy

/-- With selected bit one, realization fixes the local physical
configuration to the down-up bond word determined by the residual counts. -/
private theorem honeycombRealizes_extend_one_iff
    [NeZero m] (hm : 2 ≤ m) (d : HoneycombForwardDart m)
    (τ : HoneycombVertex m → Fin 4)
    (μ : HoneycombBondRestConfig d) (q : Fin 2 → Fin 4) :
    (honeycombExtendBondRest d μ 1).Realizes
        (glueTwoSitesS d.1.fst d.1.snd q τ) ↔
      HoneycombBondSpectatorsRealize d τ μ ∧
        q = ![
          Fin.succ (honeycombBondLeftResidual hm d μ),
          Fin.castSucc (honeycombBondRightResidual hm d μ)] := by
  constructor
  · intro hrealizes
    constructor
    · intro x hx hy
      rw [← honeycombVirtualDownCount_spectator d μ 1 0 x hx hy]
      have hxrealizes := hrealizes x
      simpa [glueTwoSitesS, hx, hy] using hxrealizes
    · funext i
      fin_cases i
      · apply Fin.ext
        have hx := hrealizes d.1.fst
        rw [honeycombVirtualDownCount_left hm d μ 1] at hx
        simpa [glueTwoSitesS] using hx.symm
      · apply Fin.ext
        have hy := hrealizes d.1.snd
        rw [honeycombVirtualDownCount_right hm d μ 1] at hy
        simpa [glueTwoSitesS, d.1.adj.ne] using hy.symm
  · rintro ⟨hspectators, rfl⟩ x
    by_cases hx : x = d.1.fst
    · subst x
      rw [honeycombVirtualDownCount_left hm d μ 1]
      simp [glueTwoSitesS]
    · by_cases hy : x = d.1.snd
      · subst x
        rw [honeycombVirtualDownCount_right hm d μ 1]
        simp [glueTwoSitesS]
      · rw [honeycombVirtualDownCount_spectator d μ 1 0 x hx hy]
        simpa [glueTwoSitesS, hx, hy] using
          hspectators x hx hy

/-- Contribution of one off-bond virtual assignment to a two-site slice. -/
private noncomputable def honeycombVBSBondFiber [NeZero m]
    (d : HoneycombForwardDart m)
    (τ : HoneycombVertex m → Fin 4)
    (μ : HoneycombBondRestConfig d) :
    (Fin 2 → Fin 4) → ℂ := by
  classical
  exact fun q =>
    honeycombSymmetrizerWeight
        (glueTwoSitesS d.1.fst d.1.snd q τ) *
      ∑ s : Fin 2,
        if (honeycombExtendBondRest d μ s).Realizes
            (glueTwoSitesS d.1.fst d.1.snd q τ) then
          honeycombSingletWeight
            (honeycombExtendBondRest d μ s)
        else 0

/-- Product of on-site symmetrizer weights away from the selected bond. -/
private noncomputable def honeycombBondSpectatorSymWeight [NeZero m]
    (d : HoneycombForwardDart m)
    (τ : HoneycombVertex m → Fin 4) : ℂ :=
  ∏ x ∈ (Finset.univ.erase d.1.fst).erase d.1.snd,
    (Real.sqrt (Nat.choose 3 (τ x).val) : ℂ)⁻¹

/-- The global symmetrizer product splits into the two endpoint factors and
one spectator factor on a two-site fibre. -/
private theorem honeycombSymmetrizerWeight_glue [NeZero m]
    (d : HoneycombForwardDart m)
    (τ : HoneycombVertex m → Fin 4) (q : Fin 2 → Fin 4) :
    honeycombSymmetrizerWeight
        (glueTwoSitesS d.1.fst d.1.snd q τ) =
      (Real.sqrt (Nat.choose 3 (q 0).val) : ℂ)⁻¹ *
        (Real.sqrt (Nat.choose 3 (q 1).val) : ℂ)⁻¹ *
          honeycombBondSpectatorSymWeight d τ := by
  classical
  let f : HoneycombVertex m → ℂ := fun x =>
    (Real.sqrt
      (Nat.choose 3
        ((glueTwoSitesS d.1.fst d.1.snd q τ) x).val) : ℂ)⁻¹
  have hxy : d.1.fst ≠ d.1.snd := d.1.adj.ne
  have hy : d.1.snd ∈
      (Finset.univ : Finset (HoneycombVertex m)).erase d.1.fst := by
    simp
  rw [honeycombSymmetrizerWeight]
  change (∏ x, f x) = _
  rw [← Finset.mul_prod_erase Finset.univ f
      (Finset.mem_univ d.1.fst),
    ← Finset.mul_prod_erase (Finset.univ.erase d.1.fst) f hy]
  change f d.1.fst * (f d.1.snd *
      ∏ x ∈ (Finset.univ.erase d.1.fst).erase d.1.snd, f x) = _
  have hleft :
      f d.1.fst =
        (Real.sqrt (Nat.choose 3 (q 0).val) : ℂ)⁻¹ := by
    simp [f, glueTwoSitesS]
  have hright :
      f d.1.snd =
        (Real.sqrt (Nat.choose 3 (q 1).val) : ℂ)⁻¹ := by
    simp [f, glueTwoSitesS]
  rw [hleft, hright]
  rw [← mul_assoc]
  apply congrArg (fun z : ℂ =>
    (Real.sqrt (Nat.choose 3 (q 0).val) : ℂ)⁻¹ *
      (Real.sqrt (Nat.choose 3 (q 1).val) : ℂ)⁻¹ * z)
  unfold honeycombBondSpectatorSymWeight
  apply Finset.prod_congr rfl
  intro x hx
  have hy' := (Finset.mem_erase.mp hx).1
  have hx' := (Finset.mem_erase.mp
    (Finset.mem_erase.mp hx).2).1
  simp [f, glueTwoSitesS, hx', hy']

/-- Classical decidability of the finite spectator realization condition. -/
private noncomputable instance honeycombBondSpectatorsRealizeDecidable
    [NeZero m] (d : HoneycombForwardDart m)
    (τ : HoneycombVertex m → Fin 4)
    (μ : HoneycombBondRestConfig d) :
    Decidable (HoneycombBondSpectatorsRealize d τ μ) :=
  Classical.propDecidable _

/-- One fibre has support on the two bond words selected by the singlet,
with opposite coefficients. -/
private theorem honeycombVBSBondFiber_eq_two_coordinate
    [NeZero m] (hm : 2 ≤ m) (d : HoneycombForwardDart m)
    (τ : HoneycombVertex m → Fin 4)
    (μ : HoneycombBondRestConfig d) (q : Fin 2 → Fin 4) :
    honeycombVBSBondFiber d τ μ q =
      if HoneycombBondSpectatorsRealize d τ μ then
        honeycombSymmetrizerWeight
            (glueTwoSitesS d.1.fst d.1.snd q τ) *
          honeycombSingletWeight
              (honeycombExtendBondRest d μ 0) *
            ((if q = ![
                Fin.castSucc (honeycombBondLeftResidual hm d μ),
                Fin.succ (honeycombBondRightResidual hm d μ)]
              then 1 else 0) -
            (if q = ![
                Fin.succ (honeycombBondLeftResidual hm d μ),
                Fin.castSucc (honeycombBondRightResidual hm d μ)]
              then 1 else 0))
      else 0 := by
  classical
  by_cases hs : HoneycombBondSpectatorsRealize d τ μ
  · rw [if_pos hs]
    simp only [honeycombVBSBondFiber, Fin.sum_univ_two,
      honeycombRealizes_extend_zero_iff hm d τ μ q,
      honeycombRealizes_extend_one_iff hm d τ μ q, hs, true_and]
    rw [honeycombSingletWeight_extend_one_eq_neg_zero]
    split_ifs <;> ring
  · rw [if_neg hs]
    simp [honeycombVBSBondFiber, Fin.sum_univ_two,
      honeycombRealizes_extend_zero_iff hm d τ μ q,
      honeycombRealizes_extend_one_iff hm d τ μ q, hs]

/-- Common nonzero normalization factor in a local Gate L VBS generator. -/
private noncomputable def honeycombBondGeneratorOuter
    (a b : Fin 3) : ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ *
    (Real.sqrt (Nat.choose 2 a.val) : ℂ) *
      (Real.sqrt (Nat.choose 2 b.val) : ℂ)

/-- The common normalization factor in every local Gate L VBS generator is
nonzero. -/
private theorem honeycombBondGeneratorOuter_ne_zero
    (a b : Fin 3) :
    honeycombBondGeneratorOuter a b ≠ 0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [honeycombBondGeneratorOuter, Real.sq_sqrt]

/-- Positive-support coordinate of a local Gate L VBS generator. -/
private def honeycombBondUpDown (a b : Fin 3) :
    Fin 2 → Fin 4 :=
  ![Fin.castSucc a, Fin.succ b]

/-- Negative-support coordinate of a local Gate L VBS generator. -/
private def honeycombBondDownUp (a b : Fin 3) :
    Fin 2 → Fin 4 :=
  ![Fin.succ a, Fin.castSucc b]

/-- One normalized spin-three-half site coefficient. -/
private noncomputable def honeycombSiteWeight (k : Fin 4) : ℂ :=
  (Real.sqrt (Nat.choose 3 k.val) : ℂ)⁻¹

/-- The two support coordinates of a Gate L generator are distinct. -/
private theorem honeycombBondUpDown_ne_downUp (a b : Fin 3) :
    honeycombBondUpDown a b ≠ honeycombBondDownUp a b := by
  intro h
  have hzero := congrFun h 0
  have hval := congrArg Fin.val hzero
  simp [honeycombBondUpDown, honeycombBondDownUp] at hval

/-- The positive Gate L support value in factored site-weight form. -/
private theorem spinThreeHalfVBSBondVec_apply_honeycombBondUpDown
    (a b : Fin 3) :
    spinThreeHalfVBSBondVec a b (honeycombBondUpDown a b) =
      honeycombBondGeneratorOuter a b *
        honeycombSiteWeight (Fin.castSucc a) *
          honeycombSiteWeight (Fin.succ b) := by
  fin_cases a <;> fin_cases b <;>
    norm_num [spinThreeHalfVBSBondVec, honeycombBondUpDown,
      honeycombBondGeneratorOuter, honeycombSiteWeight,
      Real.sq_sqrt]
  all_goals try simp_all
  all_goals ring

/-- The negative Gate L support value in factored site-weight form. -/
private theorem spinThreeHalfVBSBondVec_apply_honeycombBondDownUp
    (a b : Fin 3) :
    spinThreeHalfVBSBondVec a b (honeycombBondDownUp a b) =
      -(honeycombBondGeneratorOuter a b *
        honeycombSiteWeight (Fin.succ a) *
          honeycombSiteWeight (Fin.castSucc b)) := by
  fin_cases a <;> fin_cases b <;>
    norm_num [spinThreeHalfVBSBondVec, honeycombBondDownUp,
      honeycombBondGeneratorOuter, honeycombSiteWeight,
      Real.sq_sqrt]
  all_goals try simp_all
  all_goals ring

/-- A Gate L generator vanishes away from its two displayed supports. -/
private theorem spinThreeHalfVBSBondVec_apply_of_ne_honeycomb_support
    (a b : Fin 3) (q : Fin 2 → Fin 4)
    (hupDown : q ≠ honeycombBondUpDown a b)
    (hdownUp : q ≠ honeycombBondDownUp a b) :
    spinThreeHalfVBSBondVec a b q = 0 := by
  fin_cases a <;> fin_cases b <;>
    simp_all [spinThreeHalfVBSBondVec, honeycombBondUpDown,
      honeycombBondDownUp]

/-- Each fixed off-bond contribution is a scalar multiple of one certified
local spin-three-half VBS bond generator. -/
private theorem honeycombVBSBondFiber_eq_smul_generator
    [NeZero m] (hm : 2 ≤ m) (d : HoneycombForwardDart m)
    (τ : HoneycombVertex m → Fin 4)
    (μ : HoneycombBondRestConfig d) :
    ∃ (a b : Fin 3) (c : ℂ),
      honeycombVBSBondFiber d τ μ =
        c • spinThreeHalfVBSBondVec a b := by
  let a := honeycombBondLeftResidual hm d μ
  let b := honeycombBondRightResidual hm d μ
  let r := honeycombBondSpectatorSymWeight d τ
  let w := honeycombSingletWeight
    (honeycombExtendBondRest d μ 0)
  let o := honeycombBondGeneratorOuter a b
  by_cases hs : HoneycombBondSpectatorsRealize d τ μ
  · refine ⟨a, b, r * w * o⁻¹, ?_⟩
    funext q
    have hUp :
        ![
          Fin.castSucc (honeycombBondLeftResidual hm d μ),
          Fin.succ (honeycombBondRightResidual hm d μ)] =
          honeycombBondUpDown a b :=
      rfl
    have hDown :
        ![
          Fin.succ (honeycombBondLeftResidual hm d μ),
          Fin.castSucc (honeycombBondRightResidual hm d μ)] =
          honeycombBondDownUp a b :=
      rfl
    have hud : honeycombBondUpDown a b ≠
        honeycombBondDownUp a b :=
      honeycombBondUpDown_ne_downUp a b
    by_cases hqUp : q = honeycombBondUpDown a b
    · subst q
      rw [honeycombVBSBondFiber_eq_two_coordinate hm d τ μ,
        if_pos hs, hUp, hDown, if_pos rfl, if_neg hud]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [honeycombSymmetrizerWeight_glue,
        spinThreeHalfVBSBondVec_apply_honeycombBondUpDown]
      have ho : o ≠ 0 := honeycombBondGeneratorOuter_ne_zero a b
      simp only [sub_zero, mul_one]
      change
        honeycombSiteWeight (Fin.castSucc a) *
              honeycombSiteWeight (Fin.succ b) * r * w =
          r * w * o⁻¹ *
            (o * honeycombSiteWeight (Fin.castSucc a) *
              honeycombSiteWeight (Fin.succ b))
      field_simp [ho]
    · by_cases hqDown : q = honeycombBondDownUp a b
      · subst q
        rw [honeycombVBSBondFiber_eq_two_coordinate hm d τ μ,
          if_pos hs, hUp, hDown, if_neg hud.symm, if_pos rfl]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [honeycombSymmetrizerWeight_glue,
          spinThreeHalfVBSBondVec_apply_honeycombBondDownUp]
        have ho : o ≠ 0 :=
          honeycombBondGeneratorOuter_ne_zero a b
        simp only [honeycombBondDownUp, Matrix.cons_val_zero,
          Matrix.cons_val_one, zero_sub, mul_neg, mul_one]
        change
          -(honeycombSiteWeight (Fin.succ a) *
                honeycombSiteWeight (Fin.castSucc b) * r * w) =
            -(r * w * o⁻¹ *
              (o * honeycombSiteWeight (Fin.succ a) *
                honeycombSiteWeight (Fin.castSucc b)))
        field_simp [ho]
      · rw [honeycombVBSBondFiber_eq_two_coordinate hm d τ μ,
          if_pos hs, hUp, hDown, if_neg hqUp, if_neg hqDown,
          Pi.smul_apply, smul_eq_mul,
          spinThreeHalfVBSBondVec_apply_of_ne_honeycomb_support
            a b q hqUp hqDown]
        simp
  · refine ⟨a, b, 0, ?_⟩
    funext q
    rw [honeycombVBSBondFiber_eq_two_coordinate hm d τ μ,
      if_neg hs]
    simp

/-- The two-site slice of the finite VBS state is the sum of its off-bond
virtual fibres. -/
private theorem honeycombVBSState_twoSiteSlice_eq_sum_fibers
    [NeZero m] (d : HoneycombForwardDart m)
    (τ : HoneycombVertex m → Fin 4) :
    twoSiteSliceS d.1.fst d.1.snd (honeycombVBSState m) τ =
      ∑ μ : HoneycombBondRestConfig d,
        honeycombVBSBondFiber d τ μ := by
  classical
  funext q
  rw [twoSiteSliceS, honeycombVBSState]
  simp only [Finset.sum_apply]
  rw [sum_honeycombVirtualConfig_eq_sum_rest_bit (m := m) d
    (fun ν =>
      if ν.Realizes
          (glueTwoSitesS d.1.fst d.1.snd q τ) then
        honeycombSingletWeight ν
      else 0)]
  simp only [honeycombVBSBondFiber]
  rw [Finset.mul_sum]

/-- Every selected-bond two-site slice of the finite honeycomb VBS state lies
in the certified nine-dimensional local VBS bond subspace. -/
theorem honeycombVBSState_twoSiteSlice_mem [NeZero m]
    (hm : 2 ≤ m) (d : HoneycombForwardDart m)
    (τ : HoneycombVertex m → Fin 4) :
    twoSiteSliceS d.1.fst d.1.snd (honeycombVBSState m) τ ∈
      spinThreeHalfVBSBondSubspace := by
  rw [honeycombVBSState_twoSiteSlice_eq_sum_fibers]
  apply Submodule.sum_mem
  intro μ _
  obtain ⟨a, b, c, hfiber⟩ :=
    honeycombVBSBondFiber_eq_smul_generator hm d τ μ
  rw [hfiber]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨(a, b), rfl⟩

/-- On every canonically oriented honeycomb bond, the maximal-spin
projection annihilates the finite VBS state.  This is the per-bond
frustration-free ingredient associated with Tasaki equation (7.3.7), not a
statement about the full Hamiltonian sum. -/
theorem honeycombVBSState_bond_annihilated [NeZero m]
    (hm : 2 ≤ m) (d : HoneycombForwardDart m) :
    (bondMaxSpinProjectionS d.1.fst d.1.snd 3).mulVec
      (honeycombVBSState m) = 0 := by
  rw [bondMaxSpinProjectionS_three_mulVec_eq_zero_iff_slices
    d.1.adj.ne]
  exact honeycombVBSState_twoSiteSlice_mem hm d

end LatticeSystem.Quantum
