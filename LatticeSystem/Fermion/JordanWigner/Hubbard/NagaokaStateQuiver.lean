import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaGlobalMin
import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaMagnetizationSector
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

/-!
# Tasaki §11.2.2: the one-hole state quiver of `−M` (toward Lemma 11.9)

The connectivity condition (Definition 11.6, `nagaokaConnectivity`) is irreducibility of the
sector-restricted `−M`, i.e. strong connectivity of the quiver whose edges are the *positive*
entries of `−M`.  This file records the **edge characterisation**: `−M_{(y,τ),(x,σ)} > 0` exactly
when `x ≠ y`, the bond `x—y` is present (`t x y > 0`), and the spin configuration of the target
state `(y,τ)` is that of the source state `(x,σ)` after the hole hops `x → y`
(`hubbardSpinMove`).  This is **Step A** of Lemma 11.9 (a hole hop along a single bond), the
foundation for turning the "15-puzzle" hole-motion argument into quiver paths.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.2.2, Lemma 11.9 (the connectivity argument), pp. 386–388.
-/

namespace LatticeSystem.Fermion

open Matrix

/-- **Step A: the `−M` quiver edges.**  For `t ≥ 0`, the entry `−M_{(y,τ),(x,σ)}` of the negated
Tasaki effective matrix is strictly positive iff the hole positions differ (`x ≠ y`), the bond
`x—y` carries a non-zero hopping (`0 < t x y`), and the spin configuration of `(y,τ)` equals that
of `(x,σ)` with the hole hopped from `x` to `y` (`hubbardSpinMove`).  So a positive `−M` entry is
precisely a single hole hop along a bond of `(Λ, B)`. -/
theorem neg_tasakiEffReMatrix_pos_iff (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (q p : (x : Fin (N + 1)) × HoleSpin N x) :
    0 < (-tasakiEffReMatrix N t) q p ↔
      p.1 ≠ q.1 ∧ 0 < t p.1 q.1 ∧
        hubbardOneHoleConfig N q.1 (hubbardSpinMove N p.2.val p.1 q.1)
          = hubbardOneHoleConfig N q.1 q.2.val := by
  simp only [Matrix.neg_apply, tasakiEffReMatrix]
  by_cases hpq : p.1 = q.1
  · simp [hpq]
  · rw [if_neg hpq, neg_mul, neg_neg]
    by_cases hm : hubbardOneHoleConfig N q.1 (hubbardSpinMove N p.2.val p.1 q.1)
        = hubbardOneHoleConfig N q.1 q.2.val
    · rw [if_pos hm, mul_one]
      simp only [hm, hpq, Ne, not_false_iff, and_true, true_and]
    · rw [if_neg hm, mul_zero]
      simp [hm]

/-- The one-hole configuration ignores the spin at the hole site: updating `w` at the hole `y`
leaves `hubbardOneHoleConfig N y w` unchanged (the hole orbital is empty regardless). -/
theorem hubbardOneHoleConfig_update_hole (N : ℕ) (y : Fin (N + 1))
    (w : Fin (N + 1) → Bool) (b : Bool) :
    hubbardOneHoleConfig N y (Function.update w y b) = hubbardOneHoleConfig N y w := by
  funext k
  simp only [hubbardOneHoleConfig]
  by_cases hs : (⟨k.val / 2, by
      have hk := k.isLt
      exact (Nat.div_lt_iff_lt_mul (by norm_num)).mpr (by omega)⟩ : Fin (N + 1)).val = y.val
  · rw [if_pos hs, if_pos hs]
  · rw [if_neg hs, if_neg hs,
      Function.update_of_ne (fun h => hs (by rw [h]))]

/-- **The canonical hole-hop edge.**  When `x ≠ y` and the bond `x—y` is present (`0 < t x y`),
the `−M` quiver has a positive edge from the state `(x, σ)` to `(y, holeSpinMove N x y σ)` — the
hole hops `x → y`, carrying the spin configuration with it.  This is the elementary move used to
build hole-motion paths for Lemma 11.9. -/
theorem neg_tasakiEffReMatrix_holeSpinMove_pos (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (x y : Fin (N + 1)) (σ : HoleSpin N x) (hxy : x ≠ y) (ht : 0 < t x y) :
    0 < (-tasakiEffReMatrix N t) ⟨y, holeSpinMove N x y σ⟩ ⟨x, σ⟩ := by
  rw [neg_tasakiEffReMatrix_pos_iff]
  refine ⟨hxy, ht, ?_⟩
  change hubbardOneHoleConfig N y (hubbardSpinMove N σ.val x y)
    = hubbardOneHoleConfig N y (holeSpinMove N x y σ).val
  rw [show (holeSpinMove N x y σ).val
      = Function.update (hubbardSpinMove N σ.val x y) y true from rfl,
    hubbardOneHoleConfig_update_hole]

/-- The canonical hole-hop edge as an **arrow of the `−M` quiver** (`Matrix.toQuiver`): from
`(x, σ)` to `(y, holeSpinMove N x y σ)` whenever `x ≠ y` and `0 < t x y`.  This is the atomic
step from which hole-motion paths (Lemma 11.9) are assembled by `Quiver.Path.cons`. -/
def holeHopHom (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ) (x y : Fin (N + 1))
    (σ : HoleSpin N x) (hxy : x ≠ y) (ht : 0 < t x y) :
    (Matrix.toQuiver (-tasakiEffReMatrix N t)).Hom
      (⟨y, holeSpinMove N x y σ⟩ : (z : Fin (N + 1)) × HoleSpin N z) ⟨x, σ⟩ :=
  ⟨neg_tasakiEffReMatrix_holeSpinMove_pos N t x y σ hxy ht⟩

/-- `−M` is symmetric (for symmetric `t` with zero diagonal), so the reverse hole-hop edge is also
positive: `0 < −M_{(x,σ),(y, holeSpinMove x y σ)}`. -/
theorem neg_tasakiEffReMatrix_holeSpinMove_pos' (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0)
    (x y : Fin (N + 1)) (σ : HoleSpin N x) (hxy : x ≠ y) (ht : 0 < t x y) :
    0 < (-tasakiEffReMatrix N t) ⟨x, σ⟩ ⟨y, holeSpinMove N x y σ⟩ := by
  have hsym : (-tasakiEffReMatrix N t) (⟨x, σ⟩ : (z : Fin (N + 1)) × HoleSpin N z)
      ⟨y, holeSpinMove N x y σ⟩
      = (-tasakiEffReMatrix N t) ⟨y, holeSpinMove N x y σ⟩ ⟨x, σ⟩ := by
    rw [Matrix.neg_apply, Matrix.neg_apply, (tasakiEffReMatrix_isSymm N t htsym htdiag).apply]
  rw [hsym]
  exact neg_tasakiEffReMatrix_holeSpinMove_pos N t x y σ hxy ht

/-- The reverse hole-hop arrow of the `−M` quiver: from `(y, holeSpinMove N x y σ)` to `(x, σ)`,
available since `−M` is symmetric.  With `holeHopHom` this gives bidirectional atomic moves. -/
def holeHopHom' (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0)
    (x y : Fin (N + 1)) (σ : HoleSpin N x) (hxy : x ≠ y) (ht : 0 < t x y) :
    (Matrix.toQuiver (-tasakiEffReMatrix N t)).Hom
      (⟨x, σ⟩ : (z : Fin (N + 1)) × HoleSpin N z) ⟨y, holeSpinMove N x y σ⟩ :=
  ⟨neg_tasakiEffReMatrix_holeSpinMove_pos' N t htsym htdiag x y σ hxy ht⟩

/-- **State reachability** in the `−M` quiver: a (possibly empty) path of positive entries between
two one-hole states.  Strong connectivity of a sector (`nagaokaConnectivity`) amounts to a
*positive-length* such path between any two same-magnetization states; reachability is the
reflexive–transitive backbone for assembling those from atomic hole hops. -/
def StateReach (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (p q : (z : Fin (N + 1)) × HoleSpin N z) : Prop :=
  Nonempty ((Matrix.toQuiver (-tasakiEffReMatrix N t)).Path p q)

/-- Reachability is reflexive (empty path). -/
theorem StateReach.refl (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (p : (z : Fin (N + 1)) × HoleSpin N z) : StateReach N t p p := by
  letI := Matrix.toQuiver (-tasakiEffReMatrix N t)
  exact ⟨Quiver.Path.nil⟩

/-- **Block-diagonality of the quiver: every edge preserves magnetization.**  A positive entry of
`−M` (i.e. a quiver edge `q → p`) forces `q` and `p` to lie in the same total-`S_z^{(3)}` sector
(`holeSpinMag`).  Contrapositive of `tasakiEffReMatrix_eq_zero_of_holeSpinMag_ne`: `Ĥ_eff` conserves
`S_z^{(3)}`, so the state quiver decomposes into the magnetization sectors and every path stays in
one sector. -/
theorem neg_tasakiEffReMatrix_pos_holeSpinMag_eq (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (q p : (x : Fin (N + 1)) × HoleSpin N x) (h : 0 < (-tasakiEffReMatrix N t) q p) :
    holeSpinMag N q = holeSpinMag N p := by
  by_contra hne
  rw [Matrix.neg_apply, tasakiEffReMatrix_eq_zero_of_holeSpinMag_ne N t q p hne, neg_zero] at h
  exact lt_irrefl 0 h

/-- Reachability is transitive (path composition). -/
theorem StateReach.trans {N : ℕ} {t : Fin (N + 1) → Fin (N + 1) → ℝ}
    {p q r : (z : Fin (N + 1)) × HoleSpin N z}
    (hpq : StateReach N t p q) (hqr : StateReach N t q r) : StateReach N t p r := by
  letI := Matrix.toQuiver (-tasakiEffReMatrix N t)
  exact ⟨hpq.some.comp hqr.some⟩

/-- Reachability is symmetric: `−M` is symmetric (for symmetric `t`, zero diagonal), so reversing a
path of positive entries gives a path back.  Hence sector connectivity is undirected. -/
theorem StateReach.symm (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0)
    {p q : (z : Fin (N + 1)) × HoleSpin N z} (h : StateReach N t p q) : StateReach N t q p := by
  have hsymm : (-tasakiEffReMatrix N t)ᵀ = -tasakiEffReMatrix N t := by
    rw [Matrix.transpose_neg, (tasakiEffReMatrix_isSymm N t htsym htdiag)]
  exact ⟨hsymm ▸ Matrix.transposePath h.some⟩

/-- A single hole hop along a present bond gives reachability `(x, σ) → (y, holeSpinMove x y σ)`. -/
theorem StateReach.holeHop (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0)
    (x y : Fin (N + 1)) (σ : HoleSpin N x) (hxy : x ≠ y) (ht : 0 < t x y) :
    StateReach N t ⟨x, σ⟩ ⟨y, holeSpinMove N x y σ⟩ := by
  letI := Matrix.toQuiver (-tasakiEffReMatrix N t)
  exact ⟨(holeHopHom' N t htsym htdiag x y σ hxy ht).toPath⟩

/-- **Step B core: the 3-cycle hole motion transposes two spins.**  Moving the hole around a
length-3 loop `x → y → z → x` (distinct sites) returns it to `x` and swaps the spins at `y` and
`z`, leaving all other sites fixed.  This is Tasaki's "15-puzzle" exchange of two spins via a
short loop. -/
theorem holeSpinMove_three_cycle_val (N : ℕ) (x y z : Fin (N + 1))
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x) (σ : HoleSpin N x) :
    (holeSpinMove N z x (holeSpinMove N y z (holeSpinMove N x y σ))).val
      = fun w => if w = y then σ.val z else if w = z then σ.val y else σ.val w := by
  funext w
  simp only [holeSpinMove, Function.update_apply]
  by_cases hwx : w = x <;> by_cases hwy : w = y <;> by_cases hwz : w = z <;>
    simp_all [hxy, hyz, hzx, hxy.symm, hyz.symm, hzx.symm, σ.2]

/-- **Step B: a 3-cycle of bonds gives reachability to the spin-transposed state.**  If `x, y, z`
form a triangle of bonds (`0 < t` on each edge), the hole can travel `x → y → z → x`, returning to
`x` with the spins at `y` and `z` swapped — so `(x, σ)` reaches `(x, σ')` with `σ'` the `(y z)`
spin transposition of `σ` (same magnetization sector). -/
theorem StateReach.threeCycle (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (x y z : Fin (N + 1))
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (hbxy : 0 < t x y) (hbyz : 0 < t y z) (hbzx : 0 < t z x) (σ : HoleSpin N x) :
    StateReach N t ⟨x, σ⟩
      ⟨x, holeSpinMove N z x (holeSpinMove N y z (holeSpinMove N x y σ))⟩ :=
  (StateReach.holeHop N t htsym htdiag x y σ hxy hbxy).trans
    ((StateReach.holeHop N t htsym htdiag y z _ hyz hbyz).trans
      (StateReach.holeHop N t htsym htdiag z x _ hzx hbzx))

/-- The `(y z)` spin transposition of a one-hole state at hole `x` (with `x ∉ {y, z}`): swap the
spin values at `y` and `z`, leave the rest (and the hole at `x`) fixed. -/
def swapHoleSpin (N : ℕ) (x y z : Fin (N + 1)) (hxy : x ≠ y) (hxz : x ≠ z)
    (σ : HoleSpin N x) : HoleSpin N x :=
  ⟨fun w => if w = y then σ.val z else if w = z then σ.val y else σ.val w, by
    dsimp only; rw [if_neg hxy, if_neg hxz]; exact σ.2⟩

/-- **Step B (clean form): a bond triangle makes a spin transposition reachable.**  With bonds on
all three edges of `x, y, z`, the state `(x, σ)` reaches `(x, swapHoleSpin σ)` — the hole returns to
`x` and the spins at `y`, `z` are exchanged.  These two states share the magnetization sector
(transposition preserves total `S_z`), so this is an edge of the sector quiver's connectivity. -/
theorem StateReach.transposition (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (x y z : Fin (N + 1))
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (hbxy : 0 < t x y) (hbyz : 0 < t y z) (hbzx : 0 < t z x) (σ : HoleSpin N x) :
    StateReach N t ⟨x, σ⟩ ⟨x, swapHoleSpin N x y z hxy hzx.symm σ⟩ := by
  have h := StateReach.threeCycle N t htsym htdiag x y z hxy hyz hzx hbxy hbyz hbzx σ
  have heq : holeSpinMove N z x (holeSpinMove N y z (holeSpinMove N x y σ))
      = swapHoleSpin N x y z hxy hzx.symm σ := by
    apply Subtype.ext
    rw [holeSpinMove_three_cycle_val N x y z hxy hyz hzx σ]
    rfl
  rwa [heq] at h

/-- **Step B (length-4 loops): the 4-cycle hole motion 3-cycles three spins.**  Moving the hole
around a length-4 loop `x → y → w → z → x` (distinct sites) returns it to `x` and cyclically
permutes the spins `y → w → z → y` (i.e. site `y` receives `w`'s spin, `w` receives `z`'s, `z`
receives `y`'s), leaving all other sites fixed.  This is the length-4 case of Tasaki's exchange
mechanism. -/
theorem holeSpinMove_four_cycle_val (N : ℕ) (x y w z : Fin (N + 1))
    (hxy : x ≠ y) (hyw : y ≠ w) (hwz : w ≠ z) (hzx : z ≠ x) (hxw : x ≠ w) (hyz : y ≠ z)
    (σ : HoleSpin N x) :
    (holeSpinMove N z x (holeSpinMove N w z (holeSpinMove N y w (holeSpinMove N x y σ)))).val
      = fun v => if v = y then σ.val w else if v = w then σ.val z
          else if v = z then σ.val y else σ.val v := by
  funext v
  simp only [holeSpinMove, Function.update_apply]
  by_cases hvx : v = x <;> by_cases hvy : v = y <;> by_cases hvw : v = w <;>
      by_cases hvz : v = z <;>
    simp_all [hxy, hyw, hwz, hzx, hxw, hyz, hxy.symm, hyw.symm, hwz.symm, hzx.symm,
      hxw.symm, hyz.symm, σ.2]

/-- **Step B (length-4 loops): a 4-cycle of bonds makes the spin 3-cycle reachable.**  With bonds
on all four edges of the loop `x → y → w → z → x`, `(x, σ)` reaches `(x, σ')` where `σ'` 3-cycles
the spins at `y, w, z` — the length-4 case of Tasaki's exchange. -/
theorem StateReach.fourCycle (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (x y w z : Fin (N + 1))
    (hxy : x ≠ y) (hyw : y ≠ w) (hwz : w ≠ z) (hzx : z ≠ x)
    (hbxy : 0 < t x y) (hbyw : 0 < t y w) (hbwz : 0 < t w z) (hbzx : 0 < t z x)
    (σ : HoleSpin N x) :
    StateReach N t ⟨x, σ⟩
      ⟨x, holeSpinMove N z x (holeSpinMove N w z (holeSpinMove N y w (holeSpinMove N x y σ)))⟩ :=
  (StateReach.holeHop N t htsym htdiag x y σ hxy hbxy).trans
    ((StateReach.holeHop N t htsym htdiag y w _ hyw hbyw).trans
      ((StateReach.holeHop N t htsym htdiag w z _ hwz hbwz).trans
        (StateReach.holeHop N t htsym htdiag z x _ hzx hbzx)))

/-- The `(y w z)` spin 3-cycle of a one-hole state at hole `x` (with `x ∉ {y, w, z}`): `y` takes
`σ`'s spin at `w`, `w` takes `z`'s, `z` takes `y`'s; the rest (and the hole) fixed. -/
def cyc3HoleSpin (N : ℕ) (x y w z : Fin (N + 1)) (hxy : x ≠ y) (hxw : x ≠ w) (hxz : x ≠ z)
    (σ : HoleSpin N x) : HoleSpin N x :=
  ⟨fun v => if v = y then σ.val w else if v = w then σ.val z
      else if v = z then σ.val y else σ.val v, by
    dsimp only; rw [if_neg hxy, if_neg hxw, if_neg hxz]; exact σ.2⟩

/-- **Step B (length-4, clean form): a bond 4-loop makes a spin 3-cycle reachable.**  With bonds on
the loop `x → y → w → z → x`, `(x, σ)` reaches `(x, cyc3HoleSpin σ)` — the spins at `y, w, z` are
cyclically permuted (same magnetization sector). -/
theorem StateReach.threeCyclePerm (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (x y w z : Fin (N + 1))
    (hxy : x ≠ y) (hyw : y ≠ w) (hwz : w ≠ z) (hzx : z ≠ x) (hxw : x ≠ w) (hyz : y ≠ z)
    (hbxy : 0 < t x y) (hbyw : 0 < t y w) (hbwz : 0 < t w z) (hbzx : 0 < t z x)
    (σ : HoleSpin N x) :
    StateReach N t ⟨x, σ⟩ ⟨x, cyc3HoleSpin N x y w z hxy hxw hzx.symm σ⟩ := by
  have h := StateReach.fourCycle N t htsym htdiag x y w z hxy hyw hwz hzx hbxy hbyw hbwz hbzx σ
  have heq : holeSpinMove N z x (holeSpinMove N w z (holeSpinMove N y w (holeSpinMove N x y σ)))
      = cyc3HoleSpin N x y w z hxy hxw hzx.symm σ := by
    apply Subtype.ext
    rw [holeSpinMove_four_cycle_val N x y w z hxy hyw hwz hzx hxw hyz σ]
    rfl
  rwa [heq] at h

end LatticeSystem.Fermion

