import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaGlobalMin
import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaMagnetizationSector
import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaConnectivityClassification
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

/-- The sector matrix entry is the full `−M` entry between the underlying states: the
Perron–Frobenius sector matrix `nagaokaPFMatrixOnSector` is literally the submatrix of `−M` on the
sector, so its quiver edges are exactly the full-quiver edges between sector states. -/
theorem nagaokaPFMatrixOnSector_apply (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ) (m : ℤ)
    (i j : HoleMagSector N m) :
    nagaokaPFMatrixOnSector N t m i j = (-tasakiEffReMatrix N t) i.val j.val := by
  simp only [nagaokaPFMatrixOnSector, tasakiEffReMatrixOnSector, Matrix.neg_apply,
    Matrix.submatrix_apply]

/-- **Step C: lifting a full-quiver path to the sector quiver.**  A path of `−M` quiver edges from
`a` to `b`, with `a` in sector `m`, lifts to a path of the *sector* quiver
`toQuiver (nagaokaPFMatrixOnSector N t m)` of the same length — and `b` is automatically in sector
`m` too.  Every edge preserves magnetization (`neg_tasakiEffReMatrix_pos_holeSpinMag_eq`), so the
whole path stays inside the sector, where the sector matrix coincides with `−M`
(`nagaokaPFMatrixOnSector_apply`).  This is the bridge from the hole-motion reachability of the full
quiver to strong connectivity of each sector block (Definition 11.6 / `IsIrreducible`). -/
theorem exists_sectorPath_of_path (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ) (m : ℤ)
    {a b : (x : Fin (N + 1)) × HoleSpin N x} (ha : holeSpinMag N a = m)
    (p : @Quiver.Path _ (Matrix.toQuiver (-tasakiEffReMatrix N t)) a b) :
    ∃ (hb : holeSpinMag N b = m)
      (q : @Quiver.Path _ (Matrix.toQuiver (nagaokaPFMatrixOnSector N t m)) ⟨a, ha⟩ ⟨b, hb⟩),
      @Quiver.Path.length _ (Matrix.toQuiver (nagaokaPFMatrixOnSector N t m)) _ _ q
        = @Quiver.Path.length _ (Matrix.toQuiver (-tasakiEffReMatrix N t)) _ _ p := by
  letI iQ : Quiver _ := Matrix.toQuiver (-tasakiEffReMatrix N t)
  letI iS : Quiver (HoleMagSector N m) := Matrix.toQuiver (nagaokaPFMatrixOnSector N t m)
  induction p with
  | nil => exact ⟨ha, @Quiver.Path.nil _ iS _, rfl⟩
  | @cons c d r e ih =>
    obtain ⟨hc, q, hq⟩ := ih
    have hd : holeSpinMag N d = m :=
      (neg_tasakiEffReMatrix_pos_holeSpinMag_eq N t c d e.down).symm.trans hc
    have eS : (0 : ℝ) < nagaokaPFMatrixOnSector N t m ⟨c, hc⟩ ⟨d, hd⟩ := by
      rw [nagaokaPFMatrixOnSector_apply]; exact e.down
    refine ⟨hd, @Quiver.Path.cons _ iS ⟨a, ha⟩ ⟨c, hc⟩ ⟨d, hd⟩ q (PLift.up eS), ?_⟩
    rw [@Quiver.Path.length_cons _ iS, hq, @Quiver.Path.length_cons _ iQ]

/-- **Step C: state-quiver reachability ⟹ sector irreducibility.**  For `t ≥ 0`, if every ordered
pair of states in a magnetization sector `m` is joined by a *positive-length* path of `−M` quiver
edges (hole hops), then the sector matrix `nagaokaPFMatrixOnSector N t m` is irreducible (Definition
11.6 for that sector).  Non-negativity is `neg_tasakiEffReMatrix_nonneg`; strong connectivity lifts
each full-quiver path into the sector via `exists_sectorPath_of_path`.  This reduces the connectivity
condition to the purely combinatorial reachability of the one-hole states by hole motion. -/
theorem nagaokaPFMatrixOnSector_isIrreducible_of_reach (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) (m : ℤ) (hpos : ∀ i j, 0 ≤ t i j)
    (hreach : ∀ i j : HoleMagSector N m,
      ∃ p : @Quiver.Path _ (Matrix.toQuiver (-tasakiEffReMatrix N t)) i.val j.val,
        0 < @Quiver.Path.length _ (Matrix.toQuiver (-tasakiEffReMatrix N t)) _ _ p) :
    (nagaokaPFMatrixOnSector N t m).IsIrreducible := by
  refine ⟨fun i j => ?_, ?_⟩
  · rw [nagaokaPFMatrixOnSector_apply]; exact neg_tasakiEffReMatrix_nonneg N t hpos i.val j.val
  · letI iS : Quiver (HoleMagSector N m) := Matrix.toQuiver (nagaokaPFMatrixOnSector N t m)
    intro i j
    obtain ⟨p, hp⟩ := hreach i j
    obtain ⟨hj, q, hq⟩ := exists_sectorPath_of_path N t m i.2 p
    exact ⟨q, by rw [hq]; exact hp⟩

/-- **Step C capstone: the connectivity condition reduces to state-quiver reachability.**  For
`t ≥ 0`, if within every magnetization sector every ordered pair of one-hole states is joined by a
positive-length path of `−M` quiver edges (i.e. a non-trivial sequence of hole hops), then the
connectivity condition of Definition 11.6 (`nagaokaConnectivity`) holds.  This is the matrix/quiver
half of Lemma 11.9: it leaves exactly the combinatorial task of exhibiting those hole-motion paths
from the exchange-bond hypothesis (the "15-puzzle" argument). -/
theorem nagaokaConnectivity_of_reach (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (hpos : ∀ i j, 0 ≤ t i j)
    (hreach : ∀ (m : ℤ) (i j : HoleMagSector N m),
      ∃ p : @Quiver.Path _ (Matrix.toQuiver (-tasakiEffReMatrix N t)) i.val j.val,
        0 < @Quiver.Path.length _ (Matrix.toQuiver (-tasakiEffReMatrix N t)) _ _ p) :
    nagaokaConnectivity N t :=
  fun m => nagaokaPFMatrixOnSector_isIrreducible_of_reach N t m hpos (hreach m)

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
    simp_all [hyz, hzx, hxy.symm, hyz.symm, hzx.symm, σ.2]

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

/-- Pointwise value of `swapHoleSpin`: the spins at `y` and `z` are exchanged, all others kept. -/
theorem swapHoleSpin_val_apply (N : ℕ) (x y z : Fin (N + 1)) (hxy : x ≠ y) (hxz : x ≠ z)
    (σ : HoleSpin N x) (s : Fin (N + 1)) :
    (swapHoleSpin N x y z hxy hxz σ).val s
      = if s = y then σ.val z else if s = z then σ.val y else σ.val s := rfl

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

/-- A bond-graph edge gives a positive hopping amplitude (for symmetric `t ≥ 0`): adjacency in
`nagaokaBondGraph` means `t x y ≠ 0`, which together with `0 ≤ t x y` forces `0 < t x y`. -/
theorem nagaokaBondGraph_adj_pos (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (hpos : ∀ i j, 0 ≤ t i j) {x y : Fin (N + 1)}
    (h : (nagaokaBondGraph N t).Adj x y) : 0 < t x y := by
  obtain ⟨_, hne⟩ := h
  refine lt_of_le_of_ne (hpos x y) (fun h0 => ?_)
  rcases hne with hxy | hyx
  · exact hxy h0.symm
  · exact hyx (by rw [htsym]; exact h0.symm)

/-- **Step C (hole mobility): a bond-graph walk lifts to state-quiver reachability.**  If the hole
can travel from site `x` to site `x'` along a walk of bonds, then for any spin configuration `σ` the
state `(x, σ)` reaches *some* state `(x', τ)` (the spins carried along by the moving hole).  This is
the mobility ingredient of Lemma 11.9: the hole can be brought anywhere the bond graph allows, which
combined with the exchange-bond spin transpositions yields full sector connectivity. -/
theorem StateReach.exists_ofBondWalk (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (hpos : ∀ i j, 0 ≤ t i j)
    {x x' : Fin (N + 1)} (W : (nagaokaBondGraph N t).Walk x x') (σ : HoleSpin N x) :
    ∃ τ : HoleSpin N x', StateReach N t ⟨x, σ⟩ ⟨x', τ⟩ := by
  revert σ
  induction W with
  | nil => exact fun σ => ⟨σ, StateReach.refl N t ⟨_, σ⟩⟩
  | @cons u v w h W' ih =>
    intro σ
    have e1 : StateReach N t ⟨u, σ⟩ ⟨v, holeSpinMove N u v σ⟩ :=
      StateReach.holeHop N t htsym htdiag u v σ h.ne (nagaokaBondGraph_adj_pos N t htsym hpos h)
    obtain ⟨τ, hτ⟩ := ih (holeSpinMove N u v σ)
    exact ⟨τ, e1.trans hτ⟩

/-- **Step C (hole relocation): the hole can be moved to any bond-graph-reachable site.**  If site
`x₀` is reachable from the hole position `x` in the bond graph, then `(x, σ)` reaches some state with
the hole at `x₀`.  Specialising `StateReach.exists_ofBondWalk` to a `Reachable` hypothesis, this lets
one reduce sector connectivity to connectivity among states with a *fixed* hole position (where only
the spin configuration varies). -/
theorem StateReach.exists_hole_at (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (hpos : ∀ i j, 0 ≤ t i j)
    {x : Fin (N + 1)} (σ : HoleSpin N x) (x₀ : Fin (N + 1))
    (h : (nagaokaBondGraph N t).Reachable x x₀) :
    ∃ τ : HoleSpin N x₀, StateReach N t ⟨x, σ⟩ ⟨x₀, τ⟩ := by
  obtain ⟨W⟩ := h
  exact StateReach.exists_ofBondWalk N t htsym htdiag hpos W σ

/-- **Step C (triangle transposition from graph adjacency).**  If `x, y, z` are mutually adjacent
in the bond graph (a triangle of bonds), then with the hole at `x` the state `(x, σ)` reaches the
state with the spins at `y` and `z` exchanged (`swapHoleSpin`).  This packages
`StateReach.transposition` with `nagaokaBondGraph_adj_pos`, turning the graph-level triangle
hypothesis (as produced by a length-3 cycle / exchange bond) directly into a reachable spin
transposition. -/
theorem StateReach.transposition_of_triangle (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (hpos : ∀ i j, 0 ≤ t i j)
    {x y z : Fin (N + 1)} (hxy : (nagaokaBondGraph N t).Adj x y)
    (hyz : (nagaokaBondGraph N t).Adj y z) (hzx : (nagaokaBondGraph N t).Adj z x)
    (σ : HoleSpin N x) :
    StateReach N t ⟨x, σ⟩ ⟨x, swapHoleSpin N x y z hxy.ne hzx.ne.symm σ⟩ :=
  StateReach.transposition N t htsym htdiag x y z hxy.ne hyz.ne hzx.ne
    (nagaokaBondGraph_adj_pos N t htsym hpos hxy) (nagaokaBondGraph_adj_pos N t htsym hpos hyz)
    (nagaokaBondGraph_adj_pos N t htsym hpos hzx) σ

/-- **Step C (4-loop 3-cycle from graph adjacency).**  If `x, y, w, z` form a 4-loop of bonds in
the bond graph (consecutive edges `x—y—w—z—x`, with the two diagonals `x ≠ w`, `y ≠ z`), then with
the hole at `x` the state `(x, σ)` reaches the state with the spins at `y, w, z` cyclically permuted
(`cyc3HoleSpin`).  This packages `StateReach.threeCyclePerm` with `nagaokaBondGraph_adj_pos`, turning
a graph-level 4-cycle (as produced by a length-4 cycle / exchange bond) into a reachable spin
3-cycle. -/
theorem StateReach.threeCyclePerm_of_quad (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (hpos : ∀ i j, 0 ≤ t i j)
    {x y w z : Fin (N + 1)} (hxy : (nagaokaBondGraph N t).Adj x y)
    (hyw : (nagaokaBondGraph N t).Adj y w) (hwz : (nagaokaBondGraph N t).Adj w z)
    (hzx : (nagaokaBondGraph N t).Adj z x) (hxw : x ≠ w) (hyz : y ≠ z)
    (σ : HoleSpin N x) :
    StateReach N t ⟨x, σ⟩ ⟨x, cyc3HoleSpin N x y w z hxy.ne hxw hzx.ne.symm σ⟩ :=
  StateReach.threeCyclePerm N t htsym htdiag x y w z hxy.ne hyw.ne hwz.ne hzx.ne hxw hyz
    (nagaokaBondGraph_adj_pos N t htsym hpos hxy) (nagaokaBondGraph_adj_pos N t htsym hpos hyw)
    (nagaokaBondGraph_adj_pos N t htsym hpos hwz) (nagaokaBondGraph_adj_pos N t htsym hpos hzx) σ

/-- **A length-3 closed walk is a triangle of edges.**  A walk `z → z` of length 3 in a simple
graph decomposes as three consecutive adjacencies `z—a`, `a—b`, `b—z`.  This extracts the explicit
triangle (with its three bonds) underlying an exchange bond's length-3 cycle, feeding
`StateReach.transposition_of_triangle`. -/
theorem exists_triangle_adj_of_walk_length_three {V : Type*} (G : SimpleGraph V) {z : V}
    (c : G.Walk z z) (hlen : c.length = 3) :
    ∃ a b : V, G.Adj z a ∧ G.Adj a b ∧ G.Adj b z := by
  match c, hlen with
  | .cons h1 (.cons h2 (.cons h3 .nil)), _ => exact ⟨_, _, h1, h2, h3⟩

/-- **A length-4 closed walk is a 4-loop of edges.**  A walk `z → z` of length 4 in a simple graph
decomposes as four consecutive adjacencies `z—a`, `a—b`, `b—c`, `c—z`.  This extracts the explicit
4-loop (with its four bonds) underlying an exchange bond's length-4 cycle, feeding
`StateReach.threeCyclePerm_of_quad`. -/
theorem exists_quad_adj_of_walk_length_four {V : Type*} (G : SimpleGraph V) {z : V}
    (c : G.Walk z z) (hlen : c.length = 4) :
    ∃ a b d : V, G.Adj z a ∧ G.Adj a b ∧ G.Adj b d ∧ G.Adj d z := by
  match c, hlen with
  | .cons h1 (.cons h2 (.cons h3 (.cons h4 .nil))), _ => exact ⟨_, _, _, h1, h2, h3, h4⟩

/-- **Controlled hole transport along a walk.**  The spin configuration carried by the hole as it
travels along a walk `W : x → x'`, obtained by iterating `holeSpinMove` edge by edge.  Unlike the
existential `StateReach.exists_ofBondWalk`, this records the *exact* resulting configuration, which
is what the "15-puzzle" round-trip argument needs to compute the net spin permutation. -/
def holeWalkTransport (N : ℕ) {G : SimpleGraph (Fin (N + 1))} :
    {x x' : Fin (N + 1)} → G.Walk x x' → HoleSpin N x → HoleSpin N x'
  | _, _, SimpleGraph.Walk.nil, σ => σ
  | x, _, SimpleGraph.Walk.cons (v := v) _ W', σ => holeWalkTransport N W' (holeSpinMove N x v σ)

@[simp] theorem holeWalkTransport_nil (N : ℕ) {G : SimpleGraph (Fin (N + 1))} {x : Fin (N + 1)}
    (σ : HoleSpin N x) : holeWalkTransport N (G := G) SimpleGraph.Walk.nil σ = σ := rfl

@[simp] theorem holeWalkTransport_cons (N : ℕ) {G : SimpleGraph (Fin (N + 1))}
    {x v x' : Fin (N + 1)} (h : G.Adj x v) (W' : G.Walk v x') (σ : HoleSpin N x) :
    holeWalkTransport N (SimpleGraph.Walk.cons h W') σ
      = holeWalkTransport N W' (holeSpinMove N x v σ) := rfl

/-- **Controlled hole mobility: a bond walk reaches the explicitly transported state.**  The state
`(x, σ)` reaches `(x', holeWalkTransport W σ)` — the same reachability as
`StateReach.exists_ofBondWalk`, but with the destination configuration pinned down to the computed
transport.  Proved by induction on `W`, each edge being a `StateReach.holeHop`. -/
theorem StateReach.ofBondWalk (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (hpos : ∀ i j, 0 ≤ t i j)
    {x x' : Fin (N + 1)} (W : (nagaokaBondGraph N t).Walk x x') (σ : HoleSpin N x) :
    StateReach N t ⟨x, σ⟩ ⟨x', holeWalkTransport N W σ⟩ := by
  revert σ
  induction W with
  | nil => exact fun σ => StateReach.refl N t ⟨_, σ⟩
  | @cons u v w h W' ih =>
    intro σ
    have e1 : StateReach N t ⟨u, σ⟩ ⟨v, holeSpinMove N u v σ⟩ :=
      StateReach.holeHop N t htsym htdiag u v σ h.ne (nagaokaBondGraph_adj_pos N t htsym hpos h)
    rw [holeWalkTransport_cons]
    exact e1.trans (ih (holeSpinMove N u v σ))

/-- Moving the hole `x → y` and back `y → x` restores the configuration: `holeSpinMove` for `x ≠ y`
is invertible (its inverse moves the electron back), so the round trip is the identity. -/
theorem holeSpinMove_moveBack (N : ℕ) {x y : Fin (N + 1)} (hxy : x ≠ y) (σ : HoleSpin N x) :
    holeSpinMove N y x (holeSpinMove N x y σ) = σ :=
  (holeSpinMoveEquiv N hxy).left_inv σ

/-- **Hole transport composes along walk concatenation.**  Transporting the configuration along
`W₁ ++ W₂` equals transporting along `W₁` then along `W₂`. -/
theorem holeWalkTransport_append (N : ℕ) {G : SimpleGraph (Fin (N + 1))}
    {x y z : Fin (N + 1)} (W₁ : G.Walk x y) (W₂ : G.Walk y z) (σ : HoleSpin N x) :
    holeWalkTransport N (W₁.append W₂) σ
      = holeWalkTransport N W₂ (holeWalkTransport N W₁ σ) := by
  induction W₁ with
  | nil => rfl
  | @cons a b _ h p ih => simp only [SimpleGraph.Walk.cons_append, holeWalkTransport_cons, ih]

/-- **A round trip restores the configuration.**  Transporting the hole along a walk `W : x → x'`
and then back along its reverse returns the original configuration `σ` — the moving hole permutes
the spins, and the reversed walk inverts that permutation edge by edge.  This is the key tool for
the "15-puzzle" argument: a hole excursion that does not pass through the two sites being exchanged
leaves all spins untouched. -/
theorem holeWalkTransport_reverse (N : ℕ) {G : SimpleGraph (Fin (N + 1))}
    {x x' : Fin (N + 1)} (W : G.Walk x x') (σ : HoleSpin N x) :
    holeWalkTransport N W.reverse (holeWalkTransport N W σ) = σ := by
  induction W with
  | nil => rfl
  | @cons a b _ h p ih =>
    rw [SimpleGraph.Walk.reverse_cons, holeWalkTransport_cons, holeWalkTransport_append,
      holeWalkTransport_cons, holeWalkTransport_nil, ih, holeSpinMove_moveBack N h.ne]

/-- Pointwise value of a hole hop `x → y`: the new hole site `y` becomes `true` (empty orbital
canonicalised), the old hole site `x` receives the spin that was at `y`, every other site is
unchanged. -/
theorem holeSpinMove_val_apply (N : ℕ) (x y : Fin (N + 1)) (σ : HoleSpin N x) (s : Fin (N + 1)) :
    (holeSpinMove N x y σ).val s
      = if s = y then true else if s = x then σ.val y else σ.val s := by
  simp only [holeSpinMove, Function.update_apply]

/-- A single hole hop `x → y` only changes the spins at the old and new hole sites: at any site
`s ∉ {x, y}` the configuration is unchanged. -/
theorem holeSpinMove_apply_of_ne (N : ℕ) {x y : Fin (N + 1)} (σ : HoleSpin N x) {s : Fin (N + 1)}
    (hsx : s ≠ x) (hsy : s ≠ y) : (holeSpinMove N x y σ).val s = σ.val s := by
  rw [holeSpinMove_val_apply, if_neg hsy, if_neg hsx]

/-- **Spins off the hole's path are untouched.**  If the hole's walk `W` never visits site `s`
(`s ∉ W.support`), then transporting along `W` leaves the spin at `s` unchanged.  The hole only ever
rewrites the sites it occupies, so any site outside the walk keeps its value — the precise sense in
which a hole excursion avoiding two sites does not disturb their spins. -/
theorem holeWalkTransport_apply_of_notMem_support (N : ℕ) {G : SimpleGraph (Fin (N + 1))}
    {x x' : Fin (N + 1)} (W : G.Walk x x') (σ : HoleSpin N x) {s : Fin (N + 1)}
    (hs : s ∉ W.support) : (holeWalkTransport N W σ).val s = σ.val s := by
  induction W with
  | nil => rfl
  | @cons a b _ h p ih =>
    rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at hs
    obtain ⟨hsa, hsp⟩ := hs
    rw [holeWalkTransport_cons, ih (holeSpinMove N a b σ) hsp,
      holeSpinMove_apply_of_ne N σ hsa (fun h0 => hsp (h0 ▸ p.start_mem_support))]

/-- **Hole transport depends only on the spins along its path.**  If two configurations agree on
every site of the walk `W`, then transporting either along `W` gives results that still agree on
all of `W`'s sites.  (The hole only ever reads and writes spins at the sites it visits, so values
off the path are irrelevant to the on-path outcome.)  This is the congruence that lets a spin swap
at two *off-path* sites commute through a hole excursion. -/
theorem holeWalkTransport_val_congr (N : ℕ) {G : SimpleGraph (Fin (N + 1))}
    {x x' : Fin (N + 1)} (W : G.Walk x x') :
    ∀ (σ₁ σ₂ : HoleSpin N x), (∀ s ∈ W.support, σ₁.val s = σ₂.val s) →
      ∀ s ∈ W.support, (holeWalkTransport N W σ₁).val s = (holeWalkTransport N W σ₂).val s := by
  induction W with
  | nil => intro σ₁ σ₂ h s hs; simpa using h s hs
  | @cons a b _ hab p ih =>
    intro σ₁ σ₂ h s hs
    have hb : b ∈ (SimpleGraph.Walk.cons hab p).support := by
      rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ p.start_mem_support
    have hbval : σ₁.val b = σ₂.val b := h b hb
    have hmove : ∀ s' ∈ p.support,
        (holeSpinMove N a b σ₁).val s' = (holeSpinMove N a b σ₂).val s' := by
      intro s' hs'
      rw [holeSpinMove_val_apply, holeSpinMove_val_apply]
      by_cases e1 : s' = b
      · simp [e1]
      · by_cases e2 : s' = a
        · rw [if_neg e1, if_neg e1, if_pos e2, if_pos e2, hbval]
        · rw [if_neg e1, if_neg e1, if_neg e2, if_neg e2]
          exact h s' (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hs')
    rw [holeWalkTransport_cons, holeWalkTransport_cons]
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hs
    rcases hs with rfl | hsp
    · by_cases ha : s ∈ p.support
      · exact ih _ _ hmove s ha
      · rw [holeWalkTransport_apply_of_notMem_support N p _ ha,
          holeWalkTransport_apply_of_notMem_support N p _ ha,
          holeSpinMove_val_apply, holeSpinMove_val_apply,
          if_neg hab.ne, if_pos rfl, if_neg hab.ne, if_pos rfl, hbval]
    · exact ih _ _ hmove s hsp

/-- **The 15-puzzle exchange (Lemma 11.9, key step): an exchange bond gives a reachable spin swap
from any hole position.**  Suppose `a, y, z` form a triangle of bonds and the hole, starting at
position `p`, can travel to `a` along a walk `W` that avoids both `y` and `z` (this is what the
exchange-bond condition E2 — connectedness of `Λ ∖ {y, z}` — provides).  Then `(p, σ)` reaches
`(p, swap σ)`, where `swap` exchanges the spins at `y` and `z` and leaves everything else (including
the hole at `p`) unchanged.  The hole is routed to the triangle without disturbing `y, z`, the spins
at `y, z` are swapped by circling the triangle (`transposition_of_triangle`), and the reversed walk
restores all other spins (`holeWalkTransport_reverse` + `holeWalkTransport_val_congr`). -/
theorem StateReach.swap_via_triangle_walk (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (hpos : ∀ i j, 0 ≤ t i j)
    {a y z p : Fin (N + 1)} (hay : (nagaokaBondGraph N t).Adj a y)
    (hyz : (nagaokaBondGraph N t).Adj y z) (hza : (nagaokaBondGraph N t).Adj z a)
    (W : (nagaokaBondGraph N t).Walk p a) (hyW : y ∉ W.support) (hzW : z ∉ W.support)
    (σ : HoleSpin N p) :
    StateReach N t ⟨p, σ⟩
      ⟨p, swapHoleSpin N p y z
        (fun h => hyW (h ▸ W.start_mem_support)) (fun h => hzW (h ▸ W.start_mem_support)) σ⟩ := by
  -- supports of W and its reverse coincide
  have hyWr : y ∉ W.reverse.support := by
    rw [SimpleGraph.Walk.support_reverse]; simpa using hyW
  have hzWr : z ∉ W.reverse.support := by
    rw [SimpleGraph.Walk.support_reverse]; simpa using hzW
  set σa := holeWalkTransport N W σ with hσa
  set C := swapHoleSpin N a y z hay.ne hza.ne.symm σa with hC
  -- the three legs: hole p→a, triangle swap at a, hole a→p
  have r1 : StateReach N t ⟨p, σ⟩ ⟨a, σa⟩ := StateReach.ofBondWalk N t htsym htdiag hpos W σ
  have r2 : StateReach N t ⟨a, σa⟩ ⟨a, C⟩ :=
    StateReach.transposition_of_triangle N t htsym htdiag hpos hay hyz hza σa
  have r3 : StateReach N t ⟨a, C⟩ ⟨p, holeWalkTransport N W.reverse C⟩ :=
    StateReach.ofBondWalk N t htsym htdiag hpos W.reverse C
  -- σa agrees with σ at y and z (the walk avoids them)
  have hσay : σa.val y = σ.val y := holeWalkTransport_apply_of_notMem_support N W σ hyW
  have hσaz : σa.val z = σ.val z := holeWalkTransport_apply_of_notMem_support N W σ hzW
  -- the net transported configuration is exactly the (y z) swap of σ
  have hnet : holeWalkTransport N W.reverse C
      = swapHoleSpin N p y z (fun h => hyW (h ▸ W.start_mem_support))
          (fun h => hzW (h ▸ W.start_mem_support)) σ := by
    apply Subtype.ext
    funext s
    rw [swapHoleSpin_val_apply]
    by_cases hsy : s = y
    · subst hsy
      rw [holeWalkTransport_apply_of_notMem_support N W.reverse C hyWr, hC,
        swapHoleSpin_val_apply, if_pos rfl, hσaz, if_pos rfl]
    · by_cases hsz : s = z
      · subst hsz
        rw [holeWalkTransport_apply_of_notMem_support N W.reverse C hzWr, hC,
          swapHoleSpin_val_apply, if_neg hsy, if_pos rfl, hσay, if_neg hsy, if_pos rfl]
      · rw [if_neg hsy, if_neg hsz]
        by_cases hsW : s ∈ W.reverse.support
        · -- on-path: use congruence + round trip (C and σa agree on the path)
          have hagree : ∀ u ∈ W.reverse.support, C.val u = σa.val u := by
            intro u hu
            have huy : u ≠ y := fun h => hyWr (h ▸ hu)
            have huz : u ≠ z := fun h => hzWr (h ▸ hu)
            rw [hC, swapHoleSpin_val_apply, if_neg huy, if_neg huz]
          rw [← holeWalkTransport_val_congr N W.reverse σa C
            (fun u hu => (hagree u hu).symm) s hsW, hσa, holeWalkTransport_reverse N W σ]
        · -- off-path: both untouched, C agrees with σa, σa agrees with σ
          rw [holeWalkTransport_apply_of_notMem_support N W.reverse C hsW, hC,
            swapHoleSpin_val_apply, if_neg hsy, if_neg hsz,
            holeWalkTransport_apply_of_notMem_support N W σ
              (fun h => hsW (by rw [SimpleGraph.Walk.support_reverse]; simpa using h))]
  rw [← hnet]
  exact (r1.trans r2).trans r3

/-- The inclusion `G.induce s →g G` sending a vertex of the induced subgraph to the underlying
vertex.  (Induced adjacency is just the ambient adjacency restricted to `s`.) -/
def induceValHom {V : Type*} (G : SimpleGraph V) (s : Set V) : G.induce s →g G where
  toFun := Subtype.val
  map_rel' := fun {_ _} h => h

/-- **E2 routing: a walk avoiding two sites.**  If the subgraph induced on `Λ ∖ {y, z}` is connected
and `p, a` both avoid `y, z`, then there is a walk `p → a` in the full graph whose support avoids
both `y` and `z`.  This realises Tasaki's exchange-bond condition E2 (deleting the two exchanged
sites keeps the lattice connected) as a concrete hole route that never touches `y` or `z`, feeding
`StateReach.swap_via_triangle_walk`. -/
theorem exists_avoiding_walk_of_induce_connected {V : Type*} (G : SimpleGraph V) {y z : V}
    (hconn : (G.induce {w | w ≠ y ∧ w ≠ z}).Connected) {p a : V}
    (hp : p ≠ y ∧ p ≠ z) (ha : a ≠ y ∧ a ≠ z) :
    ∃ W : G.Walk p a, y ∉ W.support ∧ z ∉ W.support := by
  obtain ⟨W'⟩ := hconn.preconnected ⟨p, hp⟩ ⟨a, ha⟩
  have hsupp : ∀ x ∈ (W'.map (induceValHom G {w | w ≠ y ∧ w ≠ z})).support,
      x ≠ y ∧ x ≠ z := by
    intro x hx
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hx
    obtain ⟨⟨v, hv⟩, _, rfl⟩ := hx
    exact hv
  exact ⟨W'.map (induceValHom G _), fun hy => (hsupp y hy).1 rfl, fun hz => (hsupp z hz).2 rfl⟩

end LatticeSystem.Fermion

