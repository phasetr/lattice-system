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

end LatticeSystem.Fermion

