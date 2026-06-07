import LatticeSystem.Fermion.JordanWigner.Hubbard.TJHalfFillingBondAction
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJHalfFillingBondGround
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJFillingBasis

/-!
# Tasaki 11.5.3: half-filling ground amplitudes are spin-swap invariant (Theorem 11.26 PR3i-3a)

A half-filling ground state `v` is annihilated by every bond (`tJ_ground_bond_mulVec_eq_zero`,
PR3i-2), and the bond acts as a half spin-swap on the configuration basis
(`tJExchangeBond_mulVec_tJConfigOf_full`, PR3i-1).  Expanding `v` in the filling basis and reading
off the coefficient of `|Φ_{s}⟩` therefore equates the amplitudes of a configuration and its swap:

* `tJ_ground_amplitude_swap_invariant` — for an adjacent bond `⟨x,y⟩`,
  `v (tJConfigOf s) = v (tJConfigOf (tJSpinSwap s x y))`.

A connected graph's edge swaps generate the full symmetric group, so iterating this makes the ground
amplitudes depend only on the up-count — the route to the degeneracy upper bound `finrank ≤ N+2`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.3, Theorem 11.26 (pp. 445–447).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph
open scoped BigOperators

variable {N : ℕ}

/-- The spin-swap is an involution on site-states. -/
theorem tJSpinSwap_involutive_site (s : Fin (N + 1) → Fin 3) (x y : Fin (N + 1)) :
    tJSpinSwap (tJSpinSwap s x y) x y = s := by
  funext k
  simp only [tJSpinSwap_eq_comp_swap, Equiv.swap_apply_self]

/-- The spin-swap as a permutation of the half-filling sector (it preserves the up/down counts). -/
def tJFillingSwap (x y : Fin (N + 1)) (s : TJFillingSector N (N + 1)) : TJFillingSector N (N + 1) :=
  ⟨tJSpinSwap s.val x y, by rw [tJSpinSwap_count, tJSpinSwap_count]; exact s.2⟩

/-- The underlying site-state of the sector spin-swap is the site-state spin-swap. -/
@[simp] theorem tJFillingSwap_val (x y : Fin (N + 1)) (s : TJFillingSector N (N + 1)) :
    (tJFillingSwap x y s).val = tJSpinSwap s.val x y := rfl

/-- **Half-filling ground amplitudes are bond-swap invariant.**  For a ground state `v` and an
adjacent bond `⟨x,y⟩`, `v (tJConfigOf s) = v (tJConfigOf (tJSpinSwap s x y))`. -/
theorem tJ_ground_amplitude_swap_invariant (τ J : ℝ) (hJ : 0 < J)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hv : v ∈ groundSubmoduleAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) (N + 1))
    (x y : Fin (N + 1)) (hadj : (cycleGraph (N + 1)).Adj x y)
    (s : TJFillingSector N (N + 1)) :
    v (tJConfigOf N s.val) = v (tJConfigOf N (tJSpinSwap s.val x y)) := by
  classical
  have hhc : v ∈ hubbardHardcoreSubspace N := hv.2
  have hN : (fermionTotalNumber (2 * N + 1)).mulVec v = ((N + 1 : ℕ) : ℂ) • v := by
    have := hv.1.2
    rwa [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at this
  have hbz := tJ_ground_bond_mulVec_eq_zero τ J hJ hv x y hadj
  set f : TJFillingSector N (N + 1) → ℂ := tJFillingExpansionCoeff N (N + 1) v with hf
  have hcoeff : ∀ t : TJFillingSector N (N + 1), f t = v (tJConfigOf N t.val) := fun t => by
    rw [hf, tJFillingExpansionCoeff, basisVec_sum_mul]
  -- per-summand value of `bond_xy v` at the index `tJConfigOf s`
  have hterm : ∀ t : TJFillingSector N (N + 1),
      (((1 / 4 : ℂ) • (fermionSiteNumber N x * fermionSiteNumber N y) -
          fermionSpinDot N x y).mulVec (f t • basisVec (tJConfigOf N t.val))) (tJConfigOf N s.val)
        = (1 / 2 : ℂ) *
            ((if t = s then f t else 0) - (if t = tJFillingSwap x y s then f t else 0)) := by
    intro t
    rw [Matrix.mulVec_smul,
      tJExchangeBond_mulVec_tJConfigOf_full N t.val x y hadj.ne
        (tJFillingSector_full t x) (tJFillingSector_full t y),
      Pi.smul_apply, Pi.smul_apply, Pi.sub_apply, basisVec_apply, basisVec_apply, smul_eq_mul,
      smul_eq_mul]
    have e1 : (if tJConfigOf N s.val = tJConfigOf N t.val then (1 : ℂ) else 0)
        = if t = s then 1 else 0 := by
      by_cases h : t = s
      · rw [if_pos h, if_pos (by rw [h])]
      · rw [if_neg h, if_neg (fun hc => h (Subtype.ext (tJConfigOf_injective N hc).symm))]
    have e2 : (if tJConfigOf N s.val = tJConfigOf N (tJSpinSwap t.val x y) then (1 : ℂ) else 0)
        = if t = tJFillingSwap x y s then 1 else 0 := by
      by_cases h : t = tJFillingSwap x y s
      · rw [if_pos h, if_pos (by rw [h, tJFillingSwap_val, tJSpinSwap_involutive_site])]
      · rw [if_neg h, if_neg]
        intro hc
        apply h
        apply Subtype.ext
        rw [tJFillingSwap_val, tJConfigOf_injective N hc, tJSpinSwap_involutive_site]
    rw [e1, e2]
    split_ifs <;> ring
  have hval : ((1 / 4 : ℂ) • (fermionSiteNumber N x * fermionSiteNumber N y) -
        fermionSpinDot N x y).mulVec v (tJConfigOf N s.val)
      = (1 / 2 : ℂ) *
        (v (tJConfigOf N s.val) - v (tJConfigOf N (tJSpinSwap s.val x y))) := by
    conv_lhs => rw [tJ_filling_completeness (N + 1) v hhc hN, tJFillingExpansion, ← hf]
    rw [Matrix.mulVec_sum, Finset.sum_apply, Finset.sum_congr rfl (fun t _ => hterm t),
      ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' Finset.univ s f, Finset.sum_ite_eq' Finset.univ (tJFillingSwap x y s) f,
      if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _), hcoeff s, hcoeff]
    rw [tJFillingSwap_val]
  rw [hbz, Pi.zero_apply] at hval
  have h2 : (1 / 2 : ℂ) ≠ 0 := by norm_num
  have hzero : v (tJConfigOf N s.val) - v (tJConfigOf N (tJSpinSwap s.val x y)) = 0 :=
    (mul_eq_zero.mp hval.symm).resolve_left h2
  exact sub_eq_zero.mp hzero

end LatticeSystem.Fermion
