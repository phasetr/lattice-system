import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandWeightSupport
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandModePeel
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandDoubleOcc
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandSwapCoeffCore

/-!
# Tasaki §11.3.1: the no-double-occupancy spin-swap coefficient relation (toward block ≤ 1)

Applying the double annihilation `ĉ_{int(p)↓} ĉ_{int(p)↑}` (which kills a ground vector) and reading
one occupation-basis coordinate isolates exactly the two orbital-spin configurations that differ by
swapping the spins of the overlapping orbitals `p` and `p+1`: only `α_p` and `α_{p+1}` are supported
at the shared internal site `int(p)` (both with amplitude `−ν`).  The two contributions carry the
same scalar `ν²` and a relative Koszul sign of `−1` — *independent* of where `p, p+1` sit in the
occupation list — so the two coefficients are equal: `c_S = c_{S with p,(p+1) spins swapped}`.

This file sets up the position-independent Koszul sign identity and the orbital-spin ↔ occupation
config map; the coefficient extraction and the swap relation itself follow.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1.  Tracked in Issue #4346.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {K : ℕ} {ν : ℝ}
/-- **A β-free, non-doubly-occupied, half-filled config is an α-spin config.**  Its occupation set
equals that of `αs'` for `s' q := (the spin occupied at orbital q)`.  Subset (each occupied mode is
at its `s'`-spin, by no double occupancy) plus equal cardinality `K+1` forces equality. -/
theorem flatBand_occFinset_eq_alphaSpinOcc_of_betaFree_noDouble
    (f : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2)
    (hbf : ∀ q' ∈ occFinset f, ∃ r, q'.1 = Sum.inl r)
    (hnd : ∀ q : Fin (K + 1),
      ¬((Sum.inl q, (0 : Fin 2)) ∈ occFinset f ∧ (Sum.inl q, (1 : Fin 2)) ∈ occFinset f))
    (hcard : (occFinset f).card = K + 1) :
    occFinset f = occFinset (flatBandAlphaSpinOcc K
      (fun q => if (Sum.inl q, (0 : Fin 2)) ∈ occFinset f then 0 else 1)) := by
  refine Finset.eq_of_subset_of_card_le (fun x hx => ?_)
    (by rw [occFinset_alphaSpinOcc_card, hcard])
  obtain ⟨r, hr⟩ := hbf x hx
  rw [mem_occFinset_alphaSpinOcc]
  refine ⟨r, Prod.ext hr ?_⟩
  change x.2 = if (Sum.inl r, (0 : Fin 2)) ∈ occFinset f then (0 : Fin 2) else 1
  have hlt := x.2.isLt
  by_cases h0 : (Sum.inl r, (0 : Fin 2)) ∈ occFinset f
  · rw [if_pos h0]
    by_contra hne
    have hx1 : x.2 = 1 := by
      rcases (by omega : x.2.val = 0 ∨ x.2.val = 1) with h | h
      · exact absurd (Fin.ext h) hne
      · exact Fin.ext h
    have hxe : x = (Sum.inl r, (1 : Fin 2)) := Prod.ext hr hx1
    rw [hxe] at hx
    exact hnd r ⟨h0, hx⟩
  · rw [if_neg h0]
    have hx0 : x.2 ≠ 0 := by
      intro hc
      have hxe : x = (Sum.inl r, (0 : Fin 2)) := Prod.ext hr hc
      rw [hxe] at hx
      exact h0 hx
    rcases (by omega : x.2.val = 0 ∨ x.2.val = 1) with h | h
    · exact absurd (Fin.ext h) hx0
    · exact Fin.ext h

/-- **Only matching-two-hole opposite-spin α-configs survive the internal coordinate read.**  If the
two-hole coordinate of `ĉ_{int(p)↓}ĉ_{int(p)↑}` applied to `occMonomial(αs')` is nonzero, then `s'`
carries opposite pair spins and its two-hole config matches that of `s`. -/
theorem flatBand_cDownUp_int_occMonomial_repr_ne_zero_imp (hν : 0 < ν)
    (s s' : Fin (K + 1) → Fin 2) (p : Fin K)
    (hne : (flatBandOccBasis K ν).repr
        ((cDownUp K (deltaInternalSite K p.castSucc)).mulVec
          (occMonomial K ν (flatBandAlphaSpinOcc K s'))) (flatBandAlphaTwoHoleOcc K s p.castSucc)
      ≠ 0) :
    s' p.castSucc ≠ s' p.succ ∧
      flatBandAlphaTwoHoleOcc K s' p.castSucc = flatBandAlphaTwoHoleOcc K s p.castSucc := by
  have hdich : ∀ t : Fin 2, t = 0 ∨ t = 1 := by
    intro t
    rcases (by omega : t.val = 0 ∨ t.val = 1) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  by_cases hsame : s' p.castSucc = s' p.succ
  · exact absurd (by rw [flatBand_cDownUp_int_occMonomial_same s' p hsame, map_zero,
      Finsupp.zero_apply]) hne
  refine ⟨hsame, ?_⟩
  by_contra htw
  apply hne
  rcases hdich (s' p.castSucc) with h0 | h1
  · have h1 : s' p.succ = 1 := by
      rcases hdich (s' p.succ) with h | h
      · exact absurd (h0.trans h.symm) hsame
      · exact h
    obtain ⟨z, _, hz⟩ := flatBand_cDownUp_int_occMonomial_canonical hν s' p h0 h1
    rw [hz, map_smul, Finsupp.smul_apply, smul_eq_mul, ← flatBandOccBasis_apply,
      (flatBandOccBasis K ν).repr_self_apply, if_neg htw, mul_zero]
  · have h0 : s' p.succ = 0 := by
      rcases hdich (s' p.succ) with h | h
      · exact h
      · exact absurd (h1.trans h.symm) hsame
    obtain ⟨z, _, hz⟩ := flatBand_cDownUp_int_occMonomial_swap hν s' p h1 h0
    rw [hz, map_smul, Finsupp.smul_apply, smul_eq_mul, ← flatBandOccBasis_apply,
      (flatBandOccBasis K ν).repr_self_apply, if_neg htw, mul_zero]

/-- An occupation config (a `Fin 2`-valued function) is determined by its occupation finset. -/
theorem config_eq_of_occFinset_eq (f g : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2)
    (h : occFinset f = occFinset g) : f = g := by
  funext q
  have hiff := Finset.ext_iff.mp h q
  simp only [occFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hiff
  have hf2 := (f q).isLt
  have hg2 := (g q).isLt
  by_cases hf : f q = 1
  · rw [hf, hiff.mp hf]
  · have hg : g q ≠ 1 := fun hg => hf (hiff.mpr hg)
    rw [Fin.ext (by have := Fin.val_ne_of_ne hf; omega : (f q).val = (g q).val)]

/-- The occupation monomial depends only on the occupation finset. -/
theorem occMonomial_congr (f g : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2)
    (h : occFinset f = occFinset g) :
    occMonomial K ν f = occMonomial K ν g := by
  rw [occMonomial, occMonomial, h]

/-- **Two-hole configs with opposite pair spins coincide only for `s` and its pair-swap.**  If the
two-hole occupations of `s'` and `s` agree and `s'` carries opposite spins on the pair `p, p+1`,
then `s'` is `s` itself or `s` with the pair spins swapped (it must agree with `s` off the pair). -/
theorem flatBand_alphaTwoHoleOcc_eq_imp (s s' : Fin (K + 1) → Fin 2) (p : Fin K)
    (hs0 : s p.castSucc = 0) (hs1 : s p.succ = 1) (hopp : s' p.castSucc ≠ s' p.succ)
    (heq : flatBandAlphaTwoHoleOcc K s' p.castSucc = flatBandAlphaTwoHoleOcc K s p.castSucc) :
    s' = s ∨ s' = Function.update (Function.update s p.castSucc 1) p.succ 0 := by
  have hdich : ∀ t : Fin 2, t = 0 ∨ t = 1 := by
    intro t
    rcases (by omega : t.val = 0 ∨ t.val = 1) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have hne : p.castSucc ≠ p.succ := by
    intro h; have := congrArg Fin.val h; rw [Fin.val_succ, Fin.val_castSucc] at this; omega
  have hoff : ∀ q, q ≠ p.castSucc → q ≠ p.succ → s' q = s q := by
    intro q hq0 hq1
    have hc := congrFun heq (Sum.inl q, s' q)
    have hcond : ¬((Sum.inl q : Fin (K + 1) ⊕ Fin (K + 1)) = Sum.inl p.castSucc ∨
        (Sum.inl q : Fin (K + 1) ⊕ Fin (K + 1)) = Sum.inl (p.castSucc + 1)) := by
      rw [← flatBand_succ_eq_castSucc_add_one p, not_or]
      exact ⟨fun h => hq0 (Sum.inl_injective h), fun h => hq1 (Sum.inl_injective h)⟩
    simp only [flatBandAlphaTwoHoleOcc] at hc
    rw [if_neg hcond, if_neg hcond, flatBandAlphaSpinOcc_inl, flatBandAlphaSpinOcc_inl,
      if_pos rfl] at hc
    by_contra hsq
    rw [if_neg hsq] at hc
    exact absurd hc (by decide)
  have hswap0 : Function.update (Function.update s p.castSucc 1) p.succ 0 p.castSucc = 1 := by
    rw [Function.update_of_ne hne, Function.update_self]
  have hswap1 : Function.update (Function.update s p.castSucc 1) p.succ 0 p.succ = 0 :=
    Function.update_self _ _ _
  rcases hdich (s' p.castSucc) with hc0 | hc1
  · left
    funext q
    by_cases hq0 : q = p.castSucc
    · rw [hq0, hc0, hs0]
    · by_cases hq1 : q = p.succ
      · rw [hq1, hs1]
        rcases hdich (s' p.succ) with h | h
        · exact absurd (hc0.trans h.symm) hopp
        · exact h
      · exact hoff q hq0 hq1
  · right
    funext q
    by_cases hq0 : q = p.castSucc
    · rw [hq0, hc1, hswap0]
    · by_cases hq1 : q = p.succ
      · rw [hq1, hswap1]
        rcases hdich (s' p.succ) with h | h
        · exact h
        · exact absurd (hc1.trans h.symm) hopp
      · rw [hoff q hq0 hq1, Function.update_of_ne hq1, Function.update_of_ne hq0]

/-- **No orbital double occupancy in the half-filled ground subspace.**  A β-free occupation config
`g` that doubly occupies an orbital `q₀` has vanishing ground-state coordinate.  Reading the
`(q₀`-pair-erased) coordinate of `0 = ĉ_{ext(q₀)↓} ĉ_{ext(q₀)↑} v` isolates exactly the `g` term
(β-occupied configs are killed by the b̂-kernel; β-free non-doubly-occupied ones by the external
double annihilation), forcing `z_g · repr(v, g) = 0` with `z_g ≠ 0`. -/
theorem flatBandOccBasis_repr_eq_zero_of_doubleOcc (K : ℕ) (ν t U : ℝ) (ht : 0 < t) (hU : 0 < U)
    {v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ}
    (hv : v ∈ flatBandHalfFilledGroundSubmodule K ν t U) {q₀ : Fin (K + 1)}
    {g : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2}
    (hgbf : ∀ q' ∈ occFinset g, ∃ r, q'.1 = Sum.inl r)
    (hg0 : (Sum.inl q₀, (0 : Fin 2)) ∈ occFinset g)
    (hg1 : (Sum.inl q₀, (1 : Fin 2)) ∈ occFinset g) :
    (flatBandOccBasis K ν).repr v g = 0 := by
  classical
  have hE : rayleighOnVec (flatBandHamiltonian K ν t U) v = 0 := by
    rw [flatBandHalfFilledGroundSubmodule, Submodule.mem_inf] at hv
    obtain ⟨hker, _⟩ := hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hker
    unfold rayleighOnVec; rw [hker, dotProduct_zero, Complex.zero_re]
  have hcd := flatBand_groundState_doubleAnnihilation_mulVec_eq_zero K ν t U ht.le hU hE
    (deltaExternalSite K q₀)
  have hBK := flatBand_groundState_mem_BKernelSubmodule K ν t U ht hU.le hE
  -- the q₀-pair-erased config of g
  set h := Function.update (Function.update g (Sum.inl q₀, 0) 0) (Sum.inl q₀, 1) 0 with hh
  have hocch : occFinset h = ((occFinset g).erase (Sum.inl q₀, 0)).erase (Sum.inl q₀, 1) := by
    rw [hh, occFinset_update_zero, occFinset_update_zero]
  obtain ⟨zg, hzg0, hzg⟩ := flatBand_cDownUp_ext_betaFree_double K ν q₀ g hgbf hg0 hg1
  -- expand the h-coordinate of `cDownUp(ext q₀) v`
  have hexp : (flatBandOccBasis K ν).repr ((cDownUp K (deltaExternalSite K q₀)).mulVec v) h
      = ∑ f, (flatBandOccBasis K ν).repr v f *
          (flatBandOccBasis K ν).repr
            ((cDownUp K (deltaExternalSite K q₀)).mulVec (occMonomial K ν f)) h := by
    conv_lhs => rw [← (flatBandOccBasis K ν).sum_repr v]
    rw [Matrix.mulVec_sum, map_sum, Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [flatBandOccBasis_apply, Matrix.mulVec_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [hcd, map_zero, Finsupp.zero_apply] at hexp
  -- only f = g contributes
  rw [Finset.sum_eq_single g] at hexp
  · -- g term: repr(cDownUp occMonomial g)(h) = zg
    rw [hzg, map_smul, Finsupp.smul_apply, smul_eq_mul] at hexp
    have hmono : flatBandModeMonomial K ν
        (((occFinset g).erase (Sum.inl q₀, 0)).erase (Sum.inl q₀, 1)).toList
        = occMonomial K ν h := by rw [occMonomial, hocch]
    rw [hmono, ← flatBandOccBasis_apply, (flatBandOccBasis K ν).repr_self_apply, if_pos rfl,
      mul_one] at hexp
    exact (mul_eq_zero.mp hexp.symm).resolve_right hzg0
  · -- f ≠ g term vanishes
    intro f _ hfg
    by_cases hfbf : ∀ q' ∈ occFinset f, ∃ r, q'.1 = Sum.inl r
    · by_cases hfd : (Sum.inl q₀, (0 : Fin 2)) ∈ occFinset f ∧
          (Sum.inl q₀, (1 : Fin 2)) ∈ occFinset f
      · -- β-free, doubly-occ, but f ≠ g ⇒ erased coordinate differs
        obtain ⟨zf, _, hzf⟩ := flatBand_cDownUp_ext_betaFree_double K ν q₀ f hfbf hfd.1 hfd.2
        rw [hzf, map_smul, Finsupp.smul_apply, smul_eq_mul]
        have hmono : flatBandModeMonomial K ν
            (((occFinset f).erase (Sum.inl q₀, 0)).erase (Sum.inl q₀, 1)).toList
            = occMonomial K ν (Function.update (Function.update f (Sum.inl q₀, 0) 0)
                (Sum.inl q₀, 1) 0) := by
          rw [occMonomial, occFinset_update_zero, occFinset_update_zero]
        rw [hmono, ← flatBandOccBasis_apply, (flatBandOccBasis K ν).repr_self_apply, if_neg ?_,
          mul_zero, mul_zero]
        -- the erased configs differ since f ≠ g
        intro heq
        apply hfg
        funext m
        by_cases hma : m = (Sum.inl q₀, 0)
        · rw [hma]
          exact (mem_occFinset_iff f _).mp hfd.1 |>.trans ((mem_occFinset_iff g _).mp hg0).symm
        · by_cases hmb : m = (Sum.inl q₀, 1)
          · rw [hmb]
            exact (mem_occFinset_iff f _).mp hfd.2 |>.trans ((mem_occFinset_iff g _).mp hg1).symm
          · have := congrFun heq m
            simp only [hh, Function.update_of_ne hma, Function.update_of_ne hmb] at this
            exact this
      · -- β-free, not doubly-occ ⇒ cDownUp annihilates
        rw [not_and_or] at hfd
        rw [flatBand_cDownUp_ext_betaFree_eq_zero_of_not_double K ν q₀ f hfbf hfd, map_zero,
          Finsupp.zero_apply, mul_zero]
    · -- not β-free ⇒ repr(v, f) = 0 by b̂-kernel
      simp only [not_forall, not_exists] at hfbf
      obtain ⟨q', hq'occ, hq'⟩ := hfbf
      obtain ⟨u, hu⟩ : ∃ u, q'.1 = Sum.inr u := by
        cases hq'1 : q'.1 with
        | inl r => exact absurd hq'1 (by simpa using hq' r)
        | inr u => exact ⟨u, rfl⟩
      have : (Sum.inr u, q'.2) ∈ occFinset f := by
        have : (Sum.inr u, q'.2) = q' := Prod.ext hu.symm rfl
        rwa [this]
      rw [flatBandOccBasis_repr_eq_zero_of_mem_BKernel u q'.2 hBK this, zero_mul]
  · intro hg_notin; exact absurd (Finset.mem_univ g) hg_notin

/-- **Adjacent spin-swap leaves the ground coordinate-vanishing invariant (Marshall sign).**  For a
ground vector `v` and an α-config `s` carrying `(↑, ↓)` on the pair `p, p+1`, the occupation
coordinate at `αs` vanishes iff it vanishes at the pair-swapped config.  Reading the two-hole
coordinate of `0 = ĉ_{int(p)↓} ĉ_{int(p)↑} v` isolates exactly the `αs` and pair-swap terms, with
nonzero relative weights `z_s, z_swap`. -/
theorem flatBand_ground_repr_alphaSpinOcc_swap_iff (K : ℕ) (ν t U : ℝ) (hν : 0 < ν) (ht : 0 < t)
    (hU : 0 < U) {v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ}
    (hv : v ∈ flatBandHalfFilledGroundSubmodule K ν t U)
    (p : Fin K) (s : Fin (K + 1) → Fin 2) (hs0 : s p.castSucc = 0) (hs1 : s p.succ = 1) :
    (flatBandOccBasis K ν).repr v (flatBandAlphaSpinOcc K s) = 0 ↔
      (flatBandOccBasis K ν).repr v (flatBandAlphaSpinOcc K
        (Function.update (Function.update s p.castSucc 1) p.succ 0)) = 0 := by
  classical
  have hpne : p.castSucc ≠ p.succ := by
    intro h; have := congrArg Fin.val h; rw [Fin.val_succ, Fin.val_castSucc] at this; omega
  have hE : rayleighOnVec (flatBandHamiltonian K ν t U) v = 0 := by
    rw [flatBandHalfFilledGroundSubmodule, Submodule.mem_inf] at hv
    obtain ⟨hker, _⟩ := hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hker
    unfold rayleighOnVec; rw [hker, dotProduct_zero, Complex.zero_re]
  have hcd := flatBand_groundState_doubleAnnihilation_mulVec_eq_zero K ν t U ht.le hU hE
    (deltaInternalSite K p.castSucc)
  have hBK := flatBand_groundState_mem_BKernelSubmodule K ν t U ht hU.le hE
  set s_sw := Function.update (Function.update s p.castSucc 1) p.succ 0 with hssw
  have hsw0 : s_sw p.castSucc = 1 := by rw [hssw, Function.update_of_ne hpne, Function.update_self]
  have hsw1 : s_sw p.succ = 0 := by rw [hssw, Function.update_self]
  have hαne : flatBandAlphaSpinOcc K s ≠ flatBandAlphaSpinOcc K s_sw := by
    intro h
    have hh := congrFun h (Sum.inl p.castSucc, 0)
    rw [flatBandAlphaSpinOcc_inl, flatBandAlphaSpinOcc_inl, hs0, hsw0] at hh
    simp at hh
  obtain ⟨zs, hzs0, hzseq⟩ := flatBand_cDownUp_int_occMonomial_canonical hν s p hs0 hs1
  obtain ⟨zsw, hzsw0, hzsweq⟩ := flatBand_cDownUp_int_occMonomial_swap hν s_sw p hsw0 hsw1
  have htwsw : flatBandAlphaTwoHoleOcc K s_sw p.castSucc
      = flatBandAlphaTwoHoleOcc K s p.castSucc := by
    rw [hssw, flatBand_succ_eq_castSucc_add_one p]
    exact flatBandAlphaTwoHoleOcc_swap_eq K s p.castSucc
  -- expand the two-hole coordinate of `cDownUp(int p) v`
  have hexp : (flatBandOccBasis K ν).repr
        ((cDownUp K (deltaInternalSite K p.castSucc)).mulVec v)
        (flatBandAlphaTwoHoleOcc K s p.castSucc)
      = ∑ f, (flatBandOccBasis K ν).repr v f *
          (flatBandOccBasis K ν).repr
            ((cDownUp K (deltaInternalSite K p.castSucc)).mulVec (occMonomial K ν f))
            (flatBandAlphaTwoHoleOcc K s p.castSucc) := by
    conv_lhs => rw [← (flatBandOccBasis K ν).sum_repr v]
    rw [Matrix.mulVec_sum, map_sum, Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [flatBandOccBasis_apply, Matrix.mulVec_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [hcd, map_zero, Finsupp.zero_apply] at hexp
  have hca : (flatBandOccBasis K ν).repr ((cDownUp K (deltaInternalSite K p.castSucc)).mulVec
        (occMonomial K ν (flatBandAlphaSpinOcc K s)))
        (flatBandAlphaTwoHoleOcc K s p.castSucc) = zs := by
    rw [hzseq, map_smul, Finsupp.smul_apply, smul_eq_mul, ← flatBandOccBasis_apply,
      (flatBandOccBasis K ν).repr_self_apply, if_pos rfl, mul_one]
  have hcsw : (flatBandOccBasis K ν).repr ((cDownUp K (deltaInternalSite K p.castSucc)).mulVec
        (occMonomial K ν (flatBandAlphaSpinOcc K s_sw)))
        (flatBandAlphaTwoHoleOcc K s p.castSucc) = zsw := by
    rw [hzsweq, htwsw, map_smul, Finsupp.smul_apply, smul_eq_mul, ← flatBandOccBasis_apply,
      (flatBandOccBasis K ν).repr_self_apply, if_pos rfl, mul_one]
  rw [← Finset.sum_subset
      (Finset.subset_univ {flatBandAlphaSpinOcc K s, flatBandAlphaSpinOcc K s_sw}) ?_,
    Finset.sum_pair hαne, hca, hcsw] at hexp
  · constructor
    · intro h
      rw [h, zero_mul, zero_add] at hexp
      exact (mul_eq_zero.mp hexp.symm).resolve_right hzsw0
    · intro h
      rw [h, zero_mul, add_zero] at hexp
      exact (mul_eq_zero.mp hexp.symm).resolve_right hzs0
  -- the off-{αs, αsw} terms vanish
  intro f _ hf
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hf
  by_cases hrv : (flatBandOccBasis K ν).repr v f = 0
  · rw [hrv, zero_mul]
  · have hbf : ∀ q' ∈ occFinset f, ∃ r, q'.1 = Sum.inl r := by
      intro q' hq'
      by_contra hcon
      apply hrv
      obtain ⟨u, hu⟩ : ∃ u, q'.1 = Sum.inr u := by
        cases hq1 : q'.1 with
        | inl r => exact absurd ⟨r, hq1⟩ hcon
        | inr u => exact ⟨u, rfl⟩
      have hmem : (Sum.inr u, q'.2) ∈ occFinset f := by
        rw [show (Sum.inr u, q'.2) = q' from Prod.ext hu.symm rfl]; exact hq'
      exact flatBandOccBasis_repr_eq_zero_of_mem_BKernel u q'.2 hBK hmem
    have hnd : ∀ q : Fin (K + 1),
        ¬((Sum.inl q, (0 : Fin 2)) ∈ occFinset f ∧ (Sum.inl q, (1 : Fin 2)) ∈ occFinset f) :=
      fun q hd => hrv (flatBandOccBasis_repr_eq_zero_of_doubleOcc K ν t U ht hU hv hbf hd.1 hd.2)
    have hcard : (occFinset f).card = K + 1 := by
      by_contra hc; exact hrv (flatBandOccBasis_repr_eq_zero_of_card_ne t U hv hc)
    have hrecon := flatBand_occFinset_eq_alphaSpinOcc_of_betaFree_noDouble f hbf hnd hcard
    rw [occMonomial_congr f _ hrecon]
    by_contra hcoord
    obtain ⟨hopp, htweq⟩ := flatBand_cDownUp_int_occMonomial_repr_ne_zero_imp hν s _ p
      (fun h => hcoord (by rw [h, mul_zero]))
    rcases flatBand_alphaTwoHoleOcc_eq_imp s _ p hs0 hs1 hopp htweq with hs's | hs'sw
    · exact hf.1 (config_eq_of_occFinset_eq f (flatBandAlphaSpinOcc K s) (by rw [hrecon, hs's]))
    · exact hf.2 (config_eq_of_occFinset_eq f (flatBandAlphaSpinOcc K s_sw) (by rw [hrecon, hs'sw]))

/-- **Ground coordinate-vanishing is invariant under any adjacent opposite-spin transposition.**
For a ground vector `v` and an α-config `s` with opposite spins on the adjacent pair `p, p+1`, the
coordinate at `αs` vanishes iff it vanishes at the pair-transposed config. -/
theorem flatBand_ground_repr_adjSwap_iff (K : ℕ) (ν t U : ℝ) (hν : 0 < ν) (ht : 0 < t)
    (hU : 0 < U) {v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ}
    (hv : v ∈ flatBandHalfFilledGroundSubmodule K ν t U)
    (p : Fin K) (s : Fin (K + 1) → Fin 2) (hopp : s p.castSucc ≠ s p.succ) :
    (flatBandOccBasis K ν).repr v (flatBandAlphaSpinOcc K s) = 0 ↔
      (flatBandOccBasis K ν).repr v (flatBandAlphaSpinOcc K
        (Function.update (Function.update s p.castSucc (s p.succ)) p.succ (s p.castSucc))) = 0 := by
  have hpne : p.castSucc ≠ p.succ := by
    intro h; have := congrArg Fin.val h; rw [Fin.val_succ, Fin.val_castSucc] at this; omega
  have hdich : ∀ t : Fin 2, t = 0 ∨ t = 1 := by
    intro t
    rcases (by omega : t.val = 0 ∨ t.val = 1) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases hdich (s p.castSucc) with h0 | h1
  · have h1 : s p.succ = 1 := by
      rcases hdich (s p.succ) with h | h
      · exact absurd (h0.trans h.symm) hopp
      · exact h
    have hcfg : Function.update (Function.update s p.castSucc (s p.succ)) p.succ (s p.castSucc)
        = Function.update (Function.update s p.castSucc 1) p.succ 0 := by
      rw [h0, h1]
    rw [hcfg]
    exact flatBand_ground_repr_alphaSpinOcc_swap_iff K ν t U hν ht hU hv p s h0 h1
  · have h0 : s p.succ = 0 := by
      rcases hdich (s p.succ) with h | h
      · exact h
      · exact absurd (h1.trans h.symm) hopp
    set s2 := Function.update (Function.update s p.castSucc (s p.succ)) p.succ (s p.castSucc)
      with hs2
    have hs20 : s2 p.castSucc = 0 := by
      rw [hs2, Function.update_of_ne hpne, Function.update_self, h0]
    have hs21 : s2 p.succ = 1 := by rw [hs2, Function.update_self, h1]
    have hback : Function.update (Function.update s2 p.castSucc 1) p.succ 0 = s := by
      funext q
      by_cases hq0 : q = p.castSucc
      · rw [hq0, Function.update_of_ne hpne, Function.update_self, h1]
      · by_cases hq1 : q = p.succ
        · rw [hq1, Function.update_self, h0]
        · rw [Function.update_of_ne hq1, Function.update_of_ne hq0, hs2,
            Function.update_of_ne hq1, Function.update_of_ne hq0]
    have hmain := flatBand_ground_repr_alphaSpinOcc_swap_iff K ν t U hν ht hU hv p s2 hs20 hs21
    rw [hback] at hmain
    exact hmain.symm

/-- **Without an adjacent `(1,0)` descent, occupied spins propagate to the right.**  If no adjacent
orbital pair is `(↓-from-↑)` i.e. `(1, 0)`, then an up-spin at orbital `i` forces up-spins at all
later orbitals. -/
theorem flatBand_one_propagates (s : Fin (K + 1) → Fin 2)
    (h : ∀ k : Fin K, ¬(s k.castSucc = 1 ∧ s k.succ = 0)) :
    ∀ i j : Fin (K + 1), i ≤ j → s i = 1 → s j = 1 := by
  have hdich : ∀ t : Fin 2, t = 0 ∨ t = 1 := by
    intro t
    rcases (by omega : t.val = 0 ∨ t.val = 1) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have hstep : ∀ k : Fin K, s k.castSucc = 1 → s k.succ = 1 := by
    intro k hk
    rcases hdich (s k.succ) with h0 | h1
    · exact absurd ⟨hk, h0⟩ (h k)
    · exact h1
  have hgap : ∀ (m : ℕ) (i : Fin (K + 1)), s i = 1 → (hm : i.val + m < K + 1) →
      s ⟨i.val + m, hm⟩ = 1 := by
    intro m
    induction m with
    | zero =>
      intro i hi hm
      rw [show (⟨i.val + 0, hm⟩ : Fin (K + 1)) = i from Fin.ext (Nat.add_zero i.val)]; exact hi
    | succ n ih =>
      intro i hi hm
      have hn1 : i.val + n < K + 1 := by omega
      have hkK : i.val + n < K := by omega
      have hihn := ih i hi hn1
      have hcs : ((⟨i.val + n, hkK⟩ : Fin K).castSucc) = (⟨i.val + n, hn1⟩ : Fin (K + 1)) :=
        Fin.ext rfl
      have hsc : ((⟨i.val + n, hkK⟩ : Fin K).succ) = (⟨i.val + (n + 1), hm⟩ : Fin (K + 1)) :=
        Fin.ext (by simp only [Fin.val_succ]; omega)
      rw [← hsc]
      exact hstep ⟨i.val + n, hkK⟩ (by rw [hcs]; exact hihn)
  intro i j hij hi
  have hle : i.val ≤ j.val := hij
  have hj : j.val < K + 1 := j.isLt
  have hb : i.val + (j.val - i.val) < K + 1 := by omega
  have hg := hgap (j.val - i.val) i hi hb
  rwa [show (⟨i.val + (j.val - i.val), hb⟩ : Fin (K + 1)) = j from
    Fin.ext (Nat.add_sub_cancel' hle)] at hg

/-- **A config with no adjacent inversion is determined by its up-count.**  Two monotone
(`0…01…1`) configs with the same number of up-spins are equal. -/
theorem flatBand_no_adj_inv_eq (s s' : Fin (K + 1) → Fin 2)
    (hs : ∀ k : Fin K, ¬(s k.castSucc = 1 ∧ s k.succ = 0))
    (hs' : ∀ k : Fin K, ¬(s' k.castSucc = 1 ∧ s' k.succ = 0))
    (hc : (Finset.univ.filter (fun q => s q = 1)).card
        = (Finset.univ.filter (fun q => s' q = 1)).card) :
    s = s' := by
  have hdich : ∀ t : Fin 2, t = 0 ∨ t = 1 := by
    intro t
    rcases (by omega : t.val = 0 ∨ t.val = 1) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have key : ∀ (a b : Fin (K + 1) → Fin 2),
      (∀ k : Fin K, ¬(a k.castSucc = 1 ∧ a k.succ = 0)) →
      (∀ k : Fin K, ¬(b k.castSucc = 1 ∧ b k.succ = 0)) →
      (Finset.univ.filter (fun q => a q = 1)).card
        = (Finset.univ.filter (fun q => b q = 1)).card →
      ∀ q, a q = 1 → b q = 1 := by
    intro a b ha hb hcard q haq
    by_contra hbq
    have hbq0 : b q = 0 := (hdich (b q)).resolve_right hbq
    have hsub1 : Finset.Ici q ⊆ Finset.univ.filter (fun q' => a q' = 1) := fun q' hq' =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        flatBand_one_propagates a ha q q' (Finset.mem_Ici.mp hq') haq⟩
    have hsub0 : Finset.Iic q ⊆ Finset.univ.filter (fun q' => b q' = 0) := by
      intro q' hq'
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases hdich (b q') with h0 | h1
      · exact h0
      · exact absurd (flatBand_one_propagates b hb q' q (Finset.mem_Iic.mp hq') h1)
          (by rw [hbq0]; decide)
    have hc1 : (K + 1) - q.val ≤ (Finset.univ.filter (fun q' => a q' = 1)).card := by
      rw [← Fin.card_Ici]; exact Finset.card_le_card hsub1
    have hc0 : q.val + 1 ≤ (Finset.univ.filter (fun q' => b q' = 0)).card := by
      rw [← Fin.card_Iic]; exact Finset.card_le_card hsub0
    have hsplit : (Finset.univ.filter (fun q' => b q' = 0)).card
        + (Finset.univ.filter (fun q' => b q' = 1)).card = K + 1 := by
      have hh := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin (K + 1)))) (p := fun q' => b q' = 0)
      rw [Finset.card_univ, Fintype.card_fin,
        show (Finset.univ.filter (fun q' => ¬ b q' = 0))
            = Finset.univ.filter (fun q' => b q' = 1) from
          Finset.filter_congr (fun q' _ => by rcases hdich (b q') with h | h <;> simp [h])] at hh
      exact hh
    have hq := q.isLt
    omega
  funext q
  rcases hdich (s q) with h0 | h1
  · rcases hdich (s' q) with h0' | h1'
    · rw [h0, h0']
    · exact absurd (key s' s hs' hs hc.symm q h1') (by rw [h0]; decide)
  · rw [h1, key s s' hs hs' hc q h1]

/-- Split a sum over `Fin (K+1)` off the two adjacent pair positions `k, k+1`. -/
theorem flatBand_sum_split_pair (k : Fin K) (g : Fin (K + 1) → ℕ) :
    ∑ q, g q = g k.castSucc + g k.succ
      + ∑ q ∈ (Finset.univ.erase k.castSucc).erase k.succ, g q := by
  have hne : k.castSucc ≠ k.succ := by
    intro h; have := congrArg Fin.val h; rw [Fin.val_succ, Fin.val_castSucc] at this; omega
  rw [← Finset.add_sum_erase _ g (Finset.mem_univ k.castSucc),
    ← Finset.add_sum_erase _ g (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ k.succ⟩),
    ← add_assoc]

/-- **An adjacent `(1,0) → (0,1)` swap preserves the up-count and raises the weight by one.** -/
theorem flatBand_adjSwap_weight_upCount (s' : Fin (K + 1) → Fin 2) (k : Fin K)
    (h1 : s' k.castSucc = 1) (h0 : s' k.succ = 0) :
    (∑ q, (Function.update (Function.update s' k.castSucc 0) k.succ 1 q).val
        = ∑ q, (s' q).val) ∧
      (∑ q, q.val * (Function.update (Function.update s' k.castSucc 0) k.succ 1 q).val
        = (∑ q, q.val * (s' q).val) + 1) := by
  have hne : k.castSucc ≠ k.succ := by
    intro h; have := congrArg Fin.val h; rw [Fin.val_succ, Fin.val_castSucc] at this; omega
  set G := Function.update (Function.update s' k.castSucc 0) k.succ 1 with hG
  have hGksc : G k.succ = 1 := Function.update_self _ _ _
  have hGkcs : G k.castSucc = 0 := by rw [hG, Function.update_of_ne hne, Function.update_self]
  have hGoff : ∀ q, q ≠ k.castSucc → q ≠ k.succ → G q = s' q := fun q hq0 hq1 => by
    rw [hG, Function.update_of_ne hq1, Function.update_of_ne hq0]
  have hrest : ∀ (g : Fin 2 → ℕ → ℕ),
      (∑ q ∈ (Finset.univ.erase k.castSucc).erase k.succ, g (G q) q.val)
        = ∑ q ∈ (Finset.univ.erase k.castSucc).erase k.succ, g (s' q) q.val := by
    intro g
    refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [Finset.mem_erase, Finset.mem_erase] at hq
    rw [hGoff q hq.2.1 hq.1]
  refine ⟨?_, ?_⟩
  · rw [flatBand_sum_split_pair k (fun q => (G q).val),
      flatBand_sum_split_pair k (fun q => (s' q).val), hGkcs, hGksc, h1, h0,
      hrest (fun v _ => v.val)]
    simp only [Fin.val_zero, Fin.val_one, Nat.zero_add, Nat.add_zero]
  · rw [flatBand_sum_split_pair k (fun q => q.val * (G q).val),
      flatBand_sum_split_pair k (fun q => q.val * (s' q).val), hGkcs, hGksc, h1, h0,
      hrest (fun v n => n * v.val)]
    simp only [Fin.val_zero, Fin.val_one, mul_zero, mul_one, Fin.val_succ, Fin.val_castSucc]
    ring

/-- **Coordinate-vanishing propagates across all configs of equal up-count.**  If a ground vector's
coordinate vanishes at the sorted (no-adjacent-inversion) representative `rep`, it vanishes at every
α-config with the same up-count.  Strong induction on `M − weight`: an adjacent `(1,0)` raises the
weight (via the swap-iff and `flatBand_adjSwap_weight_upCount`); when none remains the config is
`rep` (sorted-unique). -/
theorem flatBand_ground_repr_zero_of_upCount (K : ℕ) (ν t U : ℝ) (hν : 0 < ν) (ht : 0 < t)
    (hU : 0 < U) {v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ}
    (hv : v ∈ flatBandHalfFilledGroundSubmodule K ν t U) (rep : Fin (K + 1) → Fin 2)
    (hrepsort : ∀ k : Fin K, ¬(rep k.castSucc = 1 ∧ rep k.succ = 0))
    (hrep0 : (flatBandOccBasis K ν).repr v (flatBandAlphaSpinOcc K rep) = 0) :
    ∀ s' : Fin (K + 1) → Fin 2, (∑ q, (s' q).val = ∑ q, (rep q).val) →
      (flatBandOccBasis K ν).repr v (flatBandAlphaSpinOcc K s') = 0 := by
  have hdich : ∀ t : Fin 2, t = 0 ∨ t = 1 := by
    intro t
    rcases (by omega : t.val = 0 ∨ t.val = 1) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have hcardval : ∀ (s : Fin (K + 1) → Fin 2),
      (Finset.univ.filter (fun q => s q = 1)).card = ∑ q, (s q).val := by
    intro s
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl (fun q _ => by rcases hdich (s q) with h | h <;> simp [h])
  have hwle : ∀ (s : Fin (K + 1) → Fin 2), (∑ q, q.val * (s q).val) ≤ (K + 1) * (K + 1) := by
    intro s
    calc ∑ q, q.val * (s q).val ≤ ∑ _q : Fin (K + 1), K :=
          Finset.sum_le_sum (fun q _ => by have := q.isLt; have := (s q).isLt; nlinarith)
      _ = (K + 1) * K := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ ≤ (K + 1) * (K + 1) := by nlinarith
  suffices H : ∀ (D : ℕ) (s' : Fin (K + 1) → Fin 2),
      (K + 1) * (K + 1) - (∑ q, q.val * (s' q).val) = D →
      (∑ q, (s' q).val = ∑ q, (rep q).val) →
      (flatBandOccBasis K ν).repr v (flatBandAlphaSpinOcc K s') = 0 by
    intro s' hc; exact H _ s' rfl hc
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
    intro s' hD hc
    by_cases hsw : ∃ k : Fin K, s' k.castSucc = 1 ∧ s' k.succ = 0
    · obtain ⟨k, hk1, hk0⟩ := hsw
      obtain ⟨huc, hwt⟩ := flatBand_adjSwap_weight_upCount s' k hk1 hk0
      have hcG : ∑ q, (Function.update (Function.update s' k.castSucc 0) k.succ 1 q).val
          = ∑ q, (rep q).val := by rw [huc, hc]
      have hwGle := hwle (Function.update (Function.update s' k.castSucc 0) k.succ 1)
      rw [hwt] at hwGle
      have hlt : (K + 1) * (K + 1) - (∑ q, q.val *
          (Function.update (Function.update s' k.castSucc 0) k.succ 1 q).val) < D := by
        rw [hwt]; omega
      have hGrepr := ih _ hlt (Function.update (Function.update s' k.castSucc 0) k.succ 1) rfl hcG
      have hopp : s' k.castSucc ≠ s' k.succ := by rw [hk1, hk0]; decide
      have hiff := flatBand_ground_repr_adjSwap_iff K ν t U hν ht hU hv k s' hopp
      rw [show Function.update (Function.update s' k.castSucc (s' k.succ)) k.succ (s' k.castSucc)
          = Function.update (Function.update s' k.castSucc 0) k.succ 1 by rw [hk0, hk1]] at hiff
      exact hiff.mpr hGrepr
    · have hs'sort : ∀ k : Fin K, ¬(s' k.castSucc = 1 ∧ s' k.succ = 0) :=
        fun k ⟨ha, hb⟩ => hsw ⟨k, ha, hb⟩
      rw [flatBand_no_adj_inv_eq s' rep hs'sort hrepsort (by rw [hcardval, hcardval, hc])]
      exact hrep0

/-- The sorted representative α-config for a block: `m` leading down-spins, the rest up. -/
def flatBandSortedRep (K m : ℕ) : Fin (K + 1) → Fin 2 := fun q => if q.val < m then 0 else 1

/-- The sorted representative has no adjacent `(1,0)` inversion. -/
theorem flatBandSortedRep_no_adj_inv (m : ℕ) : ∀ k : Fin K,
    ¬((flatBandSortedRep K m) k.castSucc = 1 ∧ (flatBandSortedRep K m) k.succ = 0) := by
  intro k ⟨h1, h0⟩
  simp only [flatBandSortedRep, Fin.val_castSucc, Fin.val_succ] at h1 h0
  by_cases hk : k.val < m
  · rw [if_pos hk] at h1; exact absurd h1 (by decide)
  · rw [if_neg hk] at h1
    by_cases hk1 : k.val + 1 < m
    · omega
    · rw [if_neg hk1] at h0; exact absurd h0 (by decide)

/-- Counting the up-spins of the sorted representative: `∑ (rep q).val = (K+1) − m`. -/
theorem flatBandSortedRep_upCount (m : ℕ) :
    ∑ q, ((flatBandSortedRep K m) q).val = (K + 1) - m := by
  have hrange : ∀ (n : ℕ),
      ∑ i ∈ Finset.range n, (if i < m then (0 : ℕ) else 1) = n - m := by
    intro n
    induction n with
    | zero => simp
    | succ p ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases hp : p < m
      · rw [if_pos hp]; omega
      · rw [if_neg hp]; omega
  calc ∑ q, ((flatBandSortedRep K m) q).val
      = ∑ q : Fin (K + 1), (if q.val < m then (0 : ℕ) else 1) := by
        refine Finset.sum_congr rfl (fun q _ => ?_)
        simp only [flatBandSortedRep]
        by_cases hq : q.val < m <;> simp [hq]
    _ = ∑ i ∈ Finset.range (K + 1), (if i < m then (0 : ℕ) else 1) :=
        (Fin.sum_univ_eq_sum_range (fun i => if i < m then (0 : ℕ) else 1) (K + 1))
    _ = (K + 1) - m := hrange (K + 1)

/-- The `Ŝ^z` weight of an α-config is `(K+1)/2` minus its up-count. -/
theorem flatBand_alphaSpinCharge_eq (s : Fin (K + 1) → Fin 2) :
    ∑ p, flatBandSpinCharge (s p) = ((K + 1 : ℕ) : ℂ) / 2 - ∑ p, ((s p).val : ℂ) := by
  simp only [flatBandSpinCharge]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  ring

open Module in
/-- **Each `Ŝ^z`-weight block of the half-filled ground subspace is at most one-dimensional.**  The
coordinate functional at the sorted representative is injective: its kernel forces every occupation
coordinate to vanish (off-sector ones by the support lemmas, the in-sector ones by the
swap-invariant propagation), hence the vector is zero. -/
theorem flatBand_block_finrank_le_one (K : ℕ) (ν t U : ℝ) (hν : 0 < ν) (ht : 0 < t) (hU : 0 < U)
    (a : Fin (K + 2)) :
    finrank ℂ ↥(flatBandHalfFilledGroundSubmodule K ν t U ⊓
      Module.End.eigenspace (fermionTotalSpinZ (2 * K + 1)).mulVecLin
        (((a : ℝ) - ((K + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ)) ≤ 1 := by
  classical
  set μ : ℂ := (((a : ℝ) - ((K + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) with hμ
  set B := flatBandHalfFilledGroundSubmodule K ν t U ⊓
    Module.End.eigenspace (fermionTotalSpinZ (2 * K + 1)).mulVecLin μ with hB
  set rep := flatBandSortedRep K a.val with hrep
  have ha : a.val ≤ K + 1 := by have := a.isLt; omega
  have hrepμ : ∑ p, flatBandSpinCharge (rep p) = μ := by
    rw [flatBand_alphaSpinCharge_eq,
      show (∑ p, ((rep p).val : ℂ)) = (((K + 1 - a.val : ℕ) : ℕ) : ℂ) from by
        rw [show (∑ p, ((rep p).val : ℂ)) = ((∑ p, (rep p).val : ℕ) : ℂ) from by push_cast; rfl,
          hrep, flatBandSortedRep_upCount],
      hμ, Nat.cast_sub ha]
    push_cast
    ring
  set Φ : ↥B →ₗ[ℂ] ℂ := (Finsupp.lapply (flatBandAlphaSpinOcc K rep)).comp
    (((flatBandOccBasis K ν).repr.toLinearMap).comp B.subtype) with hΦ
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hw' : (flatBandOccBasis K ν).repr w.1 (flatBandAlphaSpinOcc K rep) = 0 := hw
    have hwg : w.1 ∈ flatBandHalfFilledGroundSubmodule K ν t U := (Submodule.mem_inf.mp w.2).1
    have hall : ∀ f, (flatBandOccBasis K ν).repr w.1 f = 0 := by
      intro f
      by_cases hcard : (occFinset f).card = K + 1
      · by_cases hbf : ∀ q' ∈ occFinset f, ∃ r, q'.1 = Sum.inl r
        · by_cases hnd : ∀ q : Fin (K + 1),
              ¬((Sum.inl q, (0 : Fin 2)) ∈ occFinset f ∧ (Sum.inl q, (1 : Fin 2)) ∈ occFinset f)
          · have hrecon := flatBand_occFinset_eq_alphaSpinOcc_of_betaFree_noDouble f hbf hnd hcard
            set s' := fun q => if (Sum.inl q, (0 : Fin 2)) ∈ occFinset f then (0 : Fin 2) else 1
              with hs'
            have hfeq : f = flatBandAlphaSpinOcc K s' := config_eq_of_occFinset_eq f _ hrecon
            by_cases hsc : (∑ q ∈ occFinset f, flatBandSpinCharge q.2) = μ
            · have hscf : ∑ p, flatBandSpinCharge (s' p) = μ := by
                rw [← occFinset_alphaSpinOcc_spinCharge_sum, ← hrecon, hsc]
              have hcount : ∑ q, (s' q).val = ∑ q, (rep q).val := by
                have h1 : ∑ p, flatBandSpinCharge (s' p) = ∑ p, flatBandSpinCharge (rep p) := by
                  rw [hscf, hrepμ]
                rw [flatBand_alphaSpinCharge_eq, flatBand_alphaSpinCharge_eq] at h1
                have h2 := sub_right_inj.mp h1
                exact_mod_cast h2
              rw [hfeq]
              exact flatBand_ground_repr_zero_of_upCount K ν t U hν ht hU hwg rep
                (flatBandSortedRep_no_adj_inv a.val) hw' s' hcount
            · exact flatBandOccBasis_repr_eq_zero_of_spinZ_ne t U μ w.2 hsc
          · simp only [not_forall, not_not] at hnd
            obtain ⟨q, hq0, hq1⟩ := hnd
            exact flatBandOccBasis_repr_eq_zero_of_doubleOcc K ν t U ht hU hwg hbf hq0 hq1
        · rw [not_forall] at hbf
          obtain ⟨q', hq'⟩ := hbf
          rw [Classical.not_imp, not_exists] at hq'
          obtain ⟨hq'occ, hq'nr⟩ := hq'
          obtain ⟨u, hu⟩ : ∃ u, q'.1 = Sum.inr u := by
            cases hq1 : q'.1 with
            | inl r => exact absurd hq1 (hq'nr r)
            | inr u => exact ⟨u, rfl⟩
          have hmem : (Sum.inr u, q'.2) ∈ occFinset f := by
            rw [show (Sum.inr u, q'.2) = q' from Prod.ext hu.symm rfl]; exact hq'occ
          exact flatBandOccBasis_repr_eq_zero_of_mem_BKernel u q'.2
            (flatBand_groundState_mem_BKernelSubmodule K ν t U ht hU.le (by
              rw [flatBandHalfFilledGroundSubmodule, Submodule.mem_inf] at hwg
              obtain ⟨hker, _⟩ := hwg
              rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hker
              unfold rayleighOnVec; rw [hker, dotProduct_zero, Complex.zero_re])) hmem
      · exact flatBandOccBasis_repr_eq_zero_of_card_ne t U hwg hcard
    have hw1 : w.1 = 0 := (flatBandOccBasis K ν).repr.map_eq_zero_iff.mp (Finsupp.ext hall)
    exact Subtype.ext hw1
  have key := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [finrank_self] at key

end LatticeSystem.Fermion
