import LatticeSystem.Fermion.JordanWigner.Hubbard.TJExchangeNonneg
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJDiagonalMatrixElement
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJKineticSummand
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJOffDiagonal
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJEffMatrix

/-!
# Tasaki 11.5: the t-J interaction off-diagonal is `≤ 0`, hence `M_{s',s} ≤ 0` (Prop 11.24 PR-B7-3h)

The off-diagonal entries of the t-J effective matrix are non-positive — the Perron–Frobenius
hypothesis.  The kinetic part already gives `−τ·(≥0) ≤ 0` (`tJKinetic_matrixElement_nonneg`); this
file handles the exchange interaction `J·Σ_{⟨x,y⟩}(n̂_x n̂_y/4 − Ŝ_x·Ŝ_y)` and assembles the total.

For a bra `⟨Φ_{s'}|` with `s' ≠ s`:

* the density and `Ŝ³` products `n̂_x n̂_y`, `Ŝ³_x Ŝ³_y` act diagonally, so vanish (PR-B6);
* `Ŝ_x·Ŝ_y = ½(Ŝ⁺_x Ŝ⁻_y + Ŝ⁻_x Ŝ⁺_y) + Ŝ³_x Ŝ³_y`, so the surviving off-diagonal part is
  `−(J/2)·Σ_{x,y}(\,⟨Φ_{s'}|Ŝ⁺_x Ŝ⁻_y|Φ_s⟩ + ⟨Φ_{s'}|Ŝ⁻_x Ŝ⁺_y|Φ_s⟩\,)` weighted by adjacency;
* each weighted ladder element is `{0,1}`-valued — `Ŝ⁺_x Ŝ⁻_y` by `tJ_exchange_summand_zero_or_one`,
  and `Ŝ⁻_x Ŝ⁺_y` by the different-site commutation `Ŝ⁻_x Ŝ⁺_y = Ŝ⁺_y Ŝ⁻_x` (`x ≠ y`) plus the
  same lemma at `(y,x)`.

Hence the interaction off-diagonal entry is `−(J/2)·(≥0) ≤ 0` for `J ≥ 0`, and combined with the
kinetic `−τ·(≥0) ≤ 0` the full effective entry `M_{s',s} ≤ 0` for `s' ≠ s`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph
open scoped BigOperators

variable {N : ℕ}

/-- If `a` anticommutes with both `c` and `d`, it commutes with the even product `c d`. -/
private theorem anticomm_commute_mul {α : Type*} [Ring α] {a c d : α}
    (hac : a * c + c * a = 0) (had : a * d + d * a = 0) :
    a * (c * d) = c * d * a := by
  have hac' : a * c = -(c * a) := eq_neg_of_add_eq_zero_left hac
  have had' : a * d = -(d * a) := eq_neg_of_add_eq_zero_left had
  calc a * (c * d) = a * c * d := by rw [mul_assoc]
    _ = -(c * a) * d := by rw [hac']
    _ = -(c * (a * d)) := by rw [neg_mul, mul_assoc]
    _ = -(c * -(d * a)) := by rw [had']
    _ = c * d * a := by rw [mul_neg, neg_neg, mul_assoc]

/-- Two even products `a b` and `c d` of pairwise-anticommuting factors commute. -/
private theorem anticomm_commute_mul_mul {α : Type*} [Ring α] {a b c d : α}
    (hac : a * c + c * a = 0) (had : a * d + d * a = 0)
    (hbc : b * c + c * b = 0) (hbd : b * d + d * b = 0) :
    a * b * (c * d) = c * d * (a * b) := by
  have ha : a * (c * d) = c * d * a := anticomm_commute_mul hac had
  have hb : b * (c * d) = c * d * b := anticomm_commute_mul hbc hbd
  calc a * b * (c * d) = a * (b * (c * d)) := by rw [mul_assoc]
    _ = a * (c * d * b) := by rw [hb]
    _ = a * (c * d) * b := by rw [← mul_assoc]
    _ = c * d * a * b := by rw [ha]
    _ = c * d * (a * b) := by rw [mul_assoc]

/-- **Different-site spin ladders commute.**  For `x ≠ y` the bilinear (even) operators
`Ŝ⁻_x = ĉ†_{x↓}ĉ_{x↑}` and `Ŝ⁺_y = ĉ†_{y↑}ĉ_{y↓}` act on disjoint mode sets, so they commute:
`Ŝ⁻_x Ŝ⁺_y = Ŝ⁺_y Ŝ⁻_x` (four cross-site anticommutations combine to `(-1)^4 = +1`). -/
theorem fermionSiteSpinMinus_mul_Plus_comm (N : ℕ) (x y : Fin (N + 1)) (hxy : x ≠ y) :
    fermionSiteSpinMinus N x * fermionSiteSpinPlus N y
      = fermionSiteSpinPlus N y * fermionSiteSpinMinus N x := by
  unfold fermionSiteSpinMinus fermionSiteSpinPlus
  exact anticomm_commute_mul_mul
    (fermionDownCreation_upCreation_anticomm N x y)
    (fermionDownCreation_downAnnihilation_anticomm_ne N hxy)
    (fermionUpAnnihilation_upCreation_anticomm_ne N hxy)
    (fermionUpAnnihilation_downAnnihilation_anticomm N x y)

/-- **Each cyclic swapped-exchange summand is `0` or `1`.**  The graph-weighted reversed ladder
`couplingOf(cycleGraph) x y · ⟨Φ_{s'}|Ŝ⁻_x Ŝ⁺_y|Φ_s⟩` is `0` or `1`: non-adjacent pairs are killed
by the coupling, and for an adjacent pair (so `x ≠ y`) the commutation reduces it to the
`Ŝ⁺_y Ŝ⁻_x` summand at `(y,x)`, which is `{0,1}`-valued by `tJ_exchange_summand_zero_or_one`. -/
theorem tJ_exchange_swap_summand_zero_or_one (N : ℕ) (s s' : Fin (N + 1) → Fin 3)
    (x y : Fin (N + 1)) :
    couplingOf (cycleGraph (N + 1)) (1 : ℂ) x y *
        (∑ w, basisVec (tJConfigOf N s') w *
          ((fermionSiteSpinMinus N x * fermionSiteSpinPlus N y).mulVec
              (basisVec (tJConfigOf N s))) w) = 0 ∨
      couplingOf (cycleGraph (N + 1)) (1 : ℂ) x y *
        (∑ w, basisVec (tJConfigOf N s') w *
          ((fermionSiteSpinMinus N x * fermionSiteSpinPlus N y).mulVec
              (basisVec (tJConfigOf N s))) w) = 1 := by
  by_cases hAdj : (cycleGraph (N + 1)).Adj x y
  · have hxy : x ≠ y := hAdj.ne
    rw [fermionSiteSpinMinus_mul_Plus_comm N x y hxy,
      couplingOf_symm (cycleGraph (N + 1)) (1 : ℂ) x y]
    exact tJ_exchange_summand_zero_or_one N s s' y x
  · have hcoup : couplingOf (cycleGraph (N + 1)) (1 : ℂ) x y = 0 := by
      unfold couplingOf; rw [if_neg hAdj]
    rw [hcoup, zero_mul]; exact Or.inl rfl

/-! ### Matrix-element linearity helper -/

/-- The sector matrix element `⟨Φ_{s'} | op | Φ_s⟩` as a linear functional of the operator `op`. -/
private noncomputable def tJME (N : ℕ) (s s' : Fin (N + 1) → Fin 3)
    (op : ManyBodyOp (Fin (2 * N + 2))) : ℂ :=
  ∑ w, basisVec (tJConfigOf N s') w * (op.mulVec (basisVec (tJConfigOf N s))) w

/-- The matrix element of the zero operator vanishes. -/
private theorem tJME_zero (N : ℕ) (s s' : Fin (N + 1) → Fin 3) : tJME N s s' 0 = 0 := by
  unfold tJME; rw [Matrix.zero_mulVec]; simp

/-- The matrix element is additive in the operator. -/
private theorem tJME_add (N : ℕ) (s s' : Fin (N + 1) → Fin 3)
    (op₁ op₂ : ManyBodyOp (Fin (2 * N + 2))) :
    tJME N s s' (op₁ + op₂) = tJME N s s' op₁ + tJME N s s' op₂ := by
  unfold tJME
  rw [Matrix.add_mulVec]
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The matrix element respects operator subtraction. -/
private theorem tJME_sub (N : ℕ) (s s' : Fin (N + 1) → Fin 3)
    (op₁ op₂ : ManyBodyOp (Fin (2 * N + 2))) :
    tJME N s s' (op₁ - op₂) = tJME N s s' op₁ - tJME N s s' op₂ := by
  unfold tJME
  rw [Matrix.sub_mulVec]
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The matrix element is homogeneous in the scalar multiplier of the operator. -/
private theorem tJME_smul (N : ℕ) (s s' : Fin (N + 1) → Fin 3) (c : ℂ)
    (op : ManyBodyOp (Fin (2 * N + 2))) :
    tJME N s s' (c • op) = c * tJME N s s' op := by
  unfold tJME
  rw [Matrix.smul_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

/-- The matrix element commutes with a finite operator sum. -/
private theorem tJME_sum {ι : Type*} (N : ℕ) (s s' : Fin (N + 1) → Fin 3)
    (t : Finset ι) (f : ι → ManyBodyOp (Fin (2 * N + 2))) :
    tJME N s s' (∑ i ∈ t, f i) = ∑ i ∈ t, tJME N s s' (f i) := by
  classical
  refine Finset.induction_on t ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, tJME_zero]
  · intro a t' ha ih
    rw [Finset.sum_insert ha, tJME_add, ih, Finset.sum_insert ha]

/-- The matrix element respects operator negation. -/
private theorem tJME_neg (N : ℕ) (s s' : Fin (N + 1) → Fin 3)
    (op : ManyBodyOp (Fin (2 * N + 2))) :
    tJME N s s' (-op) = -tJME N s s' op := by
  unfold tJME
  rw [Matrix.neg_mulVec]
  simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

/-! ### Per-bond off-diagonal reduction -/

/-- **The per-bond interaction off-diagonal reduces to the ladder pair.**  For `s' ≠ s` the density
and `Ŝ³` products drop (diagonal), leaving
`⟨Φ_{s'}|(n̂_x n̂_y/4 − Ŝ_x·Ŝ_y)|Φ_s⟩ = −½(⟨Φ_{s'}|Ŝ⁺_x Ŝ⁻_y|Φ_s⟩ + ⟨Φ_{s'}|Ŝ⁻_x Ŝ⁺_y|Φ_s⟩)`. -/
private theorem tJ_bond_matrixElement_offdiag (N : ℕ) (s s' : Fin (N + 1) → Fin 3)
    (x y : Fin (N + 1)) (hne : s' ≠ s) :
    tJME N s s' ((1 / 4 : ℂ) • (fermionSiteNumber N x * fermionSiteNumber N y)
        - fermionSpinDot N x y)
      = -(1 / 2 : ℂ) * (tJME N s s' (fermionSiteSpinPlus N x * fermionSiteSpinMinus N y)
          + tJME N s s' (fermionSiteSpinMinus N x * fermionSiteSpinPlus N y)) := by
  unfold fermionSpinDot
  rw [tJME_sub, tJME_smul, tJME_add, tJME_smul, tJME_add,
    show tJME N s s' (fermionSiteNumber N x * fermionSiteNumber N y) = 0 from
      fermionSiteNumber_mul_offdiag_matrixElement_eq_zero N s s' x y hne,
    show tJME N s s' (fermionSiteSpinZ N x * fermionSiteSpinZ N y) = 0 from
      fermionSiteSpinZ_mul_offdiag_matrixElement_eq_zero N s s' x y hne]
  ring

/-! ### The interaction off-diagonal in ladder bond-sum form -/

/-- **The interaction matrix element as a weighted ladder bond-sum.**  For `s' ≠ s`,
`⟨Φ_{s'}|Σ_{x,y}(if Adj then n̂n̂/4 − Ŝ·Ŝ)|Φ_s⟩
   = −½·Σ_{x,y}(couplingOf x y·⟨Ŝ⁺_x Ŝ⁻_y⟩ + couplingOf x y·⟨Ŝ⁻_x Ŝ⁺_y⟩)`. -/
theorem tJInteraction_matrixElement_eq (N : ℕ) (s s' : Fin (N + 1) → Fin 3) (hne : s' ≠ s) :
    tJME N s s' (∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
        (if (cycleGraph (N + 1)).Adj x y then
            (1 / 4 : ℂ) • (fermionSiteNumber N x * fermionSiteNumber N y)
              - fermionSpinDot N x y
          else 0))
      = -(1 / 2 : ℂ) * ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
          (couplingOf (cycleGraph (N + 1)) (1 : ℂ) x y *
              tJME N s s' (fermionSiteSpinPlus N x * fermionSiteSpinMinus N y)
            + couplingOf (cycleGraph (N + 1)) (1 : ℂ) x y *
              tJME N s s' (fermionSiteSpinMinus N x * fermionSiteSpinPlus N y)) := by
  have key : ∀ x y : Fin (N + 1),
      tJME N s s' (if (cycleGraph (N + 1)).Adj x y then
          (1 / 4 : ℂ) • (fermionSiteNumber N x * fermionSiteNumber N y)
            - fermionSpinDot N x y else 0)
        = -(1 / 2 : ℂ) * (couplingOf (cycleGraph (N + 1)) (1 : ℂ) x y *
              tJME N s s' (fermionSiteSpinPlus N x * fermionSiteSpinMinus N y)
            + couplingOf (cycleGraph (N + 1)) (1 : ℂ) x y *
              tJME N s s' (fermionSiteSpinMinus N x * fermionSiteSpinPlus N y)) := by
    intro x y
    by_cases hAdj : (cycleGraph (N + 1)).Adj x y
    · rw [if_pos hAdj, tJ_bond_matrixElement_offdiag N s s' x y hne,
        show couplingOf (cycleGraph (N + 1)) (1 : ℂ) x y = 1 by
          unfold couplingOf; rw [if_pos hAdj]]
      ring
    · rw [if_neg hAdj, tJME_zero,
        show couplingOf (cycleGraph (N + 1)) (1 : ℂ) x y = 0 by
          unfold couplingOf; rw [if_neg hAdj]]
      ring
  simp only [tJME_sum]
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => key x y]
  simp only [← Finset.mul_sum]

/-! ### The interaction off-diagonal is non-positive -/

/-- **The interaction off-diagonal matrix element is non-positive.**  For `s' ≠ s` and `J ≥ 0`,
`(J·⟨Φ_{s'}|Σ_{x,y}(if Adj then n̂n̂/4 − Ŝ·Ŝ)|Φ_s⟩).re ≤ 0` with vanishing imaginary part: the
ladder bond-sum is a non-negative real (each weighted summand is `{0,1}`-valued), times `−J/2`. -/
theorem tJInteraction_matrixElement_nonpos (N : ℕ) (s s' : Fin (N + 1) → Fin 3) (J : ℝ)
    (hJ : 0 ≤ J) (hne : s' ≠ s) :
    ((J : ℂ) * tJME N s s' (∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
        (if (cycleGraph (N + 1)).Adj x y then
            (1 / 4 : ℂ) • (fermionSiteNumber N x * fermionSiteNumber N y)
              - fermionSpinDot N x y
          else 0))).re ≤ 0 ∧
      ((J : ℂ) * tJME N s s' (∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
        (if (cycleGraph (N + 1)).Adj x y then
            (1 / 4 : ℂ) • (fermionSiteNumber N x * fermionSiteNumber N y)
              - fermionSpinDot N x y
          else 0))).im = 0 := by
  -- each weighted ladder summand is `{0,1}`-valued, hence the bond-sum is a non-negative real
  have hT : ∀ x y : Fin (N + 1),
      0 ≤ (couplingOf (cycleGraph (N + 1)) (1 : ℂ) x y *
              tJME N s s' (fermionSiteSpinPlus N x * fermionSiteSpinMinus N y)
            + couplingOf (cycleGraph (N + 1)) (1 : ℂ) x y *
              tJME N s s' (fermionSiteSpinMinus N x * fermionSiteSpinPlus N y)).re ∧
        (couplingOf (cycleGraph (N + 1)) (1 : ℂ) x y *
              tJME N s s' (fermionSiteSpinPlus N x * fermionSiteSpinMinus N y)
            + couplingOf (cycleGraph (N + 1)) (1 : ℂ) x y *
              tJME N s s' (fermionSiteSpinMinus N x * fermionSiteSpinPlus N y)).im = 0 := by
    intro x y
    rcases tJ_exchange_summand_zero_or_one N s s' x y with h1 | h1 <;>
      rcases tJ_exchange_swap_summand_zero_or_one N s s' x y with h2 | h2 <;>
      · simp only [tJME] at h1 h2 ⊢
        rw [h1, h2]; norm_num
  rw [tJInteraction_matrixElement_eq N s s' hne]
  set S : ℂ := ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
      (couplingOf (cycleGraph (N + 1)) (1 : ℂ) x y *
          tJME N s s' (fermionSiteSpinPlus N x * fermionSiteSpinMinus N y)
        + couplingOf (cycleGraph (N + 1)) (1 : ℂ) x y *
          tJME N s s' (fermionSiteSpinMinus N x * fermionSiteSpinPlus N y)) with hS
  have hSre : 0 ≤ S.re := by
    rw [hS, Complex.re_sum]
    exact Finset.sum_nonneg fun x _ => by
      rw [Complex.re_sum]; exact Finset.sum_nonneg fun y _ => (hT x y).1
  have hSim : S.im = 0 := by
    rw [hS, Complex.im_sum]
    exact Finset.sum_eq_zero fun x _ => by
      rw [Complex.im_sum]; exact Finset.sum_eq_zero fun y _ => (hT x y).2
  rw [show -(1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring]
  refine ⟨?_, ?_⟩
  · simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hSim]
    nlinarith [hSre, hJ, mul_nonneg hJ hSre]
  · simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hSim]
    ring

/-! ### The full effective-matrix off-diagonal is non-positive -/

/-- The effective-matrix entry is the sector matrix element of the t-J Hamiltonian. -/
private theorem tJEffMatrix_eq_tJME (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (τ J : ℝ) (s s' : Fin (N + 1) → Fin 3) :
    tJEffMatrix N G τ J s' s = tJME N s s' (tJHamiltonian N G τ J) := by
  rw [tJEffMatrix_apply]; rfl

/-- **The t-J effective-matrix off-diagonal entries are non-positive.**  On the d=1 periodic chain,
for an odd electron count `Ne`, `τ, J ≥ 0`, and distinct sector states `s' ≠ s`, the
effective-matrix entry `M_{s',s} = ⟨Φ_{s'}|Ĥ_tJ|Φ_s⟩` is a non-positive real: the kinetic part is
`−τ·(≥0)` and the
exchange part is `−(J/2)·(≥0)`.  This is the Perron–Frobenius hypothesis for the sector matrix. -/
theorem tJEffMatrix_offdiag_nonpos (N : ℕ) (hpos : 0 < N) (s s' : Fin (N + 1) → Fin 3)
    (Ne : ℕ) (hNe : (Finset.univ.filter (fun k => s k = 1)).card
        + (Finset.univ.filter (fun k => s k = 2)).card = Ne) (hodd : Odd Ne)
    (τ J : ℝ) (hτ : 0 ≤ τ) (hJ : 0 ≤ J) (hne : s' ≠ s) :
    (tJEffMatrix N (cycleGraph (N + 1)) τ J s' s).re ≤ 0 ∧
      (tJEffMatrix N (cycleGraph (N + 1)) τ J s' s).im = 0 := by
  rw [tJEffMatrix_eq_tJME]
  unfold tJHamiltonian
  rw [tJME_add, tJME_smul, tJME_smul]
  -- kinetic: `−τ·⟨K⟩`, with `⟨K⟩` a non-negative real
  have hkin_eq : tJME N s s'
      (hubbardHardcoreProjection N * hubbardKineticOnGraph N (cycleGraph (N + 1)) 1 *
        hubbardHardcoreProjection N)
      = tJME N s s' (hubbardKineticOnGraph N (cycleGraph (N + 1)) 1) :=
    tJKinetic_matrixElement_eq N (cycleGraph (N + 1)) s s'
  have hKnn := tJKinetic_matrixElement_nonneg N hpos s s' Ne hNe hodd
  rw [show (∑ w, basisVec (tJConfigOf N s') w *
        ((hubbardKineticOnGraph N (cycleGraph (N + 1)) 1).mulVec (basisVec (tJConfigOf N s))) w)
      = tJME N s s' (hubbardKineticOnGraph N (cycleGraph (N + 1)) 1) from rfl] at hKnn
  rw [hkin_eq]
  -- interaction: `−(J/2)·(≥0)`, non-positive
  have hint := tJInteraction_matrixElement_nonpos N s s' J hJ hne
  set zK : ℂ := tJME N s s' (hubbardKineticOnGraph N (cycleGraph (N + 1)) 1) with hzK
  obtain ⟨hKre, hKim⟩ := hKnn
  obtain ⟨hIre, hIim⟩ := hint
  constructor
  · rw [Complex.add_re, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im, hKim]
    nlinarith [hKre, hτ, hIre, mul_nonneg hτ hKre]
  · rw [Complex.add_im, Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im, hKim]
    rw [hIim]; ring

end LatticeSystem.Fermion
