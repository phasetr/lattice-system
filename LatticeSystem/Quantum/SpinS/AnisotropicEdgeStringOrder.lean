import LatticeSystem.Quantum.SpinS.SiteComponent
import LatticeSystem.Quantum.SpinS.SpinOneHalfTurn
import LatticeSystem.Quantum.SpinS.AndersonTowerLocality
import LatticeSystem.Math.ComplexVectorKernel

/-!
# Tasaki §8.1.2: the global prefix-string order operator and hidden order (8.1.8)–(8.1.10)

The den Nijs–Rommelse hidden order of the `S = 1` chain is measured by the **global string
operator**

  `Ô^{(α)}_string = Σ_{x} Ŝ_x^{(α)} exp(i π Σ_{y < x} Ŝ_y^{(α)})`   (Tasaki (8.1.8), p. 236),

whose exponential factor is, at `S = 1`, the product of the per-site half turns `u_α` over the sites
strictly to the left of `x` — a `π` rotation of the sub-chain `{0, …, x-1}`.  This module builds
that operator, proves it self-adjoint, states the hidden-order hypothesis (8.1.10) as a concrete
Rayleigh bound, and converts it into the norm lower bound used by the variational argument.

Note that this left **prefix** string is a different operator from the strict two-endpoint window
string `stringOperatorS` / `stringOperatorAxisS` of `AKLTStringOrderDefs`; only the `onSiteS`
product idiom is shared.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.1.2, eqs. (8.1.8) and (8.1.10), pp. 236–237.
-/

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

variable {L : ℕ}

/-! ## Definitions -/

/-- The **prefix rotation** `R^{(α)}_{<m} = ∏_{y < m} u_α^{(y)}`, the `π` rotation about axis `α` of
the sub-chain `{0, …, m-1}`, written as an ordered product of commuting single-site half turns.
It is indexed by `m : ℕ` rather than by a site, so that the same declaration serves both the string
operator (at `m = x.val`) and the support-count argument (which compares `m ≤ z` and `z + 2 ≤ m`).
The product uses `List.ofFn ... |>.prod` because matrices form no `CommMonoid`. -/
noncomputable def edgeStringPrefixRotationS (L : ℕ) (alpha : Fin 3) (m : ℕ) :
    ManyBodyOpS (Fin L) 2 :=
  (List.ofFn fun y : Fin L => if y.val < m then onSiteS y (spinOneHalfTurnS alpha) else 1).prod

/-- The **global edge-string order operator** `Ô^{(α)}_string = Σ_x Ŝ_x^{(α)} R^{(α)}_{<x}`
(Tasaki (8.1.8), p. 236). -/
noncomputable def edgeStringOrderOpS (L : ℕ) (alpha : Fin 3) : ManyBodyOpS (Fin L) 2 :=
  ∑ x : Fin L, spinSSiteComponentS alpha x * edgeStringPrefixRotationS L alpha x.val

/-- **Hidden (string) long-range order**, Tasaki (8.1.10), p. 237: for every axis `α` the Rayleigh
expectation of `(Ô^{(α)}_string / L)²` in the state `Φ` is at least the `L`-independent constant
`q_α`.  The anisotropy `D` is deliberately absent: the ratio form *is* (8.1.10), not a
`D`-dependent hypothesis. -/
def HasStringLRO (L : ℕ) (Phi : (Fin L → Fin 3) → ℂ) (q : Fin 3 → ℝ) : Prop :=
  ∀ alpha : Fin 3, q alpha ≤ expectationRatioRe
    (((((L : ℂ)⁻¹) • edgeStringOrderOpS L alpha) ^ 2)) Phi

/-- The many-body site component is the site embedding of the single-site axis operator. -/
theorem spinSSiteComponentS_eq_onSiteS (alpha : Fin 3) (x : Fin L) :
    spinSSiteComponentS alpha x = onSiteS x (spinOneAxisS alpha) := by
  fin_cases alpha <;> rfl

/-! ## Structure of the prefix rotation -/

/-- The site-`y` factor of the prefix rotation `R^{(α)}_{<m}`: the half turn `u_α` when `y` lies
strictly left of `m`, and the identity otherwise. -/
private noncomputable def edgePrefixFactorS (L : ℕ) (alpha : Fin 3) (m : ℕ) (y : Fin L) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  if y.val < m then spinOneHalfTurnS alpha else 1

/-- Each prefix factor is an involution. -/
private theorem edgePrefixFactorS_mul_self (L : ℕ) (alpha : Fin 3) (m : ℕ) (y : Fin L) :
    edgePrefixFactorS L alpha m y * edgePrefixFactorS L alpha m y = 1 := by
  rw [edgePrefixFactorS]
  split
  · exact spinOneHalfTurnS_mul_self alpha
  · exact one_mul 1

/-- Each prefix factor is Hermitian. -/
private theorem edgePrefixFactorS_isHermitian (L : ℕ) (alpha : Fin 3) (m : ℕ) (y : Fin L) :
    (edgePrefixFactorS L alpha m y).IsHermitian := by
  rw [edgePrefixFactorS]
  split
  · exact spinOneHalfTurnS_isHermitian alpha
  · exact Matrix.isHermitian_one

/-- The prefix rotation as a product over `List.finRange`, with the factor selector exposed. -/
private theorem edgeStringPrefixRotationS_eq_map (L : ℕ) (alpha : Fin 3) (m : ℕ) :
    edgeStringPrefixRotationS L alpha m
      = ((List.finRange L).map fun y => onSiteS y (edgePrefixFactorS L alpha m y)).prod := by
  have hfun : (fun y : Fin L => if y.val < m then onSiteS y (spinOneHalfTurnS alpha) else 1)
      = fun y : Fin L => onSiteS y (edgePrefixFactorS L alpha m y) := by
    funext y
    rw [edgePrefixFactorS]
    split
    · rfl
    · exact (onSiteS_one y).symm
  rw [edgeStringPrefixRotationS, hfun, List.ofFn_eq_map]

/-- Site embeddings at distinct sites commute, so the factor list is pairwise commuting. -/
private theorem edgePrefixFactorS_pairwise (L : ℕ) (alpha : Fin 3) (m : ℕ)
    {l : List (Fin L)} (hl : l.Nodup) :
    (l.map fun y => onSiteS y (edgePrefixFactorS L alpha m y)).Pairwise Commute := by
  rw [List.pairwise_map]
  exact hl.imp fun {a b} hab => onSiteS_commute_of_ne hab _ _

/-- Splitting the prefix rotation off its site-`w` factor. -/
private theorem edgeStringPrefixRotationS_split (L : ℕ) (alpha : Fin 3) (m : ℕ) (w : Fin L) :
    edgeStringPrefixRotationS L alpha m
      = onSiteS w (edgePrefixFactorS L alpha m w) *
        ((((List.finRange L).erase w).map fun y =>
          onSiteS y (edgePrefixFactorS L alpha m y)).prod) := by
  rw [edgeStringPrefixRotationS_eq_map]
  have hperm := (List.perm_cons_erase (List.mem_finRange w)).map
    (fun y : Fin L => onSiteS y (edgePrefixFactorS L alpha m y))
  rw [hperm.prod_eq' (edgePrefixFactorS_pairwise L alpha m (List.nodup_finRange L))]
  simp

/-- The complement of the site-`w` factor commutes with every operator supported at `w`. -/
private theorem edgePrefixErased_commute (L : ℕ) (alpha : Fin 3) (m : ℕ) (w : Fin L)
    (A : Matrix (Fin 3) (Fin 3) ℂ) :
    Commute ((((List.finRange L).erase w).map fun y =>
      onSiteS y (edgePrefixFactorS L alpha m y)).prod) (onSiteS w A) := by
  refine Commute.list_prod_left _ _ ?_
  intro z hz
  rw [List.mem_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  refine onSiteS_commute_of_ne ?_ _ _
  intro hyw
  subst hyw
  exact (List.nodup_finRange L).not_mem_erase hy

/-- A product of involutive site embeddings at distinct sites is an involution. -/
private theorem onSiteListProd_mul_self (f : Fin L → Matrix (Fin 3) (Fin 3) ℂ)
    (hf : ∀ y, f y * f y = 1) :
    ∀ l : List (Fin L), l.Nodup →
      (l.map fun y => onSiteS y (f y)).prod * (l.map fun y => onSiteS y (f y)).prod = 1 := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
    intro hl
    rw [List.nodup_cons] at hl
    have hcomm : Commute (onSiteS a (f a) : ManyBodyOpS (Fin L) 2)
        ((t.map fun y => onSiteS y (f y)).prod) := by
      refine Commute.list_prod_right _ _ ?_
      intro z hz
      rw [List.mem_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      refine onSiteS_commute_of_ne ?_ _ _
      rintro rfl
      exact hl.1 hy
    rw [List.map_cons, List.prod_cons, hcomm.symm.mul_mul_mul_comm,
      onSiteS_mul_onSiteS_same, hf, onSiteS_one, ih hl.2, mul_one]

/-- A product of Hermitian site embeddings at distinct sites is Hermitian. -/
private theorem onSiteListProd_isHermitian (f : Fin L → Matrix (Fin 3) (Fin 3) ℂ)
    (hf : ∀ y, (f y).IsHermitian) :
    ∀ l : List (Fin L), l.Nodup →
      ((l.map fun y => onSiteS y (f y)).prod).IsHermitian := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
    intro hl
    rw [List.nodup_cons] at hl
    have hcomm : Commute (onSiteS a (f a) : ManyBodyOpS (Fin L) 2)
        ((t.map fun y => onSiteS y (f y)).prod) := by
      refine Commute.list_prod_right _ _ ?_
      intro z hz
      rw [List.mem_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      refine onSiteS_commute_of_ne ?_ _ _
      rintro rfl
      exact hl.1 hy
    rw [List.map_cons, List.prod_cons]
    exact Matrix.IsHermitian.mul_of_commute (onSiteS_isHermitian a (hf a)) (ih hl.2) hcomm

/-! ## Algebraic properties of the prefix rotation -/

/-- **The prefix rotation is an involution**: `R² = 1`, since each `u_α` is. -/
theorem edgeStringPrefixRotationS_mul_self (L : ℕ) (alpha : Fin 3) (m : ℕ) :
    edgeStringPrefixRotationS L alpha m * edgeStringPrefixRotationS L alpha m = 1 := by
  rw [edgeStringPrefixRotationS_eq_map]
  exact onSiteListProd_mul_self _ (edgePrefixFactorS_mul_self L alpha m) _
    (List.nodup_finRange L)

/-- **The prefix rotation is self-adjoint**, hence unitary. -/
theorem edgeStringPrefixRotationS_isHermitian (L : ℕ) (alpha : Fin 3) (m : ℕ) :
    (edgeStringPrefixRotationS L alpha m).IsHermitian := by
  rw [edgeStringPrefixRotationS_eq_map]
  exact onSiteListProd_isHermitian _ (edgePrefixFactorS_isHermitian L alpha m) _
    (List.nodup_finRange L)

/-- The prefix rotation is unitary: `RᴴR = 1`. -/
theorem edgeStringPrefixRotationS_conjTranspose_mul_self (L : ℕ) (alpha : Fin 3) (m : ℕ) :
    Matrix.conjTranspose (edgeStringPrefixRotationS L alpha m) *
        edgeStringPrefixRotationS L alpha m = 1 := by
  rw [(edgeStringPrefixRotationS_isHermitian L alpha m).eq]
  exact edgeStringPrefixRotationS_mul_self L alpha m

/-- **Sites at or beyond the prefix are untouched**: `R^{(α)}_{<m}` commutes with any operator
supported at a site `w` with `m ≤ w`. -/
theorem edgeStringPrefixRotationS_commute_onSiteS_of_le (L : ℕ) (alpha : Fin 3) (m : ℕ)
    {w : Fin L} (h : m ≤ w.val) (A : Matrix (Fin 3) (Fin 3) ℂ) :
    Commute (edgeStringPrefixRotationS L alpha m) (onSiteS w A) := by
  rw [edgeStringPrefixRotationS_split L alpha m w]
  have hfac : edgePrefixFactorS L alpha m w = 1 := if_neg (by omega)
  rw [hfac, onSiteS_one, one_mul]
  exact edgePrefixErased_commute L alpha m w A

/-- **Sites inside the prefix are conjugated by the half turn**: for `w < m`,
`R^{(α)}_{<m} A_w R^{(α)}_{<m} = (u_α A u_α)_w`. -/
theorem edgeStringPrefixRotationS_conj_onSiteS_of_lt (L : ℕ) (alpha : Fin 3) (m : ℕ)
    {w : Fin L} (h : w.val < m) (A : Matrix (Fin 3) (Fin 3) ℂ) :
    edgeStringPrefixRotationS L alpha m * onSiteS w A * edgeStringPrefixRotationS L alpha m
      = onSiteS w (spinOneHalfTurnS alpha * A * spinOneHalfTurnS alpha) := by
  set Q := ((((List.finRange L).erase w).map fun y =>
    onSiteS y (edgePrefixFactorS L alpha m y)).prod) with hQdef
  have hsplit : edgeStringPrefixRotationS L alpha m
      = onSiteS w (spinOneHalfTurnS alpha) * Q := by
    rw [hQdef, edgeStringPrefixRotationS_split L alpha m w, edgePrefixFactorS, if_pos h]
  have hpast : edgeStringPrefixRotationS L alpha m * onSiteS w A
      = onSiteS w (spinOneHalfTurnS alpha * A * spinOneHalfTurnS alpha) *
        edgeStringPrefixRotationS L alpha m := by
    rw [hsplit]
    calc onSiteS w (spinOneHalfTurnS alpha) * Q * onSiteS w A
        = onSiteS w (spinOneHalfTurnS alpha) * (Q * onSiteS w A) := by noncomm_ring
      _ = onSiteS w (spinOneHalfTurnS alpha) * (onSiteS w A * Q) :=
          by rw [(edgePrefixErased_commute L alpha m w A).eq]
      _ = onSiteS w (spinOneHalfTurnS alpha * A) * Q := by
          rw [← mul_assoc, onSiteS_mul_onSiteS_same]
      _ = onSiteS w (spinOneHalfTurnS alpha * A * spinOneHalfTurnS alpha) *
            (onSiteS w (spinOneHalfTurnS alpha) * Q) := by
          rw [← mul_assoc, onSiteS_mul_onSiteS_same, mul_assoc, mul_assoc,
            spinOneHalfTurnS_mul_self alpha, mul_one]
  rw [hpast, mul_assoc, edgeStringPrefixRotationS_mul_self, mul_one]

/-- **The prefix rotation commutes with its own axis component at every site**: inside the prefix
because `u_α` commutes with `Ŝ^{(α)}`, outside because the supports are disjoint. -/
theorem edgeStringPrefixRotationS_commute_component (L : ℕ) (alpha : Fin 3) (m : ℕ) (x : Fin L) :
    Commute (edgeStringPrefixRotationS L alpha m) (spinSSiteComponentS alpha x) := by
  rw [spinSSiteComponentS_eq_onSiteS]
  by_cases h : x.val < m
  · have hconj := edgeStringPrefixRotationS_conj_onSiteS_of_lt L alpha m h (spinOneAxisS alpha)
    rw [spinOneHalfTurnS_conj_spinOneAxisS, if_pos rfl, one_smul] at hconj
    have hstep := congrArg (fun M => M * edgeStringPrefixRotationS L alpha m) hconj
    simp only [mul_assoc, edgeStringPrefixRotationS_mul_self, mul_one] at hstep
    exact hstep
  · exact edgeStringPrefixRotationS_commute_onSiteS_of_le L alpha m (by omega) _

/-- Two prefix rotations about the same axis commute. -/
theorem edgeStringPrefixRotationS_commute_self (L : ℕ) (alpha : Fin 3) (m m' : ℕ) :
    Commute (edgeStringPrefixRotationS L alpha m) (edgeStringPrefixRotationS L alpha m') := by
  rw [edgeStringPrefixRotationS_eq_map, edgeStringPrefixRotationS_eq_map]
  refine Commute.list_prod_left _ _ ?_
  intro z hz
  rw [List.mem_map] at hz
  obtain ⟨y, _, rfl⟩ := hz
  refine Commute.list_prod_right _ _ ?_
  intro v hv
  rw [List.mem_map] at hv
  obtain ⟨w, _, rfl⟩ := hv
  by_cases hyw : y = w
  · subst hyw
    have hfac : edgePrefixFactorS L alpha m y * edgePrefixFactorS L alpha m' y
        = edgePrefixFactorS L alpha m' y * edgePrefixFactorS L alpha m y := by
      unfold edgePrefixFactorS
      split <;> split <;> simp
    change onSiteS y (edgePrefixFactorS L alpha m y) * onSiteS y (edgePrefixFactorS L alpha m' y)
      = onSiteS y (edgePrefixFactorS L alpha m' y) * onSiteS y (edgePrefixFactorS L alpha m y)
    rw [onSiteS_mul_onSiteS_same, onSiteS_mul_onSiteS_same, hfac]
  · exact onSiteS_commute_of_ne hyw _ _

/-! ## The string operator -/

/-- The string operator's site-`x` term `A_x = Ŝ_x^{(α)} R^{(α)}_{<x}` is Hermitian, since its two
factors are Hermitian and commute. -/
theorem edgeStringTerm_isHermitian (L : ℕ) (alpha : Fin 3) (x : Fin L) :
    (spinSSiteComponentS alpha x * edgeStringPrefixRotationS L alpha x.val).IsHermitian := by
  rw [spinSSiteComponentS_eq_onSiteS]
  refine Matrix.IsHermitian.mul_of_commute (onSiteS_isHermitian x (spinOneAxisS_isHermitian alpha))
    (edgeStringPrefixRotationS_isHermitian L alpha x.val) ?_
  have h := edgeStringPrefixRotationS_commute_component L alpha x.val x
  rw [spinSSiteComponentS_eq_onSiteS] at h
  exact h.symm

/-- **The string operator is self-adjoint** (Tasaki p. 236: at `S = 1` the exponential factor is its
own adjoint, and its factors act on sites disjoint from the leading spin component). -/
theorem edgeStringOrderOpS_isHermitian (L : ℕ) (alpha : Fin 3) :
    (edgeStringOrderOpS L alpha).IsHermitian := by
  change Matrix.conjTranspose (edgeStringOrderOpS L alpha) = edgeStringOrderOpS L alpha
  rw [edgeStringOrderOpS, Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun x _ => (edgeStringTerm_isHermitian L alpha x).eq

/-- All string terms mutually commute: `u_α` commutes with `Ŝ^{(α)}`, prefix rotations commute with
each other, and distinct sites are disjoint.  This is the crux of the support argument for the
double commutator. -/
theorem edgeStringTerm_commute (L : ℕ) (alpha : Fin 3) (x y : Fin L) :
    Commute (spinSSiteComponentS alpha x * edgeStringPrefixRotationS L alpha x.val)
      (spinSSiteComponentS alpha y * edgeStringPrefixRotationS L alpha y.val) := by
  have hcomp : Commute (spinSSiteComponentS alpha x) (spinSSiteComponentS alpha y) := by
    by_cases hxy : x = y
    · rw [hxy]
    · rw [spinSSiteComponentS_eq_onSiteS, spinSSiteComponentS_eq_onSiteS]
      exact onSiteS_commute_of_ne hxy _ _
  refine Commute.mul_left (Commute.mul_right hcomp ?_) ?_
  · exact (edgeStringPrefixRotationS_commute_component L alpha y.val x).symm
  · exact Commute.mul_right (edgeStringPrefixRotationS_commute_component L alpha x.val y)
      (edgeStringPrefixRotationS_commute_self L alpha x.val y.val)

/-! ## Conjugation by a global on-site involution -/

/-- **Conjugation by an involution is multiplicative**: `U (X Y) U = (U X U)(U Y U)` when
`U² = 1`. -/
theorem conj_mul_of_mul_self {U : ManyBodyOpS (Fin L) 2} (hU : U * U = 1)
    (X Y : ManyBodyOpS (Fin L) 2) :
    U * (X * Y) * U = (U * X * U) * (U * Y * U) := by
  rw [show (U * X * U) * (U * Y * U) = U * X * (U * U) * (Y * U) by noncomm_ring, hU]
  noncomm_ring

/-- Conjugation by an involution distributes over an ordered product. -/
private theorem conj_listProd {U : ManyBodyOpS (Fin L) 2} (hU : U * U = 1)
    (l : List (ManyBodyOpS (Fin L) 2)) :
    U * l.prod * U = (l.map fun X => U * X * U).prod := by
  induction l with
  | nil => simpa using hU
  | cons a t ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih, ← conj_mul_of_mul_self hU]

/-- **The prefix rotation is invariant under any global half turn**: if the involution `U` acts
site-wise by conjugation with a single-site involution `V` that fixes `u_α`, then `U R U = R`.
This is the many-body lift of `spinOneHalfTurnS_conj_spinOneHalfTurnS`. -/
theorem edgeStringPrefixRotationS_conj (L : ℕ) (alpha : Fin 3) (m : ℕ)
    (U : ManyBodyOpS (Fin L) 2) (V : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : U * U = 1) (hV : V * V = 1)
    (hVhalf : V * spinOneHalfTurnS alpha * V = spinOneHalfTurnS alpha)
    (hconj : ∀ (z : Fin L) (A : Matrix (Fin 3) (Fin 3) ℂ),
      U * onSiteS z A * U = onSiteS z (V * A * V)) :
    U * edgeStringPrefixRotationS L alpha m * U = edgeStringPrefixRotationS L alpha m := by
  rw [edgeStringPrefixRotationS_eq_map, conj_listProd hU, List.map_map]
  congr 1
  apply List.map_congr_left
  intro y _
  simp only [Function.comp_apply]
  rw [hconj]
  congr 1
  rw [edgePrefixFactorS]
  split
  · exact hVhalf
  · rw [mul_one]; exact hV

/-- **The conjugation law of the string operator** (Tasaki (8.1.12), p. 238): a global half turn
`U` acting site-wise by a single-site involution `V` that fixes `u_α` and sends `Ŝ^{(α)}` to
`c Ŝ^{(α)}` conjugates the string operator to `c` times itself. -/
theorem edgeStringOrderOpS_conj (L : ℕ) (alpha : Fin 3)
    (U : ManyBodyOpS (Fin L) 2) (V : Matrix (Fin 3) (Fin 3) ℂ) (c : ℂ)
    (hU : U * U = 1) (hV : V * V = 1)
    (hVhalf : V * spinOneHalfTurnS alpha * V = spinOneHalfTurnS alpha)
    (hVaxis : V * spinOneAxisS alpha * V = c • spinOneAxisS alpha)
    (hconj : ∀ (z : Fin L) (A : Matrix (Fin 3) (Fin 3) ℂ),
      U * onSiteS z A * U = onSiteS z (V * A * V)) :
    U * edgeStringOrderOpS L alpha * U = c • edgeStringOrderOpS L alpha := by
  rw [edgeStringOrderOpS, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [conj_mul_of_mul_self hU, edgeStringPrefixRotationS_conj L alpha x.val U V hU hV hVhalf hconj,
    spinSSiteComponentS_eq_onSiteS, hconj, hVaxis, onSiteS_smul, Matrix.smul_mul]

/-- Every string term commutes with the whole string operator, since all string terms mutually
commute. -/
theorem edgeStringTerm_commute_edgeStringOrderOpS (L : ℕ) (alpha : Fin 3) (x : Fin L) :
    Commute (spinSSiteComponentS alpha x * edgeStringPrefixRotationS L alpha x.val)
      (edgeStringOrderOpS L alpha) := by
  rw [edgeStringOrderOpS]
  exact Commute.sum_right _ _ _ fun y _ => edgeStringTerm_commute L alpha x y

/-! ## The hidden-order norm bound -/

/-- **The proof-facing form of (8.1.10)**: hidden order gives the norm lower bound
`q_α L² ‖Φ‖² ≤ ‖Ô^{(α)}_string Φ‖²`, using only self-adjointness of the string operator.  In
particular the trial vector `Ô^{(α)}_string Φ` is nonzero when `q_α > 0` and `0 < L`. -/
theorem hasStringLRO_vecNormSqRe_bound (L : ℕ) (alpha : Fin 3) {q : Fin 3 → ℝ}
    {Phi : (Fin L → Fin 3) → ℂ} (hPhi : Phi ≠ 0) (hLRO : HasStringLRO L Phi q) :
    q alpha * (L : ℝ) ^ 2 * vecNormSqRe Phi
      ≤ vecNormSqRe ((edgeStringOrderOpS L alpha).mulVec Phi) := by
  have hden : 0 < (star Phi ⬝ᵥ Phi).re := dotProduct_star_self_re_pos hPhi
  have hnn : (0 : ℝ) ≤ vecNormSqRe ((edgeStringOrderOpS L alpha).mulVec Phi) :=
    (Complex.le_def.mp (dotProduct_star_self_nonneg _)).1
  have hHerm := (edgeStringOrderOpS_isHermitian L alpha).eq
  have hnum : star Phi ⬝ᵥ (((((L : ℂ)⁻¹) • edgeStringOrderOpS L alpha) ^ 2)).mulVec Phi
      = ((L : ℂ)⁻¹ * (L : ℂ)⁻¹) *
        (star ((edgeStringOrderOpS L alpha).mulVec Phi) ⬝ᵥ
          (edgeStringOrderOpS L alpha).mulVec Phi) := by
    rw [pow_two, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← Matrix.mulVec_mulVec,
      star_dotProduct_mulVec_conjTranspose, hHerm]
  have hnumre : (star Phi ⬝ᵥ (((((L : ℂ)⁻¹) • edgeStringOrderOpS L alpha) ^ 2)).mulVec Phi).re
      = ((L : ℝ)⁻¹ * (L : ℝ)⁻¹) *
        vecNormSqRe ((edgeStringOrderOpS L alpha).mulVec Phi) := by
    rw [hnum, show ((L : ℂ)⁻¹ * (L : ℂ)⁻¹) = ((((L : ℝ)⁻¹ * (L : ℝ)⁻¹ : ℝ)) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul]
    rfl
  have hq := hLRO alpha
  rw [expectationRatioRe, hnumre, le_div_iff₀ hden] at hq
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    simpa using hnn
  · have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast h
    have hmul := mul_le_mul_of_nonneg_left hq (le_of_lt (pow_pos hL0 2))
    have hsimp : (L : ℝ) ^ 2 * (((L : ℝ)⁻¹ * (L : ℝ)⁻¹) *
        vecNormSqRe ((edgeStringOrderOpS L alpha).mulVec Phi))
        = vecNormSqRe ((edgeStringOrderOpS L alpha).mulVec Phi) := by
      field_simp
    rw [hsimp] at hmul
    have hcast : (star Phi ⬝ᵥ Phi).re = vecNormSqRe Phi := rfl
    rw [hcast] at hmul
    linarith

end LatticeSystem.Quantum
