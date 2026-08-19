import LatticeSystem.Quantum.SpinS.GeneralAKLT
import LatticeSystem.Quantum.SpinS.TwoSiteSliceS
import LatticeSystem.Quantum.SpinS.AKLTKnabe.SiteBlockEmbeddingD5b
import LatticeSystem.Quantum.SpinS.AKLTOpenChainWeylFactorization
import LatticeSystem.Quantum.SpinS.GeneralSWeylCasimir
import LatticeSystem.Quantum.SpinS.GeneralSCasimirDescent
import LatticeSystem.Math.MvPolynomial.PairwiseCoprimeProd

/-!
# Tasaki §8.3.1: the general-integer-`S` open AKLT chain, bond term and bond divisibility

Tasaki's AKLT bond term for two spin-`S` sites is *not* a single operator but a whole family
(eq. (7.3.2), p. 208, written there for `S = 2`): a positive combination
`Σ_{J=S+1}^{2S} a_J P̂_J[Ŝ_x + Ŝ_{x+1}]`, `a_J > 0`, of the projections onto the **high** total
spins, plus an arbitrary real constant ("we are giving penalties to the two highest values").
Only the kernel `⊕_{J≤S}` matters for the ground states, so the coefficients are free; the book
itself calls the explicit polynomial presentation (7.3.3), p. 208, "a very artificial
Hamiltonian".

This module builds the canonical single-polynomial member of that family, the **Casimir penalty**

`ĥ_x = q_S(Ĉ_x) = ∏_{j=0}^{S} (Ĉ_x − j(j+1))`,  `Ĉ_x = (Ŝ_x + Ŝ_{x+1})² = 2S(S+1) + 2 Ŝ_x·Ŝ_{x+1}`,

which acts on the total-spin-`J` bond subspace by the scalar `∏_{j=0}^{S}(J(J+1) − j(j+1))`: zero
for `J ≤ S` and strictly positive for `J > S`.  The two *scalar* facts about the weight function
proved here (`casimirPenaltyWeight_eq_zero`, `casimirPenaltyWeight_pos`) say exactly that `q_S` is
nonnegative at every Casimir eigenvalue; `GeneralSCasimirSpectrum` turns that into the consequence
the ground-state analysis actually uses, positive semidefiniteness of the bond term
(`bondCasimirPenaltyS_posSemidef`).  Family membership itself — the operator identity
`q_S(Ĉ) = Σ_J a_J P̂_J`, which would need the full spectral decomposition of `Ĉ` — is not proved,
and nothing in the tree consumes it.  At `S = 1` the polynomial collapses to
`24 · P̂₂[Ŝ_x + Ŝ_{x+1}]`, reproducing the
`S = 1` chain of §7.1.2, eq. (7.1.5), p. 180 up to the harmless positive factor.

The spin is a **positive integer** `S`, forced by the book: p. 209 explains that short-ranged
valence bonds exist iff `S` is an integer, and for half-odd-integer `S` the open-chain ground
states are doubly degenerate rather than `(S+1)²`-fold.  The on-site index is therefore `2 * S`
(site-state type `Fin (2S+1)`), and the odd case is excluded by the type itself.

Two reductions are proved on top of the definition.  Locally, `ĥ_x` is the block embedding
(`onEmbS`) of a single two-site matrix, so being annihilated by `ĥ_x` is a condition on each
two-site slice separately — this is what confines the remaining su(2) work to a fixed
`(2S+1)² × (2S+1)²` problem.  Globally, if every open bond annihilates a state then the
prime-power product `∏_x f_x^S` of bond factors divides its Weyl image, the polynomial input of
the `(S+1)²` ground-state count asserted at §8.3.1, p. 252.  Everything below that product is an
exact characterisation: the two-site kernel of `ĥ^loc` is *precisely* the Weyl images divisible by
`f₂^S` — obtained here by transporting the ordered product of Casimir factors through the Weyl map
(`weylMap_mulVec_bondCasimirS`) and running the polynomial Casimir descent
(`GeneralSCasimirDescent`) from the Weyl bidegree `(2S, 2S)` down to level `S`, where the descent
family annihilates its own layer — and a single bond term of the chain annihilates a state
precisely when `f_x^S` divides its Weyl image
(`bondCasimirPenaltyS_mulVec_eq_zero_iff_fBond_pow_dvd`).  Only the assembly over the `L − 1` bonds
is one-directional, since it consumes the pairwise coprimality of the bond factors.

The bond sum runs over `openBonds L`, never over `Finset.univ`: the open chain of eq. (7.2.46),
p. 205 has exactly `L − 1` bonds, and summing over `Finset.univ` silently reinstates the wrap bond
and hence the periodic model.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.1.2, eq. (7.1.5), p. 180; §7.1.3, eqs. (7.1.22)–(7.1.25), pp. 186–188; §7.2.3,
eq. (7.2.46), p. 205, Problem 7.2.3.b, p. 207 and solution (S.77), p. 508; §7.3.1,
eqs. (7.3.1)–(7.3.3) and footnote 40, pp. 208–209; §8.3.1, p. 252.
-/

open MvPolynomial

namespace LatticeSystem.Quantum

open Matrix
open LatticeSystem.Math LatticeSystem.Quantum.AKLTUniqueness
open LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## The Casimir penalty weights -/

/-- The **Casimir penalty weight** `a_J = q_S(J(J+1)) = ∏_{j=0}^{S} (J(J+1) − j(j+1))`: the value
the defining polynomial `q_S` takes at the total-spin-`J` eigenvalue `J(J+1)` of `Ĉ`.  These are the
coefficients `a_J` of Tasaki's family (7.3.2), p. 208.  Stated over `ℝ` so that positivity is
available directly; the two sign facts below are what
`GeneralSCasimirSpectrum.localCasimirPenalty_posSemidef` consumes. -/
noncomputable def casimirPenaltyWeight (S J : ℕ) : ℝ :=
  ∏ j ∈ Finset.range (S + 1), ((J : ℝ) * (J + 1) - (j : ℝ) * (j + 1))

/-- **No penalty on the low total spins.**  For `J ≤ S` the factor with `j = J` vanishes, so
`a_J = 0` — the weight vanishes exactly on the intended kernel `⊕_{J≤S}` of Tasaki's family
(7.3.2), p. 208 (the `S` valence bonds per link). -/
theorem casimirPenaltyWeight_eq_zero {S J : ℕ} (h : J ≤ S) : casimirPenaltyWeight S J = 0 :=
  Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.lt_succ_of_le h)) (by ring)

/-- **Strictly positive penalty on the high total spins.**  For `J > S` every factor satisfies
`J(J+1) > j(j+1)` (as `j ≤ S < J`), so `a_J > 0` — the weight is positive exactly on the intended
penalized total spins `J = S+1, …, 2S`, the "two highest values" of Tasaki's `S = 2` instance
(7.3.2), p. 208.  No upper bound on `J` is needed. -/
theorem casimirPenaltyWeight_pos {S J : ℕ} (h : S < J) : 0 < casimirPenaltyWeight S J := by
  refine Finset.prod_pos fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hjJ : (j : ℝ) < (J : ℝ) := by exact_mod_cast (by omega : j < J)
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  nlinarith

/-! ## The bond term and the open-chain Hamiltonian -/

/-- The **general-`S` AKLT bond term** `ĥ_x = q_S(Ĉ_x) = ∏_{j=0}^{S} (Ĉ_x − j(j+1)·1)` on the bond
`{x, y}` of two spin-`S` sites (`N = 2S`), the intended canonical single-polynomial member of
Tasaki's family (7.3.2), p. 208 with the weights `casimirPenaltyWeight S J`; the family membership
identity `q_S(Ĉ) = Σ_J a_J P̂_J` itself is not proved (see the module doc comment), only the
consequence used downstream, `bondCasimirPenaltyS_posSemidef`.

The factors are polynomials in the single operator `Ĉ = bondCasimirS x y (2S)` and hence commute,
but `ManyBodyOpS` is a noncommutative matrix ring, so the product is taken as an ordered
`List.ofFn … |>.prod` — the same shape as the *top-spin* projector `bondMaxSpinProjectionS`, from
which this differs by its index range: `j` runs over `Fin (S+1)`, i.e. the roots are `j(j+1)` for
`j = 0, …, S`, not `j = 0, …, N−1`.  The two families coincide only at `S = 1`.

The spin index is `2 * S` rather than a free `N`: the `(S+1)²`-fold degeneracy of §8.3.1, p. 252
holds for integer `S` only, and the type enforces evenness of `N = 2S`. -/
noncomputable def bondCasimirPenaltyS (x y : Λ) (S : ℕ) : ManyBodyOpS Λ (2 * S) :=
  (List.ofFn fun j : Fin (S + 1) =>
    bondCasimirS x y (2 * S) - ((j : ℂ) * (j + 1)) • (1 : ManyBodyOpS Λ (2 * S))).prod

/-- The **general-`S` open-chain AKLT Hamiltonian** `Ĥ = Σ_{x=1}^{L−1} ĥ_x`, the general-spin
counterpart of the `S = 1` open chain `openProjHamiltonianS` (Tasaki eq. (7.2.46), p. 205) and the
model whose ground space is claimed `(S+1)²`-fold degenerate at §8.3.1, p. 252.

The sum ranges over `openBonds L` (`card = L − 1`) and never over `Finset.univ`: on `Fin L` the
successor `ringSucc` wraps around, so a sum over `Finset.univ` is the *periodic* chain. -/
noncomputable def openAKLTHamiltonianGeneralS (L S : ℕ) : ManyBodyOpS (Fin L) (2 * S) :=
  ∑ x ∈ openBonds L, bondCasimirPenaltyS x (ringSucc x) S

/-- The **local (two-site) general-`S` bond term** on `ℂ^{2S+1} ⊗ ℂ^{2S+1}`: the bond term of the
single bond of a two-site chain.  Every bond term of a long chain is its block embedding
(`bondCasimirPenaltyS_eq_onEmbS`), which is what turns the ground-state condition into a fixed
finite-dimensional local problem. -/
noncomputable def localCasimirPenalty (S : ℕ) : ManyBodyOpS (Fin 2) (2 * S) :=
  bondCasimirPenaltyS (0 : Fin 2) 1 S

/-! ## `S = 1` reproduces the existing spin-one model -/

/-- **`S = 1` back-compatibility.**  `q_1(Ĉ) = Ĉ (Ĉ − 2) = 24 · P̂₂[Ŝ_x + Ŝ_y]`: at `S = 1` the
Casimir penalty is the spin-two bond projection of Tasaki eq. (7.1.5), p. 180 up to the positive
factor `24 = casimirPenaltyWeight 1 2`.  The identity holds for *any* two sites, distinct or not,
being an identity in the commutative subalgebra generated by `Ŝ_x·Ŝ_y`. -/
theorem bondCasimirPenaltyS_one {L : ℕ} (x y : Fin L) :
    bondCasimirPenaltyS x y 1 = (24 : ℂ) • bondSpin2ProjectionS x y := by
  have hC : bondCasimirS x y 2
      = (4 : ℂ) • (1 : ManyBodyOpS (Fin L) 2) + (2 : ℂ) • spinSDot x y 2 := by
    rw [bondCasimirS]
    norm_num
  change (List.ofFn fun j : Fin 2 =>
      bondCasimirS x y 2 - ((j : ℂ) * (j + 1)) • (1 : ManyBodyOpS (Fin L) 2)).prod
    = (24 : ℂ) • bondSpin2ProjectionS x y
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_cons,
    List.prod_nil, hC, bondSpin2ProjectionS]
  norm_num
  simp only [mul_sub, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
    one_mul, mul_one, smul_add]
  module

/-- **`S = 1` back-compatibility of the Hamiltonian.**  `Ĥ^{(S=1)} = 24 · Ĥ'^open`, the open
projector Hamiltonian of Tasaki eq. (7.2.46) / (7.1.7), summand by summand. -/
theorem openAKLTHamiltonianGeneralS_one (L : ℕ) :
    openAKLTHamiltonianGeneralS L 1 = (24 : ℂ) • openProjHamiltonianS L := by
  change (∑ x ∈ openBonds L, bondCasimirPenaltyS x (ringSucc x) 1)
    = (24 : ℂ) • openProjHamiltonianS L
  rw [openProjHamiltonianS, Finset.smul_sum]
  exact Finset.sum_congr rfl fun x _ => bondCasimirPenaltyS_one x (ringSucc x)

/-! ## Global-to-local reduction of the bond term -/

/-- **The bond term is a block embedding of its local two-site matrix.**  Each factor
`Ĉ − j(j+1)` is an affine expression in `Ŝ_x·Ŝ_y`, which is itself a block embedding
(`spinSDot_eq_onEmbS`); `onEmbS_list_prod` then transports the whole ordered product. -/
theorem bondCasimirPenaltyS_eq_onEmbS {x y : Λ} (hxy : x ≠ y) (S : ℕ) :
    bondCasimirPenaltyS x y S = onEmbS ![x, y] (localCasimirPenalty S) := by
  rw [localCasimirPenalty, bondCasimirPenaltyS, bondCasimirPenaltyS,
    onEmbS_list_prod ![x, y] (injective_bondEmb hxy)]
  apply congrArg List.prod
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  simp only [Function.comp_apply, bondCasimirS, sub_eq_add_neg, onEmbS_add, onEmbS_smul,
    onEmbS_neg, onEmbS_one, spinSDot_eq_onEmbS hxy (2 * S)]

/-- **Zero energy on a bond is a slicewise local condition.**  A state is annihilated by the bond
term `ĥ_{x,y}` exactly when the local matrix `localCasimirPenalty S` annihilates every two-site
slice obtained by freezing the spectator sites.  This is the reduction that confines the remaining
su(2) analysis to the fixed `(2S+1)² × (2S+1)²` two-site problem. -/
theorem bondCasimirPenaltyS_mulVec_eq_zero_iff_slices {x y : Λ} (hxy : x ≠ y) (S : ℕ)
    (Φ : (Λ → Fin (2 * S + 1)) → ℂ) :
    (bondCasimirPenaltyS x y S).mulVec Φ = 0 ↔
      ∀ τ : Λ → Fin (2 * S + 1),
        (localCasimirPenalty S).mulVec (twoSiteSliceS x y Φ τ) = 0 := by
  rw [bondCasimirPenaltyS_eq_onEmbS hxy S, onEmbS_mulVec_eq_zero_iff_twoSiteSlices hxy]

/-! ## The local kernel: Casimir descent on the two-site Weyl image -/

/-- **Weyl transport of one Casimir factor.**  The factor `Ĉ − b` of the bond term becomes the
descent step `A_{N(N+1) − b}` on the Weyl image (`weylMap_mulVec_bondCasimirS`). -/
private theorem weylMap_mulVec_bondCasimirS_sub_smul (N : ℕ) (b : ℂ)
    (ψ : (Fin 2 → Fin (N + 1)) → ℂ) :
    weylMap ((bondCasimirS (0 : Fin 2) 1 N - b • (1 : ManyBodyOpS (Fin 2) N)).mulVec ψ)
      = casimirDescentStep ((N : ℂ) * (N + 1) - b) (weylMap ψ) := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, map_sub, map_smul,
    weylMap_mulVec_bondCasimirS, casimirDescentStep, sub_smul]
  module

/-- **Weyl transport of an ordered product of Casimir factors.**  The two-site product
`∏_b (Ĉ − b)` acts on the Weyl image as the fold of the descent steps with the shifted scalars
`N(N+1) − b`; the factors are transported one at a time through `Matrix.mulVec_mulVec`. -/
theorem weylMap_mulVec_casimir_list (N : ℕ) (bs : List ℂ) (φ : (Fin 2 → Fin (N + 1)) → ℂ) :
    weylMap ((bs.map fun b =>
        bondCasimirS (0 : Fin 2) 1 N - b • (1 : ManyBodyOpS (Fin 2) N)).prod.mulVec φ)
      = List.foldr casimirDescentStep (weylMap φ) (bs.map fun b => (N : ℂ) * (N + 1) - b) := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.foldr_cons, ← Matrix.mulVec_mulVec,
      weylMap_mulVec_bondCasimirS_sub_smul, ih]

/-- **The local kernel is exactly the `f₂^S`-divisible Weyl images.**  A two-site state is
annihilated by the local bond term `ĥ^loc = ∏_{j=0}^{S}(Ĉ − j(j+1))` **iff** its Weyl image is
divisible by the `S`-th power of the bond factor.  The transported product is the Casimir descent of
level `N = 2S`, and the descent fold vanishes exactly on the `f₂^S` multiples
(`casimirDescentFold_eq_zero_iff_bondFactor_pow_dvd`); the Weyl map being injective, the two
kernels correspond.

This is the general-`S` form of Tasaki's `S = 1` computation (§7.1.3, eqs. (7.1.22)–(7.1.25),
pp. 186–188): each of the `S` valence bonds of the link contributes one factor
`f₂ = u₀v₁ − v₀u₁`. -/
theorem localCasimirPenalty_mulVec_eq_zero_iff_f2_pow_dvd (S : ℕ)
    (φ : (Fin 2 → Fin (2 * S + 1)) → ℂ) :
    (localCasimirPenalty S).mulVec φ = 0 ↔ f2 ^ S ∣ weylMap (L := 2) φ := by
  set bs : List ℂ := List.ofFn fun j : Fin (S + 1) => ((j : ℕ) : ℂ) * (((j : ℕ) : ℂ) + 1)
    with hbs
  have hprod : localCasimirPenalty S
      = (bs.map fun b =>
          bondCasimirS (0 : Fin 2) 1 (2 * S) - b • (1 : ManyBodyOpS (Fin 2) (2 * S))).prod := by
    rw [localCasimirPenalty, bondCasimirPenaltyS, hbs, List.map_ofFn]
    rfl
  have hscal : (bs.map fun b => ((2 * S : ℕ) : ℂ) * (((2 * S : ℕ) : ℂ) + 1) - b)
      = casimirPenaltyScalars (S + S) S := by
    rw [hbs, casimirPenaltyScalars, List.map_ofFn]
    refine congrArg List.ofFn (funext fun j => ?_)
    simp only [Function.comp_apply]
    push_cast
    ring
  have hfold := weylMap_mulVec_casimir_list (2 * S) bs φ
  rw [← hprod, hscal] at hfold
  have hhom := weylMap_isWeightedHomogeneous (L := 2) φ
  rw [show (∑ x : Fin 2, Finsupp.single x (2 * S) : Fin 2 →₀ ℕ)
      = Finsupp.single 0 (S + S) + Finsupp.single 1 (S + S) by
    rw [Fin.sum_univ_two, two_mul]] at hhom
  rw [← casimirDescentFold_eq_zero_iff_bondFactor_pow_dvd S hhom, ← hfold]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    exact weylMap_injective (by rw [h, map_zero])

/-! ## Prime-power bond divisibility of the Weyl image -/

/-- **The bond kernel is exactly the `f_x^S`-divisible Weyl images.**  A chain state is annihilated
by the bond term `ĥ_x` of the bond `{x, ringSucc x}` **iff** the `S`-th power of the global bond
factor `f_x = u_x v_{x+1} − v_x u_{x+1}` divides its Weyl image — the polynomial form of "the link
carries `S` valence bonds" (Tasaki §8.3.1, p. 252).

Both directions compose the same two steps, the slicewise reduction of the bond term
(`bondCasimirPenaltyS_mulVec_eq_zero_iff_slices`) and the two-site kernel description
(`localCasimirPenalty_mulVec_eq_zero_iff_f2_pow_dvd`), with the local-to-global bridge
`fBond_pow_dvd_weylMap_of_local` in one direction and its converse
`f2_pow_dvd_weylMap_bondSlice_of_fBond_pow_dvd` in the other. -/
theorem bondCasimirPenaltyS_mulVec_eq_zero_iff_fBond_pow_dvd {L : ℕ} (hL : 1 < L) (x : Fin L)
    (S : ℕ) (Φ : (Fin L → Fin (2 * S + 1)) → ℂ) :
    (bondCasimirPenaltyS x (ringSucc x) S).mulVec Φ = 0 ↔ fBond x ^ S ∣ weylMap Φ := by
  rw [bondCasimirPenaltyS_mulVec_eq_zero_iff_slices (ne_ringSucc hL x) S Φ]
  constructor
  · intro h
    exact fBond_pow_dvd_weylMap_of_local x hL S Φ fun r =>
      (localCasimirPenalty_mulVec_eq_zero_iff_f2_pow_dvd S _).mp (h r)
  · intro h τ
    exact (localCasimirPenalty_mulVec_eq_zero_iff_f2_pow_dvd S _).mpr
      (f2_pow_dvd_weylMap_bondSlice_of_fBond_pow_dvd hL x S Φ h τ)

/-- **General-`S` open-chain bond kernel implies prime-power divisibility.**  If the state `Φ` is
annihilated by the bond term of every open bond, then the product `∏_{x} f_x^S` of the `S`-th
powers of the bond factors `f_x = u_x v_{x+1} − v_x u_{x+1}` divides its Weyl image
(Tasaki §7.1.3, eqs. (7.1.22)–(7.1.25), pp. 186–188; the open-chain form is Problem 7.2.3.b,
p. 207, solution (S.77), p. 508, where the `S = 1` product carries the exponent `1`).  This is the
polynomial input of the `(S+1)²` ground-state count asserted at §8.3.1, p. 252.

The per-bond input is `bondCasimirPenaltyS_mulVec_eq_zero_iff_fBond_pow_dvd`, which identifies the
kernel of a single bond term with the `f_x^S`-divisible Weyl images.  What is proved here is the
assembly over bonds, which needs the bond factors to be pairwise relatively prime.  Coprimality of
the *powers* follows from coprimality of the factors (`IsRelPrime.pow`), so no primality argument is
repeated. -/
theorem prod_fBond_pow_dvd_weylMap_of_annihilated {L : ℕ} (hL : 2 ≤ L) (S : ℕ)
    (Φ : (Fin L → Fin (2 * S + 1)) → ℂ)
    (hΦ : ∀ x ∈ openBonds L, (bondCasimirPenaltyS x (ringSucc x) S).mulVec Φ = 0) :
    (∏ x ∈ openBonds L, fBond x ^ S) ∣ weylMap Φ := by
  have hL1 : 1 < L := hL
  refine prod_dvd_of_pairwise_isRelPrime _ _ _ (fun x hx => ?_) (fun x hx y hy hxy => ?_)
  · exact (bondCasimirPenaltyS_mulVec_eq_zero_iff_fBond_pow_dvd hL1 x S Φ).mp (hΦ x hx)
  · exact (fBond_isRelPrime_openBonds hL (Finset.mem_coe.mp hx) (Finset.mem_coe.mp hy) hxy).pow

end LatticeSystem.Quantum
