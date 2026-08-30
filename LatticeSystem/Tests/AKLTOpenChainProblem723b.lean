import LatticeSystem.Quantum.SpinS.AKLTOpenChainWeylFactorization
import LatticeSystem.Quantum.SpinS.AKLTOpenChainCompleteness
import LatticeSystem.Quantum.SpinS.AKLTUniqueness.ProductBondDivisibility

/-!
# §7.2.3 Problem 7.2.3.b — completeness of the open-chain `S = 1` AKLT ground space

(Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Problem 7.2.3.b, p. 207,
solution (S.77), p. 508.)

Signature and negative-control tests only, no production code: `example`s that pin down the exact
statements of `weight_siteWeight_apply`, `weylMapWeight_apply`, `fBond_isRelPrime_of_witness`,
`exists_open_bond_var_witness`, `fBond_isRelPrime_openBonds`, `fBond_isWeightedHomogeneous`,
`prod_openBonds_fBond_isWeightedHomogeneous`, `prod_openBonds_fBond_ne_zero`,
`prodWeight_apply_first`, `prodWeight_apply_last`, `prodWeight_apply_of_interior`,
`weylMap_openGroundForm_eq_boundary_smul_prod`, `openGroundSpace_isVBSGroundForm`,
`finrank_openAKLTGroundSpace_le_four`, `finrank_openAKLTGroundSpace_eq_four`,
`openAKLTGroundSpace_eq_span_openVBSState`, so that a later refactor cannot silently drift them.
Load-bearing controls: the wrap-bond leak control
(`prodWeight_apply_first (L := 3) = 1`, not `2`, distinguishing the open per-site weight from the
periodic one, cf. `card_openBonds 3 = 2` in `AKLTOpenChainProblem723a.lean`); the `L = 2` structural
cross-check against `finrank_vbsBondSubspace`; and the ring-side regression pinning
`fBond_isRelPrime`/`weylMap_ground_form_eq_const_smul_prod` after the `_of_witness` split.
-/

namespace LatticeSystem.Tests.AKLTOpenChainProblem723b

open MvPolynomial
open LatticeSystem.Quantum LatticeSystem.Math LatticeSystem.Quantum.AKLTUniqueness

/-! ## 1. `WeightedHomogeneousLayer` additions -/

/-- `weight_siteWeight_apply`: the per-site weight of a multidegree `d`, evaluated at a single site
`y`, is exactly the total exponent of `y`'s two Weyl variables `(y,0)` and `(y,1)`. -/
example (L : ℕ) (d : (Fin L × Fin 2) →₀ ℕ) (y : Fin L) :
    (Finsupp.weight (siteWeight (L := L)) d) y = d (y, 0) + d (y, 1) :=
  weight_siteWeight_apply d y

/-- `weylMapWeight_apply`: the aggregate per-site degree `∑_x single x 2` of the Weyl image
evaluates to `2` at every site. -/
example (L : ℕ) (y : Fin L) :
    (∑ x : Fin L, Finsupp.single x 2 : Fin L →₀ ℕ) y = 2 :=
  weylMapWeight_apply 2 y

/-! ## 2. `ProductBondDivisibility` refactor: `_of_witness` split -/

/-- `fBond_isRelPrime_of_witness`: the general witness-based coprimality lemma, valid for `1 < L`
(no `3 ≤ L` needed), so it can be reused at `L = 2` on `openBonds`. -/
example (L : ℕ) (hL : 1 < L) {x y : Fin L}
    (h : ∃ s : Fin L, (s = x ∨ s = ringSucc x) ∧ s ≠ y ∧ s ≠ ringSucc y) :
    IsRelPrime (fBond x) (fBond y) :=
  fBond_isRelPrime_of_witness hL h

/-- Regression: the cyclic `fBond_isRelPrime` keeps its exact `3 ≤ L` signature after the
`_of_witness` extraction. -/
example (L : ℕ) (hL : 3 ≤ L) {x y : Fin L} (hxy : x ≠ y) :
    IsRelPrime (fBond x) (fBond y) :=
  fBond_isRelPrime hL hxy

/-- Regression: the Stage C capstone of the ring proof still elaborates unchanged after the
`ProductBondDivisibility` refactor. -/
example (L : ℕ) (hL : 3 ≤ L) (Ψ : (Fin L → Fin 3) → ℂ) (hΨ0 : Ψ ≠ 0)
    (hΨ : ∀ x : Fin L, IsVBSGroundForm L x Ψ) :
    ∃ c : ℂ, weylMap Ψ = MvPolynomial.C c * ∏ x : Fin L, fBond x :=
  weylMap_ground_form_eq_const_smul_prod hL Ψ hΨ0 hΨ

/-! ## 3. Open-bond separation and coprimality -/

/-- `exists_open_bond_var_witness`: distinct open bonds have a separating variable witness, with
**no** hypothesis on `L` at all (unlike the cyclic `exists_bond_var_witness`, which needs
`3 ≤ L`) — this is what makes `L = 2` admissible on `openBonds`. -/
example (L : ℕ) {x y : Fin L} (hx : x ∈ openBonds L) (hy : y ∈ openBonds L) (hxy : x ≠ y) :
    ∃ s : Fin L, (s = x ∨ s = ringSucc x) ∧ s ≠ y ∧ s ≠ ringSucc y :=
  exists_open_bond_var_witness hx hy hxy

/-- `fBond_isRelPrime_openBonds`: distinct open-chain bonds give relatively prime global bond
factors, at the exact hypothesis `2 ≤ L`. -/
example (L : ℕ) (hL : 2 ≤ L) {x y : Fin L} (hx : x ∈ openBonds L) (hy : y ∈ openBonds L)
    (hxy : x ≠ y) :
    IsRelPrime (fBond x) (fBond y) :=
  fBond_isRelPrime_openBonds hL hx hy hxy

/-! ## 4. Per-site homogeneity of the bond factor and of the bond product -/

/-- `fBond_isWeightedHomogeneous`: each global bond factor `f_x` is `siteWeight`-homogeneous of
the two-site degree `single x 1 + single (ringSucc x) 1`. -/
example (L : ℕ) (x : Fin L) :
    (fBond x).IsWeightedHomogeneous (siteWeight (L := L))
      (Finsupp.single x 1 + Finsupp.single (ringSucc x) 1) :=
  fBond_isWeightedHomogeneous x

/-- `prod_openBonds_fBond_isWeightedHomogeneous`: the product over `openBonds L` (never
`Finset.univ`) is `siteWeight`-homogeneous of the summed per-bond degree. -/
example (L : ℕ) :
    (∏ x ∈ openBonds L, fBond x).IsWeightedHomogeneous (siteWeight (L := L))
      (∑ x ∈ openBonds L, (Finsupp.single x 1 + Finsupp.single (ringSucc x) 1)) :=
  prod_openBonds_fBond_isWeightedHomogeneous

/-- `prod_openBonds_fBond_ne_zero`: the product of the open bond factors is nonzero — the
load-bearing `hq0` hypothesis of the weighted cofactor lemma. -/
example (L : ℕ) (hL : 1 < L) : (∏ x ∈ openBonds L, fBond x) ≠ 0 :=
  prod_openBonds_fBond_ne_zero hL

/-! ## 5. Per-site bookkeeping: the boundary/interior degree split -/

/-- **Wrap-bond leak control**, part 1: at an *interior* site (both neighbours present) the summed
open-bond degree is `2` — this is the value **every** site would carry if the sum ranged over
`Finset.univ` (the wrap bond reinstated). -/
example (L : ℕ) {y : Fin L} (h0 : 0 < y.val) (hl : y.val + 1 < L) :
    (∑ x ∈ openBonds L, (Finsupp.single x 1 + Finsupp.single (ringSucc x) 1) : Fin L →₀ ℕ) y = 2 :=
  prodWeight_apply_of_interior h0 hl

/-- **Wrap-bond leak control**, part 2: the *first* site of the open chain carries degree `1`, not
`2` — a wrap-bond leak would silently turn this into `2`, matching the interior value. -/
example (L : ℕ) (hL : 2 ≤ L) :
    (∑ x ∈ openBonds L, (Finsupp.single x 1 + Finsupp.single (ringSucc x) 1) : Fin L →₀ ℕ)
        ⟨0, by omega⟩ = 1 :=
  prodWeight_apply_first hL

/-- **Wrap-bond leak control**, part 3: the *last* site of the open chain also carries degree
`1`. -/
example (L : ℕ) (hL : 2 ≤ L) :
    (∑ x ∈ openBonds L, (Finsupp.single x 1 + Finsupp.single (ringSucc x) 1) : Fin L →₀ ℕ)
        ⟨L - 1, by omega⟩ = 1 :=
  prodWeight_apply_last hL

/-- Concrete instantiation of the wrap-bond control at `L = 3`: the first site carries degree `1`
under the correct open-bond sum, **not** `2` (the value a leaked wrap bond would produce). -/
example :
    (∑ x ∈ openBonds 3, (Finsupp.single x 1 + Finsupp.single (ringSucc x) 1) : Fin 3 →₀ ℕ)
        ⟨0, by omega⟩ = 1 :=
  prodWeight_apply_first (L := 3) (by norm_num)

/-! ## 6. (S.77) itself — the boundary-quadratic factorization -/

/-- **Tasaki Problem 7.2.3.b, eq. (S.77), p. 508** (printed upper product index `L` corrected to
`L - 1`).  The Weyl image of any open-chain ground form factors as a boundary quadratic
`Σ c_{ab} X_{(first,a)} X_{(last,b)}` — involving **only** the two boundary sites, never an interior
one — times the product of the `L − 1` open bond factors. -/
example {m : ℕ} (Ψ : (Fin (m + 2) → Fin 3) → ℂ)
    (hΨ : ∀ x ∈ openBonds (m + 2), IsVBSGroundForm (m + 2) x Ψ) :
    ∃ c : Fin 2 × Fin 2 → ℂ,
      weylMap Ψ
        = (∑ ab : Fin 2 × Fin 2,
            MvPolynomial.C (c ab)
              * (X ((0 : Fin (m + 2)), ab.1) * X (Fin.last (m + 1), ab.2)))
            * ∏ x ∈ openBonds (m + 2), fBond x :=
  weylMap_openGroundForm_eq_boundary_smul_prod Ψ hΨ

/-! ## 7. Completeness capstone -/

/-- `openGroundSpace_isVBSGroundForm`: the open spectral bridge — every ground state of the open
AKLT chain has the VBS singlet-tensor form at every open bond. -/
example (L : ℕ) (hL : 2 ≤ L) {Ψ : (Fin L → Fin 3) → ℂ} (hΨ : Ψ ∈ openAKLTGroundSpace L) :
    ∀ x ∈ openBonds L, IsVBSGroundForm L x Ψ :=
  openGroundSpace_isVBSGroundForm hL hΨ

/-- `finrank_openAKLTGroundSpace_le_four`: the upper-bound half — the open ground space has complex
dimension at most `4`. -/
example (L : ℕ) (hL : 2 ≤ L) :
    Module.finrank ℂ (openAKLTGroundSpace L) ≤ 4 :=
  finrank_openAKLTGroundSpace_le_four hL

/-- **Problem 7.2.3.b capstone**: combined with the lower bound
`four_le_finrank_openAKLTGroundSpace`
of PR-2 (`le_antisymm`), the open `S = 1` AKLT chain has ground space of complex dimension **exactly
`4`** — the book's "exactly four-fold degenerate" claim. -/
example (L : ℕ) (hL : 2 ≤ L) :
    Module.finrank ℂ (openAKLTGroundSpace L) = 4 :=
  finrank_openAKLTGroundSpace_eq_four hL

/-- `L = 2` structural cross-check: at the smallest admissible `L` the capstone must literally match
the proved dimension of the ring-bond subspace `W` (`finrank_vbsBondSubspace`, over the same ambient
type `(Fin 2 → Fin 3) → ℂ`), since at `L = 2` the open ground space *is* the bond subspace. -/
example : Module.finrank ℂ (openAKLTGroundSpace 2) = Module.finrank ℂ vbsBondSubspace := by
  rw [finrank_openAKLTGroundSpace_eq_four (le_refl 2), finrank_vbsBondSubspace]

/-- `openAKLTGroundSpace_eq_span_openVBSState`: the literal book claim — every ground state is a
linear combination of the four `openVBSState` boundary components, not merely `4 ≤ dim ≤ 4`. -/
example (L : ℕ) (hL : 2 ≤ L) :
    openAKLTGroundSpace L
      = Submodule.span ℂ (Set.range fun r : Fin 2 × Fin 2 => openVBSState L r.1 r.2) :=
  openAKLTGroundSpace_eq_span_openVBSState hL

end LatticeSystem.Tests.AKLTOpenChainProblem723b
