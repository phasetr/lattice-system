/-
# Tasaki §7.1.3 (AKLT uniqueness), stage C3: the bond-divisibility bridge (general cyclic chain)

This file relates two-site local divisibility on the bond `{x, ringSucc x}` to divisibility of the
Weyl image of the whole chain, in **both directions**.

The `⟹` direction lifts the two-site local statement `U3a`
(`LatticeSystem.Quantum.AKLTUniqueness.LocalBondDivisibility`,
`f2_dvd_weylMap_of_mem_vbsBondSubspace`) to the full periodic chain (`U3b`):

  `IsVBSGroundForm L x Φ  ⟹  f_x ∣ weylMap Φ`,

where `f_x = u_x v_{x⁺} − v_x u_{x⁺}` is the global bond factor on the bond `{x, ringSucc x}`.
The argument factors the Weyl monomial of a chain state across the distinguished bond
(`weylMono_bond_rest_split`: `weylMono σ = restMono · rename bondEmb (weylMono₂ (bond slice of σ))`),
regroups the Weyl image fiberwise over the rest-of-chain configuration
(`weylMap_eq_bondSlice_sum`, the combinatorial core), and then discharges divisibility summand by
summand: `f_x = rename bondEmb f₂` (`rename_bondEmb_f2`), `f₂ ∣ weylMap₂ (bondSlice x Φ r)` (U3a),
so `f_x ∣` each summand by `map_dvd` and `f_x ∣ weylMap Φ` by `Finset.dvd_sum`.

The `⟸` direction (`f2_pow_dvd_weylMap_bondSlice_of_fBond_pow_dvd`) goes the other way and is what
turns a *global* divisibility statement back into a condition on every two-site slice.  Summing over
the fibers is not invertible on the nose, so the fibers are separated by a grading instead: the
off-bond weight `offBondWeight` gives the bond variables weight `0` and every other variable its own
basis vector, and the graded component of `weylMap Φ` in degree `restDeg x r` is exactly the single
fiber term of `r` (`weightedHomogeneousComponent_offBond_weylMap`).  Since `f_x` has off-bond weight
`0`, divisibility survives taking that component; collapsing the off-bond variables to `1` then
carries the component to the local two-site ring, where the off-bond monomial `restMono` becomes an
invertible constant and `f_x` becomes `f₂`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (Springer, 2020),
§7.1.3 "The Uniqueness of the Ground State", pp. 186–188, eqs. (7.1.19)–(7.1.25); §8.3.1, p. 252 for
the general-`S` bond powers; polynomial representation due to Arovas–Auerbach–Haldane [10]; proof
due to Kennedy–Lieb–Tasaki [41].
-/
import LatticeSystem.Quantum.SpinS.AKLTUniqueness.LocalBondDivisibility
import LatticeSystem.Math.MvPolynomial.WeightedHomogeneousLayer

open MvPolynomial

namespace LatticeSystem.Quantum.AKLTUniqueness

open LatticeSystem.Quantum LatticeSystem.Math

variable {L : ℕ}

variable (x : Fin L)

/-- The bond embedding `emb : Fin 2 × Fin 2 → Fin L × Fin 2` sending the local left site `0 ↦ x`
and the local right site `1 ↦ ringSucc x`, preserving the `u/v` component. -/
def bondEmb : Fin 2 × Fin 2 → Fin L × Fin 2 :=
  fun p => (if p.1 = 0 then x else ringSucc x, p.2)

/-- The global bond factor `f_x = u_x v_{x⁺} − v_x u_{x⁺}` on the full chain variables
(Tasaki §7.1.3, the factor appearing in the Weyl representation of the bond singlet). -/
noncomputable def fBond : MvPolynomial (Fin L × Fin 2) ℂ :=
  bondFactor (x, 0) (ringSucc x, 1) (x, 1) (ringSucc x, 0)

/-- `rename bondEmb` carries the local `L = 2` bond factor `f₂` to the global bond factor `f_x`
(pure `rename_X`, since `rename` is an algebra hom and `bondEmb` hits the four global variables). -/
theorem rename_bondEmb_f2 : rename (bondEmb x) f2 = fBond x := by
  simp only [f2, fBond, bondFactor, map_sub, map_mul, rename_X, bondEmb]
  norm_num

/-- `rename bondEmb` pushes the local left-site multidegree to the global site `x`
(`mapDomain_single` on each of the two `Finsupp.single` summands of `mdSite`). -/
theorem mapDomain_bondEmb_mdSite_left {N : ℕ} (k : Fin (N + 1)) :
    Finsupp.mapDomain (bondEmb x) (mdSite (0 : Fin 2) k) = mdSite x k := by
  have h0 : bondEmb x ((0 : Fin 2), (0 : Fin 2)) = (x, 0) := by simp [bondEmb]
  have h1 : bondEmb x ((0 : Fin 2), (1 : Fin 2)) = (x, 1) := by simp [bondEmb]
  rw [mdSite, mdSite, Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single,
    h0, h1]

/-- `rename bondEmb` pushes the local right-site multidegree to the global site `ringSucc x`. -/
theorem mapDomain_bondEmb_mdSite_right {N : ℕ} (k : Fin (N + 1)) :
    Finsupp.mapDomain (bondEmb x) (mdSite (1 : Fin 2) k) = mdSite (ringSucc x) k := by
  have h0 : bondEmb x ((1 : Fin 2), (0 : Fin 2)) = (ringSucc x, 0) := by simp [bondEmb]
  have h1 : bondEmb x ((1 : Fin 2), (1 : Fin 2)) = (ringSucc x, 1) := by simp [bondEmb]
  rw [mdSite, mdSite, Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single,
    h0, h1]

/-- The Clebsch–Gordan norm splits as (rest) × (two bond sites), using `x ≠ ringSucc x`.
The rest factor is the product of `cgSite` over all sites off the bond. -/
theorem cgNorm_bond_rest_split {N : ℕ} (hL : 1 < L) (σ : Fin L → Fin (N + 1)) :
    cgNorm σ =
      (∏ y ∈ (Finset.univ.erase x).erase (ringSucc x), cgSite (σ y))
        * cgSite (σ x) * cgSite (σ (ringSucc x)) := by
  have hxy : x ≠ ringSucc x := ne_ringSucc hL x
  rw [cgNorm, ← Finset.mul_prod_erase Finset.univ (fun y => cgSite (σ y)) (Finset.mem_univ x),
    ← Finset.mul_prod_erase (Finset.univ.erase x) (fun y => cgSite (σ y))
      (Finset.mem_erase.mpr ⟨Ne.symm hxy, Finset.mem_univ _⟩)]
  ring

/-- The total multidegree splits as (rest) + (two bond sites), using `x ≠ ringSucc x`. -/
theorem md_bond_rest_split {N : ℕ} (hL : 1 < L) (σ : Fin L → Fin (N + 1)) :
    md σ = (∑ y ∈ (Finset.univ.erase x).erase (ringSucc x), mdSite y (σ y))
      + mdSite x (σ x) + mdSite (ringSucc x) (σ (ringSucc x)) := by
  have hxy : x ≠ ringSucc x := ne_ringSucc hL x
  rw [md, ← Finset.add_sum_erase Finset.univ (fun y => mdSite y (σ y)) (Finset.mem_univ x),
    ← Finset.add_sum_erase (Finset.univ.erase x) (fun y => mdSite y (σ y))
      (Finset.mem_erase.mpr ⟨Ne.symm hxy, Finset.mem_univ _⟩)]
  abel

/-- The **off-bond multidegree** of a chain state `σ` at the bond `{x, ringSucc x}`: the sum of the
per-site multidegrees of the sites off the bond.  It is the exponent of the off-bond monomial
`restMono`, and read as a weighted degree (`offBondWeight`) it is the grading that separates the
rest-of-chain fibers of the Weyl image. -/
noncomputable def restDeg {N : ℕ} (σ : Fin L → Fin (N + 1)) : (Fin L × Fin 2) →₀ ℕ :=
  ∑ y ∈ (Finset.univ.erase x).erase (ringSucc x), mdSite y (σ y)

/-- The rest (off-bond) Weyl monomial of a chain state `σ` at the bond `{x, ringSucc x}`: the
single monomial carrying the off-bond multidegree `restDeg` and the product of the off-bond
Clebsch–Gordan weights.  It is the factor of `weylMono σ` that survives after stripping the two bond
sites. -/
noncomputable def restMono {N : ℕ} (σ : Fin L → Fin (N + 1)) : MvPolynomial (Fin L × Fin 2) ℂ :=
  monomial (restDeg x σ) (∏ y ∈ (Finset.univ.erase x).erase (ringSucc x), cgSite (σ y))

/-- **Per-state slice-monomial factorization.**  `weylMono σ = restMono σ · rename bondEmb
(weylMono₂ (bond slice of σ))`, where `restMono σ` is the Weyl monomial of the sites off the bond.
This composes `md_bond_rest_split`, `cgNorm_bond_rest_split`, `rename_monomial`, and the `mdSite`
mapDomain pushes — the algebraic heart of the general-`L` split identity, per state. -/
theorem weylMono_bond_rest_split {N : ℕ} (hL : 1 < L) (σ : Fin L → Fin (N + 1)) :
    weylMono σ
      = restMono x σ * rename (bondEmb x) (weylMono (L := 2) ![σ x, σ (ringSucc x)]) := by
  rw [restMono, restDeg, weylMono, weylMono, rename_monomial, monomial_mul,
    md_bond_rest_split x hL σ, cgNorm_bond_rest_split x hL σ]
  simp only [md, Fin.sum_univ_two, Finsupp.mapDomain_add, cgNorm, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    mapDomain_bondEmb_mdSite_left, mapDomain_bondEmb_mdSite_right]
  rw [monomial_eq_monomial_iff]
  left
  exact ⟨by abel, by ring⟩

/-- Factorization of the Weyl monomial of a glued configuration `glueBond x a r`: since gluing
overwrites the bond sites with `a` and keeps the rest as `r`, the rest factor depends only on `r`
and the bond factor only on `a`, giving `weylMono (glueBond x a r) = restMono r · rename bondEmb
(weylMono₂ a)`. -/
theorem weylMono_glueBond_split {N : ℕ} (hL : 1 < L) (a : Fin 2 → Fin (N + 1))
    (r : Fin L → Fin (N + 1)) :
    weylMono (glueBond x a r)
      = restMono x r * rename (bondEmb x) (weylMono (L := 2) a) := by
  have hxne : x ≠ ringSucc x := ne_ringSucc hL x
  have hgr : ∀ y ∈ (Finset.univ.erase x).erase (ringSucc x), glueBond x a r y = r y := by
    intro y hy
    rw [Finset.mem_erase] at hy
    obtain ⟨hyr, hy'⟩ := hy
    rw [Finset.mem_erase] at hy'
    obtain ⟨hyx, -⟩ := hy'
    simp [glueBond, glueTwoSitesS, hyx, hyr]
  have hrest : restMono x (glueBond x a r) = restMono x r := by
    have he : (∑ y ∈ (Finset.univ.erase x).erase (ringSucc x), mdSite y (glueBond x a r y))
        = ∑ y ∈ (Finset.univ.erase x).erase (ringSucc x), mdSite y (r y) :=
      Finset.sum_congr rfl (fun y hy => by rw [hgr y hy])
    have hc : (∏ y ∈ (Finset.univ.erase x).erase (ringSucc x), cgSite (glueBond x a r y))
        = ∏ y ∈ (Finset.univ.erase x).erase (ringSucc x), cgSite (r y) :=
      Finset.prod_congr rfl (fun y hy => by rw [hgr y hy])
    rw [restMono, restMono, restDeg, restDeg, he, hc]
  have hbond : (![glueBond x a r x, glueBond x a r (ringSucc x)] : Fin 2 → Fin (N + 1)) = a := by
    have h0 : glueBond x a r x = a 0 := by simp [glueBond, glueTwoSitesS]
    have h1 : glueBond x a r (ringSucc x) = a 1 := by
      simp [glueBond, glueTwoSitesS, Ne.symm hxne]
    rw [h0, h1]; funext i; fin_cases i <;> simp
  rw [weylMono_bond_rest_split x hL (glueBond x a r), hrest, hbond]

/-- **The general-`L` split identity (combinatorial core).**  The Weyl image of a chain state is the
fiber sum, over rest-of-chain configurations `r`, of a rest weight times the `rename bondEmb`-image
of the *local* Weyl image of the two-site bond slice `bondSlice x Φ r`.  Proof: expand the inner
`weylMap₂` as a sum over bond configurations, use the per-state factorization
`weylMono_glueBond_split`, then reindex the resulting double sum over
`(rest config, bond config) ↦ glueBond x a r` by an explicit bijection (`Finset.sum_bij'`). -/
theorem weylMap_eq_bondSlice_sum {N : ℕ} (hL : 1 < L) (Φ : (Fin L → Fin (N + 1)) → ℂ) :
    ∃ (restWeight : (Fin L → Fin (N + 1)) → MvPolynomial (Fin L × Fin 2) ℂ),
      weylMap Φ = ∑ r : Fin L → Fin (N + 1),
        restWeight r * rename (bondEmb x) (weylMap (L := 2) (bondSlice x Φ r)) := by
  classical
  refine ⟨fun r => if r x = 0 ∧ r (ringSucc x) = 0 then restMono x r else 0, ?_⟩
  have hxne : x ≠ ringSucc x := ne_ringSucc hL x
  have gb_x : ∀ (a : Fin 2 → Fin (N + 1)) (r : Fin L → Fin (N + 1)),
      glueBond x a r x = a 0 :=
    fun a r => by simp [glueBond, glueTwoSitesS]
  have gb_rs : ∀ (a : Fin 2 → Fin (N + 1)) (r : Fin L → Fin (N + 1)),
      glueBond x a r (ringSucc x) = a 1 :=
    fun a r => by simp [glueBond, glueTwoSitesS, Ne.symm hxne]
  have gb_rest : ∀ (a : Fin 2 → Fin (N + 1)) (r : Fin L → Fin (N + 1)) (k : Fin L),
      k ≠ x → k ≠ ringSucc x → glueBond x a r k = r k :=
    fun a r k hkx hkr => by simp [glueBond, glueTwoSitesS, hkx, hkr]
  -- Rewrite each summand: expand the inner Weyl map and factor through `weylMono_glueBond_split`.
  have step1 : ∀ r : Fin L → Fin (N + 1),
      (if r x = 0 ∧ r (ringSucc x) = 0 then restMono x r else 0)
        * rename (bondEmb x) (weylMap (L := 2) (bondSlice x Φ r))
      = ∑ a : Fin 2 → Fin (N + 1),
          (if r x = 0 ∧ r (ringSucc x) = 0 then
            Φ (glueBond x a r) • weylMono (glueBond x a r) else 0) := by
    intro r
    rw [show weylMap (L := 2) (bondSlice x Φ r)
          = ∑ a : Fin 2 → Fin (N + 1), bondSlice x Φ r a • weylMono (L := 2) a from by
        simp only [weylMap, Fintype.linearCombination_apply],
      map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_smul]
    by_cases hr : r x = 0 ∧ r (ringSucc x) = 0
    · rw [if_pos hr, if_pos hr, mul_smul_comm, ← weylMono_glueBond_split x hL a r]
      rfl
    · rw [if_neg hr, if_neg hr, zero_mul]
  -- Pull the (bond-independent) `ite` out of the bond sum.
  have hpull : (∑ r : Fin L → Fin (N + 1), ∑ a : Fin 2 → Fin (N + 1),
        (if r x = 0 ∧ r (ringSucc x) = 0 then
          Φ (glueBond x a r) • weylMono (glueBond x a r) else 0))
      = ∑ r : Fin L → Fin (N + 1), if r x = 0 ∧ r (ringSucc x) = 0 then
          (∑ a : Fin 2 → Fin (N + 1), Φ (glueBond x a r) • weylMono (glueBond x a r)) else 0 := by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    split_ifs <;> simp
  rw [show weylMap Φ = ∑ σ : Fin L → Fin (N + 1), Φ σ • weylMono σ from by
      simp only [weylMap, Fintype.linearCombination_apply]]
  rw [Finset.sum_congr rfl (fun r (_ : r ∈ Finset.univ) => step1 r), hpull,
    ← Finset.sum_filter, ← Finset.sum_product']
  -- Reindex `(rest config, bond config) ↦ glueBond x a r`.
  symm
  refine Finset.sum_bij'
    (fun p _ => glueBond x p.2 p.1)
    (fun σ _ => ((fun k => if k = x then (0 : Fin (N + 1)) else if k = ringSucc x then 0 else σ k),
        ![σ x, σ (ringSucc x)]))
    (fun p _ => Finset.mem_univ _)
    (fun σ _ => ?_)
    (fun p hp => ?_)
    (fun σ _ => ?_)
    (fun p _ => rfl)
  · -- `j σ` lands in the filtered product set.
    rw [Finset.mem_product]
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp, by simp⟩, Finset.mem_univ _⟩
  · -- left inverse: `j (i p) = p`.
    obtain ⟨r, a⟩ := p
    rw [Finset.mem_product, Finset.mem_filter] at hp
    obtain ⟨⟨-, hrx, hrs⟩, -⟩ := hp
    dsimp only at hrx hrs ⊢
    rw [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · funext k
      by_cases hkx : k = x
      · subst hkx; simp [hrx]
      · by_cases hkr : k = ringSucc x
        · subst hkr; simp [hrs, Ne.symm hxne]
        · simp only [if_neg hkx, if_neg hkr]; exact gb_rest a r k hkx hkr
    · rw [gb_x a r, gb_rs a r]; funext i; fin_cases i <;> simp
  · -- right inverse: `i (j σ) = σ`.
    funext k
    dsimp only
    by_cases hkx : k = x
    · subst hkx; rw [gb_x]; simp
    · by_cases hkr : k = ringSucc x
      · subst hkr; rw [gb_rs]; simp
      · rw [gb_rest _ _ k hkx hkr]; simp [hkx, hkr]

/-- **Local-to-global prime-power bridge.**  If the local bond factor `f₂` divides the local Weyl
image of *every* two-site bond slice of `Φ` to the power `S`, then the global bond factor `f_x`
divides `weylMap Φ` to the same power `S`.  Stated for a general spin `S̄ = N/2` on the sites: the
exponent `S` and the site-state index `N` are independent, the former coming from the order of
vanishing of the local kernel, the latter from the site spin.

Proof: `weylMap_eq_bondSlice_sum` writes `weylMap Φ` as a rest-fiber sum of `rename bondEmb`-images
of local bond-slice Weyl images; `rename` is an algebra hom carrying `f₂ ^ S` to `f_x ^ S`
(`rename_bondEmb_f2`, `map_pow`), so `f_x ^ S` divides each summand and hence the sum
(`Finset.dvd_sum`). -/
theorem fBond_pow_dvd_weylMap_of_local {N : ℕ} (hL : 1 < L) (S : ℕ)
    (Φ : (Fin L → Fin (N + 1)) → ℂ)
    (h : ∀ r : Fin L → Fin (N + 1), f2 ^ S ∣ weylMap (L := 2) (bondSlice x Φ r)) :
    fBond x ^ S ∣ weylMap Φ := by
  obtain ⟨restWeight, hsum⟩ := weylMap_eq_bondSlice_sum x hL Φ
  rw [hsum]
  refine Finset.dvd_sum (fun r _ => Dvd.dvd.mul_left ?_ _)
  rw [← rename_bondEmb_f2 x, ← map_pow]
  exact map_dvd _ (h r)

/-- **U3b bridge (Tasaki §7.1.3, `⟹` direction).**  If the chain state `Φ` has the VBS
singlet-tensor form on the bond `{x, ringSucc x}` (`IsVBSGroundForm`), then the global bond factor
`f_x` divides its Weyl image `weylMap Φ`.

It is the `S = 1` case of `fBond_pow_dvd_weylMap_of_local`, whose local hypothesis is discharged by
U3a (`f2_dvd_weylMap_of_mem_vbsBondSubspace`): each bond slice lies in `vbsBondSubspace`, so `f₂`
divides its local Weyl image. -/
theorem fBond_dvd_weylMap_of_isVBSGroundForm
    (hL : 1 < L) (Φ : (Fin L → Fin 3) → ℂ) (hΦ : IsVBSGroundForm L x Φ) :
    fBond x ∣ weylMap Φ := by
  rw [← pow_one (fBond x)]
  exact fBond_pow_dvd_weylMap_of_local x hL 1 Φ
    (fun r => by rw [pow_one]; exact f2_dvd_weylMap_of_mem_vbsBondSubspace _ (hΦ r))

/-! ## The off-bond grading

Grading the Weyl variables by "which site off the bond they belong to" separates the fibers that
`weylMap_eq_bondSlice_sum` sums over, while leaving the bond itself ungraded. -/

/-- The **off-bond weight** of the Weyl variables at the bond `{x, ringSucc x}`: the two variables
of each bond site have weight `0`, every other variable is its own basis vector in the multidegree
monoid.  A polynomial is `offBondWeight x`-homogeneous of degree `restDeg x r` exactly when all of
its monomials carry the off-bond multidegree of `r`, so this grading picks out one rest-of-chain
fiber and lets the bond variables vary freely. -/
noncomputable def offBondWeight : Fin L × Fin 2 → ((Fin L × Fin 2) →₀ ℕ) :=
  fun v => if v.1 = x ∨ v.1 = ringSucc x then 0 else Finsupp.single v 1

/-- The off-bond multidegree ignores the bond sites: it vanishes at both Weyl variables of `x` and
of `ringSucc x`.  This is what makes the off-bond monomial `restMono` a constant after the bond
collapse. -/
private theorem restDeg_apply_bond {N : ℕ} (σ : Fin L → Fin (N + 1)) {y : Fin L}
    (hy : y = x ∨ y = ringSucc x) (i : Fin 2) : restDeg x σ (y, i) = 0 := by
  rw [restDeg, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun z hz => ?_
  rw [Finset.mem_erase, Finset.mem_erase] at hz
  obtain ⟨hzs, hzx, -⟩ := hz
  refine mdSite_apply_ne ?_ (σ z) i
  rcases hy with rfl | rfl
  · exact hzx
  · exact hzs

/-- The off-bond multidegree reads off the site state at every site off the bond (its second Weyl
variable carries the exponent `σ y`), so two configurations with the same off-bond multidegree agree
off the bond (`eq_of_restDeg_eq`). -/
private theorem restDeg_apply_snd {N : ℕ} (σ : Fin L → Fin (N + 1)) {y : Fin L} (hx : y ≠ x)
    (hs : y ≠ ringSucc x) : restDeg x σ (y, 1) = (σ y : ℕ) := by
  rw [restDeg, Finsupp.finset_sum_apply,
    Finset.sum_eq_single y (fun z _ hz => mdSite_apply_ne hz (σ z) 1) ?_]
  · exact mdSite_apply_snd y (σ y)
  · intro hmem
    exact absurd (Finset.mem_erase.mpr ⟨hs, Finset.mem_erase.mpr ⟨hx, Finset.mem_univ y⟩⟩) hmem

/-- Configurations with the same off-bond multidegree agree at every site off the bond: the
off-bond grading resolves the rest-of-chain fiber completely. -/
private theorem eq_of_restDeg_eq {N : ℕ} {σ r : Fin L → Fin (N + 1)}
    (h : restDeg x σ = restDeg x r) {y : Fin L} (hx : y ≠ x) (hs : y ≠ ringSucc x) : σ y = r y :=
  Fin.ext (by rw [← restDeg_apply_snd x σ hx hs, ← restDeg_apply_snd x r hx hs, h])

/-- Gluing a bond configuration onto `r` leaves the off-bond multidegree untouched, so the whole
bond fiber over `r` sits in a single off-bond degree. -/
private theorem restDeg_glueBond {N : ℕ} (a : Fin 2 → Fin (N + 1)) (r : Fin L → Fin (N + 1)) :
    restDeg x (glueBond x a r) = restDeg x r := by
  simp only [restDeg]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [Finset.mem_erase, Finset.mem_erase] at hy
  obtain ⟨hys, hyx, -⟩ := hy
  rw [show glueBond x a r y = r y from by simp [glueBond, glueTwoSitesS, hyx, hys]]

/-- The single-site multidegree has off-bond weight itself off the bond and `0` on the bond: a site
off the bond contributes its whole multidegree to the grading, a bond site contributes nothing. -/
private theorem weight_offBondWeight_mdSite {N : ℕ} (y : Fin L) (k : Fin (N + 1)) :
    Finsupp.weight (offBondWeight x) (mdSite y k)
      = if y = x ∨ y = ringSucc x then 0 else mdSite y k := by
  rw [mdSite, map_add, Finsupp.weight_single, Finsupp.weight_single]
  by_cases hy : y = x ∨ y = ringSucc x
  · rw [if_pos hy, offBondWeight, offBondWeight, if_pos hy, if_pos hy, smul_zero, smul_zero,
      add_zero]
  · rw [if_neg hy, offBondWeight, offBondWeight, if_neg hy, if_neg hy, Finsupp.smul_single,
      Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one, mul_one]

/-- Every Weyl monomial is off-bond homogeneous of degree its own off-bond multidegree: the grading
is constant on each rest-of-chain fiber and separates distinct fibers. -/
private theorem weylMono_isWeightedHomogeneous_offBond {N : ℕ} (σ : Fin L → Fin (N + 1)) :
    (weylMono σ).IsWeightedHomogeneous (offBondWeight x) (restDeg x σ) := by
  refine isWeightedHomogeneous_monomial _ _ _ ?_
  rw [md, map_sum, Finset.sum_congr rfl fun y _ => weight_offBondWeight_mdSite x y (σ y), restDeg,
    ← Finset.sum_subset (Finset.subset_univ ((Finset.univ.erase x).erase (ringSucc x)))
      fun y _ hy => if_pos (by
        by_cases h1 : y = x
        · exact Or.inl h1
        by_cases h2 : y = ringSucc x
        · exact Or.inr h2
        exact absurd (Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, Finset.mem_univ y⟩⟩) hy)]
  exact Finset.sum_congr rfl fun y hy => if_neg (by
    rw [Finset.mem_erase, Finset.mem_erase] at hy
    exact fun h => h.elim (fun h' => hy.2.1 h') fun h' => hy.1 h')

/-- The global bond factor is off-bond homogeneous of degree `0`: it involves the bond variables
only, which carry no off-bond weight.  This is why divisibility by `f_x ^ S` survives passing to an
off-bond graded component. -/
theorem fBond_isWeightedHomogeneous_offBond :
    (fBond x).IsWeightedHomogeneous (offBondWeight x) 0 := by
  have hx0 : offBondWeight x (x, 0) = 0 := by simp [offBondWeight]
  have hx1 : offBondWeight x (x, 1) = 0 := by simp [offBondWeight]
  have hs0 : offBondWeight x (ringSucc x, 0) = 0 := by simp [offBondWeight]
  have hs1 : offBondWeight x (ringSucc x, 1) = 0 := by simp [offBondWeight]
  have h := bondFactor_isWeightedHomogeneous (offBondWeight x) (x, 0) (ringSucc x, 1) (x, 1)
    (ringSucc x, 0) (by rw [hx0, hx1, hs0, hs1])
  rw [hx0, hs1, add_zero] at h
  exact h

/-! ## The converse bridge: global divisibility restricts to every bond slice -/

/-- The **bond collapse** map: the algebra map that renames the two bond sites to the two sites of a
two-site chain (`x ↦ 0`, `ringSucc x ↦ 1`) and evaluates every off-bond variable at `1`.  It is a
left inverse of `rename (bondEmb x)`, sends `f_x` to `f₂`, and sends the off-bond monomial
`restMono x r` to the nonzero constant `∏ cgSite (r y)` — which is what transports a divisibility
statement from the chain ring to the local two-site ring. -/
private noncomputable def bondCollapse :
    MvPolynomial (Fin L × Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2 × Fin 2) ℂ :=
  aeval fun v => if v.1 = x then X (0, v.2) else if v.1 = ringSucc x then X (1, v.2) else 1

/-- The bond collapse renames the left bond site `x` to the local site `0`. -/
private theorem bondCollapse_X_left (i : Fin 2) : bondCollapse x (X (x, i)) = X (0, i) := by
  simp [bondCollapse]

/-- The bond collapse renames the right bond site `ringSucc x` to the local site `1`. -/
private theorem bondCollapse_X_right (hL : 1 < L) (i : Fin 2) :
    bondCollapse x (X (ringSucc x, i)) = X (1, i) := by
  simp [bondCollapse, Ne.symm (ne_ringSucc hL x)]

/-- The bond collapse carries the global bond factor to the local one, `f_x ↦ f₂` — the same
convention as `rename_bondEmb_f2` read backwards. -/
private theorem bondCollapse_fBond (hL : 1 < L) : bondCollapse x (fBond x) = f2 := by
  rw [fBond, f2, bondFactor, bondFactor, map_sub, map_mul, map_mul, bondCollapse_X_left,
    bondCollapse_X_left, bondCollapse_X_right x hL, bondCollapse_X_right x hL]

/-- The bond collapse undoes `rename (bondEmb x)`: composed with the bond embedding it is the
identity of the local two-site ring. -/
private theorem bondCollapse_rename_bondEmb (hL : 1 < L)
    (p : MvPolynomial (Fin 2 × Fin 2) ℂ) : bondCollapse x (rename (bondEmb x) p) = p := by
  rw [bondCollapse, aeval_rename,
    show ((fun v : Fin L × Fin 2 => if v.1 = x then X (0, v.2) else
        if v.1 = ringSucc x then X (1, v.2) else 1) ∘ bondEmb x)
      = (X : Fin 2 × Fin 2 → MvPolynomial (Fin 2 × Fin 2) ℂ) from ?_, aeval_X_left_apply]
  funext w
  obtain ⟨j, i⟩ := w
  fin_cases j
  · simp [bondEmb]
  · simp [bondEmb, Ne.symm (ne_ringSucc hL x)]

/-- The bond collapse turns the off-bond monomial into the nonzero constant `∏ cgSite (r y)`: all of
its variables sit off the bond and are evaluated at `1`. -/
private theorem bondCollapse_restMono {N : ℕ} (r : Fin L → Fin (N + 1)) :
    bondCollapse x (restMono x r)
      = C (∏ y ∈ (Finset.univ.erase x).erase (ringSucc x), cgSite (r y)) := by
  rw [restMono, bondCollapse, aeval_monomial, algebraMap_eq]
  refine mul_right_eq_self₀.mpr (Or.inl ?_)
  rw [Finsupp.prod]
  refine Finset.prod_eq_one fun v hv => ?_
  rw [Finsupp.mem_support_iff] at hv
  have hvx : v.1 ≠ x := fun h => hv (restDeg_apply_bond x r (Or.inl h) v.2)
  have hvs : v.1 ≠ ringSucc x := fun h => hv (restDeg_apply_bond x r (Or.inr h) v.2)
  rw [if_neg hvx, if_neg hvs, one_pow]

/-- **The off-bond graded component of a Weyl image is a single bond-slice term.**  The component of
`weylMap Φ` in off-bond degree `restDeg x r` is the off-bond monomial of `r` times the
`rename bondEmb`-image of the *local* Weyl image of the bond slice at `r`.  This is the graded
refinement of `weylMap_eq_bondSlice_sum`: that lemma sums exactly these components, and grading is
what makes the individual fiber recoverable from the sum. -/
private theorem weightedHomogeneousComponent_offBond_weylMap {N : ℕ} (hL : 1 < L)
    (Φ : (Fin L → Fin (N + 1)) → ℂ) (r : Fin L → Fin (N + 1)) :
    weightedHomogeneousComponent (offBondWeight x) (restDeg x r) (weylMap Φ)
      = restMono x r * rename (bondEmb x) (weylMap (L := 2) (bondSlice x Φ r)) := by
  classical
  rw [show weylMap Φ = ∑ σ : Fin L → Fin (N + 1), Φ σ • weylMono σ from by
      simp only [weylMap, Fintype.linearCombination_apply],
    show weylMap (L := 2) (bondSlice x Φ r)
        = ∑ a : Fin 2 → Fin (N + 1), bondSlice x Φ r a • weylMono (L := 2) a from by
      simp only [weylMap, Fintype.linearCombination_apply],
    map_sum, map_sum, Finset.mul_sum]
  have hterm : ∀ σ : Fin L → Fin (N + 1),
      weightedHomogeneousComponent (offBondWeight x) (restDeg x r) (Φ σ • weylMono σ)
        = if restDeg x σ = restDeg x r then Φ σ • weylMono σ else 0 := by
    intro σ
    rw [map_smul]
    by_cases hσ : restDeg x σ = restDeg x r
    · rw [if_pos hσ, ← hσ,
        (weylMono_isWeightedHomogeneous_offBond x σ).weightedHomogeneousComponent_same]
    · rw [if_neg hσ, (weylMono_isWeightedHomogeneous_offBond x σ).weightedHomogeneousComponent_ne _
        (Ne.symm hσ), smul_zero]
  rw [Finset.sum_congr rfl fun σ _ => hterm σ, ← Finset.sum_filter]
  symm
  refine Finset.sum_bij'
    (fun a _ => glueBond x a r)
    (fun σ _ => ![σ x, σ (ringSucc x)])
    (fun a _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, restDeg_glueBond x a r⟩)
    (fun σ _ => Finset.mem_univ _)
    (fun a _ => ?_)
    (fun σ hσ => ?_)
    (fun a _ => ?_)
  · dsimp only
    have h0 : glueBond x a r x = a 0 := by simp [glueBond, glueTwoSitesS]
    have h1 : glueBond x a r (ringSucc x) = a 1 := by
      simp [glueBond, glueTwoSitesS, Ne.symm (ne_ringSucc hL x)]
    rw [h0, h1]
    funext i
    fin_cases i <;> simp
  · rw [Finset.mem_filter] at hσ
    dsimp only
    funext k
    by_cases hkx : k = x
    · subst hkx; simp [glueBond, glueTwoSitesS]
    · by_cases hks : k = ringSucc x
      · subst hks; simp [glueBond, glueTwoSitesS, Ne.symm (ne_ringSucc hL x)]
      · rw [show glueBond x ![σ x, σ (ringSucc x)] r k = r k from by
          simp [glueBond, glueTwoSitesS, hkx, hks]]
        exact (eq_of_restDeg_eq x hσ.2 hkx hks).symm
  · rw [map_smul, mul_smul_comm, ← weylMono_glueBond_split x hL a r]
    rfl

/-- **Global-to-local prime-power bridge**, the converse of `fBond_pow_dvd_weylMap_of_local`.  If
the global bond factor `f_x` divides the Weyl image of a chain state to the power `S`, then the
local bond factor `f₂` divides the local Weyl image of *every* two-site bond slice at that bond to
the same power.  This is what turns global polynomial divisibility — the form in which the `S`
valence bonds per link are written (Tasaki §8.3.1, p. 252) — back into the slicewise condition that
the two-site bond term of the Hamiltonian sees.

Proof: the off-bond graded component in degree `restDeg x r` isolates the fiber of `r`
(`weightedHomogeneousComponent_offBond_weylMap`); `f_x ^ S` has off-bond degree `0`, so taking that
component of `f_x ^ S * q` keeps the factor `f_x ^ S`
(`weightedHomogeneousComponent_mul_of_isWeightedHomogeneous`); finally the bond collapse carries the
resulting identity into the local two-site ring, sending `f_x ↦ f₂`, undoing `rename (bondEmb x)`,
and turning the off-bond monomial into the invertible constant `∏ cgSite (r y)`. -/
theorem f2_pow_dvd_weylMap_bondSlice_of_fBond_pow_dvd {N : ℕ} (hL : 1 < L) (x : Fin L) (S : ℕ)
    (Φ : (Fin L → Fin (N + 1)) → ℂ) (h : fBond x ^ S ∣ weylMap Φ) (r : Fin L → Fin (N + 1)) :
    f2 ^ S ∣ weylMap (L := 2) (bondSlice x Φ r) := by
  obtain ⟨q, hq⟩ := h
  have hfhom : (fBond x ^ S).IsWeightedHomogeneous (offBondWeight x) 0 := by
    simpa using (fBond_isWeightedHomogeneous_offBond x).pow S
  have hcomp := weightedHomogeneousComponent_mul_of_isWeightedHomogeneous hfhom q (restDeg x r)
  rw [zero_add] at hcomp
  have hsplit := weightedHomogeneousComponent_offBond_weylMap x hL Φ r
  rw [hq, hcomp] at hsplit
  have himg := congrArg (bondCollapse x) hsplit
  rw [map_mul, map_mul, map_pow, bondCollapse_fBond x hL, bondCollapse_restMono x r,
    bondCollapse_rename_bondEmb x hL] at himg
  have hc : (∏ y ∈ (Finset.univ.erase x).erase (ringSucc x), cgSite (r y)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun y _ => cgSite_ne_zero (r y)
  set c := ∏ y ∈ (Finset.univ.erase x).erase (ringSucc x), cgSite (r y)
  set A := bondCollapse x (weightedHomogeneousComponent (offBondWeight x) (restDeg x r) q)
  refine ⟨C c⁻¹ * A, ?_⟩
  calc weylMap (L := 2) (bondSlice x Φ r)
      = C c⁻¹ * (C c * weylMap (L := 2) (bondSlice x Φ r)) := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
    _ = C c⁻¹ * (f2 ^ S * A) := by rw [← himg]
    _ = f2 ^ S * (C c⁻¹ * A) := by ring

end LatticeSystem.Quantum.AKLTUniqueness
