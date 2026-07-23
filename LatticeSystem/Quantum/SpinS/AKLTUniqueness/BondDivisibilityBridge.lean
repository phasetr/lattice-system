/-
# Tasaki §7.1.3 (AKLT uniqueness), stage C3: the bond-divisibility bridge (general cyclic chain)

This file lifts the two-site local divisibility statement `U3a`
(`LatticeSystem.Quantum.AKLTUniqueness.LocalBondDivisibility`,
`f2_dvd_weylMap_of_mem_vbsBondSubspace`) to the full periodic chain (`U3b`, the `⟹` direction):

  `IsVBSGroundForm L x Φ  ⟹  f_x ∣ weylMap Φ`,

where `f_x = u_x v_{x⁺} − v_x u_{x⁺}` is the global bond factor on the bond `{x, ringSucc x}`.

The argument factors the Weyl monomial of a chain state across the distinguished bond
(`weylMono_bond_rest_split`: `weylMono σ = restMono · rename bondEmb (weylMono₂ (bond slice of σ))`),
regroups the Weyl image fiberwise over the rest-of-chain configuration
(`weylMap_eq_bondSlice_sum`, the combinatorial core), and then discharges divisibility summand by
summand: `f_x = rename bondEmb f₂` (`rename_bondEmb_f2`), `f₂ ∣ weylMap₂ (bondSlice x Φ r)` (U3a),
so `f_x ∣` each summand by `map_dvd` and `f_x ∣ weylMap Φ` by `Finset.dvd_sum`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (Springer, 2020),
§7.1.3 "The Uniqueness of the Ground State", pp. 186–188, eqs. (7.1.19)–(7.1.25); polynomial
representation due to Arovas–Auerbach–Haldane [10]; proof due to Kennedy–Lieb–Tasaki [41].
-/
import LatticeSystem.Quantum.SpinS.AKLTUniqueness.LocalBondDivisibility

open MvPolynomial

namespace LatticeSystem.Quantum.AKLTUniqueness

open LatticeSystem.Quantum LatticeSystem.Math

variable {L : ℕ}

/-- On a chain of length `> 1` the cyclic successor `ringSucc x = x + 1 (mod L)` of a site differs
from the site itself, so the bond `{x, ringSucc x}` is genuinely two-site. -/
theorem ne_ringSucc (hL : 1 < L) (x : Fin L) : x ≠ ringSucc x := by
  intro h
  have hv := congrArg Fin.val h
  simp only [ringSucc] at hv
  by_cases hx : x.val + 1 < L
  · rw [Nat.mod_eq_of_lt hx] at hv; omega
  · have heq : x.val + 1 = L := by omega
    rw [heq, Nat.mod_self] at hv; omega

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

/-- Easy half: if the local bond factor divides a local polynomial `q`, then the global bond
factor divides its `rename`-image (`map_dvd` through the `rename` algebra hom). -/
theorem fBond_dvd_rename (q : MvPolynomial (Fin 2 × Fin 2) ℂ) (h : f2 ∣ q) :
    fBond x ∣ rename (bondEmb x) q := by
  rw [← rename_bondEmb_f2 x]
  exact map_dvd _ h

/-- `rename bondEmb` pushes the local left-site multidegree to the global site `x`
(`mapDomain_single` on each `Finsupp.single`). -/
theorem mapDomain_bondEmb_mdSite_left (k : Fin 3) :
    Finsupp.mapDomain (bondEmb x) (mdSite (0 : Fin 2) k) = mdSite x k := by
  fin_cases k <;>
    simp [mdSite, bondEmb, Finsupp.mapDomain_single, Finsupp.mapDomain_add]

/-- `rename bondEmb` pushes the local right-site multidegree to the global site `ringSucc x`. -/
theorem mapDomain_bondEmb_mdSite_right (k : Fin 3) :
    Finsupp.mapDomain (bondEmb x) (mdSite (1 : Fin 2) k) = mdSite (ringSucc x) k := by
  fin_cases k <;>
    simp [mdSite, bondEmb, Finsupp.mapDomain_single, Finsupp.mapDomain_add]

/-- The Clebsch–Gordan norm splits as (rest) × (two bond sites), using `x ≠ ringSucc x`.
The rest factor is the product of `cgSite` over all sites off the bond. -/
theorem cgNorm_bond_rest_split (hL : 1 < L) (σ : Fin L → Fin 3) :
    cgNorm σ =
      (∏ y ∈ (Finset.univ.erase x).erase (ringSucc x), cgSite (σ y))
        * cgSite (σ x) * cgSite (σ (ringSucc x)) := by
  have hxy : x ≠ ringSucc x := ne_ringSucc hL x
  rw [cgNorm, ← Finset.mul_prod_erase Finset.univ (fun y => cgSite (σ y)) (Finset.mem_univ x),
    ← Finset.mul_prod_erase (Finset.univ.erase x) (fun y => cgSite (σ y))
      (Finset.mem_erase.mpr ⟨Ne.symm hxy, Finset.mem_univ _⟩)]
  ring

/-- The total multidegree splits as (rest) + (two bond sites), using `x ≠ ringSucc x`. -/
theorem md_bond_rest_split (hL : 1 < L) (σ : Fin L → Fin 3) :
    md σ = (∑ y ∈ (Finset.univ.erase x).erase (ringSucc x), mdSite y (σ y))
      + mdSite x (σ x) + mdSite (ringSucc x) (σ (ringSucc x)) := by
  have hxy : x ≠ ringSucc x := ne_ringSucc hL x
  rw [md, ← Finset.add_sum_erase Finset.univ (fun y => mdSite y (σ y)) (Finset.mem_univ x),
    ← Finset.add_sum_erase (Finset.univ.erase x) (fun y => mdSite y (σ y))
      (Finset.mem_erase.mpr ⟨Ne.symm hxy, Finset.mem_univ _⟩)]
  abel

/-- The rest (off-bond) Weyl monomial of a chain state `σ` at the bond `{x, ringSucc x}`: the
single monomial carrying the product of the off-bond site multidegrees and Clebsch–Gordan weights.
It is the factor of `weylMono σ` that survives after stripping the two bond sites. -/
noncomputable def restMono (σ : Fin L → Fin 3) : MvPolynomial (Fin L × Fin 2) ℂ :=
  monomial (∑ y ∈ (Finset.univ.erase x).erase (ringSucc x), mdSite y (σ y))
    (∏ y ∈ (Finset.univ.erase x).erase (ringSucc x), cgSite (σ y))

/-- **Per-state slice-monomial factorization.**  `weylMono σ = restMono σ · rename bondEmb
(weylMono₂ (bond slice of σ))`, where `restMono σ` is the Weyl monomial of the sites off the bond.
This composes `md_bond_rest_split`, `cgNorm_bond_rest_split`, `rename_monomial`, and the `mdSite`
mapDomain pushes — the algebraic heart of the general-`L` split identity, per state. -/
theorem weylMono_bond_rest_split (hL : 1 < L) (σ : Fin L → Fin 3) :
    weylMono σ
      = restMono x σ * rename (bondEmb x) (weylMono (L := 2) ![σ x, σ (ringSucc x)]) := by
  rw [restMono, weylMono, weylMono, rename_monomial, monomial_mul,
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
theorem weylMono_glueBond_split (hL : 1 < L) (a : Fin 2 → Fin 3) (r : Fin L → Fin 3) :
    weylMono (glueBond x a r)
      = restMono x r * rename (bondEmb x) (weylMono (L := 2) a) := by
  have hxne : x ≠ ringSucc x := ne_ringSucc hL x
  have hgr : ∀ y ∈ (Finset.univ.erase x).erase (ringSucc x), glueBond x a r y = r y := by
    intro y hy
    rw [Finset.mem_erase] at hy
    obtain ⟨hyr, hy'⟩ := hy
    rw [Finset.mem_erase] at hy'
    obtain ⟨hyx, -⟩ := hy'
    simp [glueBond, hyx, hyr]
  have hrest : restMono x (glueBond x a r) = restMono x r := by
    have he : (∑ y ∈ (Finset.univ.erase x).erase (ringSucc x), mdSite y (glueBond x a r y))
        = ∑ y ∈ (Finset.univ.erase x).erase (ringSucc x), mdSite y (r y) :=
      Finset.sum_congr rfl (fun y hy => by rw [hgr y hy])
    have hc : (∏ y ∈ (Finset.univ.erase x).erase (ringSucc x), cgSite (glueBond x a r y))
        = ∏ y ∈ (Finset.univ.erase x).erase (ringSucc x), cgSite (r y) :=
      Finset.prod_congr rfl (fun y hy => by rw [hgr y hy])
    rw [restMono, restMono, he, hc]
  have hbond : (![glueBond x a r x, glueBond x a r (ringSucc x)] : Fin 2 → Fin 3) = a := by
    have h0 : glueBond x a r x = a 0 := by simp [glueBond]
    have h1 : glueBond x a r (ringSucc x) = a 1 := by simp [glueBond, Ne.symm hxne]
    rw [h0, h1]; funext i; fin_cases i <;> simp
  rw [weylMono_bond_rest_split x hL (glueBond x a r), hrest, hbond]

/-- **The general-`L` split identity (combinatorial core).**  The Weyl image of a chain state is the
fiber sum, over rest-of-chain configurations `r`, of a rest weight times the `rename bondEmb`-image
of the *local* Weyl image of the two-site bond slice `bondSlice x Φ r`.  Proof: expand the inner
`weylMap₂` as a sum over bond configurations, use the per-state factorization
`weylMono_glueBond_split`, then reindex the resulting double sum over
`(rest config, bond config) ↦ glueBond x a r` by an explicit bijection (`Finset.sum_bij'`). -/
theorem weylMap_eq_bondSlice_sum (hL : 1 < L) (Φ : (Fin L → Fin 3) → ℂ) :
    ∃ (restWeight : (Fin L → Fin 3) → MvPolynomial (Fin L × Fin 2) ℂ),
      weylMap Φ = ∑ r : Fin L → Fin 3,
        restWeight r * rename (bondEmb x) (weylMap (L := 2) (bondSlice x Φ r)) := by
  classical
  refine ⟨fun r => if r x = 0 ∧ r (ringSucc x) = 0 then restMono x r else 0, ?_⟩
  have hxne : x ≠ ringSucc x := ne_ringSucc hL x
  have gb_x : ∀ (a : Fin 2 → Fin 3) (r : Fin L → Fin 3), glueBond x a r x = a 0 :=
    fun a r => by simp [glueBond]
  have gb_rs : ∀ (a : Fin 2 → Fin 3) (r : Fin L → Fin 3), glueBond x a r (ringSucc x) = a 1 :=
    fun a r => by simp [glueBond, Ne.symm hxne]
  have gb_rest : ∀ (a : Fin 2 → Fin 3) (r : Fin L → Fin 3) (k : Fin L),
      k ≠ x → k ≠ ringSucc x → glueBond x a r k = r k :=
    fun a r k hkx hkr => by simp [glueBond, hkx, hkr]
  -- Rewrite each summand: expand the inner Weyl map and factor through `weylMono_glueBond_split`.
  have step1 : ∀ r : Fin L → Fin 3,
      (if r x = 0 ∧ r (ringSucc x) = 0 then restMono x r else 0)
        * rename (bondEmb x) (weylMap (L := 2) (bondSlice x Φ r))
      = ∑ a : Fin 2 → Fin 3,
          (if r x = 0 ∧ r (ringSucc x) = 0 then
            Φ (glueBond x a r) • weylMono (glueBond x a r) else 0) := by
    intro r
    rw [show weylMap (L := 2) (bondSlice x Φ r)
          = ∑ a : Fin 2 → Fin 3, bondSlice x Φ r a • weylMono (L := 2) a from by
        simp only [weylMap, Fintype.linearCombination_apply],
      map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_smul]
    by_cases hr : r x = 0 ∧ r (ringSucc x) = 0
    · rw [if_pos hr, if_pos hr, mul_smul_comm, ← weylMono_glueBond_split x hL a r]
      rfl
    · rw [if_neg hr, if_neg hr, zero_mul]
  -- Pull the (bond-independent) `ite` out of the bond sum.
  have hpull : (∑ r : Fin L → Fin 3, ∑ a : Fin 2 → Fin 3,
        (if r x = 0 ∧ r (ringSucc x) = 0 then
          Φ (glueBond x a r) • weylMono (glueBond x a r) else 0))
      = ∑ r : Fin L → Fin 3, if r x = 0 ∧ r (ringSucc x) = 0 then
          (∑ a : Fin 2 → Fin 3, Φ (glueBond x a r) • weylMono (glueBond x a r)) else 0 := by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    split_ifs <;> simp
  rw [show weylMap Φ = ∑ σ : Fin L → Fin 3, Φ σ • weylMono σ from by
      simp only [weylMap, Fintype.linearCombination_apply]]
  rw [Finset.sum_congr rfl (fun r (_ : r ∈ Finset.univ) => step1 r), hpull,
    ← Finset.sum_filter, ← Finset.sum_product']
  -- Reindex `(rest config, bond config) ↦ glueBond x a r`.
  symm
  refine Finset.sum_bij'
    (fun p _ => glueBond x p.2 p.1)
    (fun σ _ => ((fun k => if k = x then (0 : Fin 3) else if k = ringSucc x then 0 else σ k),
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

/-- **U3b bridge (Tasaki §7.1.3, `⟹` direction).**  If the chain state `Φ` has the VBS
singlet-tensor form on the bond `{x, ringSucc x}` (`IsVBSGroundForm`), then the global bond factor
`f_x` divides its Weyl image `weylMap Φ`.

Proof: `weylMap_eq_bondSlice_sum` writes `weylMap Φ` as a rest-fiber sum of `rename bondEmb`-images
of local bond-slice Weyl images; each bond slice lies in `vbsBondSubspace` (`IsVBSGroundForm`), so
`f₂` divides its local Weyl image (U3a `f2_dvd_weylMap_of_mem_vbsBondSubspace`), whence `f_x`
divides each summand (`fBond_dvd_rename`) and the whole sum (`Finset.dvd_sum`). -/
theorem fBond_dvd_weylMap_of_isVBSGroundForm
    (hL : 1 < L) (Φ : (Fin L → Fin 3) → ℂ) (hΦ : IsVBSGroundForm L x Φ) :
    fBond x ∣ weylMap Φ := by
  obtain ⟨restWeight, hsum⟩ := weylMap_eq_bondSlice_sum x hL Φ
  rw [hsum]
  refine Finset.dvd_sum (fun r _ => Dvd.dvd.mul_left ?_ _)
  exact fBond_dvd_rename x _ (f2_dvd_weylMap_of_mem_vbsBondSubspace _ (hΦ r))

end LatticeSystem.Quantum.AKLTUniqueness
