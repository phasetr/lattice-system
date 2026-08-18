import LatticeSystem.Quantum.SpinS.AKLTTwoSiteTensor
import LatticeSystem.Quantum.SpinS.MPSOrderedProdSplit
import LatticeSystem.Quantum.SpinS.AKLTKnabe.BondProjectionAlgebraD6b
import LatticeSystem.Quantum.SpinS.AKLTKnabe.GenericSpectralD7b
import LatticeSystem.Math.FrustrationFree

/-!
# Tasaki §7.2.3 (Problem 7.2.3.a): the open `S = 1` AKLT chain and its four VBS states

The AKLT chain with **open** boundary conditions (Tasaki eq. (7.2.46), p. 205)

`Ĥ^open = Σ_{x=1}^{L-1} { Ŝ_x · Ŝ_{x+1} + ⅓ (Ŝ_x · Ŝ_{x+1})² }`

has `L − 1` bonds — no wrap bond — and therefore ground energy `−(2/3)(L − 1)` rather than the
periodic `−(2/3)L`.  Its matrix-product ground states are the four **boundary components**
`Φ_{pq}(σ) = (A^{σ_1} A^{σ_2} ⋯ A^{σ_L})_{pq}` of the same AKLT tensor product whose *trace* is the
periodic state (eqs. (7.2.45), (7.2.47)–(7.2.48)); the free `S = 1/2` spins at the two ends are the
two matrix indices `p, q`.

This module proves the **lower-bound half** of Problem 7.2.3.a:

* frustration-freeness — every bond projection `P̂₂[Ŝ_x + Ŝ_{x+1}]`, `x ∈ openBonds L`, annihilates
  every `Φ_{pq}` (Lemma 7.4 applied to the bond-split of the open matrix product);
* linear independence of the four `Φ_{pq}` (evaluation at four explicit configurations);
* the ground energy `−(2/3)(L − 1)` of `Ĥ^open` (Tasaki Lemma A.9 with `ε ≡ 0`, plus the affine
  normalisation `Ĥ^open = 2 Ĥ'^open − (2/3)(L − 1)`);
* hence `4 ≤ dim` of the open ground space.

The complementary upper bound (`dim = 4`, i.e. that there are no further ground states) is the
completeness half of Problem 7.2.3.b and is **not** part of this module.

Two traps are worth recording.  First, the sum must range over `openBonds L` and never over
`Finset.univ`: with the wrap bond included the statement becomes the *periodic* one, whose ground
space is one-dimensional (`aklt_ring_ground_state_unique`), and such a leak is a silent falsity
rather than a build error.  Second, the four states are **not** orthogonal (Tasaki's solution says
so explicitly), which is why the statement is linear independence, never orthonormality.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.2.3, Problem 7.2.3, eqs. (7.2.45)–(7.2.48), pp. 205–207 (solution p. 207); I. Affleck,
T. Kennedy, E. Lieb, H. Tasaki, Commun. Math. Phys. **115**, 477 (1988).
-/

namespace LatticeSystem.Quantum

open Matrix
open LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential
open scoped ComplexOrder

variable {L : ℕ}

/-! ## The open bonds and the two Hamiltonians -/

/-- The **open bonds** of the chain `Fin L`: the sites `x` with `x.val + 1 < L`, i.e. the left
endpoints `x = 1, …, L − 1` of Tasaki eq. (7.2.46).  The last site has no right neighbour, so the
periodic wrap bond is absent. -/
def openBonds (L : ℕ) : Finset (Fin L) :=
  Finset.univ.filter fun x => x.val + 1 < L

/-- Membership in `openBonds`: exactly the sites that have a right neighbour. -/
theorem mem_openBonds {x : Fin L} : x ∈ openBonds L ↔ x.val + 1 < L := by
  simp [openBonds]

/-- The open chain has `L − 1` bonds (`ℕ`-subtraction), one fewer than the ring. -/
theorem card_openBonds (hL : 0 < L) : (openBonds L).card = L - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  have herase : openBonds (m + 1) = Finset.univ.erase (Fin.last m) := by
    ext x
    have hx := x.isLt
    simp only [mem_openBonds, Finset.mem_erase, Finset.mem_univ, and_true]
    refine ⟨fun h hlast => ?_, fun h => ?_⟩
    · rw [hlast, Fin.val_last] at h
      omega
    · have hval : x.val ≠ m := fun hv => h (Fin.ext (by rw [hv, Fin.val_last]))
      omega
  rw [herase, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

/-- On an open bond the cyclic successor is the plain successor: no wrap-around occurs. -/
theorem ringSucc_val_of_mem_openBonds {x : Fin L} (hx : x ∈ openBonds L) :
    (ringSucc x).val = x.val + 1 :=
  Nat.mod_eq_of_lt (mem_openBonds.mp hx)

/-- The **open AKLT Hamiltonian** `Ĥ^open = Σ_{x=1}^{L-1} { Ŝ_x·Ŝ_{x+1} + ⅓ (Ŝ_x·Ŝ_{x+1})² }`
(Tasaki eq. (7.2.46), p. 205), in the same doubled-sum shape as the periodic `akltHamiltonianS`
with the directed `ringCoupling` replaced by the directed `openBondCoupling`.  The open boundary is
automatic: at the last site there is no `y` with `y.val = x.val + 1`, so its inner sum vanishes and
the wrap bond simply does not exist.  There is **no** additive constant in (7.2.46). -/
noncomputable def openAKLTHamiltonianS (L : ℕ) : ManyBodyOpS (Fin L) 2 :=
  ∑ x : Fin L, ∑ y : Fin L, openBondCoupling L x y •
    (spinSDot x y 2 + ((1 : ℂ) / 3) • (spinSDot x y 2 * spinSDot x y 2))

/-- The **open projector Hamiltonian** `Ĥ'^open = Σ_{x ∈ openBonds} P̂₂[Ŝ_x + Ŝ_{x+1}]`: the
open-boundary version of eq. (7.1.7).  The bond sum runs over `openBonds L`, never over
`Finset.univ` (that would reinstate the wrap bond and turn the statement into the periodic one). -/
noncomputable def openProjHamiltonianS (L : ℕ) : ManyBodyOpS (Fin L) 2 :=
  ∑ x ∈ openBonds L, bondSpin2ProjectionS x (ringSucc x)

/-- The four **open VBS states** `Φ_{pq}(σ) = (A^{σ_1} ⋯ A^{σ_L})_{pq}` (Tasaki eqs. (7.2.45),
(7.2.47)–(7.2.48)): the boundary components of the AKLT matrix-product tensor, indexed by the two
free `S = 1/2` edge spins `p, q`.  The periodic state is the trace of the same product, i.e. the
sum of the two diagonal components. -/
noncomputable def openVBSState (L : ℕ) (p q : Fin 2) : (Fin L → Fin 3) → ℂ :=
  fun σ => orderedProd akltVBSMatrices (List.ofFn σ) p q

/-- Ring–open consistency: the periodic AKLT state is the sum of the **diagonal** boundary
components of the open one (trace = sum of the diagonal matrix entries).  This pins the two
definitions to the same matrix product, so a mismatch between the ring and the open convention
cannot go unnoticed. -/
theorem akltVBSState_eq_sum_diag_openVBSState (L : ℕ) (σ : Fin L → Fin 3) :
    akltVBSState L σ = ∑ p : Fin 2, openVBSState L p p σ := by
  simp [akltVBSState, openVBSState, Matrix.trace, Matrix.diag]

/-! ## The affine normalisation `Ĥ^open = 2 Ĥ'^open − (2/3)(L − 1)` -/

/-- At an open bond the inner `y`-sum of `Ĥ^open` collapses to the single bond `{x, x+1}` and,
by eq. (7.1.5), to `2 P̂_{x,x+1} − 2/3`.  The coupling is directed, so each bond is counted
exactly once. -/
private theorem openAKLTHamiltonianS_inner_sum_of_mem {x : Fin L} (hx : x ∈ openBonds L) :
    (∑ y : Fin L, openBondCoupling L x y •
        (spinSDot x y 2 + ((1 : ℂ) / 3) • (spinSDot x y 2 * spinSDot x y 2)))
      = (2 : ℂ) • bondSpin2ProjectionS x (ringSucc x)
        - ((2 : ℂ) / 3) • (1 : ManyBodyOpS (Fin L) 2) := by
  rw [Finset.sum_eq_single (ringSucc x)]
  · have hc : openBondCoupling L x (ringSucc x) = 1 := by
      rw [openBondCoupling]
      exact if_pos (ringSucc_val_of_mem_openBonds hx)
    rw [hc, one_smul, aklt_bond_term_eq_bondSpin2Projection]
  · intro y _ hy
    have hc : openBondCoupling L x y = 0 := by
      rw [openBondCoupling]
      refine if_neg fun hv => hy (Fin.ext ?_)
      rw [hv, ringSucc_val_of_mem_openBonds hx]
    rw [hc, zero_smul]
  · intro hx'
    exact absurd (Finset.mem_univ _) hx'

/-- At the last site (the only site outside `openBonds`) the inner `y`-sum of `Ĥ^open` vanishes:
no site of the chain sits at `x.val + 1`. -/
private theorem openAKLTHamiltonianS_inner_sum_of_notMem {x : Fin L} (hx : x ∉ openBonds L) :
    (∑ y : Fin L, openBondCoupling L x y •
        (spinSDot x y 2 + ((1 : ℂ) / 3) • (spinSDot x y 2 * spinSDot x y 2))) = 0 := by
  have hxL : ¬ x.val + 1 < L := fun h => hx (mem_openBonds.mpr h)
  refine Finset.sum_eq_zero fun y _ => ?_
  have hc : openBondCoupling L x y = 0 := by
    rw [openBondCoupling]
    refine if_neg fun hv => ?_
    have := y.isLt
    omega
  rw [hc, zero_smul]

/-- The constant part of the collapsed double sum: one copy of `(2/3) · 1` per open bond. -/
private theorem openAKLTHamiltonianS_const_sum (L : ℕ) :
    (∑ _x ∈ openBonds L, ((2 : ℂ) / 3) • (1 : ManyBodyOpS (Fin L) 2))
      = ((2 : ℂ) / 3 * ((openBonds L).card : ℂ)) • (1 : ManyBodyOpS (Fin L) 2) := by
  rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    mul_comm (((openBonds L).card : ℂ)) ((2 : ℂ) / 3)]

/-- **The normalisation of eq. (7.2.46) against eq. (7.1.7), open boundary.**  The open AKLT
Hamiltonian is the affine image `Ĥ^open = 2 Ĥ'^open − (2/3)·#openBonds` of the open projector sum.
Both constants — the factor `2` of eq. (7.1.5) and the shift, which counts **bonds** and not sites
— occur in this one statement, so neither can be applied twice nor dropped. -/
theorem openAKLTHamiltonianS_eq_affine (L : ℕ) :
    openAKLTHamiltonianS L
      = ((2 : ℝ) : ℂ) • openProjHamiltonianS L
        + ((-(2 : ℝ) / 3 * (((openBonds L).card : ℕ) : ℝ) : ℝ) : ℂ)
          • (1 : ManyBodyOpS (Fin L) 2) := by
  have hrestrict : (∑ x ∈ openBonds L, ∑ y : Fin L, openBondCoupling L x y •
      (spinSDot x y 2 + ((1 : ℂ) / 3) • (spinSDot x y 2 * spinSDot x y 2)))
      = ∑ x : Fin L, ∑ y : Fin L, openBondCoupling L x y •
        (spinSDot x y 2 + ((1 : ℂ) / 3) • (spinSDot x y 2 * spinSDot x y 2)) :=
    Finset.sum_subset (Finset.subset_univ _)
      fun x _ hx => openAKLTHamiltonianS_inner_sum_of_notMem hx
  have hcollapse : (∑ x ∈ openBonds L, ∑ y : Fin L, openBondCoupling L x y •
      (spinSDot x y 2 + ((1 : ℂ) / 3) • (spinSDot x y 2 * spinSDot x y 2)))
      = ∑ x ∈ openBonds L, ((2 : ℂ) • bondSpin2ProjectionS x (ringSucc x)
        - ((2 : ℂ) / 3) • (1 : ManyBodyOpS (Fin L) 2)) :=
    Finset.sum_congr rfl fun x hx => openAKLTHamiltonianS_inner_sum_of_mem hx
  have hc2 : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  have hcb : ((-(2 : ℝ) / 3 * (((openBonds L).card : ℕ) : ℝ) : ℝ) : ℂ)
      = -((2 : ℂ) / 3 * (((openBonds L).card : ℕ) : ℂ)) := by
    push_cast
    ring
  simp only [openProjHamiltonianS]
  rw [openAKLTHamiltonianS, ← hrestrict, hcollapse, Finset.sum_sub_distrib, ← Finset.smul_sum,
    openAKLTHamiltonianS_const_sum, hc2, hcb, neg_smul, ← sub_eq_add_neg]

/-- The ground-energy shift in Tasaki's own form: `−(2/3)(L − 1)` over the reals, with the
`ℕ`-subtraction of `card_openBonds` cleared by the guarded cast `1 ≤ L`. -/
theorem openAKLTHamiltonianS_eq_affine_sub_one (hL : 1 ≤ L) :
    openAKLTHamiltonianS L
      = ((2 : ℝ) : ℂ) • openProjHamiltonianS L
        + ((-(2 : ℝ) / 3 * ((L : ℝ) - 1) : ℝ) : ℂ) • (1 : ManyBodyOpS (Fin L) 2) := by
  have hcast : (((openBonds L).card : ℕ) : ℝ) = (L : ℝ) - 1 := by
    rw [card_openBonds (by omega), Nat.cast_sub hL, Nat.cast_one]
  rw [openAKLTHamiltonianS_eq_affine, hcast]

/-! ## Frustration-freeness of the four open VBS states -/

/-- A bond slice of an open matrix-product state is a **linear functional of the two-site tensor**:
splitting the ordered product at the bond `{x, x+1}` leaves a prefix matrix `P` and a suffix matrix
`Q` that do not see the bond configuration, and the slice is `∑_{i,j} (P_{pi} Q_{jq}) (A^{a_0}
A^{a_1})_{ij}`.  This is the open counterpart of the periodic trace decomposition F5. -/
private theorem openVBSState_bondSlice_apply {x : Fin L} (hx : x ∈ openBonds L) (p q : Fin 2)
    (τ : Fin L → Fin 3) (a : Fin 2 → Fin 3) :
    bondSlice x (openVBSState L p q) τ a
      = ∑ i : Fin 2, ∑ j : Fin 2,
          (orderedProd akltVBSMatrices ((List.ofFn τ).take x.val) p i
            * orderedProd akltVBSMatrices ((List.ofFn τ).drop (x.val + 2)) j q)
          * (akltVBSMatrices (a 0) * akltVBSMatrices (a 1)) i j := by
  have hxL : x.val + 1 < L := mem_openBonds.mp hx
  have hsucc : ringSucc x = (⟨x.val + 1, hxL⟩ : Fin L) :=
    Fin.ext (ringSucc_val_of_mem_openBonds hx)
  set σ := glueTwoSitesS x (⟨x.val + 1, hxL⟩ : Fin L) a τ with hσ
  have hx0 : σ x = a 0 := by rw [hσ, glueTwoSitesS, if_pos rfl]
  have hx1 : σ (⟨x.val + 1, hxL⟩ : Fin L) = a 1 := by
    rw [hσ, glueTwoSitesS, if_neg (by simp only [Fin.ext_iff]; omega), if_pos rfl]
  have hslice : bondSlice x (openVBSState L p q) τ a
      = orderedProd akltVBSMatrices (List.ofFn σ) p q := by
    rw [bondSlice, twoSiteSliceS, hsucc, openVBSState]
  rw [hslice, orderedProd_ofFn_bond_split akltVBSMatrices σ x hxL, hx0, hx1,
    take_ofFn_glueTwoSitesS x hxL a τ, drop_ofFn_glueTwoSitesS x hxL a τ]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Every open VBS state has the **valence-bond-solid singlet-tensor form** (Tasaki eq. (7.1.20))
at every open bond: its bond slice is a linear functional of the two-site AKLT tensor, hence lies
in the four-dimensional bond subspace `W`. -/
theorem openVBSState_isVBSGroundForm {x : Fin L} (hx : x ∈ openBonds L) (p q : Fin 2) :
    IsVBSGroundForm L x (openVBSState L p q) := fun τ =>
  mem_vbsBondSubspace_of_twoSiteTensor _ _ (openVBSState_bondSlice_apply hx p q τ)

/-- **Frustration-freeness of the open VBS states.**  The bond spin-2 projection annihilates every
`Φ_{pq}` at every open bond (Lemma 7.4, `⇐` direction).  The wrap bond is absent, so — unlike the
ring — nothing is claimed at the last site. -/
theorem bondSpin2ProjectionS_mulVec_openVBSState_eq_zero (hL : 1 < L) {x : Fin L}
    (hx : x ∈ openBonds L) (p q : Fin 2) :
    (bondSpin2ProjectionS x (ringSucc x)).mulVec (openVBSState L p q) = 0 :=
  (tasaki_lemma_7_4 hL x (openVBSState L p q)).mpr (openVBSState_isVBSGroundForm hx p q)

/-- The local lower bounds `P̂_{x,x+1} − 0 ≥ 0` of every open bond, in the shape consumed by
Tasaki Lemmas A.9 and A.10 with all local energies `ε_x ≡ 0`. -/
private theorem openBond_sub_zero_posSemidef (hL : 2 ≤ L) :
    ∀ x ∈ openBonds L,
      (bondSpin2ProjectionS x (ringSucc x)
        - ((0 : ℝ) : ℂ) • (1 : ManyBodyOpS (Fin L) 2)).PosSemidef := by
  intro x _
  simpa using bondSpin2ProjectionS_posSemidef (ne_ringSucc (by omega) x)

/-- Positivity of `Ĥ'^open` together with the vanishing `Ĥ'^open Φ_{pq} = 0`, both from a single
application of Tasaki Lemma A.9 with `ε ≡ 0` over the Finset `openBonds L`: the local bounds are
the bond positivity and the simultaneous-eigenstate hypothesis is frustration-freeness. -/
private theorem openProjHamiltonianS_posSemidef_and_mulVec (hL : 2 ≤ L) (p q : Fin 2) :
    (openProjHamiltonianS L).PosSemidef ∧
      (openProjHamiltonianS L).mulVec (openVBSState L p q) = 0 := by
  have heig : ∀ x ∈ openBonds L,
      (bondSpin2ProjectionS x (ringSucc x)).mulVec (openVBSState L p q)
        = ((0 : ℝ) : ℂ) • openVBSState L p q := by
    intro x hx
    simpa using bondSpin2ProjectionS_mulVec_openVBSState_eq_zero (by omega) hx p q
  obtain ⟨hpsd, hker⟩ :=
    LatticeSystem.Math.frustration_free_isGroundState (openBonds L)
      (fun x : Fin L => bondSpin2ProjectionS x (ringSucc x)) (fun _ => (0 : ℝ))
      (openVBSState L p q) (openBond_sub_zero_posSemidef hL) heig
  exact ⟨by simpa [openProjHamiltonianS] using hpsd, by simpa [openProjHamiltonianS] using hker⟩

/-- **Problem 7.2.3.a (frustration-free half).**  The open projector Hamiltonian is positive
semidefinite, and each of the four open VBS states is annihilated by **every** bond projection of
the open chain — so all four sit at the bottom of the spectrum simultaneously. -/
theorem openProjHamiltonianS_posSemidef_and_annihilates (hL : 2 ≤ L) :
    (openProjHamiltonianS L).PosSemidef ∧
      ∀ x ∈ openBonds L, ∀ p q : Fin 2,
        (bondSpin2ProjectionS x (ringSucc x)).mulVec (openVBSState L p q) = 0 :=
  ⟨(openProjHamiltonianS_posSemidef_and_mulVec hL 0 0).1,
    fun _ hx p q => bondSpin2ProjectionS_mulVec_openVBSState_eq_zero (by omega) hx p q⟩

/-! ## Linear independence of the four open VBS states -/

/-- The middle AKLT matrix `A¹` is the diagonal matrix `diag(½, −½)`. -/
private theorem akltVBSMatrices_one_eq_diagonal :
    akltVBSMatrices 1 = Matrix.diagonal ![(1 / 2 : ℂ), -(1 / 2 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [akltVBSMatrices, Matrix.diagonal]

/-- An all-`|0⟩` block of `n` sites contributes the diagonal matrix `diag((½)^n, (−½)^n)` to the
ordered product. -/
private theorem orderedProd_replicate_one (n : ℕ) :
    orderedProd akltVBSMatrices (List.replicate n 1)
      = Matrix.diagonal ![(1 / 2 : ℂ) ^ n, (-(1 / 2 : ℂ)) ^ n] := by
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp [orderedProd, Matrix.diagonal]
  | succ n ih =>
      rw [List.replicate_succ, orderedProd, ih, akltVBSMatrices_one_eq_diagonal,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      fin_cases i <;> simp [pow_succ] <;> ring

/-- The four evaluation configurations of Problem 7.2.3.a: the two chosen values `b₀, b₁` on the
first two sites, followed by `|0⟩` (the label `1`) on every remaining site.  The two-site prefix is
what makes `2 ≤ L` — and not `3 ≤ L` — the right hypothesis. -/
private def openLIConfig {m : ℕ} (b₀ b₁ : Fin 3) : Fin (m + 2) → Fin 3 :=
  fun k => if k.val = 0 then b₀ else if k.val = 1 then b₁ else 1

/-- The word of an evaluation configuration: `b₀ :: b₁ :: |0⟩^m`. -/
private theorem ofFn_openLIConfig {m : ℕ} (b₀ b₁ : Fin 3) :
    List.ofFn (openLIConfig (m := m) b₀ b₁) = b₀ :: b₁ :: List.replicate m 1 := by
  rw [List.ofFn_succ, List.ofFn_succ]
  have hrest : (fun i : Fin m => openLIConfig (m := m) b₀ b₁ i.succ.succ) = fun _ : Fin m => 1 := by
    funext i
    simp [openLIConfig]
  rw [hrest, List.ofFn_const]
  simp [openLIConfig]

/-- The open VBS state at an evaluation configuration is the explicit matrix entry
`(A^{b₀} A^{b₁} diag((½)^m, (−½)^m))_{pq}`. -/
private theorem openVBSState_openLIConfig {m : ℕ} (b₀ b₁ : Fin 3) (p q : Fin 2) :
    openVBSState (m + 2) p q (openLIConfig b₀ b₁)
      = (akltVBSMatrices b₀ * akltVBSMatrices b₁
          * Matrix.diagonal ![(1 / 2 : ℂ) ^ m, (-(1 / 2 : ℂ)) ^ m]) p q := by
  rw [openVBSState, ofFn_openLIConfig]
  simp only [orderedProd, orderedProd_replicate_one]
  rw [Matrix.mul_assoc]

/-- `(√2)⁻¹ (√2)⁻¹ = ½`, the only irrational input of the four evaluations. -/
private theorem sqrtTwo_inv_mul_self :
    ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = (1 / 2 : ℂ) := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- Evaluation at `(|−⟩, |+⟩, |0⟩, …)`: only the `(0,0)` boundary component survives. -/
private theorem openVBSState_config_two_zero {m : ℕ} (p q : Fin 2) :
    openVBSState (m + 2) p q (openLIConfig 2 0)
      = if p = 0 ∧ q = 0 then -((1 / 2 : ℂ) ^ (m + 1)) else 0 := by
  rw [openVBSState_openLIConfig]
  fin_cases p <;> fin_cases q <;>
    simp [akltVBSMatrices, Matrix.mul_apply, Matrix.diagonal, sqrtTwo_inv_mul_self, pow_succ]
  ring

/-- Evaluation at `(|−⟩, |0⟩, |0⟩, …)`: only the `(0,1)` boundary component survives. -/
private theorem openVBSState_config_two_one {m : ℕ} (p q : Fin 2) :
    openVBSState (m + 2) p q (openLIConfig 2 1)
      = if p = 0 ∧ q = 1 then ((Real.sqrt 2 : ℂ))⁻¹ * (-(1 / 2 : ℂ)) ^ (m + 1) else 0 := by
  rw [openVBSState_openLIConfig]
  fin_cases p <;> fin_cases q <;>
    simp [akltVBSMatrices, Matrix.mul_apply, Matrix.diagonal, pow_succ]
  ring

/-- Evaluation at `(|+⟩, |0⟩, |0⟩, …)`: only the `(1,0)` boundary component survives. -/
private theorem openVBSState_config_zero_one {m : ℕ} (p q : Fin 2) :
    openVBSState (m + 2) p q (openLIConfig 0 1)
      = if p = 1 ∧ q = 0 then -(((Real.sqrt 2 : ℂ))⁻¹ * (1 / 2 : ℂ) ^ (m + 1)) else 0 := by
  rw [openVBSState_openLIConfig]
  fin_cases p <;> fin_cases q <;>
    simp [akltVBSMatrices, Matrix.mul_apply, Matrix.diagonal, pow_succ]
  ring

/-- Evaluation at the all-`|0⟩` configuration: the two diagonal boundary components survive. -/
private theorem openVBSState_config_one_one {m : ℕ} (p q : Fin 2) :
    openVBSState (m + 2) p q (openLIConfig 1 1)
      = if p = 0 ∧ q = 0 then (1 / 2 : ℂ) ^ (m + 2)
        else if p = 1 ∧ q = 1 then (-(1 / 2 : ℂ)) ^ (m + 2) else 0 := by
  rw [openVBSState_openLIConfig]
  fin_cases p <;> fin_cases q <;>
    simp [akltVBSMatrices, Matrix.mul_apply, Matrix.diagonal, pow_succ] <;>
    ring

/-- **Problem 7.2.3.a.**  The four open VBS states `Φ_{pq}` are linearly independent.  Each of the
four evaluation configurations is load-bearing: `(|−⟩,|+⟩,|0⟩,…)` isolates `c₀₀`,
`(|−⟩,|0⟩,…)` isolates `c₀₁`, `(|+⟩,|0⟩,…)` isolates `c₁₀`, and the all-`|0⟩` configuration then
gives `c₁₁` once `c₀₀` is known.  They are *not* orthogonal (Tasaki's solution notes this
explicitly), so independence — not orthonormality — is the correct statement.  The weakest
hypothesis is `2 ≤ L`: the two-site prefix of the first configuration is all that is needed. -/
theorem openVBSState_linearIndependent (hL : 2 ≤ L) :
    LinearIndependent ℂ fun r : Fin 2 × Fin 2 => openVBSState L r.1 r.2 := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 2 := ⟨L - 2, by omega⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hval : ∀ σ : Fin (m + 2) → Fin 3,
      ∑ r : Fin 2 × Fin 2, c r * openVBSState (m + 2) r.1 r.2 σ = 0 := by
    intro σ
    have h := congrFun hc σ
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h
  have h00 := hval (openLIConfig 2 0)
  have h01 := hval (openLIConfig 2 1)
  have h10 := hval (openLIConfig 0 1)
  have h11 := hval (openLIConfig 1 1)
  rw [Fintype.sum_prod_type] at h00 h01 h10 h11
  simp only [Fin.sum_univ_two, openVBSState_config_two_zero, openVBSState_config_two_one,
    openVBSState_config_zero_one, openVBSState_config_one_one] at h00 h01 h10 h11
  norm_num at h00 h01 h10 h11
  have hc11 : c (1, 1) = 0 := by
    rw [h00, zero_mul, zero_add] at h11
    exact (mul_eq_zero.mp h11).resolve_right (pow_ne_zero _ (by norm_num))
  rintro ⟨p, q⟩
  fin_cases p <;> fin_cases q
  · exact h00
  · exact h01
  · exact h10
  · exact hc11
/-! ## The ground energy of the open chain and the `4 ≤ dim` bound -/

/-- The ground energy of the open projector Hamiltonian is `0`: it is attained by the (nonzero)
open VBS state and cannot be undercut because `Ĥ'^open ≥ 0`. -/
theorem isGroundEnergy_openProjHamiltonianS (hL : 2 ≤ L) :
    IsGroundEnergy (openProjHamiltonianS L) 0 := by
  obtain ⟨hpsd, hker⟩ := openProjHamiltonianS_posSemidef_and_mulVec hL 0 0
  refine ⟨⟨openVBSState L 0 0, (openVBSState_linearIndependent hL).ne_zero (0, 0), ?_⟩,
    fun E hE => ?_⟩
  · rw [hker]
    simp
  · exact realSpectrum_nonneg_of_posSemidef hpsd hE

/-- **The ground energy of the open AKLT chain is `−(2/3)(L − 1)`** (Tasaki eq. (7.2.46)): the
affine image of the projector ground energy `0` under `Ĥ^open = 2 Ĥ'^open − (2/3)(L − 1)`.  The
shift counts the `L − 1` **bonds**, not the `L` sites — the periodic value `−(2/3)L` is not a
ground energy here. -/
theorem isGroundEnergy_openAKLTHamiltonianS (hL : 2 ≤ L) :
    IsGroundEnergy (openAKLTHamiltonianS L) (-(2 : ℝ) / 3 * ((L : ℝ) - 1)) := by
  have hg := isGroundEnergy_affine (a := (2 : ℝ)) (b := -(2 : ℝ) / 3 * ((L : ℝ) - 1))
    (by norm_num) (isGroundEnergy_openProjHamiltonianS hL)
  rw [show (2 : ℝ) * 0 + -(2 : ℝ) / 3 * ((L : ℝ) - 1) = -(2 : ℝ) / 3 * ((L : ℝ) - 1) from by ring]
    at hg
  rw [openAKLTHamiltonianS_eq_affine_sub_one (by omega)]
  exact hg

/-- The **ground space of the open AKLT chain**: the eigenspace of `Ĥ^open` at the ground energy
`−(2/3)(L − 1)`. -/
noncomputable def openAKLTGroundSpace (L : ℕ) : Submodule ℂ ((Fin L → Fin 3) → ℂ) :=
  Module.End.eigenspace (Matrix.mulVecLin (openAKLTHamiltonianS L))
    ((-(2 : ℝ) / 3 * ((L : ℝ) - 1) : ℝ) : ℂ)

/-- The ground space is the kernel of the projector Hamiltonian.  This is pure affine algebra —
`Ĥ^open − E₀ = 2 Ĥ'^open` with `2 ≠ 0` — and needs no frustration-free input. -/
theorem openAKLTGroundSpace_eq_ker (hL : 1 ≤ L) :
    openAKLTGroundSpace L = LinearMap.ker (Matrix.mulVecLin (openProjHamiltonianS L)) := by
  ext Φ
  rw [openAKLTGroundSpace, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply,
    LinearMap.mem_ker, Matrix.mulVecLin_apply, openAKLTHamiltonianS_eq_affine_sub_one hL,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  constructor
  · intro h
    have h2 : ((2 : ℝ) : ℂ) • (openProjHamiltonianS L).mulVec Φ = 0 := by
      rw [← sub_eq_zero] at h
      simpa using h
    have hne : ((2 : ℝ) : ℂ) ≠ 0 := by norm_num
    exact (smul_eq_zero.mp h2).resolve_left hne
  · intro h
    rw [h, smul_zero, zero_add]

/-- Each open VBS state lies in the ground space of `Ĥ^open`. -/
theorem openVBSState_mem_openAKLTGroundSpace (hL : 2 ≤ L) (p q : Fin 2) :
    openVBSState L p q ∈ openAKLTGroundSpace L := by
  rw [openAKLTGroundSpace_eq_ker (by omega), LinearMap.mem_ker, Matrix.mulVecLin_apply]
  exact (openProjHamiltonianS_posSemidef_and_mulVec hL p q).2

/-- **Problem 7.2.3.a, the lower bound.**  The ground space of the open AKLT chain has complex
dimension at least `4`: the four independent boundary components `Φ_{pq}` all sit in it.  At
`L = 2` this matches the proved dimension `4` of the VBS bond subspace `W`
(`finrank_vbsBondSubspace`).  The matching upper bound is the completeness half of Problem
7.2.3.b and is not proved here. -/
theorem four_le_finrank_openAKLTGroundSpace (hL : 2 ≤ L) :
    4 ≤ Module.finrank ℂ (openAKLTGroundSpace L) := by
  have hspan : Submodule.span ℂ (Set.range fun r : Fin 2 × Fin 2 => openVBSState L r.1 r.2)
      ≤ openAKLTGroundSpace L := by
    rw [Submodule.span_le]
    rintro v ⟨⟨p, q⟩, rfl⟩
    exact openVBSState_mem_openAKLTGroundSpace hL p q
  have hfr : Module.finrank ℂ
      (Submodule.span ℂ (Set.range fun r : Fin 2 × Fin 2 => openVBSState L r.1 r.2)) = 4 := by
    rw [finrank_span_eq_card (openVBSState_linearIndependent hL)]
    simp
  rw [← hfr]
  exact Submodule.finrank_mono hspan

end LatticeSystem.Quantum
