import LatticeSystem.Fermion.JordanWigner.Hubbard.HardcoreBasis
import LatticeSystem.Fermion.JordanWigner.VacuumCreationBasisVec

/-!
# The Tasaki ordered creation-operator basis (11.2.3)

This file formalizes Tasaki eq. (11.2.3): the ordered Jordan–Wigner
creation-operator basis state of the one-hole hard-core Nagaoka sector, and
proves it equals a signed computational basis vector, from which orthonormality
is inherited.

Per (11.2.3), the basis state is

  `|Φ_{x,σ}⟩ := ĉ_{x,↑} (∏_{y∈Λ} ĉ†_{y,σ̄_y}) |vac⟩`,   `σ̄_x = ↑`,

i.e. every site is filled by an *ordered* creation product (here in increasing
Jordan–Wigner index order), and then the electron at the hole site `x` is
annihilated. This "redundant" double action is exactly Tasaki's device for
fixing the precise fermion signs that make the hopping matrix elements (11.2.5)
uniformly signed.

The key technical fact is `prod_creation_mulVec_vacuum`: applying a
strictly index-sorted product of creation operators to the vacuum yields the
computational basis vector of the occupied configuration, and *every*
Jordan–Wigner string sign along the way is `1` because each successive creation
operator acts at the smallest occupied index so far (no occupied mode lies below
it). The single annihilation at the hole then contributes the one nontrivial
string sign `ε`, giving `|Φ_{x,σ}⟩ = ε • basisVec`.

Tracked in Issue #4130. Reference: Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, 1st edition, §11.2, eq. (11.2.3), pp. 382-383.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-! ## Occupation configuration of a finite index list -/

/-- The computational configuration occupied exactly on the indices in a list
`js`: value `1` on every index appearing in `js`, and `0` elsewhere. -/
def occupationOf {M : ℕ} (js : List (Fin (M + 1))) : Fin (M + 1) → Fin 2 :=
  fun k => if k ∈ js then 1 else 0

/-- Adding an index `j` to the front of the list flips its occupation to `1`:
`occupationOf (j :: js) = (occupationOf js)[j ↦ 1]`. -/
theorem occupationOf_cons {M : ℕ} (j : Fin (M + 1)) (js : List (Fin (M + 1))) :
    occupationOf (j :: js) = Function.update (occupationOf js) j 1 := by
  funext k
  simp only [occupationOf, Function.update_apply, List.mem_cons]
  by_cases hkj : k = j
  · simp [hkj]
  · simp [hkj]

/-! ## Ordered creation product on the vacuum -/

/-- General fold lemma for the ordered creation-operator construction: a
strictly index-sorted product of creation operators applied to the
Jordan–Wigner vacuum yields the computational basis vector of the configuration
occupied on exactly those indices.

Because the list is strictly increasing, the rightmost (largest-index) operator
acts first, and every subsequent creation operator acts at an index smaller than
all currently occupied modes; hence each Jordan–Wigner string sign is `1`, and
no orbital is ever doubly created. -/
theorem prod_creation_mulVec_vacuum (M : ℕ) (js : List (Fin (M + 1)))
    (hsorted : js.Pairwise (· < ·)) :
    (List.prod (js.map (fermionMultiCreation M))).mulVec (fermionMultiVacuum M) =
      basisVec (occupationOf js) := by
  induction js with
  | nil =>
    have hempty : occupationOf ([] : List (Fin (M + 1))) = (fun _ => 0) := by
      funext k; simp [occupationOf]
    rw [List.map_nil, List.prod_nil, Matrix.one_mulVec, hempty]
    rfl
  | cons j js ih =>
    obtain ⟨hjs, htail⟩ := List.pairwise_cons.mp hsorted
    -- `j` is below every element of the tail, so `j ∉ js`.
    have hjnotin : j ∉ js := fun hj => absurd (hjs j hj) (lt_irrefl j)
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih htail,
      fermionMultiCreation_mulVec_basisVec]
    -- The orbital `j` is empty in the tail configuration.
    have hempty : occupationOf js j = 0 := by simp [occupationOf, hjnotin]
    rw [if_pos hempty]
    -- Every mode below `j` is empty in the tail configuration, so the sign is 1.
    have hsign : jwSign M j (occupationOf js) = 1 := by
      unfold jwSign
      refine Finset.prod_eq_one (fun k hk => ?_)
      simp only [Finset.mem_filter] at hk
      have hknotin : k ∉ js := fun hk' => by
        have := hjs k hk'
        omega
      simp [occupationOf, hknotin]
    rw [hsign, one_smul, occupationOf_cons]

/-! ## The Tasaki ordered-creation basis state -/

/-- The list of Jordan–Wigner indices occupied by the all-filled configuration
with spin `τ`: site `s` contributes its up-orbital `2s` if `τ s` and its
down-orbital `2s + 1` otherwise. Listing the sites in increasing order makes the
index list strictly increasing. -/
def tasakiIndexList (N : ℕ) (τ : Fin (N + 1) → Bool) : List (Fin (2 * N + 2)) :=
  (List.finRange (N + 1)).map (fun s => spinfulIndex N s (if τ s then 0 else 1))

/-- The Tasaki ordered-creation basis state `|Φ_{x,σ}⟩` of eq. (11.2.3):
fill every site by the increasing-order creation product for the spin
configuration `σ̄ = σ[x ↦ ↑]`, then annihilate the spin-up electron at the hole
site `x`. -/
noncomputable def hubbardTasakiBasisState (N : ℕ) (x : Fin (N + 1))
    (σ : Fin (N + 1) → Bool) : (Fin (2 * N + 2) → Fin 2) → ℂ :=
  (fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N x 0) *
      List.prod ((tasakiIndexList N (Function.update σ x true)).map
        (fermionMultiCreation (2 * N + 1)))).mulVec
    (fermionMultiVacuum (2 * N + 1))

/-! ## Auxiliary facts about `tasakiIndexList` -/

/-- Joint injectivity of `spinfulIndex` in the site and the spin label. -/
private theorem spinfulIndex_inj (N : ℕ) {a a' : Fin (N + 1)} {r r' : Fin 2}
    (h : spinfulIndex N a r = spinfulIndex N a' r') : a = a' ∧ r = r' := by
  have hv : 2 * a.val + r.val = 2 * a'.val + r'.val := by
    have := congrArg Fin.val h
    simpa [spinfulIndex] using this
  have hr := r.isLt
  have hr' := r'.isLt
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

/-- Every spinful index decomposes as `spinfulIndex N a r`. -/
private theorem exists_spinfulIndex (N : ℕ) (k : Fin (2 * N + 2)) :
    ∃ (a : Fin (N + 1)) (r : Fin 2), k = spinfulIndex N a r := by
  have hk := k.isLt
  refine ⟨⟨k.val / 2, (Nat.div_lt_iff_lt_mul (by norm_num)).mpr (by omega)⟩,
    ⟨k.val % 2, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
  apply Fin.ext
  simp only [spinfulIndex]
  omega

/-- Membership in `tasakiIndexList`: `spinfulIndex N a r` is occupied exactly
when `r` is the orbital selected by the spin `τ a`. -/
theorem mem_tasakiIndexList_iff (N : ℕ) (τ : Fin (N + 1) → Bool)
    (a : Fin (N + 1)) (r : Fin 2) :
    spinfulIndex N a r ∈ tasakiIndexList N τ ↔ r = (if τ a then 0 else 1) := by
  unfold tasakiIndexList
  rw [List.mem_map]
  constructor
  · rintro ⟨s, _, hs⟩
    obtain ⟨rfl, hr⟩ := spinfulIndex_inj N hs
    exact hr.symm
  · intro hr
    exact ⟨a, List.mem_finRange a, by rw [hr]⟩

/-- The list `tasakiIndexList N τ` is strictly increasing: the indices are the
images under `spinfulIndex` of the increasing site list, and `spinfulIndex` is
strictly monotone in the site regardless of the spin label. -/
theorem tasakiIndexList_sorted (N : ℕ) (τ : Fin (N + 1) → Bool) :
    (tasakiIndexList N τ).Pairwise (· < ·) := by
  unfold tasakiIndexList
  refine List.Pairwise.map _ (fun a b hab => ?_)
    (List.sortedLT_finRange (N + 1)).pairwise
  -- `a < b` as sites ⇒ `2a + r ≤ 2a + 1 < 2b ≤ 2b + r'` as indices.
  have ha := (if τ a then (0 : Fin 2) else 1).isLt
  have hb := (if τ b then (0 : Fin 2) else 1).isLt
  have hab' : a.val < b.val := hab
  simp only [spinfulIndex, Fin.lt_def]
  omega

/-! ## The Tasaki basis state is a signed computational basis vector -/

/-- The full-occupation configuration with one electron annihilated at the
hole's up-orbital is exactly the one-hole configuration: removing the spin-up
electron at `x` from the all-filled configuration `σ[x ↦ ↑]` gives
`hubbardOneHoleConfig N x σ`. -/
private theorem update_occupationOf_eq_oneHoleConfig (N : ℕ) (x : Fin (N + 1))
    (σ : Fin (N + 1) → Bool) :
    Function.update (occupationOf (tasakiIndexList N (Function.update σ x true)))
        (spinfulIndex N x 0) 0 =
      hubbardOneHoleConfig N x σ := by
  funext k
  obtain ⟨a, r, rfl⟩ := exists_spinfulIndex N k
  have hr2 : r = 0 ∨ r = 1 := by
    rcases r with ⟨rv, hrv⟩; interval_cases rv
    · exact Or.inl rfl
    · exact Or.inr rfl
  -- Occupation of the all-filled `σ[x ↦ ↑]` configuration at `(a, r)`.
  have hocc : occupationOf (tasakiIndexList N (Function.update σ x true))
        (spinfulIndex N a r) =
      (if r = (if (Function.update σ x true) a then (0 : Fin 2) else 1) then 1
        else 0) := by
    simp only [occupationOf]
    by_cases hr : r = (if (Function.update σ x true) a then (0 : Fin 2) else 1)
    · rw [if_pos ((mem_tasakiIndexList_iff N _ a r).mpr hr), if_pos hr]
    · rw [if_neg (fun hcon => hr ((mem_tasakiIndexList_iff N _ a r).mp hcon)),
        if_neg hr]
  rw [Function.update_apply, hocc]
  by_cases hax : a = x
  · -- At the hole site: `σ̄_a = ↑`, selected orbital `0`.
    subst hax
    simp only [Function.update_self, if_true]
    rcases hr2 with rfl | rfl
    · rw [if_pos rfl, hubbardOneHoleConfig_apply_up, if_pos rfl]
    · have hne : spinfulIndex N a 1 ≠ spinfulIndex N a 0 := fun h =>
        absurd (spinfulIndex_inj N h).2 (by decide)
      rw [if_neg hne, hubbardOneHoleConfig_apply_down, if_pos rfl]
      decide
  · -- Away from the hole: `σ̄_a = σ_a`, and the hole-orbital update never fires.
    have hne : spinfulIndex N a r ≠ spinfulIndex N x 0 := fun h =>
      hax (spinfulIndex_inj N h).1
    have hax' : a.val ≠ x.val := fun h => hax (Fin.ext h)
    rw [if_neg hne, Function.update_of_ne hax]
    rcases hr2 with rfl | rfl
    · rw [hubbardOneHoleConfig_apply_up, if_neg hax']
      by_cases hσ : σ a <;> simp [hσ]
    · rw [hubbardOneHoleConfig_apply_down, if_neg hax']
      by_cases hσ : σ a <;> simp [hσ]

/-- The Jordan–Wigner string sign of annihilating the spin-up electron at the
hole site `x` in the all-filled configuration `σ[x ↦ ↑]`. This is the single
nontrivial fermion sign produced by the ordered-creation construction. -/
noncomputable def hubbardTasakiBasisSign (N : ℕ) (x : Fin (N + 1))
    (σ : Fin (N + 1) → Bool) : ℂ :=
  jwSign (2 * N + 1) (spinfulIndex N x 0)
    (occupationOf (tasakiIndexList N (Function.update σ x true)))

/-- The Tasaki ordered-creation basis state equals a signed computational basis
vector: `|Φ_{x,σ}⟩ = ε • basisVec (hubbardOneHoleConfig N x σ)`, where the sign
`ε = hubbardTasakiBasisSign N x σ` is the single Jordan–Wigner annihilation
string sign. This is the content of Tasaki eq. (11.2.3) recast onto the
sign-free `basisVec` basis. -/
theorem hubbardTasakiBasisState_eq_smul_basisVec (N : ℕ) (x : Fin (N + 1))
    (σ : Fin (N + 1) → Bool) :
    hubbardTasakiBasisState N x σ =
      hubbardTasakiBasisSign N x σ • basisVec (hubbardOneHoleConfig N x σ) := by
  unfold hubbardTasakiBasisState hubbardTasakiBasisSign
  rw [← Matrix.mulVec_mulVec,
    prod_creation_mulVec_vacuum (2 * N + 1) _
      (tasakiIndexList_sorted N (Function.update σ x true)),
    fermionMultiAnnihilation_mulVec_basisVec]
  -- The hole's up-orbital is occupied in the all-filled configuration.
  have hocc : occupationOf (tasakiIndexList N (Function.update σ x true))
      (spinfulIndex N x 0) = 1 := by
    simp only [occupationOf]
    rw [if_pos ((mem_tasakiIndexList_iff N _ x 0).mpr (by simp))]
  rw [if_pos hocc, update_occupationOf_eq_oneHoleConfig]

/-- The annihilation string sign squares to `1` (it is a product of `±1`). -/
theorem hubbardTasakiBasisSign_mul_self (N : ℕ) (x : Fin (N + 1))
    (σ : Fin (N + 1) → Bool) :
    hubbardTasakiBasisSign N x σ * hubbardTasakiBasisSign N x σ = 1 := by
  unfold hubbardTasakiBasisSign jwSign
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one (fun k _ => ?_)
  by_cases h : occupationOf (tasakiIndexList N (Function.update σ x true)) k = 0 <;>
    simp [h]

/-! ## Orthonormality of the Tasaki basis states -/

/-- Real bilinear pairing of two Tasaki basis states: it is the product of the
two string signs times the indicator that their one-hole configurations agree.
Orthonormality is inherited from the underlying computational basis vectors. -/
theorem hubbardTasakiBasisState_inner (N : ℕ) (x x' : Fin (N + 1))
    (σ σ' : Fin (N + 1) → Bool) :
    ∑ τ : Fin (2 * N + 2) → Fin 2,
        hubbardTasakiBasisState N x σ τ * hubbardTasakiBasisState N x' σ' τ =
      hubbardTasakiBasisSign N x σ * hubbardTasakiBasisSign N x' σ' *
        (if hubbardOneHoleConfig N x' σ' = hubbardOneHoleConfig N x σ then 1
          else 0) := by
  simp only [hubbardTasakiBasisState_eq_smul_basisVec, Pi.smul_apply,
    smul_eq_mul]
  rw [← basisVec_inner (hubbardOneHoleConfig N x σ) (hubbardOneHoleConfig N x' σ'),
    Finset.mul_sum]
  exact Finset.sum_congr rfl (fun τ _ => by ring)

/-- Each Tasaki basis state is normalized: its self-overlap is `1` (the string
sign squares to `1` and the configuration matches itself). -/
theorem hubbardTasakiBasisState_self_inner (N : ℕ) (x : Fin (N + 1))
    (σ : Fin (N + 1) → Bool) :
    ∑ τ : Fin (2 * N + 2) → Fin 2,
        hubbardTasakiBasisState N x σ τ * hubbardTasakiBasisState N x σ τ = 1 := by
  rw [hubbardTasakiBasisState_inner, if_pos rfl, mul_one,
    hubbardTasakiBasisSign_mul_self]

end LatticeSystem.Fermion
