import LatticeSystem.Quantum.SpinS.DressedHeisenberg

/-!
# Off-`{x, y}`-agree vanishing variants of the dressed-Heisenberg matrix
(build-speed companion)

Build-speed companion to `DressedHeisenberg.lean`. Hosts the
trailing section "Off-`{x, y}`-agree vanishing variants (γ-3 prep)"
through the final
`dressedHeisenbergS_apply_re_nonpos_of_ne_bipartite`
(originally lines 1056..1361 of the parent file).

Splitting these blocks out drops the parent from ~1362 lines to
~1055 lines. Downstream files that need only the core
dressed-Heisenberg matrix API can keep importing the parent;
consumers of the off-`{x, y}`-agree vanishing / re-nonpos
arguments should import this companion.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 Theorem 2.3 (Marshall–Lieb–Mattis).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Off-`{x, y}`-agree vanishing variants (γ-3 prep)

These three lemmas package the vanishing cases of the two-site
matrix-element formula: when σ', σ off-`{x, y}`-agree but the
spinSDot factor is forced to zero by some structural reason, the
dressed-Heisenberg matrix element vanishes too. -/

/-- **Off-`{x, y}`-agree dressed vanishing, magnetization mismatch**:
when σ', σ off-`{x, y}`-agree with σ' ≠ σ but carry different
magnetization quantum numbers, the dressed matrix element vanishes
(via the two-site formula and `spinSDot_apply_eq_zero_of_mag_ne`). -/
theorem dressedHeisenbergS_apply_eq_zero_of_off_two_site_agree_of_mag_ne
    (A : V → Bool) {J : V → V → ℂ} {x y : V} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : V → Fin (N + 1)} (hne : σ' ≠ σ)
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hmag : magEigenvalueS σ ≠ magEigenvalueS σ') :
    dressedHeisenbergS A J N σ' σ = 0 := by
  rw [dressedHeisenbergS_apply_of_off_two_site_agree A hxy N hne h]
  rw [spinSDot_apply_eq_zero_of_mag_ne x y N hmag]
  ring

/-- **Off-`{x, y}`-agree dressed vanishing at `x` non-`±1` shift**:
when σ', σ off-`{x, y}`-agree with σ' ≠ σ and σ' x val differs from
σ x val by an amount other than `±1`, the dressed matrix element
vanishes (via the two-site formula and the spinSDot diff-at-x-not-pm1
vanishing lemma). -/
theorem dressedHeisenbergS_apply_eq_zero_of_off_two_site_agree_diff_at_x_not_pm1
    (A : V → Bool) {J : V → V → ℂ} {x y : V} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : V → Fin (N + 1)} (hne : σ' ≠ σ)
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hσx : σ' x ≠ σ x)
    (hxp : (σ' x).val + 1 ≠ (σ x).val)
    (hxm : (σ x).val + 1 ≠ (σ' x).val) :
    dressedHeisenbergS A J N σ' σ = 0 := by
  rw [dressedHeisenbergS_apply_of_off_two_site_agree A hxy N hne h]
  rw [spinSDot_apply_eq_zero_of_off_two_site_agree_diff_at_x_not_pm1
    hxy N h hσx hxp hxm]
  ring

/-- **Off-`{x, y}`-agree dressed vanishing at `y` non-`±1` shift**:
symmetric of `..._diff_at_x_not_pm1`. -/
theorem dressedHeisenbergS_apply_eq_zero_of_off_two_site_agree_diff_at_y_not_pm1
    (A : V → Bool) {J : V → V → ℂ} {x y : V} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : V → Fin (N + 1)} (hne : σ' ≠ σ)
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hσy : σ' y ≠ σ y)
    (hyp : (σ' y).val + 1 ≠ (σ y).val)
    (hym : (σ y).val + 1 ≠ (σ' y).val) :
    dressedHeisenbergS A J N σ' σ = 0 := by
  rw [dressedHeisenbergS_apply_of_off_two_site_agree A hxy N hne h]
  rw [spinSDot_apply_eq_zero_of_off_two_site_agree_diff_at_y_not_pm1
    hxy N h hσy hyp hym]
  ring

/-- Helper: configurations agreeing off `{x, y}` have equal
magnetizations iff `(σ x).val + (σ y).val = (σ' x).val + (σ' y).val`. -/
private theorem magEigenvalueS_eq_iff_of_off_two_site_agree
    {x y : V} (hxy : x ≠ y) {N : ℕ} {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    magEigenvalueS σ' = magEigenvalueS σ ↔
      (σ' x).val + (σ' y).val = (σ x).val + (σ y).val := by
  classical
  have hsplit : ∀ τ : V → Fin (N + 1),
      magSumS τ =
        (∑ k ∈ ((Finset.univ : Finset V) \ ({x, y} : Finset V)),
            (τ k).val) + ((τ x).val + (τ y).val) := by
    intro τ
    unfold magSumS
    rw [← Finset.sum_sdiff (Finset.subset_univ ({x, y} : Finset V))]
    congr 1
    rw [Finset.sum_insert (Finset.notMem_singleton.mpr hxy),
      Finset.sum_singleton]
  have hrest :
      ∑ k ∈ (Finset.univ : Finset V) \ ({x, y} : Finset V), (σ' k).val =
        ∑ k ∈ (Finset.univ : Finset V) \ ({x, y} : Finset V), (σ k).val := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
      not_or, Finset.mem_univ, true_and] at hk
    rw [h k hk.1 hk.2]
  unfold magEigenvalueS
  constructor
  · intro hmag
    have hsumeq : magSumS σ' = magSumS σ := by
      have : ((magSumS σ' : ℂ)) = ((magSumS σ : ℂ)) := by linear_combination -hmag
      exact_mod_cast this
    rw [hsplit σ', hsplit σ, hrest] at hsumeq
    omega
  · intro hxy_sum
    have hsumeq : magSumS σ' = magSumS σ := by
      rw [hsplit σ', hsplit σ, hrest]
      omega
    push_cast [hsumeq]
    ring

/-- **Full off-diagonal dressed Heisenberg non-positivity on a bipartite
bond** (Tasaki §2.5 Property (ii) for general spin, all cases unified):

For `x ≠ y` with bipartite indicator `A x ≠ A y`, real symmetric
coupling `J` with `(J x y).re ≥ 0`, and *any* `σ' ≠ σ` agreeing off
`{x, y}`,

    `Re (dressedHeisenbergS A J N σ' σ) ≤ 0`.

Case analysis on the values of σ', σ at `{x, y}`:
- differ at exactly one site → `dressed = 0` (one_site_diff).
- differ at both, magnetization mismatched → `dressed = 0` (mag_ne).
- differ at both, mag conserved, `|Δσ x| ≠ 1` → `dressed = 0`
  (`diff_at_x_not_pm1`).
- differ at both, mag conserved, `|Δσ x| = 1` → exactly one of the
  four bipartite raising/lowering non-positivity lemmas (γ-2e). -/
theorem dressedHeisenbergS_apply_re_nonpos_of_off_two_site_agree_bipartite
    {x y : V} (hxy : x ≠ y) (N : ℕ)
    (A : V → Bool) (hAne : A x ≠ A y)
    {J : V → V → ℂ} (hJ_real : (J x y).im = 0) (hJ_nn : 0 ≤ (J x y).re)
    (hJ_sym : J x y = J y x)
    {σ' σ : V → Fin (N + 1)} (hne : σ' ≠ σ)
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (dressedHeisenbergS A J N σ' σ).re ≤ 0 := by
  -- Decompose A x ≠ A y into the two Bool sublattice configurations.
  have hA_or :
      (A x = true ∧ A y = false) ∨ (A x = false ∧ A y = true) := by
    have hxbool : A x = true ∨ A x = false := by
      cases A x <;> simp
    have hybool : A y = true ∨ A y = false := by
      cases A y <;> simp
    rcases hxbool with hax | hax <;> rcases hybool with hay | hay
    · exact (hAne (hax.trans hay.symm)).elim
    · exact Or.inl ⟨hax, hay⟩
    · exact Or.inr ⟨hax, hay⟩
    · exact (hAne (hax.trans hay.symm)).elim
  by_cases hσx : σ' x = σ x
  · -- σ' x = σ x; σ' ≠ σ forces difference at y → one_site_diff at y.
    have hσy : σ' y ≠ σ y := by
      intro hσy
      apply hne
      funext k
      by_cases hkx : k = x
      · subst hkx; exact hσx
      · by_cases hky : k = y
        · subst hky; exact hσy
        · exact h k hkx hky
    have hagree_y : ∀ k, k ≠ y → σ' k = σ k := fun k hky => by
      by_cases hkx : k = x
      · subst hkx; exact hσx
      · exact h k hkx hky
    rw [dressedHeisenbergS_apply_eq_zero_of_one_site_diff A J N
      hagree_y hσy]
    simp
  · by_cases hσy : σ' y = σ y
    · -- σ' y = σ y; differ only at x → one_site_diff at x.
      have hagree_x : ∀ k, k ≠ x → σ' k = σ k := fun k hkx => by
        by_cases hky : k = y
        · subst hky; exact hσy
        · exact h k hkx hky
      rw [dressedHeisenbergS_apply_eq_zero_of_one_site_diff A J N
        hagree_x hσx]
      simp
    · -- σ' x ≠ σ x AND σ' y ≠ σ y: both differ.
      -- Case on the difference at x.
      by_cases hxraise : (σ x).val + 1 = (σ' x).val
      · -- σ' x = σ x + 1: raising at x.
        by_cases hylower : (σ' y).val + 1 = (σ y).val
        · -- σ y = σ' y + 1: lowering at y. Mag conserved → use bipartite.
          rcases hA_or with ⟨hAx, hAy⟩ | ⟨hAx, hAy⟩
          · -- A x = true, A y = false.
            exact dressedHeisenbergS_apply_re_nonpos_bipartite_x
              hxy N A hAx hAy hJ_real hJ_nn hJ_sym h hxraise hylower
          · -- A x = false, A y = true.
            exact dressedHeisenbergS_apply_re_nonpos_bipartite_y_lowering
              hxy N A hAx hAy hJ_real hJ_nn hJ_sym h hxraise hylower
        · -- σ y val + 1 ≠ σ' y val. Either raising at y too (mag-ne) or non-pm1.
          by_cases hyraise : (σ y).val + 1 = (σ' y).val
          · -- raising at y too: mag mismatched (both raised).
            have hzero : dressedHeisenbergS A J N σ' σ = 0 := by
              apply dressedHeisenbergS_apply_eq_zero_of_off_two_site_agree_of_mag_ne
                A hxy N hne h
              intro hmag
              have hsum := (magEigenvalueS_eq_iff_of_off_two_site_agree
                hxy h).mp hmag.symm
              omega
            rw [hzero]; simp
          · -- σ' y val differs from σ y val by ≥ 2.
            have hzero : dressedHeisenbergS A J N σ' σ = 0 :=
              dressedHeisenbergS_apply_eq_zero_of_off_two_site_agree_diff_at_y_not_pm1
                A hxy N hne h hσy hylower hyraise
            rw [hzero]; simp
      · -- (σ x).val + 1 ≠ (σ' x).val.
        by_cases hxlower : (σ' x).val + 1 = (σ x).val
        · -- σ' x val + 1 = σ x val: lowering at x.
          by_cases hyraise : (σ y).val + 1 = (σ' y).val
          · -- raising at y: mag conserved → bipartite.
            rcases hA_or with ⟨hAx, hAy⟩ | ⟨hAx, hAy⟩
            · -- A x = true, A y = false.
              exact dressedHeisenbergS_apply_re_nonpos_bipartite_x_lowering
                hxy N A hAx hAy hJ_real hJ_nn hJ_sym h hxlower hyraise
            · -- A x = false, A y = true.
              exact dressedHeisenbergS_apply_re_nonpos_bipartite_y
                hxy N A hAx hAy hJ_real hJ_nn hJ_sym h hxlower hyraise
          · -- σ y val + 1 ≠ σ' y val.
            by_cases hylower : (σ' y).val + 1 = (σ y).val
            · -- σ' y val + 1 = σ y val: lowering at y too. Mag mismatched.
              have hzero : dressedHeisenbergS A J N σ' σ = 0 := by
                apply dressedHeisenbergS_apply_eq_zero_of_off_two_site_agree_of_mag_ne
                  A hxy N hne h
                intro hmag
                have hsum := (magEigenvalueS_eq_iff_of_off_two_site_agree
                  hxy h).mp hmag.symm
                omega
              rw [hzero]; simp
            · -- σ' y differs by ≥ 2 from σ y.
              have hzero : dressedHeisenbergS A J N σ' σ = 0 :=
                dressedHeisenbergS_apply_eq_zero_of_off_two_site_agree_diff_at_y_not_pm1
                  A hxy N hne h hσy hylower hyraise
              rw [hzero]; simp
        · -- |σ' x - σ x| ≥ 2.
          have hzero : dressedHeisenbergS A J N σ' σ = 0 :=
            dressedHeisenbergS_apply_eq_zero_of_off_two_site_agree_diff_at_x_not_pm1
              A hxy N hne h hσx hxlower hxraise
          rw [hzero]; simp

/-- **Global off-diagonal dressed Heisenberg non-positivity** (Tasaki §2.5
Theorem 2.2 input for general spin):

For real symmetric coupling `J` supported on bipartite bonds (`A x = A y
⟹ J x y = 0`) with `(J x y).re ≥ 0`, every off-diagonal entry of the
dressed Heisenberg matrix has non-positive real part:

    `Re (dressedHeisenbergS A J N σ' σ) ≤ 0` for all `σ' ≠ σ`.

This is the Phase B-γ γ-3 input to Perron–Frobenius. The proof
case-splits on the cardinality of the difference set
`D := {k | σ' k ≠ σ k}`:
- `|D| = 1`: `dressedHeisenbergS_apply_eq_zero_of_one_site_diff` → 0.
- `|D| = 2` with `D = {x, y}`:
  - `A x = A y`: bipartite-supported `J` forces both `J x y, J y x = 0`,
    so the two-site formula gives `dressed = 0`.
  - `A x ≠ A y`: apply the per-bond unified non-positivity
    (`dressedHeisenbergS_apply_re_nonpos_of_off_two_site_agree_bipartite`).
- `|D| ≥ 3`: `dressedHeisenbergS_apply_eq_zero_of_three_diff` → 0. -/
theorem dressedHeisenbergS_apply_re_nonpos_of_ne_bipartite
    (A : V → Bool) (N : ℕ)
    {J : V → V → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    {σ' σ : V → Fin (N + 1)} (hne : σ' ≠ σ) :
    (dressedHeisenbergS A J N σ' σ).re ≤ 0 := by
  classical
  let D := (Finset.univ : Finset V).filter (fun k => σ' k ≠ σ k)
  have hDne : D.Nonempty := by
    obtain ⟨z, hz⟩ := Function.ne_iff.mp hne
    exact ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz⟩⟩
  obtain ⟨x, hxD⟩ := hDne
  have hσx : σ' x ≠ σ x := (Finset.mem_filter.mp hxD).2
  by_cases hD1 : (D.erase x).Nonempty
  · -- |D| ≥ 2.
    obtain ⟨y, hyD⟩ := hD1
    have hxy : x ≠ y := (Finset.mem_erase.mp hyD).1.symm
    have hyD' : y ∈ D := (Finset.mem_erase.mp hyD).2
    have hσy : σ' y ≠ σ y := (Finset.mem_filter.mp hyD').2
    by_cases hD2 : ((D.erase x).erase y).Nonempty
    · -- |D| ≥ 3: three_diff vanishing.
      obtain ⟨z, hzD⟩ := hD2
      have hyz : y ≠ z := (Finset.mem_erase.mp hzD).1.symm
      have hzD' : z ∈ D.erase x := (Finset.mem_erase.mp hzD).2
      have hxz : x ≠ z := (Finset.mem_erase.mp hzD').1.symm
      have hσz : σ' z ≠ σ z :=
        (Finset.mem_filter.mp (Finset.mem_erase.mp hzD').2).2
      have hzero : dressedHeisenbergS A J N σ' σ = 0 :=
        dressedHeisenbergS_apply_eq_zero_of_three_diff A J N
          hxy hxz hyz hσx hσy hσz
      rw [hzero]; simp
    · -- |D| = 2: D = {x, y}. So σ' σ off-{x, y}-agree.
      have hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k := by
        intro k hkx hky
        by_contra hkne
        have hkD : k ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hkne⟩
        have hkD' : k ∈ D.erase x := Finset.mem_erase.mpr ⟨hkx, hkD⟩
        have hkD'' : k ∈ (D.erase x).erase y :=
          Finset.mem_erase.mpr ⟨hky, hkD'⟩
        exact hD2 ⟨k, hkD''⟩
      by_cases hAne : A x = A y
      · -- A x = A y: bipartite J forces (J x y) = (J y x) = 0.
        have hJxy : J x y = 0 := hJ_bipartite x y hAne
        have hJyx : J y x = 0 := hJ_bipartite y x hAne.symm
        have hzero : dressedHeisenbergS A J N σ' σ = 0 := by
          rw [dressedHeisenbergS_apply_of_off_two_site_agree A hxy N
            hne hagree]
          rw [hJxy, hJyx]
          ring
        rw [hzero]; simp
      · -- A x ≠ A y: apply the per-bond unified non-positivity.
        exact dressedHeisenbergS_apply_re_nonpos_of_off_two_site_agree_bipartite
          hxy N A hAne (hJ_real x y) (hJ_nn x y) (hJ_sym x y) hne hagree
  · -- |D| = 1: D = {x}. So σ' σ agree off {x}.
    have hagree : ∀ k, k ≠ x → σ' k = σ k := by
      intro k hkx
      by_contra hkne
      have hkD : k ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hkne⟩
      have hkD' : k ∈ D.erase x := Finset.mem_erase.mpr ⟨hkx, hkD⟩
      exact hD1 ⟨k, hkD'⟩
    have hzero : dressedHeisenbergS A J N σ' σ = 0 :=
      dressedHeisenbergS_apply_eq_zero_of_one_site_diff A J N hagree hσx
    rw [hzero]; simp


end LatticeSystem.Quantum
