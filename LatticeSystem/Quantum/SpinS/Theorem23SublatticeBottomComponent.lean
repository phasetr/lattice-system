import LatticeSystem.Quantum.SpinS.Theorem23SublatticeMagProjInfra
import LatticeSystem.Quantum.SpinS.SublatticeMagShift
import LatticeSystem.Quantum.SpinS.SublatticeSpinLadderDef
import LatticeSystem.Quantum.SpinS.JointLadderIterateSublatticeMag

/-!
# The bottom sublattice-`A` magnetization component is `Ŝ_A^-`-killed

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3), option (a),
Route 5 brick 2b (see `.self-local/tex/3717-coupled-total-spin-lower-bound.tex`).

For a total lowest-weight vector `w` (`Ŝ⁻_tot w = 0`, total magnetization `m`,
simultaneous sublattice-Casimir eigenvector at `α, β`), the **minimal-`A`-magnetization
nonzero component** `v* := sublatticeMagProjFn A p_min w` is `Ŝ_A^-`-killed.  Indeed
projecting `Ŝ⁻_tot w = Ŝ_A^- w + Ŝ_¬A^- w = 0` onto the magnetization level just below
`p_min`: the `Ŝ_A^-` part lands there only from the `p_min` component (giving
`Ŝ_A^- v*`), while the `Ŝ_¬A^-` part preserves `A`-magnetization and only sees the
already-vanishing `p_min−1` component.  Hence `Ŝ_A^- v* = 0`, and `v*` inherits the
two sublattice Casimir eigenvalues (`Theorem23SublatticeMagProjInfra`) and the total
magnetization `m` (so its `Ŝ_¬A^(3)` eigenvalue is `m − p_min`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Bottom-component extraction**: a total lowest-weight vector `w` in the joint
sublattice-Casimir eigenspace yields a non-zero `Ŝ_A^-`-killed simultaneous weight
vector `v` with `Ŝ_A^(3) v = p v`, `Ŝ_¬A^(3) v = (m−p) v` and the inherited Casimir
eigenvalues `α, β`. -/
theorem exists_sublattice_A_lowestWeight_component (A : Λ → Bool)
    {m α β : ℂ} {w : (Λ → Fin (N + 1)) → ℂ} (hw_ne : w ≠ 0)
    (hztot : (totalSpinSOp3 Λ N).mulVec w = m • w)
    (hker : (totalSpinSOpMinus Λ N).mulVec w = 0)
    (hcasA : (sublatticeSpinSquaredS N A).mulVec w = α • w)
    (hcasB : (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec w = β • w) :
    ∃ (p : ℂ) (v : (Λ → Fin (N + 1)) → ℂ), v ≠ 0 ∧
      (sublatticeSpinSOp3 N A).mulVec v = p • v ∧
      (sublatticeSpinSOp3 N (fun x => ! A x)).mulVec v = (m - p) • v ∧
      (sublatticeSpinSOpMinus N A).mulVec v = 0 ∧
      (sublatticeSpinSquaredS N A).mulVec v = α • v ∧
      (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec v = β • v := by
  classical
  set sA : ℂ := ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2
    with hsA
  set K : ℕ := (Finset.univ.filter (fun x : Λ => A x = true)).card * N with hK
  -- The magnetization-level components.
  set f : Fin (K + 1) → (Λ → Fin (N + 1)) → ℂ :=
    fun k => sublatticeMagProjFn A (sA - (k.val : ℂ)) w with hf
  have hdecomp : (∑ k, f k) = w := sum_sublatticeMagProjFn_eq A w
  -- Each component lies in its magnetization level.
  have hf_mem : ∀ k, f k ∈ sublatticeMagSubspaceS A (sA - (k.val : ℂ)) := fun k =>
    sublatticeMagProjFn_mem_sublatticeMagSubspaceS A _ w
  -- The support of nonzero components is nonempty (else w = 0).
  have hsupp_ne : (Finset.univ.filter (fun k => f k ≠ 0)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    apply hw_ne
    rw [← hdecomp]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    simpa using h (Finset.mem_univ k)
  set k₀ := (Finset.univ.filter (fun k => f k ≠ 0)).max' hsupp_ne with hk₀
  have hk₀_ne : f k₀ ≠ 0 := by
    have := (Finset.univ.filter (fun k => f k ≠ 0)).max'_mem hsupp_ne
    rw [Finset.mem_filter] at this
    exact this.2
  have hk₀_max : ∀ k, k₀ < k → f k = 0 := by
    intro k hlt
    by_contra hne
    have hmem : k ∈ Finset.univ.filter (fun k => f k ≠ 0) := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hne⟩
    exact absurd ((Finset.univ.filter (fun k => f k ≠ 0)).le_max' k hmem) (not_le.mpr hlt)
  -- Commute facts for inheriting the total Sz and Casimirs through the projection.
  have hcomm_tot : Commute (sublatticeSpinSOp3 N A) (totalSpinSOp3 Λ N) := by
    rw [totalSpinSOp3_eq_sublattice_sum (N := N) A]
    exact (Commute.refl _).add_right (sublatticeSpinSOp3_cross_commute (N := N) A)
  refine ⟨sA - (k₀.val : ℂ), f k₀, hk₀_ne, ?_, ?_, ?_, ?_, ?_⟩
  · -- Ŝ_A^(3) (f k₀) = (sA − k₀) • (f k₀): f k₀ ∈ its A-mag level.
    exact (mem_sublatticeMagSubspaceS_iff A _ _).mp (hf_mem k₀)
  · -- Ŝ_¬A^(3) (f k₀) = (m − (sA − k₀)) • (f k₀): total Sz = m, minus A-Sz.
    have htot_inherit : (totalSpinSOp3 Λ N).mulVec (f k₀) = m • f k₀ := by
      rw [hf, ← sublatticeMagProjFn_mulVec_of_commute A _ (totalSpinSOp3 Λ N) hcomm_tot w,
        hztot, sublatticeMagProjFn_smul]
    have hA3 : (sublatticeSpinSOp3 N A).mulVec (f k₀) = (sA - (k₀.val : ℂ)) • f k₀ :=
      (mem_sublatticeMagSubspaceS_iff A _ _).mp (hf_mem k₀)
    have hsplit : (totalSpinSOp3 Λ N).mulVec (f k₀) =
        (sublatticeSpinSOp3 N A).mulVec (f k₀) +
          (sublatticeSpinSOp3 N (fun x => ! A x)).mulVec (f k₀) := by
      rw [totalSpinSOp3_eq_sublattice_sum (N := N) A, Matrix.add_mulVec]
    rw [htot_inherit, hA3] at hsplit
    have : (sublatticeSpinSOp3 N (fun x => ! A x)).mulVec (f k₀) =
        m • f k₀ - (sA - (k₀.val : ℂ)) • f k₀ := by
      rw [hsplit]; abel
    rw [this, ← sub_smul]
  · -- Ŝ_A^- (f k₀) = 0.
    -- Project Ŝ⁻_tot w = 0 onto the level below k₀.
    set L₁ : ℂ := (sA - (k₀.val : ℂ)) - 1 with hL₁
    have hminus_split : (totalSpinSOpMinus Λ N).mulVec w =
        (sublatticeSpinSOpMinus N A).mulVec w +
          (sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec w := by
      rw [totalSpinSOpMinus_eq_sublattice_sum (N := N) A, Matrix.add_mulVec]
    have hproj0 : sublatticeMagProjFn A L₁ ((totalSpinSOpMinus Λ N).mulVec w) = 0 := by
      rw [hker]; funext σ; simp [sublatticeMagProjFn]
    rw [hminus_split, sublatticeMagProjFn_add] at hproj0
    -- The Ŝ_A^- contribution equals Ŝ_A^- (f k₀).
    have hA_term : sublatticeMagProjFn A L₁ ((sublatticeSpinSOpMinus N A).mulVec w) =
        (sublatticeSpinSOpMinus N A).mulVec (f k₀) := by
      conv_lhs => rw [← hdecomp, Matrix.mulVec_sum, sublatticeMagProjFn_sum]
      rw [Finset.sum_eq_single k₀]
      · -- the k₀ term: Ŝ_A^- (f k₀) ∈ level L₁, projector is identity.
        exact sublatticeMagProjFn_of_mem A L₁
          (sublatticeSpinSOpMinus_mulVec_mem_sublatticeMagSubspaceS_of_mem A (hf_mem k₀))
      · -- other terms vanish: Ŝ_A^- (f k) ∈ level (sA − k − 1) ≠ L₁ for k ≠ k₀.
        intro k _ hkne
        refine sublatticeMagProjFn_of_mem_ne A ?_
          (sublatticeSpinSOpMinus_mulVec_mem_sublatticeMagSubspaceS_of_mem A (hf_mem k))
        rw [hL₁]
        intro hcontra
        apply hkne
        exact Fin.ext (by exact_mod_cast (sub_right_inj.mp (sub_left_inj.mp hcontra)).symm)
      · intro h; exact absurd (Finset.mem_univ k₀) h
    -- The Ŝ_¬A^- contribution vanishes termwise.
    have hB_term : sublatticeMagProjFn A L₁ ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec w) = 0 := by
      conv_lhs => rw [← hdecomp, Matrix.mulVec_sum, sublatticeMagProjFn_sum]
      refine Finset.sum_eq_zero (fun k _ => ?_)
      -- Ŝ_¬A^- (f k) ∈ A-mag level (sA − k) [preserves A-mag].
      have hmemBk : (sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec (f k) ∈
          sublatticeMagSubspaceS A (sA - (k.val : ℂ)) :=
        mem_sublatticeMagSubspaceS_of_commute A _ (sublatticeSpinSOpMinus N (fun x => ! A x))
          (sublatticeSpinSOp3_cross_commute_sublatticeSpinSOpMinus A) (hf_mem k)
      by_cases hk : sA - (k.val : ℂ) = L₁
      · -- level matches L₁ ⟹ k = k₀ + 1 > k₀ ⟹ f k = 0.
        have hkval : (k.val : ℂ) = (k₀.val : ℂ) + 1 := by
          rw [hL₁] at hk; linear_combination -hk
        have hlt : k₀ < k := by
          rw [Fin.lt_def]
          have : (k.val : ℤ) = (k₀.val : ℤ) + 1 := by exact_mod_cast hkval
          omega
        have hfk0 : f k = 0 := hk₀_max k hlt
        rw [hfk0, Matrix.mulVec_zero]
        funext σ; simp [sublatticeMagProjFn]
      · exact sublatticeMagProjFn_of_mem_ne A (Ne.symm hk) hmemBk
    rw [hA_term, hB_term, add_zero] at hproj0
    exact hproj0
  · -- (Ŝ_A)² inheritance.
    exact sublatticeMagProjFn_sublatticeSpinSquaredS A _ hcasA
  · -- (Ŝ_¬A)² inheritance.
    exact sublatticeMagProjFn_sublatticeSpinSquaredS_complement A _ hcasB

end LatticeSystem.Quantum
