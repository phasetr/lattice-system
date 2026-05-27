import LatticeSystem.Quantum.SpinS.SublatticeMagWeightComponent

/-!
# Sublattice magnetization-projection infrastructure

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3), option (a),
Route 5 brick 2a (see `.self-local/tex/3717-coupled-total-spin-lower-bound.tex`).

Basic algebraic facts about the pointwise sublattice-`A` magnetization projector
`sublatticeMagProjFn A M`:
* idempotence on its own magnetization subspace,
* annihilation of other magnetization subspaces,
* commutation with any operator that commutes with `Ŝ_A^(3)` (preserves the grading),
and hence Casimir-eigenvalue inheritance: the magnetization component of a sublattice
Casimir eigenvector is again a Casimir eigenvector at the same eigenvalue.  These feed
the bottom-component extraction of the coupled total-spin lower bound.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Projector idempotence**: on its own magnetization subspace the projector is the
identity. -/
theorem sublatticeMagProjFn_of_mem (A : Λ → Bool) (M : ℂ)
    {u : (Λ → Fin (N + 1)) → ℂ} (hu : u ∈ sublatticeMagSubspaceS A M) :
    sublatticeMagProjFn A M u = u := by
  funext σ
  unfold sublatticeMagProjFn
  by_cases h : sublatticeMagEigenvalueS A σ = M
  · rw [if_pos h]
  · rw [if_neg h]
    exact (sublatticeMagSubspaceS_apply_eq_zero_of_sublatticeMagEigenvalueS_ne A hu h).symm

/-- **Projector orthogonality**: the projector annihilates a different magnetization
subspace. -/
theorem sublatticeMagProjFn_of_mem_ne (A : Λ → Bool) {M M' : ℂ} (hne : M ≠ M')
    {u : (Λ → Fin (N + 1)) → ℂ} (hu : u ∈ sublatticeMagSubspaceS A M') :
    sublatticeMagProjFn A M u = 0 := by
  funext σ
  unfold sublatticeMagProjFn
  by_cases h : sublatticeMagEigenvalueS A σ = M
  · rw [if_pos h]
    exact sublatticeMagSubspaceS_apply_eq_zero_of_sublatticeMagEigenvalueS_ne A hu
      (by rw [h]; exact hne)
  · rw [if_neg h]; rfl

omit [DecidableEq Λ] in
/-- The projector distributes over finite sums. -/
theorem sublatticeMagProjFn_sum (A : Λ → Bool) (M : ℂ) {ι : Type*} (s : Finset ι)
    (f : ι → (Λ → Fin (N + 1)) → ℂ) :
    sublatticeMagProjFn A M (∑ i ∈ s, f i) = ∑ i ∈ s, sublatticeMagProjFn A M (f i) := by
  funext σ
  simp only [sublatticeMagProjFn, Finset.sum_apply]
  by_cases h : sublatticeMagEigenvalueS A σ = M <;> simp [h]

/-- **Projector commutes with grading-preserving operators**: if `T` commutes with
`Ŝ_A^(3)`, the magnetization projector commutes with `T`. -/
theorem sublatticeMagProjFn_mulVec_of_commute (A : Λ → Bool) (M : ℂ)
    (T : ManyBodyOpS Λ N) (hcomm : Commute (sublatticeSpinSOp3 N A) T)
    (u : (Λ → Fin (N + 1)) → ℂ) :
    sublatticeMagProjFn A M (T.mulVec u) = T.mulVec (sublatticeMagProjFn A M u) := by
  classical
  -- Decompose u over the magnetization levels.
  have hdecomp : u = ∑ k : Fin ((Finset.univ.filter (fun x : Λ => A x = true)).card * N + 1),
      sublatticeMagProjFn A
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2 -
          (k.val : ℂ)) u := (sum_sublatticeMagProjFn_eq A u).symm
  -- Apply T and the projector through the finite sum.
  conv_lhs => rw [hdecomp, Matrix.mulVec_sum, sublatticeMagProjFn_sum]
  conv_rhs => rw [hdecomp, sublatticeMagProjFn_sum, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  set Mk : ℂ := ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2 -
    (k.val : ℂ) with hMk
  -- The k-th component lies in level Mk; T preserves it.
  have hmemk : sublatticeMagProjFn A Mk u ∈ sublatticeMagSubspaceS A Mk :=
    sublatticeMagProjFn_mem_sublatticeMagSubspaceS A Mk u
  have hT : T.mulVec (sublatticeMagProjFn A Mk u) ∈ sublatticeMagSubspaceS A Mk :=
    mem_sublatticeMagSubspaceS_of_commute A Mk T hcomm hmemk
  by_cases hk : Mk = M
  · subst hk
    rw [sublatticeMagProjFn_of_mem A Mk hT, sublatticeMagProjFn_of_mem A Mk hmemk]
  · rw [sublatticeMagProjFn_of_mem_ne A (Ne.symm hk) hT,
      sublatticeMagProjFn_of_mem_ne A (Ne.symm hk) hmemk, Matrix.mulVec_zero]

/-- **Casimir inheritance for the sublattice-`A` projector**: the magnetization
component of an `(Ŝ_A)²`-eigenvector is again an `(Ŝ_A)²`-eigenvector at the same
eigenvalue. -/
theorem sublatticeMagProjFn_sublatticeSpinSquaredS (A : Λ → Bool) (M : ℂ)
    {α : ℂ} {w : (Λ → Fin (N + 1)) → ℂ}
    (hcas : (sublatticeSpinSquaredS N A).mulVec w = α • w) :
    (sublatticeSpinSquaredS N A).mulVec (sublatticeMagProjFn A M w) =
      α • sublatticeMagProjFn A M w := by
  rw [← sublatticeMagProjFn_mulVec_of_commute A M (sublatticeSpinSquaredS N A)
    (sublatticeSpinSquaredS_commute_sublatticeSpinSOp3 (Λ := Λ) (N := N) A).symm w,
    hcas, sublatticeMagProjFn_smul]

/-- **Complement-Casimir inheritance for the sublattice-`A` projector**: the
sublattice-`A` magnetization component of an `(Ŝ_¬A)²`-eigenvector is again an
`(Ŝ_¬A)²`-eigenvector at the same eigenvalue. -/
theorem sublatticeMagProjFn_sublatticeSpinSquaredS_complement (A : Λ → Bool) (M : ℂ)
    {β : ℂ} {w : (Λ → Fin (N + 1)) → ℂ}
    (hcas : (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec w = β • w) :
    (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec (sublatticeMagProjFn A M w) =
      β • sublatticeMagProjFn A M w := by
  -- `Commute (Ŝ_¬A)² (Ŝ_A^(3))` from the complement lemma at `¬A` (with `¬¬A = A`).
  have hcomm : Commute (sublatticeSpinSquaredS N (fun x => ! A x)) (sublatticeSpinSOp3 N A) := by
    have h := sublatticeSpinSquaredS_commute_sublatticeSpinSOp3_complement
      (Λ := Λ) (N := N) (fun x => ! A x)
    have hnotnot : (fun x => ! (! A x)) = A := by funext x; simp
    rwa [hnotnot] at h
  rw [← sublatticeMagProjFn_mulVec_of_commute A M (sublatticeSpinSquaredS N (fun x => ! A x))
    hcomm.symm w, hcas, sublatticeMagProjFn_smul]

end LatticeSystem.Quantum
