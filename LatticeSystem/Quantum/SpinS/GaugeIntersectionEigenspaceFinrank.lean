import LatticeSystem.Quantum.SpinS.GaugeEigenspaceFinrank

/-!
# Intersection eigenspace dimension is preserved under similarity that commutes with `Q`

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Generalises `matrix_similar_eigenspace_finrank_eq` (#3746 family) to intersections with a
second operator's eigenspace, provided the similarity `U` commutes with that operator `Q`:
`(eig H' μ ⊓ ker(Q=c))` and `(eig H μ ⊓ ker(Q=c))` have equal finrank when `H' = U⁻¹ H U`
and `QU = UQ`.

Used by (g.3) to transfer the dressed-`Ĥ'` per-parity-block `eig ⊓ ker(P=±1) ≤ 1` bound
(#3834) to the bare `Ĥ'`, via the diagonal Marshall similarity `Θ_A` (which commutes with the
diagonal magnetization-parity `P`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Intersection eigenspace dimension is a similarity invariant when `Q` commutes with `U`**:
if `U * Uinv = 1`, `Uinv * U = 1`, `H' = Uinv * H * U`, and `Q * U = U * Q`, then for every
`μ, c` the intersected eigenspaces `eig H' μ ⊓ ker(Q=c)` and `eig H μ ⊓ ker(Q=c)` have
equal finrank.

(`Q` itself need not commute with `H` or `H'`; only with the similarity `U` and `Uinv`.) -/
theorem matrix_similar_eigenspace_inter_finrank_eq
    {U Uinv H H' Q : Matrix n n ℂ}
    (hUU : U * Uinv = 1) (hUinvU : Uinv * U = 1)
    (hsim : H' = Uinv * H * U) (hQU : Q * U = U * Q) (μ c : ℂ) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin' H') μ ⊓
        End.eigenspace (Matrix.toLin' Q) c) =
      finrank ℂ ↥(End.eigenspace (Matrix.toLin' H) μ ⊓
        End.eigenspace (Matrix.toLin' Q) c) := by
  set e : (n → ℂ) ≃ₗ[ℂ] (n → ℂ) := Matrix.toLin'OfInv hUinvU hUU with he
  have he_v : ∀ v, e v = U *ᵥ v := fun v => by rw [he]; exact Matrix.toLin'_apply U v
  have he_symm : ∀ w, e.symm w = Uinv *ᵥ w := fun w => by rw [he]; exact Matrix.toLin'_apply Uinv w
  -- `Q` commutes with `Uinv` too: derive from `Q * U = U * Q` by left/right multiplication.
  have hQUinv : Q * Uinv = Uinv * Q := by
    have h1 : Uinv * Q * U = Uinv * (U * Q) := by rw [mul_assoc, hQU]
    have h2 : Uinv * (U * Q) = Q := by rw [← mul_assoc, hUinvU, one_mul]
    have h3 : Uinv * Q * U = Q := by rw [h1, h2]
    have h4 := congrArg (fun x => x * Uinv) h3
    simp only at h4
    rw [mul_assoc, hUU, mul_one] at h4
    exact h4.symm
  have hmap : (End.eigenspace (Matrix.toLin' H') μ ⊓
        End.eigenspace (Matrix.toLin' Q) c).map e.toLinearMap =
      End.eigenspace (Matrix.toLin' H) μ ⊓ End.eigenspace (Matrix.toLin' Q) c := by
    ext w
    simp only [Submodule.mem_map, Submodule.mem_inf, End.mem_eigenspace_iff,
      Matrix.toLin'_apply, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨v, ⟨hv_eig, hv_ker⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · -- Eigenspace transfer (same as base lemma).
        rw [hsim] at hv_eig
        rw [he_v, Matrix.mulVec_mulVec]
        have := congrArg (fun x => U *ᵥ x) hv_eig
        simp only [Matrix.mulVec_mulVec, Matrix.mulVec_smul] at this
        rw [show U * (Uinv * H * U) = H * U by
          rw [← mul_assoc, ← mul_assoc, hUU, one_mul]] at this
        exact this
      · -- Ker(Q=c) transfer using QU = UQ:
        -- Q *ᵥ (U *ᵥ v) = (Q*U) *ᵥ v = (U*Q) *ᵥ v = U *ᵥ (Q *ᵥ v) = U *ᵥ (c • v) = c • (U *ᵥ v).
        rw [he_v, Matrix.mulVec_mulVec, hQU, ← Matrix.mulVec_mulVec, hv_ker,
            Matrix.mulVec_smul]
    · rintro ⟨hw_eig, hw_ker⟩
      refine ⟨e.symm w, ⟨?_, ?_⟩, by
        rw [he_v, he_symm, Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]⟩
      · -- Eigenspace transfer back.
        have key : (Uinv * H * U) *ᵥ (Uinv *ᵥ w) = Uinv *ᵥ (H *ᵥ w) := by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
          congr 2
          rw [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
        rw [hsim, he_symm, key, hw_eig, Matrix.mulVec_smul]
      · -- Ker(Q=c) transfer back using Q * Uinv = Uinv * Q (hQUinv).
        rw [he_symm, Matrix.mulVec_mulVec, hQUinv, ← Matrix.mulVec_mulVec, hw_ker,
            Matrix.mulVec_smul]
  rw [LinearEquiv.finrank_eq (e.submoduleMap (End.eigenspace (Matrix.toLin' H') μ ⊓
    End.eigenspace (Matrix.toLin' Q) c)), hmap]

end LatticeSystem.Quantum
