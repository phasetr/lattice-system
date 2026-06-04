import LatticeSystem.Fermion.JordanWigner.Number

/-!
# Generic move-through lemmas for operator products on the Fock vacuum

Model-agnostic lemmas for acting with an operator on an ordered product
`(∏_{p∈ps} A p) |vac⟩` of operators applied to the Jordan–Wigner vacuum.  They are
the combinatorial core of the flat-band ground-state arguments (Tasaki §11.3.1)
and apply verbatim to any model built from creation operators on the vacuum
(Mielke's flat band, the general theory of §11.3.4, …), so they live here rather
than in a model-specific file.

* `anticomm_listProd_mulVec_vacuum`: if `B` kills the vacuum and anticommutes with
  every factor, then `B · (∏ A) |vac⟩ = 0`.
* `charge_listProd_mulVec_vacuum`: if `Q` kills the vacuum and each factor raises
  its charge by one, then `Q · (∏ A) |vac⟩ = (#factors) · (∏ A) |vac⟩`.
* `dualAnnihilation_peel_listProd_mulVec_vacuum`: a dual annihilation removes the
  leading creation, `c · (A · ∏ B) |vac⟩ = (∏ B) |vac⟩`.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- **Anticommutation move-through.** If `B` annihilates the vacuum and
anticommutes with each factor `A p`, then `B · (∏_p A p) |vac⟩ = 0` (anticommute
`B` rightward through the product, then `B |vac⟩ = 0`). -/
theorem anticomm_listProd_mulVec_vacuum {M : ℕ} {ι : Type*}
    (B : ManyBodyOp (Fin (M + 1))) (A : ι → ManyBodyOp (Fin (M + 1))) (ps : List ι)
    (hBvac : B.mulVec (fermionMultiVacuum M) = 0)
    (hanti : ∀ p ∈ ps, B * A p + A p * B = 0) :
    (B * (ps.map A).prod).mulVec (fermionMultiVacuum M) = 0 := by
  induction ps with
  | nil => simpa using hBvac
  | cons p ps ih =>
    rw [List.map_cons, List.prod_cons, ← Matrix.mul_assoc,
      eq_neg_of_add_eq_zero_left (hanti p (by simp)),
      Matrix.neg_mul, Matrix.mul_assoc, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec,
      ih (fun q hq => hanti q (by simp [hq])), Matrix.mulVec_zero, neg_zero]

/-- **Charge move-through.** If `Q` annihilates the vacuum and each factor `A p`
raises the `Q`-charge by one (`Q · A p = A p · Q + A p`), then `Q` acts on
`(∏_p A p) |vac⟩` with eigenvalue equal to the number of factors. -/
theorem charge_listProd_mulVec_vacuum {M : ℕ} {ι : Type*}
    (Q : ManyBodyOp (Fin (M + 1))) (A : ι → ManyBodyOp (Fin (M + 1))) (ps : List ι)
    (hQvac : Q.mulVec (fermionMultiVacuum M) = 0)
    (hcomm : ∀ p ∈ ps, Q * A p = A p * Q + A p) :
    (Q * (ps.map A).prod).mulVec (fermionMultiVacuum M) =
      (ps.length : ℂ) • ((ps.map A).prod).mulVec (fermionMultiVacuum M) := by
  induction ps with
  | nil => simpa using hQvac
  | cons p ps ih =>
    have hih := ih (fun q hq => hcomm q (by simp [hq]))
    rw [List.map_cons, List.prod_cons, ← Matrix.mul_assoc, hcomm p (by simp),
      Matrix.add_mul, Matrix.mul_assoc, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hih,
      Matrix.mulVec_smul, List.length_cons, Nat.cast_succ, ← Matrix.mulVec_mulVec,
      add_smul, one_smul]

/-- **Dual-annihilation peel.** If `c` annihilates the vacuum, anticommutes to `1`
with `A` (`c·A + A·c = 1`), and anticommutes to `0` with every factor of the
ordered product `(qs.map B).prod`, then `c` removes the leading factor `A`:
`c · (A · ∏ B) |vac⟩ = (∏ B) |vac⟩`. -/
theorem dualAnnihilation_peel_listProd_mulVec_vacuum {M : ℕ} {ι : Type*}
    (c A : ManyBodyOp (Fin (M + 1))) (B : ι → ManyBodyOp (Fin (M + 1))) (qs : List ι)
    (hcvac : c.mulVec (fermionMultiVacuum M) = 0)
    (hc1 : c * A + A * c = 1)
    (hc0 : ∀ q ∈ qs, c * B q + B q * c = 0) :
    (c * (A * (qs.map B).prod)).mulVec (fermionMultiVacuum M) =
      ((qs.map B).prod).mulVec (fermionMultiVacuum M) := by
  have hcA : c * A = 1 - A * c := by rw [eq_sub_iff_add_eq]; exact hc1
  have hPvac0 : (c * (qs.map B).prod).mulVec (fermionMultiVacuum M) = 0 :=
    anticomm_listProd_mulVec_vacuum c B qs hcvac hc0
  rw [← Matrix.mul_assoc, hcA, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hPvac0, Matrix.mulVec_zero, sub_zero]

end LatticeSystem.Fermion
