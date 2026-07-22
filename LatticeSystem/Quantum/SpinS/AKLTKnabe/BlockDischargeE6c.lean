import LatticeSystem.Quantum.SpinS.AKLTKnabe.BlockDischargeE6b

/-!
# Gate E6 (part c): the block bounds on the sectors

Part c of the Gate E6 landing (Issue #5094, Tasaki §7.1.4).  Section 6: the block
bounds `blockBound*E6` assembled from the sum-of-squares certificates.  Imports
`BlockDischargeE6b`.
-/

namespace LatticeSystem.Quantum.AKLTSl2BlockDischargeE6

open LatticeSystem.Quantum
open LatticeSystem.Quantum.AKLTSl2SubmoduleProbeE2
open LatticeSystem.Quantum.AKLTSl2LadderSectorsE3
open LatticeSystem.Quantum.AKLTSl2WindowReductionE4
open LatticeSystem.Quantum.AKLTSl2HighestWeightBoundE5
open LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential
open scoped ComplexOrder

/-! ## 6. The block bounds on the sectors -/

/-- **A nonzero entry makes the total squared length of a complex tuple positive.**  Stated
once for an arbitrary finite tuple, so that the four sector-sized statements below are thin
adapters instead of quadratically many explicit nonnegativity chains. -/
private theorem posSumFinE6 {n : ℕ} (a : Fin n → ℂ) (i : Fin n) (h : a i ≠ 0) :
    (0 : ℝ) < (∑ j, (a j).re ^ 2) + ∑ j, (a j).im ^ 2 := by
  have hre : (a i).re ^ 2 ≤ ∑ j, (a j).re ^ 2 :=
    Finset.single_le_sum (f := fun j => (a j).re ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have him : (a i).im ^ 2 ≤ ∑ j, (a j).im ^ 2 :=
    Finset.single_le_sum (f := fun j => (a j).im ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  linarith [sqAddSqPosOfNeZeroE6 (a i) h]

/-- **A nonzero component makes the total squared length of a 4-tuple positive.**  A thin
adapter of `posSumFinE6` to the 4 components of the sector. -/
private theorem posSum4E6 (a0 a1 a2 a3 : ℂ)
    (hne : a0 ≠ 0 ∨ a1 ≠ 0 ∨ a2 ≠ 0 ∨ a3 ≠ 0) :
    (0 : ℝ) < (a0.re ^ 2 + a1.re ^ 2 + a2.re ^ 2 + a3.re ^ 2)
      + (a0.im ^ 2 + a1.im ^ 2 + a2.im ^ 2 + a3.im ^ 2) := by
  have key : ∀ i : Fin 4, ![a0, a1, a2, a3] i ≠ 0 →
      (0 : ℝ) < (a0.re ^ 2 + a1.re ^ 2 + a2.re ^ 2 + a3.re ^ 2)
        + (a0.im ^ 2 + a1.im ^ 2 + a2.im ^ 2 + a3.im ^ 2) := by
    intro i hi
    have hkey := posSumFinE6 ![a0, a1, a2, a3] i hi
    simp [Fin.sum_univ_succ] at hkey
    linarith
  rcases hne with h | h | h | h
  · exact key 0 h
  · exact key 1 h
  · exact key 2 h
  · exact key 3 h

/-- **A nonzero component makes the total squared length of a 10-tuple positive.**  A thin
adapter of `posSumFinE6` to the 10 components of the sector. -/
private theorem posSum10E6 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : ℂ)
    (hne : a0 ≠ 0 ∨ a1 ≠ 0 ∨ a2 ≠ 0 ∨ a3 ≠ 0 ∨ a4 ≠ 0 ∨ a5 ≠ 0 ∨ a6 ≠ 0 ∨ a7 ≠ 0 ∨ a8 ≠ 0 ∨
      a9 ≠ 0) :
    (0 : ℝ) < (a0.re ^ 2 + a1.re ^ 2 + a2.re ^ 2 + a3.re ^ 2 + a4.re ^ 2 + a5.re ^ 2 +
      a6.re ^ 2 + a7.re ^ 2 + a8.re ^ 2 + a9.re ^ 2)
      + (a0.im ^ 2 + a1.im ^ 2 + a2.im ^ 2 + a3.im ^ 2 + a4.im ^ 2 + a5.im ^ 2 + a6.im ^ 2 +
        a7.im ^ 2 + a8.im ^ 2 + a9.im ^ 2) := by
  have key : ∀ i : Fin 10, ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] i ≠ 0 →
      (0 : ℝ) < (a0.re ^ 2 + a1.re ^ 2 + a2.re ^ 2 + a3.re ^ 2 + a4.re ^ 2 + a5.re ^ 2 +
        a6.re ^ 2 + a7.re ^ 2 + a8.re ^ 2 + a9.re ^ 2)
        + (a0.im ^ 2 + a1.im ^ 2 + a2.im ^ 2 + a3.im ^ 2 + a4.im ^ 2 + a5.im ^ 2 + a6.im ^ 2 +
          a7.im ^ 2 + a8.im ^ 2 + a9.im ^ 2) := by
    intro i hi
    have hkey := posSumFinE6 ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] i hi
    simp [Fin.sum_univ_succ] at hkey
    linarith
  rcases hne with h | h | h | h | h | h | h | h | h | h
  · exact key 0 h
  · exact key 1 h
  · exact key 2 h
  · exact key 3 h
  · exact key 4 h
  · exact key 5 h
  · exact key 6 h
  · exact key 7 h
  · exact key 8 h
  · exact key 9 h

/-- **A nonzero component makes the total squared length of a 16-tuple positive.**  A thin
adapter of `posSumFinE6` to the 16 components of the sector. -/
private theorem posSum16E6 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : ℂ)
    (hne : a0 ≠ 0 ∨ a1 ≠ 0 ∨ a2 ≠ 0 ∨ a3 ≠ 0 ∨ a4 ≠ 0 ∨ a5 ≠ 0 ∨ a6 ≠ 0 ∨ a7 ≠ 0 ∨ a8 ≠ 0 ∨
      a9 ≠ 0 ∨ a10 ≠ 0 ∨ a11 ≠ 0 ∨ a12 ≠ 0 ∨ a13 ≠ 0 ∨ a14 ≠ 0 ∨ a15 ≠ 0) :
    (0 : ℝ) < (a0.re ^ 2 + a1.re ^ 2 + a2.re ^ 2 + a3.re ^ 2 + a4.re ^ 2 + a5.re ^ 2 +
      a6.re ^ 2 + a7.re ^ 2 + a8.re ^ 2 + a9.re ^ 2 + a10.re ^ 2 + a11.re ^ 2 + a12.re ^ 2 +
      a13.re ^ 2 + a14.re ^ 2 + a15.re ^ 2)
      + (a0.im ^ 2 + a1.im ^ 2 + a2.im ^ 2 + a3.im ^ 2 + a4.im ^ 2 + a5.im ^ 2 + a6.im ^ 2 +
        a7.im ^ 2 + a8.im ^ 2 + a9.im ^ 2 + a10.im ^ 2 + a11.im ^ 2 + a12.im ^ 2 + a13.im ^ 2 +
        a14.im ^ 2 + a15.im ^ 2) := by
  have key : ∀ i : Fin 16,
      ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] i ≠ 0 →
      (0 : ℝ) < (a0.re ^ 2 + a1.re ^ 2 + a2.re ^ 2 + a3.re ^ 2 + a4.re ^ 2 + a5.re ^ 2 +
        a6.re ^ 2 + a7.re ^ 2 + a8.re ^ 2 + a9.re ^ 2 + a10.re ^ 2 + a11.re ^ 2 + a12.re ^ 2 +
        a13.re ^ 2 + a14.re ^ 2 + a15.re ^ 2)
        + (a0.im ^ 2 + a1.im ^ 2 + a2.im ^ 2 + a3.im ^ 2 + a4.im ^ 2 + a5.im ^ 2 + a6.im ^ 2 +
          a7.im ^ 2 + a8.im ^ 2 + a9.im ^ 2 + a10.im ^ 2 + a11.im ^ 2 + a12.im ^ 2 + a13.im ^ 2 +
          a14.im ^ 2 + a15.im ^ 2) := by
    intro i hi
    have hkey := posSumFinE6
      ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] i hi
    simp [Fin.sum_univ_succ] at hkey
    linarith
  rcases hne with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact key 0 h
  · exact key 1 h
  · exact key 2 h
  · exact key 3 h
  · exact key 4 h
  · exact key 5 h
  · exact key 6 h
  · exact key 7 h
  · exact key 8 h
  · exact key 9 h
  · exact key 10 h
  · exact key 11 h
  · exact key 12 h
  · exact key 13 h
  · exact key 14 h
  · exact key 15 h

/-- **A nonzero component makes the total squared length of a 19-tuple positive.**  A thin
adapter of `posSumFinE6` to the 19 components of the sector. -/
private theorem posSum19E6 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17
    a18 : ℂ)
    (hne : a0 ≠ 0 ∨ a1 ≠ 0 ∨ a2 ≠ 0 ∨ a3 ≠ 0 ∨ a4 ≠ 0 ∨ a5 ≠ 0 ∨ a6 ≠ 0 ∨ a7 ≠ 0 ∨ a8 ≠ 0 ∨
      a9 ≠ 0 ∨ a10 ≠ 0 ∨ a11 ≠ 0 ∨ a12 ≠ 0 ∨ a13 ≠ 0 ∨ a14 ≠ 0 ∨ a15 ≠ 0 ∨ a16 ≠ 0 ∨ a17 ≠ 0 ∨
      a18 ≠ 0) :
    (0 : ℝ) < (a0.re ^ 2 + a1.re ^ 2 + a2.re ^ 2 + a3.re ^ 2 + a4.re ^ 2 + a5.re ^ 2 +
      a6.re ^ 2 + a7.re ^ 2 + a8.re ^ 2 + a9.re ^ 2 + a10.re ^ 2 + a11.re ^ 2 + a12.re ^ 2 +
      a13.re ^ 2 + a14.re ^ 2 + a15.re ^ 2 + a16.re ^ 2 + a17.re ^ 2 + a18.re ^ 2)
      + (a0.im ^ 2 + a1.im ^ 2 + a2.im ^ 2 + a3.im ^ 2 + a4.im ^ 2 + a5.im ^ 2 + a6.im ^ 2 +
        a7.im ^ 2 + a8.im ^ 2 + a9.im ^ 2 + a10.im ^ 2 + a11.im ^ 2 + a12.im ^ 2 + a13.im ^ 2 +
        a14.im ^ 2 + a15.im ^ 2 + a16.im ^ 2 + a17.im ^ 2 + a18.im ^ 2) := by
  have key : ∀ i : Fin 19,
      ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18] i ≠ 0
          →
      (0 : ℝ) < (a0.re ^ 2 + a1.re ^ 2 + a2.re ^ 2 + a3.re ^ 2 + a4.re ^ 2 + a5.re ^ 2 +
        a6.re ^ 2 + a7.re ^ 2 + a8.re ^ 2 + a9.re ^ 2 + a10.re ^ 2 + a11.re ^ 2 + a12.re ^ 2 +
        a13.re ^ 2 + a14.re ^ 2 + a15.re ^ 2 + a16.re ^ 2 + a17.re ^ 2 + a18.re ^ 2)
        + (a0.im ^ 2 + a1.im ^ 2 + a2.im ^ 2 + a3.im ^ 2 + a4.im ^ 2 + a5.im ^ 2 + a6.im ^ 2 +
          a7.im ^ 2 + a8.im ^ 2 + a9.im ^ 2 + a10.im ^ 2 + a11.im ^ 2 + a12.im ^ 2 + a13.im ^ 2 +
          a14.im ^ 2 + a15.im ^ 2 + a16.im ^ 2 + a17.im ^ 2 + a18.im ^ 2) := by
    intro i hi
    have hkey := posSumFinE6
      ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18] i hi
    simp [Fin.sum_univ_succ] at hkey
    linarith
  rcases hne with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact key 0 h
  · exact key 1 h
  · exact key 2 h
  · exact key 3 h
  · exact key 4 h
  · exact key 5 h
  · exact key 6 h
  · exact key 7 h
  · exact key 8 h
  · exact key 9 h
  · exact key 10 h
  · exact key 11 h
  · exact key 12 h
  · exact key 13 h
  · exact key 14 h
  · exact key 15 h
  · exact key 16 h
  · exact key 17 h
  · exact key 18 h

/-- **From the two real quadratic bounds to the eigenvalue bound.**  If the quadratic form
dominates `(2/5)` on both the real and the imaginary component vectors, and at least one of them
is nonzero, then `μ ≥ 2/5`. -/
private theorem leOfQuadE6 (μ X Y : ℝ) (hx : 2 / 5 * X ≤ μ * X) (hy : 2 / 5 * Y ≤ μ * Y)
    (hpos : 0 < X + Y) : 2 / 5 ≤ μ := by
  by_contra hc
  push Not at hc
  nlinarith [hx, hy, hpos, mul_pos (sub_pos.mpr hc) hpos]

/-- **From the two second-order bounds to the Knabe block bound.**  If the Knabe quadratic
`t = μ² − (2/5) μ` has nonnegative product with both squared lengths, at least one of which is
positive, then `t ≥ 0`. -/
private theorem nonnegOfQuadE6 (t X Y : ℝ) (hx : 0 ≤ t * X) (hy : 0 ≤ t * Y)
    (hpos : 0 < X + Y) : 0 ≤ t := by
  by_contra hc
  push Not at hc
  nlinarith [hx, hy, hpos, mul_pos (neg_pos.mpr hc) hpos]

/-- **The Knabe block bound carried by the whole sector `V_1`.**  A nonzero vector of the
sector satisfying the eigenvalue equations of `ĥ|V_1` for a real `μ` forces `μ ≥ 2/5`.
The highest-weight condition `Ŝ⁺_tot u = 0` is *not* used. -/
theorem blockBoundV1E6 (μ : ℝ) (a0 a1 a2 a3 : ℂ)
    (e0 : ((5 / 2 : ℝ) : ℂ) * a0 + ((1 / 2 : ℝ) : ℂ) * a1
      = ((μ : ℝ) : ℂ) * a0)
    (e1 : ((1 / 2 : ℝ) : ℂ) * a0 + ((2 : ℝ) : ℂ) * a1 + ((1 / 2 : ℝ) : ℂ) * a2
      = ((μ : ℝ) : ℂ) * a1)
    (e2 : ((1 / 2 : ℝ) : ℂ) * a1 + ((2 : ℝ) : ℂ) * a2 + ((1 / 2 : ℝ) : ℂ) * a3
      = ((μ : ℝ) : ℂ) * a2)
    (e3 : ((1 / 2 : ℝ) : ℂ) * a2 + ((5 / 2 : ℝ) : ℂ) * a3
      = ((μ : ℝ) : ℂ) * a3)
    (hne : a0 ≠ 0 ∨ a1 ≠ 0 ∨ a2 ≠ 0 ∨ a3 ≠ 0) :
    2 / 5 ≤ μ := by
  have r0 := row2PartE6 Complex.re Complex.add_re ofRealMulReE6 e0
  have s0 := row2PartE6 Complex.im Complex.add_im ofRealMulImE6 e0
  have r1 := row3PartE6 Complex.re Complex.add_re ofRealMulReE6 e1
  have s1 := row3PartE6 Complex.im Complex.add_im ofRealMulImE6 e1
  have r2 := row3PartE6 Complex.re Complex.add_re ofRealMulReE6 e2
  have s2 := row3PartE6 Complex.im Complex.add_im ofRealMulImE6 e2
  have r3 := row2PartE6 Complex.re Complex.add_re ofRealMulReE6 e3
  have s3 := row2PartE6 Complex.im Complex.add_im ofRealMulImE6 e3
  have hx := quadV1E6 μ a0.re a1.re a2.re a3.re r0 r1 r2 r3
  have hy := quadV1E6 μ a0.im a1.im a2.im a3.im s0 s1 s2 s3
  exact leOfQuadE6 μ _ _ hx hy (posSum4E6 a0 a1 a2 a3 hne)

/-- **The Knabe block bound carried by the whole sector `V_2`.**  A nonzero vector of the
sector satisfying the eigenvalue equations of `ĥ|V_2` for a real `μ` forces `μ ≥ 2/5`.
The highest-weight condition `Ŝ⁺_tot u = 0` is *not* used. -/
theorem blockBoundV2E6 (μ : ℝ) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : ℂ)
    (e0 : ((13 / 6 : ℝ) : ℂ) * a0 + ((1 / 3 : ℝ) : ℂ) * a1 + ((1 / 6 : ℝ) : ℂ) * a2
      = ((μ : ℝ) : ℂ) * a0)
    (e1 : ((1 / 3 : ℝ) : ℂ) * a0 + ((13 / 6 : ℝ) : ℂ) * a1 + ((1 / 3 : ℝ) : ℂ) * a2 +
      ((1 / 2 : ℝ) : ℂ) * a3
      = ((μ : ℝ) : ℂ) * a1)
    (e2 : ((1 / 6 : ℝ) : ℂ) * a0 + ((1 / 3 : ℝ) : ℂ) * a1 + ((4 / 3 : ℝ) : ℂ) * a2 +
      ((1 / 3 : ℝ) : ℂ) * a4 + ((1 / 6 : ℝ) : ℂ) * a5
      = ((μ : ℝ) : ℂ) * a2)
    (e3 : ((1 / 2 : ℝ) : ℂ) * a1 + ((3 / 2 : ℝ) : ℂ) * a3 + ((1 / 2 : ℝ) : ℂ) * a4 +
      ((1 / 2 : ℝ) : ℂ) * a6
      = ((μ : ℝ) : ℂ) * a3)
    (e4 : ((1 / 3 : ℝ) : ℂ) * a2 + ((1 / 2 : ℝ) : ℂ) * a3 + ((5 / 3 : ℝ) : ℂ) * a4 +
      ((1 / 3 : ℝ) : ℂ) * a5 + ((1 / 2 : ℝ) : ℂ) * a7
      = ((μ : ℝ) : ℂ) * a4)
    (e5 : ((1 / 6 : ℝ) : ℂ) * a2 + ((1 / 3 : ℝ) : ℂ) * a4 + ((4 / 3 : ℝ) : ℂ) * a5 +
      ((1 / 3 : ℝ) : ℂ) * a8 + ((1 / 6 : ℝ) : ℂ) * a9
      = ((μ : ℝ) : ℂ) * a5)
    (e6 : ((1 / 2 : ℝ) : ℂ) * a3 + ((2 : ℝ) : ℂ) * a6 + ((1 / 2 : ℝ) : ℂ) * a7
      = ((μ : ℝ) : ℂ) * a6)
    (e7 : ((1 / 2 : ℝ) : ℂ) * a4 + ((1 / 2 : ℝ) : ℂ) * a6 + ((3 / 2 : ℝ) : ℂ) * a7 +
      ((1 / 2 : ℝ) : ℂ) * a8
      = ((μ : ℝ) : ℂ) * a7)
    (e8 : ((1 / 3 : ℝ) : ℂ) * a5 + ((1 / 2 : ℝ) : ℂ) * a7 + ((13 / 6 : ℝ) : ℂ) * a8 +
      ((1 / 3 : ℝ) : ℂ) * a9
      = ((μ : ℝ) : ℂ) * a8)
    (e9 : ((1 / 6 : ℝ) : ℂ) * a5 + ((1 / 3 : ℝ) : ℂ) * a8 + ((13 / 6 : ℝ) : ℂ) * a9
      = ((μ : ℝ) : ℂ) * a9)
    (hne : a0 ≠ 0 ∨ a1 ≠ 0 ∨ a2 ≠ 0 ∨ a3 ≠ 0 ∨ a4 ≠ 0 ∨ a5 ≠ 0 ∨ a6 ≠ 0 ∨ a7 ≠ 0 ∨ a8 ≠ 0 ∨
      a9 ≠ 0) :
    2 / 5 ≤ μ := by
  have r0 := row3PartE6 Complex.re Complex.add_re ofRealMulReE6 e0
  have s0 := row3PartE6 Complex.im Complex.add_im ofRealMulImE6 e0
  have r1 := row4PartE6 Complex.re Complex.add_re ofRealMulReE6 e1
  have s1 := row4PartE6 Complex.im Complex.add_im ofRealMulImE6 e1
  have r2 := row5PartE6 Complex.re Complex.add_re ofRealMulReE6 e2
  have s2 := row5PartE6 Complex.im Complex.add_im ofRealMulImE6 e2
  have r3 := row4PartE6 Complex.re Complex.add_re ofRealMulReE6 e3
  have s3 := row4PartE6 Complex.im Complex.add_im ofRealMulImE6 e3
  have r4 := row5PartE6 Complex.re Complex.add_re ofRealMulReE6 e4
  have s4 := row5PartE6 Complex.im Complex.add_im ofRealMulImE6 e4
  have r5 := row5PartE6 Complex.re Complex.add_re ofRealMulReE6 e5
  have s5 := row5PartE6 Complex.im Complex.add_im ofRealMulImE6 e5
  have r6 := row3PartE6 Complex.re Complex.add_re ofRealMulReE6 e6
  have s6 := row3PartE6 Complex.im Complex.add_im ofRealMulImE6 e6
  have r7 := row4PartE6 Complex.re Complex.add_re ofRealMulReE6 e7
  have s7 := row4PartE6 Complex.im Complex.add_im ofRealMulImE6 e7
  have r8 := row4PartE6 Complex.re Complex.add_re ofRealMulReE6 e8
  have s8 := row4PartE6 Complex.im Complex.add_im ofRealMulImE6 e8
  have r9 := row3PartE6 Complex.re Complex.add_re ofRealMulReE6 e9
  have s9 := row3PartE6 Complex.im Complex.add_im ofRealMulImE6 e9
  have hx := quadV2E6 μ a0.re a1.re a2.re a3.re a4.re a5.re a6.re a7.re a8.re a9.re r0 r1 r2 r3 r4
    r5 r6 r7 r8 r9
  have hy := quadV2E6 μ a0.im a1.im a2.im a3.im a4.im a5.im a6.im a7.im a8.im a9.im s0 s1 s2 s3 s4
    s5 s6 s7 s8 s9
  exact leOfQuadE6 μ _ _ hx hy (posSum10E6 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 hne)

/-- **The Knabe block bound carried by the whole sector `V_3`.**  A nonzero vector of the
sector satisfying the eigenvalue equations of `ĥ|V_3` for a real `μ` forces
`0 ≤ μ² − (2/5) μ`.  The highest-weight condition `Ŝ⁺_tot u = 0` is *not* used, and neither
is any basis of `hw_3`. -/
theorem blockBound2V3E6 (μ : ℝ) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 :
    ℂ)
    (e0 : ((2 : ℝ) : ℂ) * a0 + ((1 / 2 : ℝ) : ℂ) * a1 + ((1 / 2 : ℝ) : ℂ) * a2
      = ((μ : ℝ) : ℂ) * a0)
    (e1 : ((1 / 2 : ℝ) : ℂ) * a0 + ((5 / 3 : ℝ) : ℂ) * a1 + ((1 / 3 : ℝ) : ℂ) * a3 +
      ((1 / 6 : ℝ) : ℂ) * a5
      = ((μ : ℝ) : ℂ) * a1)
    (e2 : ((1 / 2 : ℝ) : ℂ) * a0 + ((7 / 6 : ℝ) : ℂ) * a2 + ((1 / 3 : ℝ) : ℂ) * a3 +
      ((1 / 6 : ℝ) : ℂ) * a4 + ((1 / 2 : ℝ) : ℂ) * a7
      = ((μ : ℝ) : ℂ) * a2)
    (e3 : ((1 / 3 : ℝ) : ℂ) * a1 + ((1 / 3 : ℝ) : ℂ) * a2 + ((11 / 6 : ℝ) : ℂ) * a3 +
      ((1 / 3 : ℝ) : ℂ) * a4 + ((1 / 3 : ℝ) : ℂ) * a5 + ((1 / 2 : ℝ) : ℂ) * a8
      = ((μ : ℝ) : ℂ) * a3)
    (e4 : ((1 / 6 : ℝ) : ℂ) * a2 + ((1 / 3 : ℝ) : ℂ) * a3 + ((7 / 6 : ℝ) : ℂ) * a4 +
      ((1 / 2 : ℝ) : ℂ) * a6 + ((1 / 2 : ℝ) : ℂ) * a9
      = ((μ : ℝ) : ℂ) * a4)
    (e5 : ((1 / 6 : ℝ) : ℂ) * a1 + ((1 / 3 : ℝ) : ℂ) * a3 + ((5 / 6 : ℝ) : ℂ) * a5 +
      ((1 / 2 : ℝ) : ℂ) * a6 + ((1 / 3 : ℝ) : ℂ) * a10 + ((1 / 6 : ℝ) : ℂ) * a13
      = ((μ : ℝ) : ℂ) * a5)
    (e6 : ((1 / 2 : ℝ) : ℂ) * a4 + ((1 / 2 : ℝ) : ℂ) * a5 + ((7 / 6 : ℝ) : ℂ) * a6 +
      ((1 / 3 : ℝ) : ℂ) * a11 + ((1 / 6 : ℝ) : ℂ) * a14
      = ((μ : ℝ) : ℂ) * a6)
    (e7 : ((1 / 2 : ℝ) : ℂ) * a2 + ((5 / 3 : ℝ) : ℂ) * a7 + ((1 / 3 : ℝ) : ℂ) * a8 +
      ((1 / 6 : ℝ) : ℂ) * a9
      = ((μ : ℝ) : ℂ) * a7)
    (e8 : ((1 / 2 : ℝ) : ℂ) * a3 + ((1 / 3 : ℝ) : ℂ) * a7 + ((5 / 3 : ℝ) : ℂ) * a8 +
      ((1 / 3 : ℝ) : ℂ) * a9 + ((1 / 2 : ℝ) : ℂ) * a10
      = ((μ : ℝ) : ℂ) * a8)
    (e9 : ((1 / 2 : ℝ) : ℂ) * a4 + ((1 / 6 : ℝ) : ℂ) * a7 + ((1 / 3 : ℝ) : ℂ) * a8 +
      ((5 / 6 : ℝ) : ℂ) * a9 + ((1 / 3 : ℝ) : ℂ) * a11 + ((1 / 6 : ℝ) : ℂ) * a12
      = ((μ : ℝ) : ℂ) * a9)
    (e10 : ((1 / 3 : ℝ) : ℂ) * a5 + ((1 / 2 : ℝ) : ℂ) * a8 + ((5 / 3 : ℝ) : ℂ) * a10 +
      ((1 / 2 : ℝ) : ℂ) * a11 + ((1 / 3 : ℝ) : ℂ) * a13
      = ((μ : ℝ) : ℂ) * a10)
    (e11 : ((1 / 3 : ℝ) : ℂ) * a6 + ((1 / 3 : ℝ) : ℂ) * a9 + ((1 / 2 : ℝ) : ℂ) * a10 +
      ((11 / 6 : ℝ) : ℂ) * a11 + ((1 / 3 : ℝ) : ℂ) * a12 + ((1 / 3 : ℝ) : ℂ) * a14
      = ((μ : ℝ) : ℂ) * a11)
    (e12 : ((1 / 6 : ℝ) : ℂ) * a9 + ((1 / 3 : ℝ) : ℂ) * a11 + ((5 / 3 : ℝ) : ℂ) * a12 +
      ((1 / 2 : ℝ) : ℂ) * a15
      = ((μ : ℝ) : ℂ) * a12)
    (e13 : ((1 / 6 : ℝ) : ℂ) * a5 + ((1 / 3 : ℝ) : ℂ) * a10 + ((5 / 3 : ℝ) : ℂ) * a13 +
      ((1 / 2 : ℝ) : ℂ) * a14
      = ((μ : ℝ) : ℂ) * a13)
    (e14 : ((1 / 6 : ℝ) : ℂ) * a6 + ((1 / 3 : ℝ) : ℂ) * a11 + ((1 / 2 : ℝ) : ℂ) * a13 +
      ((7 / 6 : ℝ) : ℂ) * a14 + ((1 / 2 : ℝ) : ℂ) * a15
      = ((μ : ℝ) : ℂ) * a14)
    (e15 : ((1 / 2 : ℝ) : ℂ) * a12 + ((1 / 2 : ℝ) : ℂ) * a14 + ((2 : ℝ) : ℂ) * a15
      = ((μ : ℝ) : ℂ) * a15)
    (hne : a0 ≠ 0 ∨ a1 ≠ 0 ∨ a2 ≠ 0 ∨ a3 ≠ 0 ∨ a4 ≠ 0 ∨ a5 ≠ 0 ∨ a6 ≠ 0 ∨ a7 ≠ 0 ∨ a8 ≠ 0 ∨
      a9 ≠ 0 ∨ a10 ≠ 0 ∨ a11 ≠ 0 ∨ a12 ≠ 0 ∨ a13 ≠ 0 ∨ a14 ≠ 0 ∨ a15 ≠ 0) :
    0 ≤ μ * μ - 2 / 5 * μ := by
  have r0 := row3PartE6 Complex.re Complex.add_re ofRealMulReE6 e0
  have s0 := row3PartE6 Complex.im Complex.add_im ofRealMulImE6 e0
  have r1 := row4PartE6 Complex.re Complex.add_re ofRealMulReE6 e1
  have s1 := row4PartE6 Complex.im Complex.add_im ofRealMulImE6 e1
  have r2 := row5PartE6 Complex.re Complex.add_re ofRealMulReE6 e2
  have s2 := row5PartE6 Complex.im Complex.add_im ofRealMulImE6 e2
  have r3 := row6PartE6 Complex.re Complex.add_re ofRealMulReE6 e3
  have s3 := row6PartE6 Complex.im Complex.add_im ofRealMulImE6 e3
  have r4 := row5PartE6 Complex.re Complex.add_re ofRealMulReE6 e4
  have s4 := row5PartE6 Complex.im Complex.add_im ofRealMulImE6 e4
  have r5 := row6PartE6 Complex.re Complex.add_re ofRealMulReE6 e5
  have s5 := row6PartE6 Complex.im Complex.add_im ofRealMulImE6 e5
  have r6 := row5PartE6 Complex.re Complex.add_re ofRealMulReE6 e6
  have s6 := row5PartE6 Complex.im Complex.add_im ofRealMulImE6 e6
  have r7 := row4PartE6 Complex.re Complex.add_re ofRealMulReE6 e7
  have s7 := row4PartE6 Complex.im Complex.add_im ofRealMulImE6 e7
  have r8 := row5PartE6 Complex.re Complex.add_re ofRealMulReE6 e8
  have s8 := row5PartE6 Complex.im Complex.add_im ofRealMulImE6 e8
  have r9 := row6PartE6 Complex.re Complex.add_re ofRealMulReE6 e9
  have s9 := row6PartE6 Complex.im Complex.add_im ofRealMulImE6 e9
  have r10 := row5PartE6 Complex.re Complex.add_re ofRealMulReE6 e10
  have s10 := row5PartE6 Complex.im Complex.add_im ofRealMulImE6 e10
  have r11 := row6PartE6 Complex.re Complex.add_re ofRealMulReE6 e11
  have s11 := row6PartE6 Complex.im Complex.add_im ofRealMulImE6 e11
  have r12 := row4PartE6 Complex.re Complex.add_re ofRealMulReE6 e12
  have s12 := row4PartE6 Complex.im Complex.add_im ofRealMulImE6 e12
  have r13 := row4PartE6 Complex.re Complex.add_re ofRealMulReE6 e13
  have s13 := row4PartE6 Complex.im Complex.add_im ofRealMulImE6 e13
  have r14 := row5PartE6 Complex.re Complex.add_re ofRealMulReE6 e14
  have s14 := row5PartE6 Complex.im Complex.add_im ofRealMulImE6 e14
  have r15 := row3PartE6 Complex.re Complex.add_re ofRealMulReE6 e15
  have s15 := row3PartE6 Complex.im Complex.add_im ofRealMulImE6 e15
  have hx := quad2V3E6 μ a0.re a1.re a2.re a3.re a4.re a5.re a6.re a7.re a8.re a9.re a10.re a11.re
    a12.re a13.re a14.re a15.re r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  have hy := quad2V3E6 μ a0.im a1.im a2.im a3.im a4.im a5.im a6.im a7.im a8.im a9.im a10.im a11.im
    a12.im a13.im a14.im a15.im s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15
  exact nonnegOfQuadE6 _ _ _ hx hy (posSum16E6 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
    a15 hne)

/-- **The Knabe block bound carried by the whole sector `V_4`.**  A nonzero vector of the
sector satisfying the eigenvalue equations of `ĥ|V_4` for a real `μ` forces
`0 ≤ μ² − (2/5) μ`.  The highest-weight condition `Ŝ⁺_tot u = 0` is *not* used, and neither
is any basis of `hw_4`. -/
theorem blockBound2V4E6 (μ : ℝ) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
    a17 a18 : ℂ)
    (e0 : ((13 / 6 : ℝ) : ℂ) * a0 + ((1 / 3 : ℝ) : ℂ) * a1 + ((1 / 6 : ℝ) : ℂ) * a3
      = ((μ : ℝ) : ℂ) * a0)
    (e1 : ((1 / 3 : ℝ) : ℂ) * a0 + ((5 / 3 : ℝ) : ℂ) * a1 + ((1 / 2 : ℝ) : ℂ) * a2 +
      ((1 / 3 : ℝ) : ℂ) * a3 + ((1 / 2 : ℝ) : ℂ) * a6
      = ((μ : ℝ) : ℂ) * a1)
    (e2 : ((1 / 2 : ℝ) : ℂ) * a1 + ((3 / 2 : ℝ) : ℂ) * a2 + ((1 / 2 : ℝ) : ℂ) * a4 +
      ((1 / 2 : ℝ) : ℂ) * a7
      = ((μ : ℝ) : ℂ) * a2)
    (e3 : ((1 / 6 : ℝ) : ℂ) * a0 + ((1 / 3 : ℝ) : ℂ) * a1 + ((1 / 2 : ℝ) : ℂ) * a3 +
      ((1 / 3 : ℝ) : ℂ) * a4 + ((1 / 6 : ℝ) : ℂ) * a5 + ((1 / 3 : ℝ) : ℂ) * a8 +
        ((1 / 6 : ℝ) : ℂ) * a13
      = ((μ : ℝ) : ℂ) * a3)
    (e4 : ((1 / 2 : ℝ) : ℂ) * a2 + ((1 / 3 : ℝ) : ℂ) * a3 + ((4 / 3 : ℝ) : ℂ) * a4 +
      ((1 / 3 : ℝ) : ℂ) * a5 + ((1 / 3 : ℝ) : ℂ) * a9 + ((1 / 6 : ℝ) : ℂ) * a14
      = ((μ : ℝ) : ℂ) * a4)
    (e5 : ((1 / 6 : ℝ) : ℂ) * a3 + ((1 / 3 : ℝ) : ℂ) * a4 + ((4 / 3 : ℝ) : ℂ) * a5 +
      ((1 / 3 : ℝ) : ℂ) * a10 + ((1 / 6 : ℝ) : ℂ) * a15
      = ((μ : ℝ) : ℂ) * a5)
    (e6 : ((1 / 2 : ℝ) : ℂ) * a1 + ((3 / 2 : ℝ) : ℂ) * a6 + ((1 / 2 : ℝ) : ℂ) * a7 +
      ((1 / 2 : ℝ) : ℂ) * a8
      = ((μ : ℝ) : ℂ) * a6)
    (e7 : ((1 / 2 : ℝ) : ℂ) * a2 + ((1 / 2 : ℝ) : ℂ) * a6 + ((7 / 6 : ℝ) : ℂ) * a7 +
      ((1 / 3 : ℝ) : ℂ) * a9 + ((1 / 6 : ℝ) : ℂ) * a11
      = ((μ : ℝ) : ℂ) * a7)
    (e8 : ((1 / 3 : ℝ) : ℂ) * a3 + ((1 / 2 : ℝ) : ℂ) * a6 + ((4 / 3 : ℝ) : ℂ) * a8 +
      ((1 / 3 : ℝ) : ℂ) * a9 + ((1 / 6 : ℝ) : ℂ) * a10 + ((1 / 3 : ℝ) : ℂ) * a13
      = ((μ : ℝ) : ℂ) * a8)
    (e9 : ((1 / 3 : ℝ) : ℂ) * a4 + ((1 / 3 : ℝ) : ℂ) * a7 + ((1 / 3 : ℝ) : ℂ) * a8 +
      ((2 : ℝ) : ℂ) * a9 + ((1 / 3 : ℝ) : ℂ) * a10 + ((1 / 3 : ℝ) : ℂ) * a11 +
        ((1 / 3 : ℝ) : ℂ) * a14
      = ((μ : ℝ) : ℂ) * a9)
    (e10 : ((1 / 3 : ℝ) : ℂ) * a5 + ((1 / 6 : ℝ) : ℂ) * a8 + ((1 / 3 : ℝ) : ℂ) * a9 +
      ((4 / 3 : ℝ) : ℂ) * a10 + ((1 / 2 : ℝ) : ℂ) * a12 + ((1 / 3 : ℝ) : ℂ) * a15
      = ((μ : ℝ) : ℂ) * a10)
    (e11 : ((1 / 6 : ℝ) : ℂ) * a7 + ((1 / 3 : ℝ) : ℂ) * a9 + ((7 / 6 : ℝ) : ℂ) * a11 +
      ((1 / 2 : ℝ) : ℂ) * a12 + ((1 / 2 : ℝ) : ℂ) * a16
      = ((μ : ℝ) : ℂ) * a11)
    (e12 : ((1 / 2 : ℝ) : ℂ) * a10 + ((1 / 2 : ℝ) : ℂ) * a11 + ((3 / 2 : ℝ) : ℂ) * a12 +
      ((1 / 2 : ℝ) : ℂ) * a17
      = ((μ : ℝ) : ℂ) * a12)
    (e13 : ((1 / 6 : ℝ) : ℂ) * a3 + ((1 / 3 : ℝ) : ℂ) * a8 + ((4 / 3 : ℝ) : ℂ) * a13 +
      ((1 / 3 : ℝ) : ℂ) * a14 + ((1 / 6 : ℝ) : ℂ) * a15
      = ((μ : ℝ) : ℂ) * a13)
    (e14 : ((1 / 6 : ℝ) : ℂ) * a4 + ((1 / 3 : ℝ) : ℂ) * a9 + ((1 / 3 : ℝ) : ℂ) * a13 +
      ((4 / 3 : ℝ) : ℂ) * a14 + ((1 / 3 : ℝ) : ℂ) * a15 + ((1 / 2 : ℝ) : ℂ) * a16
      = ((μ : ℝ) : ℂ) * a14)
    (e15 : ((1 / 6 : ℝ) : ℂ) * a5 + ((1 / 3 : ℝ) : ℂ) * a10 + ((1 / 6 : ℝ) : ℂ) * a13 +
      ((1 / 3 : ℝ) : ℂ) * a14 + ((1 / 2 : ℝ) : ℂ) * a15 + ((1 / 3 : ℝ) : ℂ) * a17 +
      ((1 / 6 : ℝ) : ℂ) * a18
      = ((μ : ℝ) : ℂ) * a15)
    (e16 : ((1 / 2 : ℝ) : ℂ) * a11 + ((1 / 2 : ℝ) : ℂ) * a14 + ((3 / 2 : ℝ) : ℂ) * a16 +
      ((1 / 2 : ℝ) : ℂ) * a17
      = ((μ : ℝ) : ℂ) * a16)
    (e17 : ((1 / 2 : ℝ) : ℂ) * a12 + ((1 / 3 : ℝ) : ℂ) * a15 + ((1 / 2 : ℝ) : ℂ) * a16 +
      ((5 / 3 : ℝ) : ℂ) * a17 + ((1 / 3 : ℝ) : ℂ) * a18
      = ((μ : ℝ) : ℂ) * a17)
    (e18 : ((1 / 6 : ℝ) : ℂ) * a15 + ((1 / 3 : ℝ) : ℂ) * a17 + ((13 / 6 : ℝ) : ℂ) * a18
      = ((μ : ℝ) : ℂ) * a18)
    (hne : a0 ≠ 0 ∨ a1 ≠ 0 ∨ a2 ≠ 0 ∨ a3 ≠ 0 ∨ a4 ≠ 0 ∨ a5 ≠ 0 ∨ a6 ≠ 0 ∨ a7 ≠ 0 ∨ a8 ≠ 0 ∨
      a9 ≠ 0 ∨ a10 ≠ 0 ∨ a11 ≠ 0 ∨ a12 ≠ 0 ∨ a13 ≠ 0 ∨ a14 ≠ 0 ∨ a15 ≠ 0 ∨ a16 ≠ 0 ∨ a17 ≠ 0 ∨
      a18 ≠ 0) :
    0 ≤ μ * μ - 2 / 5 * μ := by
  have r0 := row3PartE6 Complex.re Complex.add_re ofRealMulReE6 e0
  have s0 := row3PartE6 Complex.im Complex.add_im ofRealMulImE6 e0
  have r1 := row5PartE6 Complex.re Complex.add_re ofRealMulReE6 e1
  have s1 := row5PartE6 Complex.im Complex.add_im ofRealMulImE6 e1
  have r2 := row4PartE6 Complex.re Complex.add_re ofRealMulReE6 e2
  have s2 := row4PartE6 Complex.im Complex.add_im ofRealMulImE6 e2
  have r3 := row7PartE6 Complex.re Complex.add_re ofRealMulReE6 e3
  have s3 := row7PartE6 Complex.im Complex.add_im ofRealMulImE6 e3
  have r4 := row6PartE6 Complex.re Complex.add_re ofRealMulReE6 e4
  have s4 := row6PartE6 Complex.im Complex.add_im ofRealMulImE6 e4
  have r5 := row5PartE6 Complex.re Complex.add_re ofRealMulReE6 e5
  have s5 := row5PartE6 Complex.im Complex.add_im ofRealMulImE6 e5
  have r6 := row4PartE6 Complex.re Complex.add_re ofRealMulReE6 e6
  have s6 := row4PartE6 Complex.im Complex.add_im ofRealMulImE6 e6
  have r7 := row5PartE6 Complex.re Complex.add_re ofRealMulReE6 e7
  have s7 := row5PartE6 Complex.im Complex.add_im ofRealMulImE6 e7
  have r8 := row6PartE6 Complex.re Complex.add_re ofRealMulReE6 e8
  have s8 := row6PartE6 Complex.im Complex.add_im ofRealMulImE6 e8
  have r9 := row7PartE6 Complex.re Complex.add_re ofRealMulReE6 e9
  have s9 := row7PartE6 Complex.im Complex.add_im ofRealMulImE6 e9
  have r10 := row6PartE6 Complex.re Complex.add_re ofRealMulReE6 e10
  have s10 := row6PartE6 Complex.im Complex.add_im ofRealMulImE6 e10
  have r11 := row5PartE6 Complex.re Complex.add_re ofRealMulReE6 e11
  have s11 := row5PartE6 Complex.im Complex.add_im ofRealMulImE6 e11
  have r12 := row4PartE6 Complex.re Complex.add_re ofRealMulReE6 e12
  have s12 := row4PartE6 Complex.im Complex.add_im ofRealMulImE6 e12
  have r13 := row5PartE6 Complex.re Complex.add_re ofRealMulReE6 e13
  have s13 := row5PartE6 Complex.im Complex.add_im ofRealMulImE6 e13
  have r14 := row6PartE6 Complex.re Complex.add_re ofRealMulReE6 e14
  have s14 := row6PartE6 Complex.im Complex.add_im ofRealMulImE6 e14
  have r15 := row7PartE6 Complex.re Complex.add_re ofRealMulReE6 e15
  have s15 := row7PartE6 Complex.im Complex.add_im ofRealMulImE6 e15
  have r16 := row4PartE6 Complex.re Complex.add_re ofRealMulReE6 e16
  have s16 := row4PartE6 Complex.im Complex.add_im ofRealMulImE6 e16
  have r17 := row5PartE6 Complex.re Complex.add_re ofRealMulReE6 e17
  have s17 := row5PartE6 Complex.im Complex.add_im ofRealMulImE6 e17
  have r18 := row3PartE6 Complex.re Complex.add_re ofRealMulReE6 e18
  have s18 := row3PartE6 Complex.im Complex.add_im ofRealMulImE6 e18
  have hx := quad2V4E6 μ a0.re a1.re a2.re a3.re a4.re a5.re a6.re a7.re a8.re a9.re a10.re a11.re
    a12.re a13.re a14.re a15.re a16.re a17.re a18.re r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
    r14 r15 r16 r17 r18
  have hy := quad2V4E6 μ a0.im a1.im a2.im a3.im a4.im a5.im a6.im a7.im a8.im a9.im a10.im a11.im
    a12.im a13.im a14.im a15.im a16.im a17.im a18.im s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13
    s14 s15 s16 s17 s18
  exact nonnegOfQuadE6 _ _ _ hx hy (posSum19E6 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
    a15 a16 a17 a18 hne)

end LatticeSystem.Quantum.AKLTSl2BlockDischargeE6
