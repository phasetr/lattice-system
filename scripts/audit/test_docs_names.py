#!/usr/bin/env python3
r"""Regression tests for the compressed-notation expansion of docs_names.py.

Run: python3 scripts/audit/test_docs_names.py

Every fixture below is a verbatim excerpt of `docs/index.md` / `tex/proof-guide.tex`
(the notations are what those files actually use, not invented ones), and every
case asserts BOTH directions: the family members must be recognised, and names
that merely look similar must NOT be — the expansion feeds a deletion sweep, so an
over-broad reading is as harmful as a missed one.
"""
from __future__ import annotations
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import docs_names as D  # noqa: E402


def index(text: str):
    """Build the documented-name index from a raw (unnormalized) fixture."""
    return D.index_from_text(D.normalize(text))


class ExpansionCase(unittest.TestCase):
    """Shared assertions over an index built from a fixture."""

    def assertDocumented(self, text, *names):
        exact, prefixes = index(text)
        for n in names:
            self.assertTrue(D.is_documented(n, exact, prefixes),
                            f"{n!r} should be documented by {text!r}")

    def assertNotDocumented(self, text, *names):
        exact, prefixes = index(text)
        for n in names:
            self.assertFalse(D.is_documented(n, exact, prefixes),
                             f"{n!r} should NOT be documented by {text!r}")


class TestBrace(ExpansionCase):
    def test_axis_family(self):
        t = "| `spinOnePiRot{1,2,3}_sq` | `(u_a)^2 = 1` |"
        self.assertDocumented(t, "spinOnePiRot1_sq", "spinOnePiRot2_sq",
                              "spinOnePiRot3_sq")
        self.assertNotDocumented(t, "spinOnePiRot4_sq", "spinOnePiRot1_cube")

    def test_two_groups_cross_product(self):
        t = "`spinOnePiRot{1,2,3}_mulVec_spinOne{Plus,Zero,Minus}`"
        self.assertDocumented(t, "spinOnePiRot1_mulVec_spinOnePlus",
                              "spinOnePiRot3_mulVec_spinOneMinus")
        self.assertNotDocumented(t, "spinOnePiRot1_mulVec_spinOneUp")

    def test_empty_alternative_and_spaces(self):
        self.assertDocumented("`single_offset_succ_{,swap_}mem_adjoin`",
                              "single_offset_succ_mem_adjoin",
                              "single_offset_succ_swap_mem_adjoin")
        self.assertDocumented("`hubbardChain{Hamiltonian, Gibbs}_isHermitian`",
                              "hubbardChainGibbs_isHermitian")


class TestSlash(ExpansionCase):
    def test_abbreviated_right_side(self):
        t = "| `spinOneOpPlus/Minus_conjTranspose` | `(S^pm)^dag = S^mp` |"
        self.assertDocumented(t, "spinOneOpPlus_conjTranspose",
                              "spinOneOpMinus_conjTranspose")
        self.assertNotDocumented(t, "spinOneOpZero_conjTranspose")

    def test_alternation_in_the_middle(self):
        t = "`becTowerState_pos/neg_rayleigh_bound_halfFilling`"
        self.assertDocumented(t, "becTowerState_pos_rayleigh_bound_halfFilling",
                              "becTowerState_neg_rayleigh_bound_halfFilling")

    def test_both_sides_full_names(self):
        t = "`angRaise/angLower_normSq`"
        self.assertDocumented(t, "angRaise_normSq", "angLower_normSq")

    def test_left_alternative_kept_verbatim(self):
        t = "`totalSpinHalfSquared_mulVec_basisVec_all_up/down`"
        self.assertDocumented(t, "totalSpinHalfSquared_mulVec_basisVec_all_up",
                              "totalSpinHalfSquared_mulVec_basisVec_all_down")

    def test_paths_and_prose_are_not_families(self):
        self.assertNotDocumented("see `AngularMomentum/Ladder` and add/sub/smul",
                                 "Ladder", "sub", "smul", "AngularMomentum")

    def test_right_side_alone_is_not_emitted(self):
        # The truncated reading would register a bare `sub_*` and swallow every
        # `sub_…` declaration in the tree.
        t = "`sublatticeSpinSOpPlus_add_sublatticeSpinSOpMinus` / `_sub_*`"
        self.assertNotDocumented(t, "sub_totally_bogus_dead_lemma")
        self.assertDocumented(t, "sublatticeSpinSOpPlus_sub_sublatticeSpinSOpMinus")


class TestContinuation(ExpansionCase):
    def test_suffix_replaces_trailing_segments(self):
        t = "| `complexConjugationSpinHalf_sq` / `_add` / `_smul` | antilinear |"
        self.assertDocumented(t, "complexConjugationSpinHalf_sq",
                              "complexConjugationSpinHalf_add",
                              "complexConjugationSpinHalf_smul")
        self.assertNotDocumented(t, "complexConjugationSpinHalf_mul")

    def test_no_space_around_the_slash(self):
        t = "`tJHamiltonian_mulVec_preserves_number`/`_spinZ`"
        self.assertDocumented(t, "tJHamiltonian_mulVec_preserves_spinZ")

    def test_base_may_be_brace_compressed(self):
        t = "| `spinSOp{Plus,Minus}_apply_top` / `_bottom` |"
        self.assertDocumented(t, "spinSOpPlus_apply_top", "spinSOpMinus_apply_bottom")

    def test_trailing_underscore_is_an_infix_replacement(self):
        t = ("`neelSquareState_inner_spinHalfDot_horizontal_adjacent_eq_neg_one_quarter`"
             " / `_vertical_adjacent_` / `_horizontal_wrap_`")
        self.assertDocumented(
            t, "neelSquareState_inner_spinHalfDot_vertical_adjacent_eq_neg_one_quarter",
            "neelSquareState_inner_spinHalfDot_horizontal_wrap_eq_neg_one_quarter")

    def test_tex_form_across_a_line_break(self):
        t = "\\texttt{fermionAnnihilation\\_mulVec\\_vacuum} /\n\\texttt{\\_occupied}"
        self.assertDocumented(t, "fermionAnnihilation_mulVec_occupied")

    def test_first_word_head_is_not_a_family(self):
        # Cutting the base down to `right` would register the wildcard `right_theta_*`.
        t = "| `rightGauge_conj_ringLeftHamiltonian` / `_theta_*` |"
        self.assertDocumented(t, "rightGauge_conj_ringLeftHamiltonian",
                              "rightGauge_conj_theta_anything")
        self.assertNotDocumented(t, "right_theta_bogus_dead_lemma")


class TestStar(ExpansionCase):
    def test_anchored_wildcard(self):
        t = "| `spinOnePiRot{1,2,3}_comm_*` | integer-spin commutation |"
        self.assertDocumented(t, "spinOnePiRot1_comm_spinOnePiRot2",
                              "spinOnePiRot3_comm_spinOnePiRot1")
        self.assertNotDocumented(t, "spinOnePiRot1_sq")

    def test_unanchored_star_is_markdown_emphasis(self):
        t = "all* of the **axiom** cases are arbitrary*"
        self.assertNotDocumented(t, "allAlignedStateS_bogus", "axioms_bogus")


class TestProseAndTex(ExpansionCase):
    def test_prose_words_are_not_names(self):
        t = "this lemma computes the trace of the matrix and the state"
        self.assertNotDocumented(t, "lemma", "trace", "matrix", "state")

    def test_texttt_does_not_glue_to_its_argument(self):
        t = "Hermiticity (\\texttt{mielkeHamiltonian\\_isHermitian})"
        self.assertDocumented(t, "mielkeHamiltonian_isHermitian")
        self.assertNotDocumented(t, "textttmielkeHamiltonian_isHermitian")

    def test_a_longer_name_does_not_document_its_prefix(self):
        t = "`fermionUpProjection_commute_fermionDownProjection_of_any`"
        self.assertDocumented(t, "fermionUpProjection_commute_fermionDownProjection_of_any")
        self.assertNotDocumented(t, "fermionUpProjection_commute_fermionDownProjection")


class TestIndexSafety(unittest.TestCase):
    def test_missing_document_is_fatal(self):
        with self.assertRaises(SystemExit):
            D.index_names([str(Path(D.REPO_ROOT) / "docs" / "does-not-exist.md")])

    def test_empty_index_is_fatal(self):
        # An index with no names would report every declaration as deletable.
        self.assertEqual(index("no identifiers here at all"), (set(), set()))
        with self.assertRaises(SystemExit):
            D.index_names([str(Path(D.REPO_ROOT) / "docs" / "nope1.md")])

    def test_real_docs_index_is_populated(self):
        exact, prefixes = D.index_names()
        self.assertGreater(len(exact), 1000)
        self.assertTrue(D.is_documented("spinOneRot1_zero", exact, prefixes))
        self.assertFalse(D.is_documented("sqrt2_mul_sqrt2", exact, prefixes))


if __name__ == "__main__":
    unittest.main(verbosity=2)
