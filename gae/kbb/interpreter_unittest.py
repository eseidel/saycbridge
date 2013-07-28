import unittest2
from kbb.interpreter import BidInterpreter
from core.callhistory import CallHistory
from core.suit import CLUBS, DIAMONDS, HEARTS, SPADES, NOTRUMP


class BidInterpreterTest(unittest2.TestCase):
    def setUp(self):
        self.interpreter = BidInterpreter()

    def _rule_for_last_call(self, call_history_string):
        history = CallHistory.from_string(call_history_string)
        knowledge, knowledge_builder = self.interpreter.knowledge_from_history(history)
        matched_rules = knowledge_builder.matched_rules()
        return matched_rules[-1]

    def _hand_knowledge_from_last_call(self, call_history_string):
        history = CallHistory.from_string(call_history_string)
        knowledge, _ = self.interpreter.knowledge_from_history(history)
        return knowledge.rho

    def test_not_crash(self):
        # We used to hit an assert when considering SecondNegative for 3C (it shouldn't match, but was asserting).
        self._rule_for_last_call("2C,P,2D,P,2H,P,2S,P,2N,P,3C")

    # FIXME: It's possible these various asserts should be combined
    # so that we can do multiple tests only running the interpreter once over a history.
    def _assert_point_range(self, call_history_string, expected_point_range):
        history = CallHistory.from_string(call_history_string)
        knowledge, matched_rules = self.interpreter.knowledge_from_history(history)
        # We use rho() instead of me() because knowledge_from_history auto-rotates the Knowledge.
        self.assertEqual(knowledge.rho.hcp_range_tuple(), expected_point_range)

    def _assert_rule_name(self, call_history_string, expected_rule_name):
        last_rule = self._rule_for_last_call(call_history_string)
        self.assertEqual(last_rule.name(), expected_rule_name)

    def test_one_level_opening(self):
        self._assert_point_range("1C", (12, 21))
        self._assert_rule_name("1C", "MinorOpen")

    def test_lead_directing_double(self):
        self._assert_rule_name("P,1N,P,2C,X", "LeadDirectingDouble")
        self._assert_rule_name("P,1N,P,2C,P,2D,X", "LeadDirectingDouble")
        self._assert_rule_name("2C X", "LeadDirectingDouble")

    def test_negative_double(self):
        # From p133:
        hand_knowledge = self._hand_knowledge_from_last_call("1C 1D X")
        self.assertEquals(hand_knowledge.min_length(HEARTS), 4)
        self.assertEquals(hand_knowledge.min_length(SPADES), 4)
        hand_knowledge = self._hand_knowledge_from_last_call("1D 1H X")
        self.assertEquals(hand_knowledge.min_length(SPADES), 4)
        self.assertEquals(hand_knowledge.max_length(SPADES), 4)
        hand_knowledge = self._hand_knowledge_from_last_call("1D 1S X")
        self.assertEquals(hand_knowledge.min_length(HEARTS), 4)

    def test_michaels_minor_request(self):
        self._assert_rule_name("1H 2H P 2N", "MichaelsMinorRequest")
        self._assert_rule_name("1S 2S P 2N", "MichaelsMinorRequest")
        self._assert_rule_name("2H 3H P 4C", "MichaelsMinorRequest")
        self._assert_rule_name("2S 3S P 4C", "MichaelsMinorRequest")
        # FIXME: We don't currently support 4-level Michaels
        # self._assert_rule_name("3H 4H P 4N", "MichaelsMinorRequest")
        # self._assert_rule_name("3S 4S P 4N", "MichaelsMinorRequest")
        self._assert_rule_name("2H 3H 4H 4N", "UnforcedMichaelsMinorRequest")
        self._assert_rule_name("2H 3H 4H 4N", "UnforcedMichaelsMinorRequest")

    def _assert_is_stayman(self, history_string, should_be_stayman):
        knowledge = self._hand_knowledge_from_last_call(history_string)
        self.assertEqual(knowledge.last_call.stayman, should_be_stayman)

    def test_stayman(self):
        self._assert_is_stayman("1N P 2C", True)
        self._assert_is_stayman("1N P 3C", False)
        self._assert_is_stayman("1N 2C X", True)
        self._assert_is_stayman("2N P 3C", True)
        self._assert_is_stayman("3N P 4C", True)
        self._assert_is_stayman("4N P 5C", False)
        self._assert_is_stayman("1D P 1H P 2N P 3C", False)
        self._assert_is_stayman("2C P 2D P 2N P 3C", True)
        self._assert_is_stayman("2C P 2D P 3N P 4C", True)
        self._assert_is_stayman("2C P 2D P 4N P 5C", False)

        # FIXME: These 2C -> 5N sequences should be changed to use 3N
        # once we introduce 3N as meaning "minimum", since currently
        # the bidder asserts trying to interpret 3N since the partnership
        # clearly has 30+ points and can make 5N.  No sense in wasting
        # all that bidding space to show a minimum 22hcp however.
        self._assert_is_stayman("2C P 2H P 5N P 6C", False)
        self._assert_is_stayman("2C P 2S P 5N P 6C", False)
        self._assert_is_stayman("2C P 2N P 5N P 6C", False)
        # FIXME: It seems this should be stayman showing 4 hearts and 4 points?
        # self._assert_is_stayman("2C 2S P P 2N P 3C", True)
        # FIXME: It seems this should be stayman showing 4 hearts and ?? points?
        # self._assert_is_stayman("2C 2S P P 3N P 4C", True)

    def _assert_is_jacoby_transfer(self, history_string, should_be_transfer):
        knowledge = self._hand_knowledge_from_last_call(history_string)
        self.assertEqual(knowledge.last_call.jacoby_transfer, should_be_transfer)

    def test_jacoby_transfers(self):
        self._assert_is_jacoby_transfer("1N P 2D", True)
        self._assert_is_jacoby_transfer("1N P 2H", True)
        self._assert_is_jacoby_transfer("1N P 2S", False)  # Special transfer, not jacoby
        self._assert_is_jacoby_transfer("1N X 2D", True)
        self._assert_is_jacoby_transfer("1N 2C 2D", True)
        self._assert_is_jacoby_transfer("1N X 2H", True)
        self._assert_is_jacoby_transfer("1N 2C 2H", True)

        self._assert_is_jacoby_transfer("2N X 3D", True)
        self._assert_is_jacoby_transfer("2N 3C 3D", True)
        self._assert_is_jacoby_transfer("2N X 3H", True)
        self._assert_is_jacoby_transfer("2N 3C 3H", True)

        # Although we might like to play these as a transfer, that's not currently SAYC:
        self._assert_is_jacoby_transfer("1N 2D X", False)
        self._assert_is_jacoby_transfer("1N 2D 2H", False)

    def _assert_is_gerber(self, history_string, should_be_gerber):
        last_rule = self._rule_for_last_call(history_string)
        if should_be_gerber:
            self.assertEqual(last_rule.name(), "Gerber")
        else:
            self.assertNotEqual(last_rule.name(), "Gerber")

    def test_gerber(self):
        self._assert_is_gerber("1N P 4C", True)
        self._assert_is_gerber("1D P 1S P 1N P 4C", True)
        # FIXME: Should this really be gerber?  Currently we treat it as such.
        self._assert_is_gerber("1N 3S 4C", True)
        self._assert_is_gerber("2C P 2N P 4C", True)

    def test_4N_over_jacoby_2N(self):
        # 4N is not a valid bid over Jacoby2N.
        self.assertEqual(self._rule_for_last_call("1H P 2N P 4N"), None)

    def test_is_fourth_suit_forcing(self):
        # Raising FSF never makes any sense, and is not a FSF bid.
        self.assertEqual(self._rule_for_last_call("1D,P,1S,P,2C,P,2H,P,3C,P,3H"), None)

    def _assert_is_takeout(self, history_string, should_be_takeout):
        knowledge = self._hand_knowledge_from_last_call(history_string)
        self.assertEqual(knowledge.last_call.takeout_double, should_be_takeout)

    def test_is_takeout(self):
        self._assert_is_takeout("1H X", True)
        self._assert_is_takeout("1H P 2H X", True)
        self._assert_is_takeout("1H P 1S X", True)
        self._assert_is_takeout("1H 1S X", False)

    def test_help_suit_game_try(self):
        # We believe 2S here is called a HelpSuitGameTry even though it's very similar to a reverse.
        self._assert_rule_name("1H P 2H P 2S", "HelpSuitGameTry")

    def test_4H_does_not_assert(self):
        self._assert_rule_name("1C 2N P 3H P 4H", "MajorGame")
