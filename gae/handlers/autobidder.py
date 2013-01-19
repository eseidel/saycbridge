from core.call import Pass
from kbb import KnowledgeBasedBidder


# FIXME: Should this this be moved down and shared by saycbot.py?
class Autobidder(object):
    def __init__(self):
        self.bidder = KnowledgeBasedBidder()

    def _bid_next_hand(self, board):
        position_to_call = board.call_history.position_to_call()
        hand = board.deal.hands[position_to_call]
        bid, rule, hand_knowledge = self.bidder.find_bid_and_rule_and_hand_knowledge_for(hand, board.call_history)
        board.call_history.calls.append(bid or Pass())
        return [bid, rule, hand_knowledge]

    def bid_all_hands(self, board, until_position=None):
        bids_and_rules_and_hand_knowledges = []
        while not board.call_history.is_complete() and board.call_history.position_to_call() != until_position:
            bids_and_rules_and_hand_knowledges.append(self._bid_next_hand(board))
        return bids_and_rules_and_hand_knowledges
