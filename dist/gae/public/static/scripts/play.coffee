class RankPromoter
    constructor: (@visibleHands, @bidHistory) ->
        

    rankPromotedValue: (card) ->
        return card


class PlaySelector
    constructor: (@bidHistory, @vulnerability) ->

    _randomChoice: (list) ->
        return list[0]

    _selectRandomLegalCard: (hand, trick) ->
        leadSuit = trick.leadSuit()
        if leadSuit
            cardsInSuit = hand.cardsInSuit(leadSuit)
            if cardsInSuit.length > 0
                return @_randomChoice cardsInSuit
        return @_randomChoice hand.cards

    # This could be taught to avoid opponent's suit.
    _longestAndStrongest: (hand) ->
        longestSuits = hand.longestSuits()
        longestSuits.sort (a, b) =>
            return hand.highCardPointsInSuit(b) - hand.highCardPointsInSuit(a)
        return longestSuits[0]

    _selectSuitToLead: (hand) ->
        return @_longestAndStrongest(hand)

    selectNextCard: (hand, otherHand, playHistory) ->
        position = playHistory.nextToPlay()
        # otherHand is normally the dummy, but can be the declarer's hand when considering what to play for the dummy.
        otherHandPosition = if position == playHistory.dummy() then playHistory.declarer else playHistory.dummy()

        visibleHands = [hand]
        if otherHand
            visibleHands.push otherHand
        @rankPromoter = new RankPromoter visibleHands, playHistory

        trick = playHistory.currentTrick()
        playedCards = trick.cardsPlayed()
        switch playedCards.length
            when 0
                # We're leading, oh boy.
                if not otherHand # Opening lead
                    suitToLead = @_selectSuitToLead(hand)

            when 1 then
                # Second hand low
            when 2 then
                # Third hand high
            when 3 then
                # Win it if you can and your partner hasn't, otherwise duck

        return @_selectRandomLegalCard(hand, trick)


window.play = window.play or {}
play = window.play
play.PlaySelector = PlaySelector
