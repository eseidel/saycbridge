class Position
    constructor: (@name) ->
        

    @NORTH = new Position 'N'
    @EAST = new Position 'E'
    @SOUTH = new Position 'S'
    @WEST = new Position 'W'
    @POSITIONS = [Position.NORTH, Position.EAST, Position.SOUTH, Position.WEST]

    index: ->
        return 'NESW'.indexOf @name

    @fromIndex: (index) ->
        return Position.POSITIONS[index]

    @fromChar: (positionChar) ->
        positionIndex = "NESW".indexOf(positionChar)
        return Position.fromIndex(positionIndex)

    identifier: ->
        return @name

    @fromIdentifier: (identifier) ->
        return Position.fromChar(identifier)

    @fromString: (string) ->
        positionChar = {
            north: 'N',
            south: 'S',
            east: 'E',
            west: 'W',
        }[string.toLowerCase()]
        return Position.fromChar(positionChar)

    # Alway positive.
    offsetFrom: (other) ->
        return (@index() - other.index() + 4) % 4

    lho: ->
        return Position.fromIndex (@index() + 1) % 4

    partner: ->
        return Position.fromIndex (@index() + 2) % 4

    rho: ->
        return Position.fromIndex (@index() + 3) % 4

    inPartnershipWith: (other) ->
        if @name in "EW"
            return other.name in "EW"
        return other.name in "NS"

    displayName: ->
        return {
            N: 'North',
            E: 'East',
            S: 'South',
            W: 'West',
        }[@name]

    toJSON: ->
        return @name


class Strain
    constructor: (@name) ->
        if @name not in 'CDHSN'
            throw "Unknown Strain " + @name

    @ORDERED_CHARS = "CDHSN"

    @CLUBS = new Strain 'C'
    @DIAMONDS = new Strain 'D'
    @HEARTS = new Strain 'H'
    @SPADES = new Strain 'S'
    @NOTRUMP = new Strain 'N'
    @STRAINS = [
        Strain.CLUBS,
        Strain.DIAMONDS,
        Strain.HEARTS,
        Strain.SPADES,
        Strain.NOTRUMP,
    ]

    index: ->
        return Strain.ORDERED_CHARS.indexOf(@name)

    gameLevel: ->
        if @isNotrump()
            return 3
        if @isMajor()
            return 4
        return 5

    isMinor: ->
        return @name in "CD"

    isMajor: ->
        return @name in "HS"

    isNotrump: ->
        return @name == 'N'

    displayName: ->
        return {
            C: 'Clubs',
            D: 'Diamonds',
            H: 'Hearts',
            S: 'Spades',
            N: 'Notrump',
        }[@name]

    identifier: ->
        return @name

    @fromIdentifier: (identifier) ->
        return Strain.fromChar(identifier)

    @isKnownChar: (strainChar) ->
        return strainChar in Strain.ORDERED_CHARS

    @fromChar: (strainChar) ->
        strainIndex = Strain.ORDERED_CHARS.indexOf(strainChar)
        return Strain.STRAINS[strainIndex]


class Suit extends Strain
    constructor: (@name) ->
        if @name not in 'CDHS'
            throw "Unknown Suit " + @name
        super @name

    @SUITS = @STRAINS[0..3]

    @fromChar: (suitChar) ->
        suitIndex = "CDHS".indexOf(suitChar)
        return Suit.SUITS[suitIndex]


class Rank
    constructor: (@name) ->

    displayRank: ->
        if @name is 'T'
            return '10'
        return @name

    index: ->
        '23456789TJQKA'.indexOf(@name)

    highCardPoints: ->
        return {
            A: 4,
            K: 3,
            Q: 2,
            J: 1,
        }[@name] or 0

    @pbnRankFromDisplayRank: (displayRank) ->
        if displayRank is '10'
            return 'T'
        return displayRank

    @_cachedRanks = []

    @fromChar: (rankChar) ->
        rank = @_cachedRanks[rankChar]
        if not rank
            rank = new Rank rankChar
            @_cachedRanks[rankChar] = rank
        return rank


class Card
    constructor: (@suit, @rank) ->

    shortName: ->
        return @rank.name + @suit.name

    highCardPoints: ->
        @rank.highCardPoints()

    identifier: ->
        suitIndex = 'CDHS'.indexOf(@suit.name)
        return suitIndex * 13 + @rank.index()

    @fromIdentifier: (identifier) ->
        suitIndex = Math.floor(identifier / 13)
        cardIndex = identifier - suitIndex * 13
        suitChar = 'CDHS'[suitIndex]
        rankChar = '23456789TJQKA'[cardIndex]
        return @fromShortName(rankChar + suitChar)

    @_cachedCards = []

    @fromShortName: (shortName) ->
        card = @_cachedCards[shortName]
        if not card
            card = new Card Suit.fromChar(shortName[1]), Rank.fromChar(shortName[0])
            @_cachedCards[shortName] = card
        return card

    @fromSuitAndRank: (suit, rank) ->
        return Card.fromShortName rank.name + suit.name


class Call
    constructor: (@name) ->
        if @name.length == 2 and @name != 'XX'
            @level = +@name[0]
            @strain = Strain.fromChar @name[1]

    isBid: ->
        return not @isPass() and not @isDouble() and not @isRedouble()

    isPass: ->
        return @name == 'P'

    isDouble: ->
        return @name == 'X'

    isRedouble: ->
        return @name == 'XX'

    @_cachedCalls = []

    @fromString: (name) ->
        call = @_cachedCalls[name]
        if not call
            call = new Call name
            @_cachedCalls[name] = call
        return call


class Vulnerability
    constructor: (@_identifier) ->
        @_identifier ?= 'NO'

    isVulnerable: (position) ->
        if @_identifier == 'NO'
            return false
        if @_identifier == 'BO'
            return true
        # Position.name should be 'N', 'S', 'E', 'W'.
        return position.name in @_identifier

    identifier: ->
        return @_identifier

    @fromIdentifier: (identifier) ->
        return new Vulnerability identifier

    @fromString: (string) ->
        # FIXME: This is kinda a hack to support QuickTricks recap parsing.
        identifier = {
            'N-S': 'NS',
            'E-W': 'EW',
            'Both': 'BO',
            'None': 'NO'
        }[string]
        return Vulnerability.fromIdentifier identifier

    name: ->
        return {
            NS: 'N-S',
            EW: 'E-W',
            BO: 'Both',
            NO: 'None',
        }[@_identifier]

    @fromBoardNumber: (boardNumber) ->
        # http://www.jazclass.aust.com/bridge/scoring/score11.htm
        # FIXME: There must be a more compact way to represent this series.
        vulnerabilityString = {
            0: 'E-W', # board 16
            1: 'None',
            2: 'N-S',
            3: 'E-W',
            4: 'Both',
            5: 'N-S',
            6: 'E-W',
            7: 'Both',
            8: 'None',
            9: 'E-W',
            10: 'Both',
            11: 'None',
            12: 'N-S',
            13: 'Both',
            14: 'None',
            15: 'N-S',
        }[boardNumber % 16]
        return Vulnerability.fromString(vulnerabilityString)

    toJSON: ->
        return @identifier()


class Hand
    constructor: (@cards) ->
        @cards ?= []

    @fromPBNString: (pbnString) ->
        cards = []
        for cardRanks, suitIndex in pbnString.split('.')
            suitChar = 'CDHS'[suitIndex]
            cards.push.apply cards, (Card.fromShortName(rankChar + suitChar) for rankChar in cardRanks)
        return new Hand cards

    suitLengths: ->
        return (@cardsInSuit(suit).length for suit in Suit.SUITS)

    longestSuits: ->
        longestSuitLength = Math.max.apply(Math, @suitLengths())
        return (suit for suit in Suit.SUITS when @cardsInSuit(suit).length == longestSuitLength)

    cardsInSuit: (suit) ->
        return (card for card in @cards when card.suit.name == suit.name)

    playCard: (card) ->
        cardIndex = @cards.indexOf(card)
        console.assert cardIndex >= 0, "Card " + card.shortName() + " not in hand " + (card.shortName() for card in @cards)
        @cards.splice(cardIndex, 1)

    isBalanced: ->
        doubletonCount = 0
        for suit in Suit.SUITS
            length = @cardsInSuit(suit).length
            if length > 5 or length < 2
                return false
            if length == 2
                doubletonCount += 1
        return doubletonCount < 2

    isRuleOfTwenty: ->
        suitLengths = @suitLengths()
        suitLengths.sort()
        return (suitLengths[3] + suitLengths[2] + @highCardPoints()) >= 20

    highCardPoints: ->
        highCardPoints = 0
        for card in @cards
            highCardPoints += card.highCardPoints()
        return highCardPoints

    highCardPointsInSuit: (suit) ->
        highCardPoints = 0
        for card in @cardsInSuit(suit)
            highCardPoints += card.highCardPoints()
        return highCardPoints

    pbnString: ->
        # JavaScript's String object doesn't have a sort() function, so we have to use arrays.
        rankNamesBySuit = [[], [], [], []]
        for card in @cards
            suitIndex = 'CDHS'.indexOf(card.suit.name)
            rankNamesBySuit[suitIndex].push card.rank.name

        for rankNames in rankNamesBySuit
            rankOrder = "AKQJT98765432"
            rankNames.sort (a, b) =>
                return rankOrder.indexOf(a) - rankOrder.indexOf(b)

        return (rankNames.join('') for rankNames in rankNamesBySuit).join('.')


class Deal
    @_emptyHands: ->
        return (new Hand for index in [0..3])

    @_validate: (hands) ->
        allCards = []
        for hand in hands
            for card in hand.cards
                if card in allCards
                    throw "Duplicate card: " + card.shortName()
                allCards.push card.shortName()
        if allCards.length != 52
            throw "Incorrect number of cards " + allCards.length

    constructor: (@hands)->
        if @hands
            Deal._validate(@hands)
        else
            @hands = Deal._emptyHands()

    # http://en.wikipedia.org/wiki/Fisher-Yates_shuffle
    @_fisherYatesShuffle: (list) ->
        if list.length == 0
            return list
        swap = (list, i, j) ->
            temp = list[i]
            list[i] = list[j]
            list[j] = temp
        for index in [list.length - 1..0]
            swap list, index, Math.floor(Math.random() * (index + 1))
        return list

    @fromJSON: (json) ->
        hands = [
            Hand.fromPBNString(json.north),
            Hand.fromPBNString(json.east),
            Hand.fromPBNString(json.south),
            Hand.fromPBNString(json.west),
        ]
        return new Deal hands

    @random: ->
        # FIXME: A better random would generate a random identifier
        # and use from_identifier.  However our current identifier
        # space is not compact.  We can generate identifiers
        # which are not valid deals.
        hands = @_emptyHands()
        shuffledCards = @_fisherYatesShuffle([0...52])
        for cardIdentifier, deckIndex in shuffledCards
            position = deckIndex % 4  # Give one to each player in turn.
            hands[position].cards.push Card.fromIdentifier(cardIdentifier)
        return new Deal hands

    handForPosition: (position) ->
        return @hands[position.index()]

    # This is not maximally efficient, we could use
    # combinadics to use 96bits instead of 104.

    identifier: ->
        positionForCard = new Array(52)
        for hand, positionIndex in @hands
            for card in hand.cards
                positionForCard[card.identifier()] = positionIndex

        # positionForCard represents a 52-digit number in base 4
        # We're going to split it into 4-digit hunks and convert to base 16.
        identifier = ""
        hexChars = '0123456789abcdef'
        for offset in [0...26]
            # A single hex digit encodes 4 bits where as our previous encoding was 2.
            hexIndex = positionForCard[offset * 2 + 0] * 4 +  positionForCard[offset * 2 + 1]
            identifier += hexChars[hexIndex]
        return identifier

    @fromIdentifier: (identifierString) ->
        if identifierString.length > 29
            return Deal.fromOldIdentifier(identifierString)
        hands = Deal._emptyHands()
        hexChars = '0123456789abcdef'
        for hexChar, charIndex in identifierString
            hexIndex = hexChars.indexOf(hexChar)
            highHandIndex = Math.floor(hexIndex / 4)
            lowHandIndex = hexIndex - highHandIndex * 4
            highCard = Card.fromIdentifier(charIndex * 2 + 0)
            lowCard = Card.fromIdentifier(charIndex * 2 + 1)
            hands[highHandIndex].cards.push highCard
            hands[lowHandIndex].cards.push lowCard
        return new Deal hands


    oldIdentifier: ->
        # We're constructing a 52 digit number in base 4.
        # When converted to a base-10 string it is our identifier.
        identifier = new BigNumber(0)
        four = new BigNumber(4)
        for hand, positionIndex in @hands
            for card in hand.cards
                # Calculate which place in the 52-digit base-4 number we're working with:
                digitPlace = four.pow(card.identifier())
                # The value at that place is 0-3 correponding to the position.
                digitValue = digitPlace.multiply(positionIndex)
                identifier = identifier.add(digitValue)
        return "" + identifier

    @fromOldIdentifier: (identifierString) ->
        identifier = new BigNumber(identifierString)
        hands = Deal._emptyHands()
        four = new BigNumber(4)

        for cardIdentifier in [51..0]
            card = Card.fromIdentifier(cardIdentifier)
            powerOfFour = four.pow(cardIdentifier)
            handIndex = identifier.divide(powerOfFour).intPart()
            identifier = identifier.subtract(powerOfFour.multiply(handIndex))
            hands[handIndex].cards.push card
        return new Deal hands

    toJSON: ->
        return {
            north: @hands[0].pbnString(),
            east: @hands[1].pbnString(),
            south: @hands[2].pbnString(),
            west: @hands[3].pbnString(),
        }


class Board
    constructor: (@number, @deal)->
        @number ?= Math.floor(Math.random() * 16) + 1
        @deal ?= Deal.random()
        # We cache the dealIdentifier so that we can modify the hands during play.
        @cachedDealIdentifier = @deal.identifier()
        # Deal rotates NESW starting North on board 1.
        @dealer = Position.fromChar("WNES"[@number % 4])
        @vulnerability = Vulnerability.fromBoardNumber(@number)

    @random: ->
        return new Board

    identifier: ->
        return @number + "-" + @cachedDealIdentifier

    @fromIdentifier: (identifer) ->
        [number, dealIdentifier] = identifer.split('-')
        return new Board +number, Deal.fromIdentifier(dealIdentifier)

    toJSON: ->
        return {
            number: @number,
            deal: @deal.toJSON(),
            vulnerability: @vulnerability.toJSON(),
            dealer: @dealer.toJSON(),
        }


class Trick
    # Trump?
    constructor: (@leader, @trump, @cards)->
        @cards ?= [null, null, null, null]

    cardPlayedBy: (position) ->
        return @cards[position.index()]

    cardsPlayed: ->
        return (card for card in @cards when card)

    isComplete: ->
        return null not in @cards

    _isNewBestCard: (winningCard, newCard) ->
        if winningCard.suit == newCard.suit
            return winningCard.rank.index() < newCard.rank.index()
        if newCard.suit == @trump
            return true
        # This assumes that best_card was played before new_card thus wins if suits are different.
        return false

    leadCard: ->
        return @cards[@leader.index()]

    leadSuit: ->
        leadCard = @leadCard()
        if leadCard
            return leadCard.suit
        return null

    winner: ->
        winnerIndex = null
        for offset in [0...4]
            positionIndex = (@leader.index() + offset) % 4
            card = @cards[positionIndex]
            if not card
                break
            if winnerIndex == null
                winnerIndex = positionIndex
                continue
            winningCard = @cards[winnerIndex]
            if @_isNewBestCard(winningCard, card)
                winnerIndex = positionIndex

        return Position.fromIndex(winnerIndex)

    nextToPlay: ->
        for offset in [0...4]
            positionIndex = (@leader.index() + offset) % 4
            if not @cards[positionIndex]
                return Position.fromIndex(positionIndex)
        return null

    identifier: ->
        identifierForCard = (card) ->
            if not card
                return 'NP'
            return card.shortName()
        return (identifierForCard(card) for card in @cards).join ''

    @_chunkString = (string, chunkSize) ->
        return string.match new RegExp('.{1,' + chunkSize + '}','g')

    @fromStringAndLeaderAndTrump: (trickString, leader, trump) ->
        cardFromIdentifier = (identifier) ->
            if identifier == 'NP'
                return null
            return Card.fromShortName(identifier)

        cards = (cardFromIdentifier(identifier) for identifier in Trick._chunkString(trickString, 2))
        return new Trick leader, trump, cards

    @emptyWithLeaderAndTrump: (leader, trump) ->
        return new Trick leader, trump


class PlayHistory
    constructor: (@declarer, @trump, @tricks) ->
        @tricks ?= []

    beginPlay: (callHistory) ->
        @declarer = callHistory.declarer()
        @trump = callHistory.contract().strain
        @createNextTrickIfNecessary()

    dummy: ->
        return @declarer.partner()

    isDummyVisible: ->
        return @tricks.length > 1 or (@currentTrick() and @currentTrick().cardsPlayed().length > 0)

    copy: ->
        # FIXME: This is a hack.
        if @isEmpty()
            return PlayHistory.empty()
        return PlayHistory.fromIdentifier(@identifier())

    tricksTakenByPartnershipOf: (position) ->
        tricksTaken = 0
        for trick in @tricks
            if not trick.isComplete()
                break
            winner = trick.winner()
            if winner and position.inPartnershipWith(winner)
                tricksTaken += 1
        return tricksTaken

    nextToPlay: ->
        if @isComplete()
            return null
        if not @isDummyVisible()  # A cheat for checking if this is the first play.
            return @declarer.lho
        if @currentTrick().isComplete()  # This branch should not be necessary.
            return @currentTrick().winner()
        return @currentTrick().nextToPlay()

    isComplete: ->
        return @tricks.length > 12 and @currentTrick().isComplete()

    previousTrick: ->
        # FIXME: Should this return the "last trick" after play is complete?
        if @tricks.length < 2
            return null
        return @tricks[@tricks.length - 2]

    currentTrick: ->
        # FIXME: Should this return null once play is complete?
        return @tricks[@tricks.length - 1]

    playCard: (card) ->
        nextToPlay = @nextToPlay()
        console.assert not @currentTrick()[nextToPlay.index()]
        @currentTrick().cards[nextToPlay.index()] = card
        # Should this automatically move to the next trick?
        @createNextTrickIfNecessary()

    createNextTrickIfNecessary: ->
        if @currentTrick()
            if not @currentTrick().isComplete()
                return
            if @isComplete()
                return
        @tricks.push Trick.emptyWithLeaderAndTrump(@nextToPlay(), @trump)

    isEmpty: ->
        return not @declarer

    identifier: ->
        # We've not been initialized yet, no identifier.
        if @isEmpty()
            return ""
        tricksIdentifier = (trick.identifier() for trick in @tricks).join('')
        return [@declarer.identifier(), @trump.identifier(), tricksIdentifier].join('*')

    @_tricksFromIdentifier: (tricksIdentifier, declarer, trump) ->
        tricks = []
        if not tricksIdentifier
            return tricks
        lastTrick = null
        console.assert (tricksIdentifier.length % 8) == 0
        for trickString in Trick._chunkString(tricksIdentifier, 8)
            leader = if previousTrick then previousTrick.winner() else declarer.lho
            previousTrick = Trick.fromStringAndLeaderAndTrump(trickString, leader, trump)
            tricks.push previousTrick
        return tricks

    @fromIdentifier: (identifier) ->
        [dealerIdentifier, trumpIdentifier, tricksIdentifier] = identifier.split("*")
        declarer = Position.fromChar(dealerIdentifier)
        trump = Strain.fromChar(trumpIdentifier)
        tricks = PlayHistory._tricksFromIdentifier(tricksIdentifier, declarer, trump)
        return new PlayHistory declarer, trump, tricks

    @empty: ->
        return new PlayHistory


class CallHistory
    # FIXME: Should this have @board instead of @dealer?
    constructor: (@calls, @_dealer) ->
        @calls ?= []
        @_dealer ?= Position.NORTH

    lastBid: ->
        if not @calls.length
            return null
        for call in (@calls[i] for i in [@calls.length - 1..0])
            if call.isBid()
                return call
        return null

    canDouble: ->
        if not @lastNonPass() or not @lastNonPass().isBid() or not @nextToCall()
            return false
        return not @nextToCall().inPartnershipWith(@declarer())

    canRedouble: ->
        if not @lastNonPass() or not @lastNonPass().isDouble() or not @nextToCall()
            return false
        return @nextToCall().inPartnershipWith(@declarer())

    _indexOfLastNonPass: ->
        if not @calls.length
            return null
        for index in [@calls.length - 1..0]
            if not @calls[index].isPass()
                return index
        return null

    lastToNotPass: ->
        index = @_indexOfLastNonPass()
        if index == null
            return null
        return @_positionFromCallOffset(index)

    lastNonPass: ->
        index = @_indexOfLastNonPass()
        if index == null
            return null
        return @calls[index]

    _positionFromCallOffset: (offset) ->
        return Position.fromIndex((@_dealer.index() + offset) % 4)

    lastToCall: ->
        if not @calls.length
            return null
        return @_positionFromCallOffset(@calls.length - 1)

    nextToCall: ->
        if @isComplete()
            return null
        return @_positionFromCallOffset(@calls.length)

    indexOfLastCallByPosition: (position) ->
        offsetFromDeclarer = position.offsetFrom(@_dealer)
        multiplier = Math.floor(@calls.length / 4)
        lastCallIndex = multiplier * 4 + offsetFromDeclarer
        if lastCallIndex > @calls.length - 1
            return lastCallIndex - 4
        return lastCallIndex

    callsUpToLastCallByPosition: (position) ->
        return @calls[...@indexOfLastCallByPosition(position)]

    lastCallByPosition: (position) ->
        return @calls[@indexOfLastCallByPosition(position)]

    contract: ->
        if @isPassOut()
            return null
        lastBid = @lastBid()
        if not lastBid?
            return null

        lastNonPass = @lastNonPass()
        doubleString = ''
        if lastNonPass.isDouble()
            doubleString = 'X'
        if lastNonPass.isRedouble()
            doubleString = 'XX'
        return Contract.fromString(lastBid.name + doubleString)

    declarer: ->
        lastBid = @lastBid()
        if not lastBid
            return null
        lastBidIndex = @calls.indexOf(lastBid)
        lastBidder = @_positionFromCallOffset(lastBidIndex)
        for call, callIndex in @calls
            if call.strain == lastBid.strain
                caller = @_positionFromCallOffset(callIndex)
                if caller.inPartnershipWith(lastBidder)
                    return caller
        throw "Error calculating declarer, this should never be reached."

    isEmpty: ->
        return @calls.length == 0

    resetToEmpty: ->
        @calls = []

    isComplete: ->
        if @calls.length <= 3
            return false
        for call in @calls[-3..]
            if not call.isPass()
                return false
        return true

    isPassOut: ->
        return @isComplete() and @calls.length == 4 and @calls[0].isPass()

    callsString: ->
        return (call.name for call in @calls).join(' ')

    hasPrefix: (prefix) ->
        return @callsString().indexOf(prefix.callsString()) == 0

    @fromCallsStringAndDealerChar: (callsString, dealerChar) ->
        if callsString
            calls = callsString.split(' ').map (callName) ->
                return Call.fromString(callName)
        dealer = Position.fromChar(dealerChar)
        return new CallHistory calls, dealer

    identifier: ->
        return (call.name for call in @calls).join(',')

    @fromIdentifier: (identifier) ->
        if identifier == ''
            return new CallHistory
        return new CallHistory (Call.fromString(name) for name in identifier.split(','))

    possibleNextCalls: ->
        possibleCalls = []
        if @isComplete()
            return possibleCalls

        possibleCalls.push Call.fromString('P')

        lastNonPass = @lastNonPass()
        caller = @nextToCall()
        if lastNonPass and @lastToNotPass() != caller.partner()
            if lastNonPass.isBid()
                possibleCalls.push Call.fromString('X')
            else if lastNonPass.isDouble()
                possibleCalls.push Call.fromString('XX')

        lastBid = @lastBid()
        for level in [1..7]
            if lastBid and level < lastBid.level
                continue
            for strain in Strain.STRAINS
                if lastBid and level == lastBid.level and strain.index() <= lastBid.strain.index()
                    continue
                possibleCalls.push Call.fromString("" + level + strain.name)
        return possibleCalls


class Round
    replayHistoryOnBoard: ->
        for trick in @playHistory.tricks
            for card, positionIndex in trick.cards
                if not card
                    continue
                position = Position.fromIndex(positionIndex)
                @board.deal.handForPosition(position).playCard(card)

    playCard: (card) ->
        nextToPlay = @playHistory.nextToPlay()
        @playHistory.playCard(card)
        @board.deal.handForPosition(nextToPlay).playCard(card)

    constructor: (@board, @callHistory, @playHistory) ->
        @board ?= Board.random()
        @callHistory ?= new CallHistory
        # FIXME: This is a hack.  We should probably pass the Board when creating the CallHistory.
        @callHistory._dealer = @board.dealer
        @playHistory ?= PlayHistory.empty()
        # FIXME: Not sure this is the right place to do this.
        if @callHistory.isComplete() and @callHistory.contract()
            @playHistory.trump = @callHistory.contract().strain
            @playHistory.declarer = @callHistory.declarer()
            @replayHistoryOnBoard()

    resetToEmpty: ->
        @callHistory.resetToEmpty()
        @playHistory = PlayHistory.empty()

    toJSON: ->
        return {
            board: @board.toJSON(),
        }

    identifier: ->
        identifier = @board.identifier()
        if not @callHistory.isEmpty()
            identifier += ':' + @callHistory.identifier()
        if @callHistory.isComplete() and not @playHistory.isEmpty()
            identifier += '@' + @playHistory.identifier()
        return identifier

    @emptyWithBoard: (board) ->
        return new Round board

    @fromBoardAndCallHistory: (board, callHistory) ->
        return new Round board, callHistory

    @fromIdentifier: (identifier) ->
        if not identifier
            return null
        if '@' in identifier
            [boardAndCallHistoryIdentifer, playHistoryIdentifer] = identifier.split('@')
            playHistory = PlayHistory.fromIdentifier playHistoryIdentifer
        else
            boardAndCallHistoryIdentifer = identifier

        if ':' in boardAndCallHistoryIdentifer
            [boardIdentifier, callHistoryIdentifer] = boardAndCallHistoryIdentifer.split(':')
            callHistory = CallHistory.fromIdentifier callHistoryIdentifer
        else
            boardIdentifier = boardAndCallHistoryIdentifer

        board = Board.fromIdentifier boardIdentifier
        return new Round board, callHistory, playHistory


class Contract
    constructor: (@name) ->
        @level = +@name[0] # 1-7
        @strain = Strain.fromChar @name[1] # C, D, H, S, N

    @fromString: (string) ->
        return new Contract string

    isDoubled: ->
        # e.g. 1HX
        return @name.length == 3

    isRedoubled: ->
        # e.g. 7SXX
        return @name.length == 4

    isGameOrAbove: ->
        return @strain.gameLevel() <= @level

    isGame: ->
        return @strain.gameLevel() <= @level < 6

    isPartScore: ->
        return @level < @strain.gameLevel()

    isSmallSlam: ->
        return @level == 6

    isGrandSlam: ->
        return @level == 7


window.model = window.model or {}
model = window.model
model.Board = Board
model.Call = Call
model.Card = Card
model.CallHistory = CallHistory
model.Contract = Contract
model.Deal = Deal
model.Hand = Hand
model.PlayHistory = PlayHistory
model.Position = Position
model.Rank = Rank
model.Round = Round
model.Strain = Strain
model.Suit = Suit
model.Vulnerability = Vulnerability
