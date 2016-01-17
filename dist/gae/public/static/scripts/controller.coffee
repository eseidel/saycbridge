class ErrorReporter
    @suppressAlerts = false

    @reportError: (errorText) ->
        console.log errorText
        if window._gaq
            window._gaq.push ['_trackEvent', 'General', 'Errors', 'error']

    @alertError: (alertText) ->
        if @suppressAlerts
            return
        alert(alertText)


$(window).bind 'beforeunload', (event) =>
    ErrorReporter.suppressAlerts = true
    return null


class Autobidder
    @autobidURL = "/json/autobid"

    @updateInterpreterCache: (board, callHistory, interpretedCalls) ->
        firstInterpretedIndex = callHistory.calls.length - interpretedCalls.length
        console.assert firstInterpretedIndex >= 0, "Invalid firstInterpretedIndex", firstInterpretedIndex, "for", callHistory, interpretedCalls
        for interpretationTuple, interpretationIndex in interpretedCalls
            callsIndex = firstInterpretedIndex + interpretationIndex
            calls = callHistory.calls[0..callsIndex]
            interpretation = Interpretation.fromBoardAndCallsAndJSONTuple(board, calls, interpretationTuple)
            BidInterpreter.cache.storeByBoardAndCalls(board, calls, interpretation)

    @bidAllHands: (board, callback) ->
        jqxhr = $.getJSON Autobidder.autobidURL, board.toJSON(), (data, textStatus, jqXHR) =>
            if board.number != data['board_number']
                throw "Invalid response from server" + data['board_number'] + " != " + board.number
            callHistory = model.CallHistory.fromCallsStringAndDealerChar(data['calls_string'], board.dealer.name)
            Autobidder.updateInterpreterCache(board, callHistory, data['autobid_interpretations'])
            callback(board, callHistory)
        jqxhr.error (jqXHR, textStatus, errorThrown) =>
            ErrorReporter.reportError("Error autobidding board: " + board.identifier())
            ErrorReporter.alertError("Sorry there has been an error communicating with the bidding server.  Please skip to the next hand.")

    @bidHandsUntil: (board, callHistory, stopPosition, callback) ->
        boardJSON = board.toJSON()
        boardJSON['calls_string'] = callHistory.callsString()
        boardJSON['until_position'] = stopPosition.name

        if document.location.hostname == "localhost"
            boardJSON['cache_bust'] = new Date

        jqxhr = $.getJSON Autobidder.autobidURL, boardJSON, (data, textStatus, jqXHR) =>
            console.assert board.number == data['board_number']
            callHistory = model.CallHistory.fromCallsStringAndDealerChar(data['calls_string'], board.dealer.name)
            autobidContinuation = model.CallHistory.fromCallsStringAndDealerChar(data['autobid_continuation'], board.dealer.name)
            Autobidder.updateInterpreterCache(board, autobidContinuation, data['autobid_interpretations'])
            callback(board, callHistory, autobidContinuation)
        jqxhr.error (jqXHR, textStatus, errorThrown) =>
            ErrorReporter.reportError("Error autobidding board: " + board.identifier())
            ErrorReporter.alertError("Sorry there has been an error communicating with the bidding server.  Please skip to the next hand.")


class Interpretation
    constructor: (@board, @calls, @callName, @ruleName, @constraintsString, @explanation, @rulePriority, @saycPage) ->


    @fromBoardAndCallsAndJSONDict: (board, calls, json) ->
        return new Interpretation board, calls, json['call_name'], json['rule_name'], json['knowledge_string'], json['explanation'], json['priority'], json['sayc_page']

    @fromBoardAndCallsAndJSONTuple: (board, calls, jsonTuple) ->
        [bidName, ruleName, constraintsString, explanation, priority, saycPage] = jsonTuple
        callName = '?'
        return new Interpretation board, calls, callName, ruleName, constraintsString, explanation, priority, saycPage


class InterpretationCache
    constructor: ->
        @_cache = {}

    _identifierFromBoardAndCalls: (board, calls) ->
        # FIXME: This could just use vulernabilty and dealer, instead of the full board identifier.
        return board.identifier() + ':' + (call.name for call in calls).join(',')

    lookupByBoardAndCalls: (board, calls) ->
        identifier = @_identifierFromBoardAndCalls(board, calls)
        return @_cache[identifier]

    storeByBoardAndCalls: (board, calls, interpretation) ->
        identifier = @_identifierFromBoardAndCalls(board, calls)
        cachedInterpretation = @_cache[identifier]
        if cachedInterpretation
            console.log "WARNING: Re-caching interpretation for", identifier
            console.assert cachedInterpretation.constraintsString == interpretation.constraintsString, "Invalid cache?", cachedInterpretation, interpretation
        @_cache[identifier] = interpretation


class BidInterpreter
    @interpretURL = "/json/interpret"
    @interpret2URL = "/json/interpret2"
    @cache = new InterpretationCache

    @cachedInterpretationForLastCallInCallsFromBoard: (calls, board) ->
        return BidInterpreter.cache.lookupByBoardAndCalls(board, calls)

    @interpretLastCallInCallsFromBoard: (calls, board, callback) ->
        interpretation = BidInterpreter.cache.lookupByBoardAndCalls(board, calls)
        if interpretation
            return callback(calls, interpretation)

        requestJSON = {
            'calls_string': (call.name for call in calls).join(','),
            'dealer': board.dealer.name,
            'vulnerability': board.vulnerability.name(),
        }
        if document.location.hostname == "localhost"
            requestJSON['cache_bust'] = new Date

        jqxhr = $.getJSON BidInterpreter.interpretURL, requestJSON, (data, textStatus, jqXHR) =>
            interpretation = Interpretation.fromBoardAndCallsAndJSONDict(board, calls, data)
            BidInterpreter.cache.storeByBoardAndCalls(board, calls, interpretation)
            callback(calls, interpretation)
        jqxhr.error (jqXHR, textStatus, errorThrown) =>
            ErrorReporter.reportError("Error interpreting bids for board: " + board.identifier())
            ErrorReporter.alertError("Sorry there has been an error communicating with the bidding server.  Please skip to the next hand.")

     @interpretNextCallsFromCallsAndBoard: (calls, board, callback) ->
        # FIXME: Add caching
        requestJSON = {
            'calls_string': (call.name for call in calls).join(','),
            'dealer': board.dealer.name,
            'vulnerability': board.vulnerability.name(),
            'revision': bidder_revision,
        }
        if document.location.hostname == "localhost"
            requestJSON['cache_bust'] = new Date

        jqxhr = $.getJSON BidInterpreter.interpret2URL, requestJSON, (data, textStatus, jqXHR) =>
            interpretations = (Interpretation.fromBoardAndCallsAndJSONDict(board, calls, jsonDict) for jsonDict in data)
            callback(interpretations)
        jqxhr.error (jqXHR, textStatus, errorThrown) =>
            ErrorReporter.reportError("Error interpreting bids for board: " + board.identifier())
            ErrorReporter.alertError("Sorry there has been an error communicating with the bidding server.  Please skip to the next hand.")


class Autoplay
    constructor: (useRemote) ->
        @useRemove = useRemote

    _otherVisiblePosition: (playHistory) ->
        if playHistory.nextToPlay() == playHistory.dummy()
            return playHistory.declarer

        if playHistory.isDummyVisible()
            return playHistory.dummy()
        return null

    _localPlayHandsUntil: (round, stopPositions, callback) ->
        newPlayHistory = round.playHistory.copy()
        selector = new play.PlaySelector(round.bidHistory, round.board.vulnerability)

        while newPlayHistory.nextToPlay()
            if newPlayHistory.nextToPlay() in stopPositions
                break

            hand = round.board.deal.handForPosition(newPlayHistory.nextToPlay())

            otherPosition = @_otherVisiblePosition(newPlayHistory)
            otherHand = if otherPosition then round.board.deal.handForPosition(otherPosition) else null

            cardToPlay = selector.selectNextCard(hand, otherHand, newPlayHistory)
            newPlayHistory.playCard(cardToPlay)

        callback(round, newPlayHistory)

    _remotePlayHandsUntil: (round, stopPositions, callback) ->


    playHandsUntil: (round, stopPositions, callback) ->
        # Things that the player should be told:
        # Hand to be played
        # Dummy's hand (if visible)
        # Played cards (including where they came from)

        if @useRemove
            @_remotePlayHandsUntil(round, stopPositions, callback)
        else
            @_localPlayHandsUntil(round, stopPositions, callback)


class ScoreCalculator
    @penaltyMap: (contract, vulnerable) ->
        if vulnerable
            if contract.isDoubled()
                return [200, 300]
            if contract.isRedoubled()
                return [400, 600]
            return [100]
        if contract.isDoubled()
            return [100, 200, 200, 300]
        if contract.isRedoubled()
            return [200, 400, 400, 600]
        return [50]

    @penaltyForUndertrick: (contract, vulnerable, undertrickNumber) ->
        console.assert undertrickNumber > 0
        penaltyMap = @penaltyMap(contract, vulnerable)
        # Use whatever the last penalty is for all additional undertricks.
        # undertrickNumber is 1-based.
        return penaltyMap[Math.min(undertrickNumber, penaltyMap.length) - 1]

    @penaltyForUndertricks: (contract, vulnerable, undertrickCount) ->
        penalty = 0
        for undertrickIndex in [1..undertrickCount]
            penalty += @penaltyForUndertrick(contract, vulnerable, undertrickIndex)
        return penalty

    @contractPoints: (contract) ->
        pointsPerLevel = if contract.strain.isMinor() then 20 else 30
        doubleMultiplier = 1
        if contract.isDoubled()
            doubleMultiplier = 2
        else if contract.isRedoubled()
            doubleMultiplier = 4
        notrumpBonus = if contract.strain.isNotrump() then 10 else 0
        return (pointsPerLevel * contract.level + notrumpBonus) * doubleMultiplier

    @levelBonus: (contract, vulnerable) ->
        if contract.isGrandSlam()
            return if vulnerable then 2000 else 1300
        if contract.isSmallSlam()
            return if vulnerable then 1250 else 800
        if @contractPoints(contract) >= 100  # "game" is defined as any contract worth more than 100 points.
            return if vulnerable then 500 else 300
        # Otherwise the partscore bonus is always 50.
        return 50

    @doubleBonus: (contract) ->
        if contract.isRedoubled()
            return 100
        if contract.isDoubled()
            return 50
        return 0

    @overtrickMultiplier: (contract, vulnerable) ->
        if contract.isDoubled() or contract.isRedoubled()
            redoubleMultiplier = if contract.isRedoubled() then 2 else 1
            vulnerableMultiplier = if vulnerable then 2 else 1
            return 100 * redoubleMultiplier * vulnerableMultiplier
        # Otherwise we just get the normal points per level.
        return if contract.strain.isMinor() then 20 else 30

    @overtrickBonus: (overtrickCount, contract, vulnerable) ->
        return overtrickCount * @overtrickMultiplier(contract, vulnerable)

    @northSouthScoreFor: (contract, vulnerable, contractOffset, declarer) ->
        declarerScore = @scoreFor(contract, vulnerable, contractOffset)
        return if declarer in [model.Position.NORTH, model.Position.SOUTH] then declarerScore else -declarerScore

    @northSouthScoreForRound: (round) ->
        if round.callHistory.isPassOut()
            return 0
        declarer = round.callHistory.declarer()
        contract = round.callHistory.contract()
        vulnerable = round.board.vulnerability.isVulnerable(declarer)
        contractOffset = round.playHistory.tricksTakenByPartnershipOf(declarer) - contract.level - 6
        return @northSouthScoreFor(contract, vulnerable, contractOffset, declarer)

    @scoreFor: (contract, vulnerable, contractOffset) ->
        if contractOffset < 0
            defenderScore = @penaltyForUndertricks(contract, vulnerable, -contractOffset)
            return -defenderScore

        declarerScore = @contractPoints(contract) + @levelBonus(contract, vulnerable) +
            @doubleBonus(contract) + @overtrickBonus(contractOffset, contract, vulnerable)
        return declarerScore


# Wraps a Round model object and manages effemeral state and callbacks.
class RoundController
    constructor: (@round) ->
        @position = model.Position.SOUTH  # FIXME: This is a hack.
        @_autobidContinuationCallbacks = []
        @_fullAutobidCallbacks = []

    _replaceCalls: (calls) ->
        @round.callHistory.calls = calls

    recordCall: (call) ->
        @round.callHistory.calls.push call

    requestFullAutobid: (callback) ->
        if @fullAutobid
            if callback
                callback(@fullAutobid)
            return

        if callback
            @_fullAutobidCallbacks.push callback
        Autobidder.bidAllHands @round.board, (board, fullAutobid) =>
            @_updateFullAutobid(fullAutobid)

    _updateFullAutobid: (fullAutobid) ->
        console.assert not @fullAutobid, "Replacing existing full autobid?"
        @fullAutobid = fullAutobid
        # If we happen to be on the auto-bid path, we can also update our autobidContinuation
        if @fullAutobid.hasPrefix(@round.callHistory)
            if @autobidContinuation
                console.assert @fullAutobid.callsString() == @autobidContinuation.callsString()
            @_updateAutobidContinuation(@fullAutobid)

        callback(@fullAutobid) while callback = @_fullAutobidCallbacks.pop()

    _updateAutobidContinuation: (autobidContinuation) ->
        @autobidContinuation = autobidContinuation
        callback(@autobidContinuation) while callback = @_autobidContinuationCallbacks.pop()

    requestAutobidContinuation: (callback) ->
        if @autobidContinuation
            if callback
                callback(@autobidContinuation)
            return

        if callback
            @_autobidContinuationCallbacks.push callback

        # This should rarely be hit, autobidContinuation is populated as part of bidAllOtherHands.
        Autobidder.bidHandsUntil @round.board, @round.callHistory, @position, (board, callHistory, autobidContinuation) =>
            @_updateAutobidContinuation(autobidContinuation)

    bidAllOtherHands: (untilPosition, callback) ->
        if @autobidContinuation and @autobidContinuation.hasPrefix(@round.callHistory)
            # Our current bid string matches what the autobidder expects, we don't even need to talk to the server.
            nextToCall = @round.callHistory.nextToCall()
            # If the bidding is complete, we have nothing to do.
            if nextToCall
                bidsNeeded = untilPosition.offsetFrom(nextToCall)
                newCalls = @autobidContinuation.calls[...@round.callHistory.calls.length + bidsNeeded]  # FIXME: This should respect position.
                @_replaceCalls(newCalls)
            callback()
            return

        Autobidder.bidHandsUntil @round.board, @round.callHistory, untilPosition, (board, callHistory, autobidContinuation) =>
            @_replaceCalls(callHistory.calls)
            @_updateAutobidContinuation(autobidContinuation)
            callback()

    beginPlay: ->
        @round.playHistory.beginPlay(@round.callHistory)

    _replaceTricks: (tricks) ->
        @round.playHistory.tricks = tricks

    playAllOtherHands: (untilPositions, callback) ->
        autoplay = new Autoplay
        autoplay.playHandsUntil @round, untilPositions, (round, playHistory) =>
            @_replaceTricks(playHistory.tricks)
            callback()

    @newWithBoard: (board) ->
        round = model.Round.emptyWithBoard(board)
        return new RoundController round

    @fromRound: (round) ->
        return new RoundController round


window.controller = window.controller or {}
controller = window.controller
controller.Autobidder = Autobidder
controller.Autoplay = Autoplay
controller.BidInterpreter = BidInterpreter
controller.RoundController = RoundController
controller.ScoreCalculator = ScoreCalculator

