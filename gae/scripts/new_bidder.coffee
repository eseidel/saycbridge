# TODO:
# - show sp/lp
# - show spinner while bidding/disable clicks
# - Add basic play


isAndroid = navigator.userAgent.toLowerCase().search("android") != -1


class BiddingController
    constructor: (@main, @roundController) ->
        @round = @roundController.round
        @hand = @round.board.deal.handForPosition(@main.position)

    robotIsToCall: ->
        nextToCall = @round.callHistory.nextToCall()
        return nextToCall and nextToCall.name != @main.position.name

    recordCall: (call) ->
        @roundController.recordCall call
        @main.updateView()  # We intentionally do not save the state here.
        @bidAllOtherHands()

    createOption: (name, value) ->
        option = document.createElement 'option'
        option.value = value or name
        option.textContent = name
        return option

    createDealSelector: (selectedName, changeFunction) ->
        dealSelectDiv = document.createElement 'div'
        dealSelectDiv.className = 'dealselect'
        dealSelectDiv.appendChild document.createTextNode "deal: "
        dealSelect = document.createElement 'select'
        dealSelect.appendChild @createOption('random', 'random')
        dealSelect.appendChild @createOption('notrump hands', 'notrump')
        dealSelect.appendChild @createOption('preempts', 'preempts')
        dealSelect.appendChild @createOption('2c opens', 'twoclub')
        $('option', dealSelect).each (index, option) =>
            if option.value == selectedName
                option.selected = "1"

        $(dealSelect).change changeFunction
        dealSelectDiv.appendChild dealSelect
        return dealSelectDiv

    _createBackButton: ->
        backButton = document.createElement 'div'
        $(backButton).addClass('back')
        $(backButton).addClass('button')
        backButton.textContent = 'back'
        $(backButton).click (event) =>
            window.history.back()
            event.preventDefault()
        return backButton

    setupView: ->
        @main.setTitle "Bidding Practice"

        content = document.body

        @historyTable = view.CallHistoryTable.fromBoardAndHistory(@round.board, @round.callHistory, @robotIsToCall())
        $(@historyTable, 'a').bind 'click', (event) ->
            if window._gaq
                window._gaq.push ['_trackEvent', 'Bidding', 'Help', "Explain Bid"]
        content.appendChild @historyTable
        content.appendChild document.createElement 'hr'

        @handView = view.CardHandView.fromHand(@hand)
        content.appendChild @handView
        content.appendChild document.createElement 'hr'

        @biddingBox = view.BiddingBox.fromHistoryAndCallFunction @round.callHistory, (call) =>
            @recordCall call

        content.appendChild @biddingBox
        content.appendChild document.createElement 'hr'

        @suggestBidBox = view.SuggestBidBox.fromRoundController(@roundController)
        $(@suggestBidBox, 'a').bind 'click', (event) ->
            if window._gaq
                window._gaq.push ['_trackEvent', 'Bidding', 'Help', "Suggest Bid"]
        content.appendChild @suggestBidBox

        @skipHandLink = @main.createNextHandLink('skip hand', 'skiphand')
        content.appendChild @skipHandLink

        @rebidHandLink = @main.createRebidHandLink('rebid')
        content.appendChild @rebidHandLink

        # If we're a Safari Web Clip, we should have our own back button.
        if window.navigator.standalone
            @backLink = @_createBackButton()
            content.appendChild @backLink

        @dealSelect = @createDealSelector @main.boardDealer.filterName, (event) =>
            option = $("option:selected", event.target)[0]
            @main.setDealFilterAndRedeal(option.value)

        content.appendChild @dealSelect

        if @robotIsToCall()
            @bidAllOtherHands()
        else
            # If it's the human's turn, we save our state so they
            # can come back to to the start of this board if needed.
            @main.saveState()

        # Pre-load the request for the full autobid, even though we won't need it yet.
        @roundController.requestFullAutobid null

    updateView: ->
        @historyTable.updateFromCallHistory(@round.callHistory, @robotIsToCall())
        @biddingBox.updateFromCallHistory(@round.callHistory)

    bidAllOtherHands: ->
        # FIXME: We want some sort of notification from RoundController
        # every time a bid is added.  For now we're hackishly hiding any shown
        # hint here.
        @suggestBidBox.hideSuggestion()

        @roundController.bidAllOtherHands @main.position, =>
            @main.saveState()
            # This updateView is needed to make the rebidHand link work.
            @updateView()


class BiddingResultsController
    constructor: (@main, @roundController) ->
        @round = @roundController.round

    setupView: ->
        @main.setTitle "Bidding Results"
        content = document.body

        @historyTable = view.CallHistoryTable.fromBoardAndHistory(@round.board, @round.callHistory)
        $(@historyTable, 'a').bind 'click', (event) ->
            if window._gaq
                window._gaq.push ['_trackEvent', 'Bidding', 'Help', "Explain Bid"]
        content.appendChild @historyTable

        @autobidResult = view.AutobidResult.fromRoundController(@roundController)
        content.appendChild @autobidResult
        content.appendChild document.createElement 'hr'

        @dealView = view.DealView.fromDeal(@round.board.deal)
        content.appendChild @dealView

        @nextHandLink = @main.createNextHandLink('next hand', 'nexthand')
        content.appendChild @nextHandLink
        content.appendChild document.createElement 'hr'

        @dealStats = view.DealStats.fromDeal(@round.board.deal)
        content.appendChild @dealStats
        content.appendChild document.createElement 'hr'

        @rebidHandLink = @main.createRebidHandLink('rebid')
        content.appendChild @rebidHandLink

        @unittestsView = view.DebugInfo.fromRound(@round)
        content.appendChild @unittestsView

    updateView: ->
        # This view is non-interactive, no?


class PlayController
    constructor: (@main, @roundController) ->
        @roundController.beginPlay() # Copies the declarer and contract from bidHistory to playHistory.
        @round = @roundController.round

    robotIsToPlay: ->
        nextToPlay = @round.playHistory.nextToPlay()
        if not nextToPlay
            return false
        return nextToPlay not in @humanPositions()

    humanPositions: ->
        if @main.position.inPartnershipWith(@round.playHistory.declarer)
            return [@main.position, @main.position.partner()]
        return [@main.position]

    playCard: (card) ->
        @round.playCard card
        @main.updateView()  # We intentionally do not save state here.
        @roundController.playAllOtherHands @humanPositions(), =>
            @main.saveState()

    setupView: ->
        @main.setTitle "Play"

        content = document.body

        @historyTable = view.CallHistoryTable.fromBoardAndHistory(@round.board, @round.callHistory)
        content.appendChild @historyTable
        @playStats = view.PlayStats.fromRound @round
        content.appendChild @playStats

        @playTable = view.PlayTable.fromRound @round
        #@playTable.showAllHands() # For debugging.
        content.appendChild @playTable

        @lastTrick = view.LastTrickView.fromPlayHistory @round.playHistory
        content.appendChild @lastTrick

        if @robotIsToPlay()
            @roundController.playAllOtherHands @humanPositions(), =>
                @main.saveState()
        else
            # If we aren't sending off a play request to the server, we still need to update.
            # This handles the case where we're supposed to lead on load.
            @updateView()

    updateView: ->
        @playTable.updateView()
        @lastTrick.updateView()
        @playStats.updateView()

        if @round.playHistory.isComplete() and @playTable.parentNode
            content = @playTable.parentNode
            originalDeal = model.Deal.fromIdentifier @round.board.cachedDealIdentifier
            @dealView = view.DealView.fromDeal(originalDeal)
            @dealStats = view.DealStats.fromDeal(originalDeal)
            content.replaceChild(@dealStats, @playTable)
            content.insertBefore(@dealView, @dealStats)

            @trickList = view.TrickList.fromPlayHistory(@round.playHistory)
            content.replaceChild @trickList, @lastTrick
            @scoreView = view.ScoreView.fromRound(@round)

            @nextHandLink = @main.createNextHandLink('next hand', 'nexthand')
            content.appendChild @nextHandLink
            @unittestsView = view.DebugInfo.fromRound(@round)
            content.appendChild @unittestsView

        $('.rank', @playTable).bind 'click', (event) =>
            event.preventDefault()
            rankView = event.target
            while rankView and not rankView.rank
                rankView = rankView.parentNode
            suitGroup = rankView.parentNode
            positionView = suitGroup.parentNode
            while positionView and not positionView.position
                positionView = positionView.parentNode
            if positionView.position != @round.playHistory.nextToPlay()
                # We should beep
                alert "It is " + @round.playHistory.nextToPlay().displayName()  + "'s turn to play."
                return
            card = model.Card.fromSuitAndRank suitGroup.suit, rankView.rank
            @playCard(card)


class BoardDealer
    constructor: (@filterName) ->
        @filtersByName = {
            twoclub: (board) ->
                hand = board.deal.handForPosition(model.Position.SOUTH)
                return hand.highCardPoints() >= 22
            notrump: (board) ->
                hand = board.deal.handForPosition(model.Position.SOUTH)
                return hand.highCardPoints() in [15..25] and hand.isBalanced()
            preempts: (board) ->
                hand = board.deal.handForPosition(model.Position.SOUTH)
                if hand.isRuleOfTwenty()
                    return false
                for length in hand.suitLengths()
                    if length >= 6
                        return true
                return false
        }

    setFilter: (@filterName) ->
        

    newBoard: ->
        filter = @filtersByName[@filterName]
        while true
            board = model.Board.random()
            if not filter or filter(board)
                return board


class MainController
    constructor: ->
        # The about text is static to make it most accessible to search engines.
        @aboutDiv = document.getElementById('about')

        @position = model.Position.SOUTH # FIXME: Should read this from the URL.
        @boardDealer = new BoardDealer

        [@basePath, round] = @basePathAndRoundFromPath(window.location.pathname)
        if not round
            round = model.Round.emptyWithBoard(@boardDealer.newBoard())
            @initialLoadFromBaseURL = true

        @basePath = @cannonicalizeBasePath @basePath
        @practiceBidding = @isPracticeBiddingBasePath @basePath

        @roundController = controller.RoundController.fromRound(round)
        @preloadNextBoard()

    isPracticeBiddingBasePath: (basePath) ->
        return basePath != "/play"

    cannonicalizeBasePath: (basePath) ->
        if basePath == "/play"
            return basePath
        return "/bid"

    setTitle: (title) ->
        document.title = title + " - SAYC Bridge"

    basePathAndRoundFromPath: (path) ->
        pathWithoutLeadingSlash = path[1..]
        if '/' in pathWithoutLeadingSlash
            [basePath, roundIdentifier] = pathWithoutLeadingSlash.split('/')
            basePath = "/" + basePath
            round = model.Round.fromIdentifier roundIdentifier
        else
            basePath = path
            round = null
        return [basePath, round]

    bidPathForRound: (round) ->
        return @basePath + '/' + round.identifier()

    createRebidHandLink: (className) ->
        rebidHandLink = document.createElement 'div'
        $(rebidHandLink).addClass('button')
        $(rebidHandLink).addClass(className)
        currentPath = @bidPathForRound @roundController.round
        rebidPath = currentPath.split(':')[0]  # FIXME: This is a hack depending on knowledge of round identfiers.
        rebidHandLink.href = rebidPath
        rebidHandLink.textContent = "rebid hand"
        $(rebidHandLink).bind 'click', (event) =>
            @reloadBoardWithEmptyBidding()
            if window._gaq
                window._gaq.push ['_trackEvent', 'Bidding', 'Boards', 'rebid board']
            event.preventDefault()
        return rebidHandLink

    reportError: (message) ->
        # We should XHR the error information back to the server.
        console.log("ERROR: " + message)

    preloadNextBoard: ->
        if @nextRoundController
            return
        board = @boardDealer.newBoard()
        @nextRoundController = controller.RoundController.newWithBoard(board)
        @nextRoundController.requestFullAutobid null

    reloadBoardWithEmptyBidding: ->
        @roundController.round.resetToEmpty()
        @setupView()

    setDealFilterAndRedeal: (filterName) ->
        @boardDealer.setFilter filterName
        @nextRoundController = null
        @loadNewBoard()

    loadNewBoard: ->
        if @nextRoundController
            @roundController = @nextRoundController
            @nextRoundController = null
        else
            board = @boardDealer.newBoard()
            @roundController = controller.RoundController.newWithBoard(board)

        @preloadNextBoard()
        @setupView()

    createNextHandLink: (textContent, className) ->
        nextHandLink = document.createElement 'div'
        $(nextHandLink).addClass('button')
        $(nextHandLink).addClass(className)
        nextHandLink.href = @basePath
        nextHandLink.textContent = textContent
        $(nextHandLink).bind 'click', (event) =>
            @loadNewBoard()
            if window._gaq
                window._gaq.push ['_trackEvent', 'Bidding', 'Boards', textContent]
            event.preventDefault()
        return nextHandLink

    saveState: ->
        urlForCurrentState = @bidPathForRound @roundController.round
        # If we already have a history entry for the current URL, no need to save.
        if window.location.pathname == urlForCurrentState
            @reportError "Ignoring request to make duplicate history entry."
            return

        state = { 'roundIdentifier': @roundController.round.identifier() }
        if @initialLoadFromBaseURL
            # We use replaceState to avoid the back button taking users to a new random board.
            window.History.replaceState state, "", urlForCurrentState
            @initialLoadFromBaseURL = false
        else
            window.History.pushState state, "", urlForCurrentState

    updateFromState: (state) ->
        urlParser = document.createElement 'a'
        urlParser.href = state.url
        urlParser.pathname

        [basePath, newRound] = @basePathAndRoundFromPath(urlParser.pathname)
        if not newRound
            @reportError "null round from " + urlParser.path
            return

        # If this is a state change not caused by our saveState calls, do a full update.
        if newRound.identifier() != @roundController.round.identifier()
            @roundController = controller.RoundController.fromRound(newRound)
            # FIXME: This will leave the wrong @nextRoundController, no?
            @setupView()
            return

        controllerClass =  @phaseControllerClassFromBasePathAndRound @basePath, @roundController.round
        if @phaseController.constructor != controllerClass
            # Such as clicking next from http://localhost:8080/bid/1-b473bc774f4835a9882c5cea19:P,P
            @setupView()
        else
            @updateView()

    phaseControllerClassFromBasePathAndRound: (basePath, round) ->
        # Scenerios:
        # 1.  Bidding Practice
        # - bidding
        # - done bidding, show hands
        # 2. Play
        # - bidding
        # - play
        # - done play, show hands and score
        if round.callHistory.isComplete()
            if @isPracticeBiddingBasePath basePath
                return BiddingResultsController
            return PlayController
        return BiddingController

    phaseControllerClassForPath: (path) ->
        [basePath, round] = @basePathAndRoundFromPath path
        return @phaseControllerClassFromBasePathAndRound basePath, round

    setupView: ->
        $(document.body).empty()

        phaseControllerClass = @phaseControllerClassFromBasePathAndRound @basePath, @roundController.round
        @phaseController = new phaseControllerClass @, @roundController
        @phaseController.setupView()

        # Hack to make the scrollbar disappear on android.
        # We want to reset the user to the top of the screen anytime we're loading a new board.
        window.setTimeout('window.scrollTo(0, 1)', 0)

        document.body.appendChild @aboutDiv

    updateView: ->
        @phaseController.updateView()


$ ->
    window.mainController = new MainController
    window.mainController.setupView()

    History.Adapter.bind window, 'statechange', (event) ->
        # FIXME: We are losing the "next board" state when going backwards...
        window.mainController.updateFromState(History.getState())
