HTMLAnchorElement.prototype.htmlTag = 'a'
HTMLButtonElement.prototype.htmlTag = 'button'
HTMLDivElement.prototype.htmlTag = 'div'
HTMLImageElement.prototype.htmlTag = 'img'
HTMLPreElement.prototype.htmlTag = 'pre'
HTMLTableCellElement.prototype.htmlTag = 'td'
HTMLTableElement.prototype.htmlTag = 'table'
HTMLTableRowElement.prototype.htmlTag = 'tr'


# FIXME: These ugly hacks are to support both FF and Chrome.
# Need to find a nicer way to write these.
if window.HTMLSpanElement
    HTMLSpanElement = window.HTMLSpanElement
    HTMLSpanElement.prototype.htmlTag = 'span'
else
    class HTMLSpanElement extends HTMLElement
        htmlTag: 'span'


if window.HTMLCodeElement
    HTMLCodeElement = window.HTMLCodeElement
    HTMLCodeElement.prototype.htmlTag = 'code'
else
    class HTMLCodeElement extends HTMLElement
        htmlTag: 'code'


# FIXME: alloc should move onto a View baseclass..
alloc = (constructor, args...) ->
   element = document.createElement constructor.prototype.htmlTag
   element.__proto__ = constructor.prototype
   constructor.apply element, args
   return element


class WaitingImage extends HTMLImageElement
    constructor: ->
        @src = '/images/spinner.gif'

    @new: ->
        return alloc @


class SuitView extends HTMLSpanElement
    constructor: (@suit) ->
        $(@).addClass 'suit'
        $(@).addClass @cssClass()
        @textContent = @displayString()

    cssClass: ->
        return {
            C: 'clubs',
            D: 'diamonds',
            H: 'hearts',
            S: 'spades',
        }[@suit.name]

    displayString: ->
        return {
            C: '\u2663',
            D: '\u2666',
            H: '\u2665',
            S: '\u2660',
        }[@suit.name]

    @fromSuit: (suit) ->
        return alloc @, suit


class StrainView extends SuitView
    constructor: (@strain) ->
        @suit = @strain # So that SuitView doesn't get confused.
        $(@).addClass 'strain'
        $(@).addClass @cssClass()
        @textContent = @displayString()

    cssClass: ->
        if @strain.name == 'N'
            return 'notrump'
        return super

    displayString: ->
        if @strain.name == 'N'
            return 'NT'
        return super

    @fragmentReplacingStrainChars: (string) ->
        fragment = document.createDocumentFragment()
        currentSubstring = ''
        for char in string
            # FIXME: This is a horrible hack for the explorer page which uses "4rS" and expects the "S" not to be replaced.
            if model.Strain.isKnownChar(char) and currentSubstring and currentSubstring[currentSubstring.length-1].match /[-+0-9]/
                if currentSubstring
                    fragment.appendChild document.createTextNode(currentSubstring)
                    currentSubstring = ''
                fragment.appendChild StrainView.fromStrain(model.Strain.fromChar(char))
                continue
            currentSubstring += char
        if currentSubstring
            fragment.appendChild document.createTextNode(currentSubstring)
        return fragment

    @fromStrain: (strain) ->
        return alloc @, strain


class RankView extends HTMLSpanElement
    constructor: (@rank) ->
        @className = 'rank'
        @textContent = @rank.displayRank()

    @fromRank: (rank) ->
        return alloc @, rank


class CardView extends HTMLDivElement
    constructor: (@card) ->
        @className = 'card'
        @appendChild RankView.fromRank(@card.rank)
        @appendChild SuitView.fromSuit(@card.suit)

    @fromCard: (card) ->
        return alloc @, card


class SuitGroup extends HTMLDivElement
    constructor: (@suit, @ranks) ->
        $(@).addClass 'suitgroup'
        $(@).addClass @cssClass()
        rankOrder = "AKQJT98765432"
        @ranks.sort (a, b) =>
            return  rankOrder.indexOf(a.name) - rankOrder.indexOf(b.name)
        for rank in @ranks
            @appendChild RankView.fromRank(rank)

    cssClass: ->
        return {
            C: 'clubs',
            D: 'diamonds',
            H: 'hearts',
            S: 'spades',
        }[@suit.name]

    @fromCardsWithSuit: (cards, suit) ->
        ranks = (card.rank for card in cards)
        return alloc @, suit, ranks


class HandStats extends HTMLDivElement
    constructor: (@hand) ->
        @className = 'handstats'
        @appendChild document.createTextNode "" + @hand.highCardPoints() + " hcp"

    @fromHand: (hand) ->
        return alloc @, hand


class BiddingHandView extends HTMLDivElement
    constructor: (@hand) ->
        @className = 'biddinghand'
        @appendChild ListHandView.fromHand @hand
        @appendChild HandStats.fromHand(@hand)

    @fromHand: (hand) ->
        return alloc @, hand


class HandView extends HTMLDivElement
    constructor: (@hand, @sortOrder) ->
        @className = 'hand'
        @sortOrder ?= "SHDC"
        for suitChar in @sortOrder
            suit = model.Suit.fromChar suitChar
            @appendChild SuitGroup.fromCardsWithSuit(@hand.cardsInSuit(suit), suit)

    @fromHand: (hand) ->
        return alloc @, hand


class ListHandView extends HandView
    constructor: (hand) ->
        super hand
        $(@).addClass 'listhand'

    @fromHand: (hand) ->
        return alloc @, hand


class CardHandView extends HandView
    constructor: (hand) ->
        sortOrder = "DCHS"
        if hand.suitLengths()[0] == 0
            sortOrder = "CDSH"
        super hand, sortOrder
        $(@).addClass 'cardhand'

    @fromHand: (hand) ->
        return alloc @, hand


class PositionView extends HTMLDivElement
    constructor: (@hand, @position, useListHand) ->
        $(@).addClass 'position'
        $(@).addClass @cssClass()
        if useListHand
            @appendChild ListHandView.fromHand(@hand)
        else
            @appendChild CardHandView.fromHand(@hand)
        @appendChild HandStats.fromHand(@hand)

    cssClass: ->
        return {
            N: 'north',
            W: 'west',
            S: 'south',
            E: 'east',
        }[@position.name]

    @fromPositionAndHand: (position, hand, useListHand) ->
        return alloc @, hand, position, useListHand


class GridView extends HTMLTableElement
    constructor: (width, height) ->
        for rowIndex in [0...height]
            row = @insertRow(-1)
            for cellIndex in [0...width]
                row.insertCell(-1)
        # Do not call HTMLTableElement's constructor

    @createEmpty: (width, height) ->
        return alloc @, width, height


class PositionGrid extends GridView
    constructor: ->
        super 3, 3

    north: ->
        return @rows[0].cells[1]

    south: ->
        return @rows[2].cells[1]

    east: ->
        return @rows[1].cells[2]

    west: ->
        return @rows[1].cells[0]

    center: ->
        return @rows[1].cells[1]

    cellForPosition: (position) ->
        if position == model.Position.NORTH
            return @north()
        if position == model.Position.SOUTH
            return @south()
        if position == model.Position.EAST
            return @east()
        console.assert position == model.Position.WEST
        return @west()


class DealView extends PositionGrid
    createPositionView: (positionChar) ->
        position = model.Position.fromChar(positionChar)
        @appendChild PositionView.fromPositionAndHand position, @deal.handForPosition(position), true

    constructor: (@deal) ->
        @className = 'deal'
        super
        @setupView()

    setupView: ->
        @north().appendChild @createPositionView 'N'
        @west().appendChild @createPositionView 'W'
        @east().appendChild @createPositionView 'E'
        @south().appendChild @createPositionView 'S'
        @center().appendChild alloc PositionLabels

    @fromDeal: (deal) ->
        return alloc @, deal


class SuitCount extends HTMLSpanElement
    constructor: (@count) ->
        @className = 'suitcount'
        if count > 7
            @style.color = 'blue'
            @style.fontWeight = 'bold'
        @textContent = count

    @fromCount: (count) ->
        return alloc @, count


class PointCount extends HTMLSpanElement
    constructor: (@count) ->
        @className = 'pointcount'
        if count > 24
            @style.color = 'blue'
            @style.fontWeight = 'bold'
        @textContent = count

    @fromCount: (count) ->
        return alloc @, count


class PartnershipHandStats extends HTMLDivElement
    constructor: (@position, @deal) ->
        @partner = @position.partner()
        partnerShipName = @position.name + '-' + @partner.name
        @appendChild document.createTextNode partnerShipName + ': '
        count = @deal.handForPosition(@position).highCardPoints() + @deal.handForPosition(@partner).highCardPoints()
        @appendChild PointCount.fromCount(count)
        @appendChild document.createTextNode " hcp"

        for suit in model.Suit.SUITS
            count = @deal.handForPosition(@position).cardsInSuit(suit).length + @deal.handForPosition(@partner).cardsInSuit(suit).length
            @appendChild SuitCount.fromCount(count)
            @appendChild SuitView.fromSuit(suit)
            if suit != model.Suit.SPADES
                @appendChild document.createTextNode ','

    @fromPositionAndDeal: (position, deal) ->
        return alloc @, position, deal


class DealStats extends HTMLDivElement
    constructor: (@deal) ->
        @className = 'dealstats'
        @appendChild PartnershipHandStats.fromPositionAndDeal(model.Position.NORTH, @deal)
        @appendChild PartnershipHandStats.fromPositionAndDeal(model.Position.EAST, @deal)

    @fromDeal: (deal) ->
        return alloc @, deal


class BidLevel extends HTMLSpanElement
    constructor: (level) ->
        @className = 'level'
        @textContent = level

    @fromChar: (levelChar) ->
        return alloc @, levelChar


class CallCard extends HTMLTableCellElement
    constructor: (@call) ->
        @className = 'callcard'
        @appendChild CallView.fromCall(call, true)

    @fromCall: (call) ->
        return alloc @, call


class LevelRow extends HTMLTableRowElement
    constructor: (@level) ->
        @className = 'levelrow'
        for strain in model.Strain.STRAINS
            call = model.Call.fromString("" + @level + strain.name)
            @appendChild CallCard.fromCall(call)

    @fromLevel: (level) ->
        return alloc @, level


class SpecialLevelRow extends HTMLTableRowElement
    constructor: ->
        @className = 'specialbids'
        redoubleCard = CallCard.fromCall(model.Call.fromString('XX'))
        redoubleCard.id = 'redouble'
        redoubleCard.firstChild.textContent = 'X X'
        @appendChild redoubleCard
        passCard = CallCard.fromCall(model.Call.fromString('P'))
        passCard.id = 'pass'
        passCard.firstChild.textContent = 'P A S S'
        passCard.colSpan = "3"
        @appendChild passCard
        doubleCard = CallCard.fromCall(model.Call.fromString('X'))
        doubleCard.id = 'double'
        @appendChild doubleCard


class StatefulBiddingBox extends HTMLDivElement
    constructor: (@recordCall) ->
        @className = 'statefulbidder'
        @selectedLevel = null
        @history = null
        @setupView()

    _createBidButton: (text) ->
        button = document.createElement 'span'
        $(button).addClass 'bid'
        $(button).addClass 'button'
        if text
            button.textContent = text
        return button

    _createBidButtonWithChild: (child) ->
        button = @_createBidButton()
        button.appendChild child
        return button

    _createBidButtonFromCallName: (callName) ->
        call = model.Call.fromString(callName)
        callView = CallView.fromCall(call, true)
        return @_createBidButtonWithChild(callView)

    _createSpecialsTable: ->
        specialsTable = document.createElement 'table'
        specialsTable.className = 'specialstable'
        specialsRow = specialsTable.insertRow(-1)
        doubleCell = specialsRow.insertCell(-1)
        doubleCell.style.cssText = 'width: 20%'
        doubleCell.appendChild @_createBidButtonFromCallName('X')
        specialsRow.insertCell(-1).appendChild @_createBidButtonFromCallName('P')
        redoubleCell = specialsRow.insertCell(-1)
        redoubleCell.style.cssText = 'width: 20%'
        redoubleCell.appendChild @_createBidButtonFromCallName('XX')
        return specialsTable

    _createLevelsTable: ->
        levelsTable = document.createElement 'table'
        levelsTable.className = 'levelstable'
        levelRow = levelsTable.insertRow(-1)
        for level in [1..7]
            levelButton = @_createBidButton(level)
            levelRow.insertCell(-1).appendChild levelButton
        return levelsTable

    _createStrainsTable: ->
        strainsTable = document.createElement 'table'
        strainsTable.className = 'strainstable'
        strainRow = strainsTable.insertRow(-1)
        for strain in model.Strain.STRAINS
            strainButton =  @_createBidButtonWithChild StrainView.fromStrain(strain)
            strainCell = strainRow.insertCell(-1)
            if strain.name == 'NT'
                strainCell.colSpan = '2'
            strainCell.appendChild strainButton
        return strainsTable

    setupView: ->
        @appendChild @_createLevelsTable()
        @appendChild @_createStrainsTable()
        @appendChild @_createSpecialsTable()

    _shouldEnableLevelButton: (levelButton, history) ->
        lastBid = history.lastBid()
        if not lastBid
            return true
        level = parseInt(levelButton.textContent)
        if lastBid.strain.isNotrump()
            return level > lastBid.level
        return level >= lastBid.level

    _shouldEnableStrainButton: (strainButton, selectedLevel, history) ->
        lastBid = history.lastBid()
        if not lastBid
            return true
        if selectedLevel > lastBid.level
            return true
        return selectedLevel == lastBid.level and strainButton.lastChild.strain.index() > lastBid.strain.index()

    _firstAvailableLevel: (history) ->
        lastBid = history.lastBid()
        if not lastBid
            return 1
        if lastBid.strain.isNotrump()
            return lastBid.level + 1
        return lastBid.level

    _setDisabled: (button, disabled, onclick) ->
        $(button).toggleClass('disabled', disabled)
        button.onclick = onclick

    _selectLevel: (level) ->
        @selectedLevel = level
        for levelButton in $('.levelstable .button', @)
            $(levelButton).toggleClass('selected', level == parseInt(levelButton.textContent))

        for strainButton in $('.strainstable .button', @)
            strainView = strainButton.lastChild
            $(strainButton).empty()
            # strainButton.appendChild document.createTextNode level
            strainButton.appendChild strainView
            @_setDisabled strainButton, not @_shouldEnableStrainButton(strainButton, level, @history), (event) =>
                button = event.target
                while not $(button).hasClass('button')
                    button = button.parentNode
                strainView = button.lastChild
                @recordCall model.Call.fromString("" + level + strainView.strain.name)

    _shouldEnableSpecialCallButton: (specialButton, history) ->
        call = specialButton.firstChild.call
        if call.isPass()
            return true
        if call.isDouble()
            return history.canDouble()
        if call.isRedouble()
            return history.canRedouble()
        console.assert false

    updateFromCallHistory: (@history) ->
        for specialButton in $('.specialstable .button', @)
            @_setDisabled specialButton, not @_shouldEnableSpecialCallButton(specialButton, @history), (event) =>
                button = event.target
                while not $(button).hasClass('button')
                    button = button.parentNode
                callView = button.firstChild
                @recordCall callView.call

        for levelButton in $('.levelstable .button', @)
            @_setDisabled levelButton, not @_shouldEnableLevelButton(levelButton, @history), (event) =>
                @_selectLevel(parseInt(event.target.textContent))

        @_selectLevel @_firstAvailableLevel(@history)

    @fromHistoryAndCallFunction: (history, recordCall) ->
        box = alloc @, recordCall
        box.updateFromCallHistory(history)
        return box


class BiddingBox extends HTMLTableElement
    constructor: (@recordCall) ->
        @className = 'bidbox'
        @shouldShowAllLevels = false
        @setupView()
        @defaultLevelsToShow = 4

    _insertShowAllLevelsRow: ->
        row = @insertRow(-1)
        showAllLevelsCell = row.insertCell(-1)
        showAllLevelsCell.colSpan = '7'
        showAllLevelsLink = document.createElement 'a'
        showAllLevelsLink.href = '#'
        showAllLevelsLink.textContent = 'show all bids'
        $(showAllLevelsLink).click (event) =>
            @shouldShowAllLevels = true
            @_updateView()
            event.preventDefault()
        showAllLevelsCell.appendChild showAllLevelsLink

    setupView: ->
        @specialLevel = alloc SpecialLevelRow
        @appendChild @specialLevel
        @levels = (LevelRow.fromLevel(level) for level in [1..7])
        for level in @levels
            @appendChild level
        @showAllLevelsRow = @_insertShowAllLevelsRow()

        $('.callcard', @).bind 'click', (event) =>
            callCard = event.target
            while not $(callCard).hasClass('callcard')
                callCard = callCard.parentNode
            callView = $('.call', callCard)[0]
            @recordCall callView.call

    @fromHistoryAndCallFunction: (history, recordCall) ->
        box = alloc @, recordCall
        box.updateFromCallHistory(history)
        return box

    _setVisibility: (element, visible) ->
        visibilityString = if visible then 'visible' else 'hidden'
        $(element).css('visibility', visibilityString)

    _isPossibleCall: (call, history) ->
        if call.isPass()
            return true
        if call.isDouble()
            return history.canDouble()
        if call.isRedouble()
            return history.canRedouble()
        lastBid = history.lastBid()
        if not lastBid
            return true
        if call.level > lastBid.level
            return true
        return call.level == lastBid.level and call.strain.index() > lastBid.strain.index()

    _isPossibleLevel: (levelRow, history) ->
        lastBid = history.lastBid()
        if not lastBid
            return true
        if lastBid.strain.isNotrump()
            return levelRow.level > lastBid.level
        return levelRow.level >= lastBid.level

    _shouldShowLevel: (levelRow, history, shouldShowAllLevels) ->
        if shouldShowAllLevels
            return true
        lastBid = history.lastBid()
        lastBidLevel = if lastBid then lastBid.level else 0
        return levelRow.level - lastBidLevel <= @defaultLevelsToShow

    _updateView: ->
        lastBid = @cachedHistory.lastBid()
        lastBidLevel = if lastBid then lastBid.level else 0

        for card in $('.callcard', this)
            @_setVisibility(card, @_isPossibleCall(card.call, @cachedHistory))
        for levelRow in $('.levelrow', this)
            shouldShow = @_isPossibleLevel(levelRow, @cachedHistory) and @_shouldShowLevel(levelRow, @cachedHistory, @shouldShowAllLevels) 
            displayValue = if shouldShow then '' else 'none'
            $(levelRow).css('display', displayValue)

        showAllLevelsLink = (lastBidLevel + @defaultLevelsToShow < 7) and not @shouldShowAllLevels
        $(@showAllLevelsRow).toggle(showAllLevelsLink)

    updateFromCallHistory: (history) ->
        @cachedHistory = history
        @_updateView()


class ContractView extends HTMLSpanElement
    constructor: (@contract) ->
        @setupView()

    setupView: ->
        @appendChild BidLevel.fromChar(@contract.level)
        @appendChild document.createTextNode " "
        @appendChild StrainView.fromStrain(@contract.strain)
        @appendChild document.createTextNode " "
        @appendChild document.createTextNode @contract.name[2..]

    @fromContract: (contract) ->
        return alloc @, contract


class ContractAndDeclarerView extends HTMLSpanElement
    constructor: (@callHistory) ->
        @className = 'result'
        if @callHistory.isPassOut()
            @textContent = 'Pass Out'
        else
            @appendChild ContractView.fromContract(callHistory.contract())
            @appendChild document.createTextNode " "
            @appendChild document.createTextNode callHistory.declarer().name

    @fromHistory: (callHistory) ->
        return alloc @, callHistory


class CallView extends HTMLSpanElement
    _displayNameForCall: (call) ->
        if call.isPass()
            return 'Pass'
        # FIXME: We probably should use 'Dbl' instead of X in the history table.
        # if call.isDouble()
        #     return 'Dbl'
        # if call.isRedouble()
        #     return 'Rdbl'
        return call.name

    constructor: (@call, includeSpace) ->
        @className = 'call'
        if @call.isBid()
            @appendChild BidLevel.fromChar(@call.level)
            if includeSpace
                @appendChild document.createTextNode " "
            @appendChild StrainView.fromStrain(@call.strain)
        else
            @textContent = @_displayNameForCall(@call)

    @fromCall: (call, includeSpace) ->
        return alloc @, call, includeSpace


class ExploreLink extends HTMLAnchorElement
    constructor: (calls) ->
        @className = 'explore'
        calls = calls.slice()  # So that we don't modify the array we're passed in.
        @lastCall = calls.pop()
        @previousCalls = calls
        @appendChild CallView.fromCall(@lastCall)
        @href = '/explore/' + (call.name for call in @previousCalls).join(",")

    @fromPartialHistory: (calls) ->
        return alloc @, calls


class InlineCallHistory extends HTMLDivElement
    constructor: (@callHistory) ->
        @className = 'history'
        lastIndex = @callHistory.calls.length - 1
        if @callHistory.isComplete() and not @callHistory.isPassOut()
            # Ignore the last 3 passes if we're showing a complete history.
            lastIndex -= 3
        for index in [0..lastIndex]
            partialHistory = @callHistory.calls[..index]
            @appendChild ExploreLink.fromPartialHistory(partialHistory)
            @appendChild document.createTextNode " "

    @fromHistory: (callHistory) ->
        return alloc @, callHistory


class ConstraintsView extends HTMLDivElement
    constructor: (@constraintsString) ->
        @setupView()

    setupView: ->
        # FIXME: This is a huge hack because we don't have a constraint object yet.
        # FIXME: Maybe this logic belongs on the server instead?
        constraintsString = @constraintsString
        if not constraintsString
            return
        replacements = [
            [/2o3/g, "at least two of the top three honors"],
            [/3o5/g, "at least three of the top five honors"],
            [/3rS/g, "at least a third-round stopper"],
            [/4rS/g, "at least a fourth-round stopper"],
            ["aces(1)", "1 ace"],
            ["aces(2)", "2 aces"],
            ["aces(3)", "3 aces"],
            ["aces(0 or 4)", "0 or 4 aces"],
            ["kings(1)", "1 king"],
            ["kings(2)", "2 kings"],
            ["kings(3)", "3 kings"],
            ["kings(0 or 4)", "0 or 4 kings"],
        ]
        for [needle, substitution] in replacements
            constraintsString = constraintsString.replace(needle, substitution)
        @appendChild StrainView.fragmentReplacingStrainChars(constraintsString)

    @fromConstraintsString: (constraintsString) ->
        return alloc @, constraintsString


class RuleName extends HTMLDivElement
    constructor: (@ruleName) ->
        @className = 'rule_name'
        @ruleName = @ruleName.replace(/([1-9A-Z])/g, " $1")
        # A couple exceptions to the spacing rules:
        @ruleName = @ruleName.replace(/R H O/g, "RHO")
        @ruleName = @ruleName.replace(/L H O/g, "LHO")
        @ruleName = @ruleName.replace(/\sN$/g, "NT")
        @textContent = @ruleName

    @fromRuleName: (ruleName) ->
        return alloc @, ruleName


class RuleExplanation extends HTMLDivElement
    constructor: (@interpretation) ->
        @setupView()

    setupView: ->
        if @interpretation.ruleName
            @appendChild RuleName.fromRuleName @interpretation.ruleName
        else
            @textContent = "Sorry! I don't know what that bid means."

        @appendChild ConstraintsView.fromConstraintsString @interpretation.constraintsString

        if @interpretation.explanation
            explanationPara = document.createElement 'p'
            explanationPara.textContent = @interpretation.explanation
            @appendChild explanationPara

    @fromInterpretation: (interpretation) ->
        return alloc @, interpretation


class BidInterpretationView extends HTMLDivElement
    constructor: (@board, @calls) ->
        @setupView()

    setupView: ->
        # Could show score for highlighed contract?
        # Does it include doubles?  What happens when you click on a double?
        ruleDiv = document.createElement 'div'
        ruleDiv.textContent = "Interpreting bids... "
        ruleDiv.appendChild WaitingImage.new()
        @appendChild ruleDiv

        controller.BidInterpreter.interpretLastCallInCallsFromBoard @calls, @board, (calls, interpretation) =>
            $(ruleDiv).empty()
            ruleDiv.appendChild RuleExplanation.fromInterpretation(interpretation)

        exploreLink = ExploreLink.fromPartialHistory @calls
        exploreLink.textContent = "open in bid explorer"
        @appendChild exploreLink

    @fromBoardAndCalls: (board, calls) ->
        return alloc @, board, calls


class CallButton extends HTMLButtonElement
    constructor: (@call) ->
        $(@).addClass('bid_button')
        @.appendChild CallView.fromCall(@call)

    @fromCall: (call) ->
        return alloc @, call


class CallExplorerTable extends HTMLTableElement
    constructor: (@callHistory) ->
        @className = 'explore_table'
        @setupView()

    _rowForCall: (call) ->
        for row in @rows
            if row.cells[0].textContent == 'Bid'
                continue
            if row.cells[0].firstChild.firstChild.call.name == call.name
                return row

    setupView: ->
        headerRow = @insertRow(-1)
        headerRow.insertCell(-1).textContent = "Bid"
        headerRow.insertCell(-1).textContent = "Rule"
        headerRow.insertCell(-1).textContent = "Pri."
        headerRow.insertCell(-1).textContent = "Resulting Knowledge"

        board = new model.Board(1) # This is a hack, we just want a non-vuln board to display.
        for possibleCall in @callHistory.possibleNextCalls()
            callRow = @insertRow(-1)
            callRow.insertCell(-1).appendChild CallButton.fromCall(possibleCall)
            callRow.insertCell(-1).appendChild WaitingImage.new()
            callRow.insertCell(-1).appendChild WaitingImage.new()
            callRow.insertCell(-1).appendChild WaitingImage.new()

            calls = @callHistory.calls.slice()
            calls.push possibleCall
            # FIXME: Need to figure out how to bind callRow and then delete _rowForCall.
            controller.BidInterpreter.interpretLastCallInCallsFromBoard calls, board, (calls, interpretation) =>
                row = @_rowForCall(calls[calls.length - 1])
                row.cells[1].textContent = if interpretation.ruleName then interpretation.ruleName else ""
                row.cells[2].textContent = if interpretation.rulePriority then interpretation.ruleName else ""
                row.cells[3].textContent = ""
                row.cells[3].appendChild StrainView.fragmentReplacingStrainChars(interpretation.constraintsString)

    @fromCallHistory: (callHistory) ->
        return alloc @, callHistory


class CallHistoryTable extends HTMLTableElement
    constructor: (@board, @callHistory, @showLoadingSpinner) ->
        @className = 'history'
        @positionsInDisplayOrder = [
            model.Position.WEST,
            model.Position.NORTH,
            model.Position.EAST,
            model.Position.SOUTH
        ]
        @setupView()

    updateFromCallHistory: (@callHistory, @showLoadingSpinner) ->
        @hideHelp()
        $(@).empty()
        @setupView()

    setupView: ->
        headerRow = @insertRow(-1)
        for position in @positionsInDisplayOrder
            positionHeader = document.createElement('th')
            headerRow.appendChild(positionHeader)
            positionHeader.textContent = position.displayName()
            vulnerabilityClass = if @board.vulnerability.isVulnerable(position) then 'vulnerable' else  'nonvulnerable'
            positionHeader.className = vulnerabilityClass

        # FIXME: This would probably be cleaner using a biddingRounds() and callForRound() like bidhistory.py uses.
        firstRow = @insertRow(-1)
        for position in @positionsInDisplayOrder
            if position.index() == @board.dealer.index()
                break
            firstRow.insertCell(-1)  # Add empty cells for all players before the dealer.

        firstDisplayPositionIndex = @positionsInDisplayOrder[0].index()
        currentRow = firstRow
        biddingComplete = @callHistory.isComplete()
        for call, callIndex in @callHistory.calls
            positionIndex = (@board.dealer.index() + callIndex) % model.Position.POSITIONS.length
            if positionIndex == firstDisplayPositionIndex and callIndex != 0
                currentRow = @insertRow(-1)
            partialHistory = @callHistory.calls[0..callIndex]
            currentCell = currentRow.insertCell(-1)
            currentCell.appendChild ExploreLink.fromPartialHistory(partialHistory)

            # FIXME: This should be keyed off of some sort of debug flag.
            if window.location.hostname.indexOf('localhost') != -1
                # Useful for finding None bids:
                interpretation = controller.BidInterpreter.cachedInterpretationForLastCallInCallsFromBoard(partialHistory, @board)
                if interpretation and not interpretation.ruleName
                    # FIXME: This should be a class on the ExploreLink?
                    currentCell.style.backgroundColor = 'orange'

        if not biddingComplete
            if @callHistory.lastToCall() and @callHistory.lastToCall().index() == model.Position.WEST.index()
                currentRow = @insertRow(-1)
            currentCell = currentRow.insertCell(-1)
            if @showLoadingSpinner
                currentCell.appendChild WaitingImage.new()
            else
                currentCell.textContent = '?'

        # This is a big hack:
        $('a', this).bind 'click', (event) =>
            event.preventDefault()
            callCell = event.target
            while callCell and callCell.tagName != 'TD'
                callCell = callCell.parentNode
            if @highlightedCell == callCell
                @hideHelp()
            else
                @showHelpForCallCell(callCell)

        $('a', this).each (index, link) =>
            # If we don't do this, then MobileSafari will show the naviagation bar on every link click.
            link.href = '#'

    hideHelp: ->
        $('.highlighted', this).removeClass('highlighted')
        $('.helprow', this).remove()
        @highlightedCell = null

    addHelpRowBelowCallCell: (callCell) ->
        callView = $('.call', callCell)[0]
        currentRow = callCell.parentNode

        helpRow = document.createElement 'tr'
        helpRow.className = 'helprow'
        helpCell = helpRow.insertCell(-1)
        helpCell.colSpan = '4'

        oldExploreLink = $('.explore', callCell)[0]
        calls = oldExploreLink.previousCalls.concat [oldExploreLink.lastCall]

        helpCell.appendChild BidInterpretationView.fromBoardAndCalls @board, calls

        $(currentRow).after helpRow

    showHelpForCallCell: (callCell) ->
        @hideHelp()
        @addHelpRowBelowCallCell(callCell)
        $(callCell).addClass('highlighted')
        @highlightedCell = callCell

    @fromBoardAndHistory: (board, callHistory, showLoadingSpinner) ->
        return alloc @, board, callHistory, showLoadingSpinner


class SuggestBidBox extends HTMLDivElement
    constructor: (@roundController)->
        @className = 'suggestbid'
        @hideSuggestion()

    createSuggestLink: ->
        suggestLink = document.createElement 'div'
        $(suggestLink).addClass('suggest')
        $(suggestLink).addClass('button')
        suggestLink.href = '#'
        suggestLink.textContent = 'suggest bid'
        return suggestLink

    hideSuggestion: ->
        @shouldShowAutobid = false
        @updateView()

    updateView: ->
        $(@).empty()
        if not @shouldShowAutobid
            @suggestLink = @createSuggestLink()
            $(@suggestLink).bind 'click', (event) =>
                event.preventDefault()
                @shouldShowAutobid = true
                @updateView()
            @appendChild @suggestLink
        else
            @textContent = 'Autobidder says: '
            if @roundController.autobidContinuation
                nextCallIndex = @roundController.round.callHistory.calls.length
                nextCall = @roundController.autobidContinuation.calls[nextCallIndex]
                calls = @roundController.round.callHistory.calls.slice()
                calls.push nextCall
                interpretation = controller.BidInterpreter.cachedInterpretationForLastCallInCallsFromBoard(calls, @roundController.round.board)
                if not interpretation.ruleName
                    @appendChild document.createTextNode "Sorry, I don't know!"
                else
                    @appendChild CallView.fromCall(nextCall)
                    @appendChild document.createElement 'hr'
                    @appendChild RuleExplanation.fromInterpretation(interpretation)
            else
                @appendChild WaitingImage.new()
                @roundController.requestAutobidContinuation =>
                    @updateView()

    @fromRoundController: (roundController)->
        return alloc @, roundController


class AutobidResult extends HTMLDivElement
    constructor: (@roundController)->
        @className = 'autobidresult'
        @setupView()

    setupView: ->
        if not @roundController.fullAutobid
            @roundController.requestFullAutobid (fullAutobid) =>
                @setupView()
            # Empty until we have something to say.
            $(@).css('visibility', 'hidden')
            @textContent = 'empty'
            return

        $(@).css('visibility', '')
        if @roundController.fullAutobid.callsString() == @roundController.round.callHistory.callsString()
            @style.color = 'green'
            @textContent = '\u2713 matches autobidder'
            if window._gaq
                window._gaq.push ['_trackEvent', 'Bidding', 'Result', 'matched autobidder']
        else
            @textContent = 'Autobidder: '
            @showTableLink = document.createElement 'a'
            @showTableLink.href = '#'
            $(@showTableLink).bind 'click', (event) =>
                event.preventDefault()
                $(@showTableLink).replaceWith CallHistoryTable.fromBoardAndHistory @roundController.round.board, @roundController.fullAutobid
                # FIXME: Should walk through each cell and compare it to the actual table, highlighting any difference (or maybe just the first?)
            @showTableLink.appendChild ContractAndDeclarerView.fromHistory(@roundController.fullAutobid)
            @appendChild @showTableLink
            if window._gaq
                window._gaq.push ['_trackEvent', 'Bidding', 'Result', 'differed from autobidder']


    @fromRoundController: (roundController) ->
        return alloc @, roundController


class TrickView extends PositionGrid
    constructor: (@trick, @nextToPlay) ->
        @className = 'trick'
        super
        @setupView()

    # This may belong somewhere else.
    arrowForPosition: (position) ->
        return {
            W: '\u2190',
            N: '\u2191',
            E: '\u2192',
            S: '\u2193',
        }[position.name]

    setupView: ->
        for positionChar in "NWES"
            position = model.Position.fromChar(positionChar)
            card = if @trick then @trick.cardPlayedBy(position) else null
            positionCell = @cellForPosition(position)
            if card
                positionCell.appendChild CardView.fromCard(card)
            if position == @nextToPlay
                # Should show a spinner when it's the bot?
                positionCell.appendChild document.createTextNode @arrowForPosition(position)

    @fromTrick: (trick, nextToPlay) ->
        return alloc @, trick, nextToPlay


class LastTrickView extends HTMLDivElement
    constructor: (@playHistory) ->
        @updateView()

    updateView: ->
        $(@).empty()
        lastTrick = @playHistory.previousTrick()
        if not lastTrick
            return
        @textContent = 'Last Trick:'
        @trickView = TrickView.fromTrick(lastTrick)
        @appendChild @trickView

    @fromPlayHistory: (playHistory) ->
        alloc @, playHistory


class PositionLabels extends PositionGrid
    constructor: ->
        @className = 'positionlabels'
        super
        @setupView()

    setupView: ->
        @north().textContent = 'N'
        @west().textContent = 'W'
        @east().textContent = 'E'
        @south().textContent = 'S'


# FIXME: I don't think this wants to be a PositionGrid long term, as top/bottom hand display will be different from sides.
class PlayTable extends PositionGrid
    # Includes:
    # current trick (playHistory)
    # dummy's hand (deal)
    # player's hand (player, deal)
    # turned cards as score (maybe)

    constructor: (@player, @deal, @playHistory) ->
        @className = 'playtable'
        super
        @updateView()
        @shouldShowAllHands = false

    showAllHands: ->
        @shouldShowAllHands = true
        @updateView()

    _showHand: (position) ->
        positionCell = @cellForPosition(position)
        $(positionCell).empty()
        positionCell.appendChild PositionView.fromPositionAndHand(position, @deal.handForPosition(position))

    _visiblePositions: ->
        if @shouldShowAllHands
            return model.Position.POSITIONS

        dummy = @playHistory.dummy()
        if @player == dummy
            visibleHands = [@player.partner()]
        else
            visibleHands = [@player]
        # We only show the dummy if visible.  Currently, even if it's our hand.
        if @playHistory.isDummyVisible()
            visibleHands.push dummy
        return visibleHands

    updateView: ->
        $(@center()).empty()
        @center().appendChild TrickView.fromTrick(@playHistory.currentTrick(), @playHistory.nextToPlay())
        for position in @_visiblePositions()
            @_showHand(position)

    @fromRound: (round) ->
        player = model.Position.SOUTH # FIXME: We probably shouldn't assume south is the player.
        return alloc @, player, round.board.deal, round.playHistory


class TrickCounts extends HTMLDivElement
    constructor: (@playHistory) ->
        @setupView()

    setupView: ->
        @northSouthCount = document.createElement 'span'
        @eastWestCount = document.createElement 'span'
        @appendChild document.createTextNode 'Us: '
        @appendChild @northSouthCount
        @appendChild document.createTextNode ' Them: '
        @appendChild @eastWestCount
        @updateView()

    updateView: ->
        # FIXME: Could highlight once  made the contract, or known to be down?
        @northSouthCount.textContent = @playHistory.tricksTakenByPartnershipOf model.Position.NORTH
        @eastWestCount.textContent = @playHistory.tricksTakenByPartnershipOf model.Position.EAST

    @fromPlayHistory: (playHistory) ->
        return alloc @, playHistory


class PlayStats extends HTMLDivElement
    # Current Trick Count
    # Contract
    # Link to History?
    # Link to score?
    # value of current contract?

    constructor: (@round) ->
        @setupView()

    setupView: ->
        @contractDiv = document.createElement 'div'
        @contractDiv.textContent = 'Contract: '
        @contractDiv.appendChild ContractAndDeclarerView.fromHistory @round.callHistory
        @appendChild @contractDiv

        @trickCounts = TrickCounts.fromPlayHistory @round.playHistory
        @appendChild @trickCounts

    updateView: ->
        @trickCounts.updateView()

    @fromRound: (round) ->
        return alloc @, round


class DebugInfo extends HTMLDivElement
    constructor: (@round) ->
        @className = 'debuginfo'
        clickToShowLink = document.createElement 'a'
        clickToShowLink.textContent = 'show unittests'
        clickToShowLink.href = '#'
        $(clickToShowLink).bind 'click', (event) =>
            event.preventDefault()
            $(@).empty()
            @appendChild RoundUnittests.fromRound @round
        @appendChild clickToShowLink

    @fromRound: (round) ->
        return alloc @, round


class RoundUnittests extends HTMLCodeElement
    unittestForPosition: (position) ->
        lastCall = @round.callHistory.lastCallByPosition position
        historyString = (call.name for call in @round.callHistory.callsUpToLastCallByPosition(position)).join(' ')
        vulnerability = @round.board.vulnerability.name()
        hand = @round.board.deal.handForPosition position

        unittestString = "['" + hand.pbnString() + "', '" + lastCall.name + "', '" + historyString
        if vulnerability != 'None'
            unittestString += "', '" + vulnerability
        unittestString += "'],  # " + @round.board.identifier() + ", " + position.name

        return unittestString

    constructor: (@round) ->
        @className = 'unittests'
        @setupView()

    setupView: ->
        lines = []
        lines.push "# board " + @round.board.identifier()
        for position in model.Position.POSITIONS
            lines.push @unittestForPosition position
        @textContent = lines.join('\n')

    @fromRound: (round) ->
        return alloc @, round


class ScoreDetail extends HTMLTableElement
    _addRow: (explanation, score) ->
        if score == 0
            return
        row = @insertRow(-1)
        scoreCell = row.insertCell(-1)
        scoreCell.className = 'score'
        scoreCell.textContent = score
        row.insertCell(-1).textContent = explanation
        return row

    constructor: (@contract, @vulnerable, @contractOffset) ->
        @className = 'scoredetail'
        @setupView()

    setupView: ->
        calc = controller.ScoreCalculator

        if @contractOffset >= 0
            contractPoints = calc.contractPoints(@contract)
            @_addRow("Contract", contractPoints)
            vulnerablePrefix = if @vulnerable then "Vul " else ""
            if contractPoints < 100
                levelBonusLabel = "Partscore"
            else if @contract.isSmallSlam()
                levelBonusLabel = vulnerablePrefix + "Small Slam"
            else if @contract.isGrandSlam()
                levelBonusLabel = vulnerablePrefix + "Grand Slam"
            else
                levelBonusLabel = vulnerablePrefix + "Game Bonus"
            @_addRow(levelBonusLabel, calc.levelBonus(@contract, @vulnerable))
            doubleLabel = if @contract.isRedoubled() then "Redouble Bonus" else "Double Bonus"
            @_addRow(doubleLabel, calc.doubleBonus(@contract))
            overtrickMultiplier = calc.overtrickMultiplier(@contract, @vulnerable)
            overtricksLabel = "Overtricks (" + @contractOffset + " \u00D7 " + overtrickMultiplier + ")"
            @_addRow(overtricksLabel, calc.overtrickBonus(@contractOffset, @contract, @vulnerable))
        else
            for undertrickNumber in [1..-@contractOffset]
                @_addRow("Undertrick #" + undertrickNumber, -calc.penaltyForUndertrick(@contract, @vulnerable, undertrickNumber))

        totalRow = @_addRow("Total", calc.scoreFor(@contract, @vulnerable, @contractOffset))
        totalRow.className = 'total'

    @fromResultTuple: (contract, vulnerable, contractOffset) ->
        return alloc @, contract, vulnerable, contractOffset


class ScoreView extends HTMLDivElement
    constructor: (round) ->


    @fromRound: (round) ->
        return alloc @, round


class TrickList extends HTMLTableElement
    constructor: (@playHistory) ->
        @className = 'tricklist'
        @setupView()

    appendRowForTrick: (trick) ->
        trickRow = @insertRow(-1)
        for position in model.Position.POSITIONS
            playedCardCell = trickRow.insertCell(-1)
            playedCard = trick.cards[position.index()]
            cardView = CardView.fromCard(playedCard)
            $(cardView).removeClass 'card'  # This is a hack
            if position == trick.leader
                $(cardView).addClass 'lead'
            if position == trick.winner()
                $(cardView).addClass 'winner'
            playedCardCell.appendChild cardView

    setupView: ->
        headerRow = @insertRow(-1)
        for position in model.Position.POSITIONS
            positionLableCell = headerRow.insertCell(-1)
            positionLableCell.textContent = position.displayName()

        for trick in @playHistory.tricks
            @appendRowForTrick trick

    @fromPlayHistory: (playHistory) ->
        return alloc @, playHistory


class CallInterpretation extends HTMLDivElement
    constructor: (@interpretation) ->
        @className = 'call_interpretation'
        @setupView()

    setupView: ->
        console.log @interpretation
        if @interpretation.constraintsString and @interpretation.ruleName
            @appendChild RuleExplanation.fromInterpretation @interpretation
        else
            @textContent = '\u2014' # &emdash;

    @from: (interpretation) ->
        return alloc @, interpretation


class CallDescription extends HTMLTableRowElement
    constructor: (@call) ->
        @className = 'call_description'
        @setupView()

    setupView: ->
        @insertCell(-1).appendChild StrainView.fragmentReplacingStrainChars(@call.name)
        @interpretationCell = @insertCell(-1)

    didDetermineInterpretation: (@interpretation) ->
        @interpretationCell.appendChild CallInterpretation.from(@interpretation)

    @fromCall: (call) ->
        return alloc @, call


class CallMenu extends HTMLTableElement
    constructor: (@callHistory) ->
        @className = 'call_menu'
        @setupView()

    _rowForCall: (callName) ->
        for row in @rows
            if row.call.name == callName
                return row

    setupView: ->
        for possibleCall in @callHistory.possibleNextCalls()
            @appendChild CallDescription.fromCall possibleCall
        board = new model.Board(1) # This is a hack, we just want a non-vuln board to display.
        controller.BidInterpreter.interpretNextCallsFromCallsAndBoard @callHistory.calls, board, (interpretations) =>
            @classList.add 'ready'
            for interpretation in interpretations
                row = @_rowForCall interpretation.callName
                row.didDetermineInterpretation interpretation

    @fromCallHistory: (callHistory) ->
        return alloc @, callHistory



window.view = window.view or {}
view = window.view
view.AutobidResult = AutobidResult
view.BiddingBox = BiddingBox
view.BiddingHandView = BiddingHandView
view.CallExplorerTable = CallExplorerTable
view.CallHistoryTable = CallHistoryTable
view.CallMenu = CallMenu
view.CallView = CallView
view.CardHandView = CardHandView
view.ContractAndDeclarerView = ContractAndDeclarerView
view.ContractView = ContractView
view.DealStats = DealStats
view.DealView = DealView
view.DebugInfo = DebugInfo
view.GridView = GridView
view.HandView = HandView
view.InlineCallHistory = InlineCallHistory
view.LastTrickView = LastTrickView
view.PlayStats = PlayStats
view.PlayTable = PlayTable
view.RoundUnittests = RoundUnittests
view.ScoreDetail = ScoreDetail
view.ScoreView = ScoreView
view.StrainView = StrainView
view.StatefulBiddingBox = StatefulBiddingBox
view.SuggestBidBox = SuggestBidBox
view.TrickList = TrickList
view.TrickView = TrickView

